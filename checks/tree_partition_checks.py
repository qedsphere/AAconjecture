"""Finite checks for the bag-forest simulation argument; standard library only.

These check identities and constructions, not the dimension-uniform
simulation theorem. Run: python3 checks/tree_partition_checks.py
"""

from collections import Counter, defaultdict
from decimal import Decimal as D, getcontext
from itertools import product
from math import log, cosh
from random import Random

RNG = Random(20261114)
getcontext().prec = 70
TOL = D("1e-45")


def exp(x):
    return D(str(x)).exp()


def kernel(rows, cols, bound):
    weights = [exp(RNG.uniform(-9, 9)) for _ in range(cols)]
    phi = [[D(str(RNG.uniform(-bound, bound))) for _ in range(cols)] for _ in range(rows)]
    result = []
    for values in phi:
        unnormalized = [w*exp(-v) for w, v in zip(weights, values)]
        total = sum(unnormalized)
        result.append([v/total for v in unnormalized])
    return result


def common_part(k):
    m = [min(row[t] for row in k) for t in range(len(k[0]))]
    q = sum(m)
    assert 0 < q <= 1 + TOL
    return m, q


def check_kernels():
    count = 0
    for rows, cols, bound in product((2, 4, 8), (2, 4, 8), (0.02, 0.4, 2.0)):
        for _ in range(5):
            k = kernel(rows, cols, bound)
            m, q = common_part(k)
            floor = exp(-4*bound)
            assert q >= floor-TOL
            residual = [[(v-m[t])/(1-q) for t, v in enumerate(row)] for row in k]
            for row, res in zip(k, residual):
                assert min(res) >= -TOL
                assert abs(sum(res)-1) < TOL
                for t, value in enumerate(row):
                    assert abs(m[t]+(1-q)*res[t]-value) < TOL
                    assert m[t]/value >= floor-TOL
                    posterior_copy = 1-m[t]/value
                    assert -TOL <= posterior_copy <= 1-floor+TOL
                    # Bayes weights for reset and residual branches.
                    assert abs((1-posterior_copy)*value-m[t]) < TOL
            count += 1
    return count


def source_symbols(k):
    """Discard unused randomness: emit (branch, map table, prior mass)."""
    rows, cols = len(k), len(k[0])
    m, q = common_part(k)
    out = [(0, (t,)*rows, m[t]) for t in range(cols)]
    residual = [[(v-m[t])/(1-q) for t, v in enumerate(row)] for row in k]
    for table in product(range(cols), repeat=rows):
        weight = 1-q
        for s, t in enumerate(table):
            weight *= residual[s][t]
        if weight > 0:
            out.append((1, table, weight))
    assert abs(sum(weight for _, _, weight in out)-1) < TOL
    return out


def check_joint_posteriors():
    # Three bags of sizes 1, 2, 1: state spaces 2 -> 4 -> 2.
    # Enumerate the entire independent-source space and its pushforward.
    k1, k2 = kernel(2, 4, 0.6), kernel(4, 2, 0.8)
    z1, z2 = source_symbols(k1), source_symbols(k2)
    root = (D("0.37"), D("0.63"))
    mass, joint = defaultdict(D), defaultdict(lambda: defaultdict(D))
    for s, i, j in product(range(2), range(len(z1)), range(len(z2))):
        c1, a1, p1 = z1[i]
        c2, a2, p2 = z2[j]
        t = a1[s]
        u = a2[t]
        prob = root[s]*p1*p2
        mass[s, t, u] += prob
        joint[s, t, u][i, j] += prob
    for x in product(range(2), range(4), range(2)):
        s, t, u = x
        expected = root[s]*k1[s][t]*k2[t][u]
        assert abs(mass[x]-expected) < TOL
        active = [D(0), D(0)]
        both_active = D(0)
        for i, j in product(range(len(z1)), range(len(z2))):
            c1, a1, p1 = z1[i]
            c2, a2, p2 = z2[j]
            posterior = joint[x].get((i, j), D(0))/expected
            factor = (p1/k1[s][t] if a1[s] == t else D(0))
            factor *= (p2/k2[t][u] if a2[t] == u else D(0))
            assert abs(posterior-factor) < TOL
            active[0] += c1*posterior
            active[1] += c2*posterior
            both_active += c1*c2*posterior
        m1, _ = common_part(k1)
        m2, _ = common_part(k2)
        assert abs(active[0]-(1-m1[t]/k1[s][t])) < TOL
        assert abs(active[1]-(1-m2[u]/k2[t][u])) < TOL
        assert abs(both_active-active[0]*active[1]) < TOL
        assert both_active <= (1-exp(-4*0.6))*(1-exp(-4*0.8))+TOL
    return len(mass)


def check_cactus_partitions():
    for _ in range(100):
        bags, assignment = [{0}], {0: 0}
        edges, bag_parent = [], {}
        n = 1
        for _ in range(40):
            attachment = RNG.randrange(n)
            if RNG.random() < 0.3:
                edges.append((attachment, n))
                child = len(bags)
                bags.append({n})
                assignment[n] = child
                bag_parent[child] = assignment[attachment]
                n += 1
            else:
                length = RNG.randrange(3, 25)
                fresh = list(range(n, n+length-1))
                n += length-1
                cycle = [attachment]+fresh
                edges.extend(zip(cycle, cycle[1:]+cycle[:1]))
                parent = assignment[attachment]
                lo, hi = 0, len(fresh)-1
                while lo <= hi:
                    bag = {fresh[lo], fresh[hi]}
                    child = len(bags)
                    bags.append(bag)
                    bag_parent[child] = parent
                    for v in bag:
                        assert v not in assignment
                        assignment[v] = child
                    parent = child
                    lo, hi = lo+1, hi-1
        assert len(assignment) == n
        assert max(map(len, bags)) <= 2
        interfaces = Counter()
        for u, v in edges:
            a, b = assignment[u], assignment[v]
            if a != b:
                assert bag_parent.get(a) == b or bag_parent.get(b) == a
                interfaces[tuple(sorted((a, b)))] += 1
        assert max(interfaces.values(), default=0) <= 2
        assert len(interfaces) == len(bags)-1
        assert all(parent < child for child, parent in bag_parent.items())
    return 100


def check_failure_boundary():
    def gain(t):
        return (4*log(cosh(2*t))-log(cosh(4*t)))/2
    lo, hi = 0.0, 1.0
    for _ in range(70):
        mid = (lo+hi)/2
        if gain(mid) < log(2)/32:
            lo = mid
        else:
            hi = mid
    root = (lo+hi)/2
    assert abs(gain(root)-log(2)/32) < 1e-14
    return root


if __name__ == "__main__":
    print(f"PASS: {check_kernels()} finite-state transition kernels")
    print(f"PASS: exact-source enumeration, posterior factorization at {check_joint_posteriors()} outputs")
    print(f"PASS: {check_cactus_partitions()} cactus partitions, each with 40 added blocks")
    print(f"Pairwise gadget sufficient failure boundary beta*j = {check_failure_boundary():.10f}")
