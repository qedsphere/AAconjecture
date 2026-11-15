# Prompt: continue polynomial-influence AA research for Gibbs measures

You are continuing an existing mathematical research project in the same workspace. Do not restart from scratch, do not assume the main theorem is already proved, and do not treat earlier agent reports as authoritative without re-deriving them.

## Required reading first

Read these files before doing new research:

1. `results/polynomial-aa-research-handoff.md` — consolidated theorem inventory, proof sketches, obstructions and current priorities.
2. `.ultramath/smwh6ji5o/REVIEWED-LITERATURE.md` — exact accepted hypotheses, corrections and source conventions.
3. The source corresponding to your assigned direction:
   - `.ultramath/smwh6ji5o/m3/polynomial_AA_Gibbs_derivative_route.md` and `.ultramath/smwh8cksq/m1/replacement-A.md` for the default priority below;
   - `.ultramath/smwh84hiq/m1/weighted-routing-gibbs.md` for the (WA) alternative;
   - `.ultramath/smwh89pww/m1/manuscript.md` for conditional product decompositions;
   - `.ultramath/smwh8a9it/m2/main.md` for the accepted fixed-support theorem.

Only afterwards choose a new artifact or numerical experiment. Do not modify a proof while you are still checking it; put new work in a clearly named new directory or file under `results/`.

## The actual open problem

Let

$$H(x)=-\sum_{|A|\ge2}J_A\chi_A(x)-\sum_i h_ix_i,
\qquad \mu_\beta(x)=e^{-\beta H(x)}/Z,
\qquad \chi_A(x)=\prod_{i\in A}x_i,$$

and define

$$\omega=\beta\max_i\sum_{A\ni i,\ |A|\ge2}(|A|-1)|J_A|,
\qquad \Lambda=\max_i\beta|h_i|.$$

The general target is an $n$-independent function $S(v,d)>0$ such that, in an explicitly stated high-temperature regime such as $\omega\le1/8$, every real-valued multilinear $p$ with

$$\deg p\le d,\qquad \|p\|_\infty\le1,\qquad \operatorname{Var}_{\mu_\beta}(p)\ge v$$

satisfies

$$\max_i\operatorname{Inf}^{\mathrm{fl}}_i(p)\ge S(v,d).$$

Unless deliberately studying a restricted class, allow arbitrary field strengths, interaction arities and coordinate-support sizes. The central unresolved case is degree $d\ge2$ with unrestricted support. Do not silently replace it by Boolean-valued $p$, bounded support, bounded hitting number, or a resampling influence.

## Conventions you must preserve

For $\partial_i p=(p(+1,x_{-i})-p(-1,x_{-i}))/2$ and $\theta_i=\mu(x_i=1\mid x_{-i})$,

$$\operatorname{Inf}^{\mathrm{fl}}_i(p)
=4\mathbb E_\mu[(\partial_i p)^2],$$

$$\operatorname{Inf}^{\mathrm{pv}}_i(p)
=4\mathbb E_\mu[\theta_i(1-\theta_i)(\partial_i p)^2],$$

$$\operatorname{Inf}^{\mathrm{rs2}}_i(p)
=2\operatorname{Inf}^{\mathrm{pv}}_i(p)
=8\mathbb E_\mu[\theta_i(1-\theta_i)(\partial_i p)^2].$$

Hence $\operatorname{Inf}^{\mathrm{fl}}\ge4\operatorname{Inf}^{\mathrm{pv}}
=2\operatorname{Inf}^{\mathrm{rs2}}$. A fourth, TV/pivotal resampling notion appears in the alphabet work and must not be confused with squared-difference resampling.

## What is already accepted

- Every product measure with arbitrary biases, including degenerate coordinates, has an $n$-free polynomial AA theorem. There are two accepted proofs: a facial weighted-all-pairs argument and a live/dry-coordinate argument.
- Degree one has the sharp sufficient bound
  $$\max_i\operatorname{Inf}^{\mathrm{fl}}_i(p)
  \ge4\operatorname{Var}(p)^2/\Lambda(\mu)^2.$$
  At $\omega\le1/8$, $\alpha\le2\omega\le1/4$ gives $\Lambda\le5/3$.
- **Important correction:** the earlier iff claim about sequences has a normalization gap and is **not accepted**. If $L=\sum_i|a_i|$, the argument gives $L^2\ge N$ and $\operatorname{Var}(p)\ge N/L^2$, not $\operatorname{Var}(p)\ge1$. Do not assert necessity.
- Zero-field degree-two centred-Gram control holds: for Dobrushin $r<1$,
  $$\operatorname{Var}(p)
  \le\frac{\max\{2\Lambda_1,1\}}{1-r}\sum_S\widehat p(S)^2,$$
  hence $\Lambda_2\le32/9$ at $\omega\le1/8$. This is auxiliary, not yet AA.
- AA is proved for fixed-coordinate-support polynomials and for bounded hitting sets/star forests, with explicit constants.
- AA is also proved under bounded total strength, finite interaction budgets, and for product-alphabet/block-product classes.
- The five-coordinate pentagon gives $S(v,2)\le16v^2/9$ at $v=3/4$. This is an upper extremal example, not an optimal lower-bound theorem.

The general target remains open. All four derivation swarms have completed their scoped assignments; do not relaunch them merely to repeat those results.

## Default priority: prove or refute m3's base inequality (B) at zero-field degree $2$

This is the narrowest remaining input in one accepted conditional route. Start here unless you have a concrete reason to choose another direction.

Investigate whether there is an $n$-independent $\lambda_0>0$ such that, for every zero-field Gibbs measure in the $\omega\le1/8$ regime and every multilinear $q$ with $\deg q\le2$ and $\|q\|_\infty\le1$,

$$\boxed{\widehat q(\emptyset)^2
\le\lambda_0^{-1}\|q\|_{L^2(\mu)}^2.}\tag{B}$$

The low-degree centred-Gram theorem above now supplies the other auxiliary input (H2c). Under (H1), (H2c) and (B), m3 gives

$$\max_i\operatorname{Inf}^{\mathrm{pv}}_i(p)
\ge\lambda_0c^2
\left(\frac{v}{\Lambda C_2^{4/3}}\right)^3.$$

The flip lower bound follows by multiplying by $4$.

**Required caution:** $\mathbb E_\mu q$ and $\widehat q(\emptyset)$ are means under different measures. They cannot be identified except where separately proved.

Begin with exact small cases (independent Ising pairs and short cycles). Determine whether (B) is true in the whole zero-field class or only a subclass. Seek either:

- an explicit $n$-independent $\lambda_0$ with a full proof; or
- a family demonstrating that no such uniform constant exists, with exact variance, coefficient, sup-norm and $\omega$ calculations.

If you establish (B), write the composed theorem explicitly and state every remaining hypothesis. If you only reduce it to another property, do not report a solution.

## Alternative directions if (B) is resistant

Choose at most one initially and explain why it is not just a renamed earlier reduction.

### A. General Gibbs weighted all-pairs (WA) or CI-avg

Prove an $n$-uniform (WA) or CI-avg constant at $\omega\le1/8$. The accepted chain makes either sufficient for all-degree AA. The relevant proof must use an averaged estimate: subcube-uniform pair-weight distortions grow exponentially in extensive models. Avoid a mere Hamming-distance routing ratio or a global bijection requirement; actual routing is per pair with a facial constraint.

### B. One-sided marginal-product $L^2$ domination $(H_d)$

Investigate whether, for $\nu=\bigotimes_i\mu_i$,

$$\mathbb E_\mu[q^2]\le A_d\mathbb E_\nu[q^2]$$

uniformly in $n$ for $\deg q\le d$ and $\deg q\le d-1$. This would transfer arbitrary-product AA through a different mechanism. A two-sided variance bridge is refuted, but the one-sided statement is not automatically excluded.

### C. Conditional product decompositions beyond bounded hitting number

Try to extend the accepted hitting-set argument. A useful extension needs multiple environments/cut sets **and** a valid max-versus-average selection argument. Simply making many independent blocks reintroduces the selection problem and proves nothing by itself.

## Obstructions you must check before proposing a proof

Do not repeat these failed approaches or quote them as AA counterexamples:

- Uniform centred Gram at $d\ge3$ is false inside $\omega\le1/8$ for independent Ising pair blocks, with ratio $(1-r^2)+r^2(m-1)\to\infty$. It does not refute AA.
- The unrestricted degree-two centred-Gram statement fails with nonzero fields, even for biased products.
- Global Gibbs-to-product density ratios generally lose $e^{-\Theta(n)}$. Support-local marginals are a different matter.
- Bounded conditional odds and full support alone do not imply AA. The hidden-field witnesses have $\omega=\Theta(n)$, so they do not refute $\omega\le1/8$.
- Posterior history symbols conditional only on the final physical configuration are not product. Complete-trajectory independence does not repair this.
- Naive history composition can lose a factor $n$ in variance error and make the degree grow with $n$.
- Unordered dependent-measure Efron–Stein is false.
- The global atom floor $\min_x\mu(x)$ is at most $2^{-n}$. Do not confuse it with a local conditional-odds floor.
- Do not treat query-AA simulation as polynomial-influence AA.
- Do not use the withdrawn arXiv:1911.03748 as a theorem source.

Use arXiv:2611.11626 for the uniform-cube AA exposition. Use arXiv:2611.09773 only after checking the exact theorem at its point of use. BDST's antipodal routing constant is $1/2$, and the downstream routing constant is $1/4$, not14.

## Required standards for any theorem

For every statement you write, specify:

1. The Hamiltonian family, fields, weighted-strength/Dobrushin hypothesis, and any support or vertex-cover restriction.
2. The influence convention and every conversion factor.
3. The precise quantifier order: $v,d$ and model parameters fixed before $n$; the final bound independent of $n$.
4. Every imported theorem, exact source, hypotheses and normalization, and why those assumptions hold at the point of use.
5. Which terms are proved, imported assumptions, heuristic arguments or numerical evidence.
6. A check against pair-block and biased-product obstructions and against degenerate fields/coordinates when relevant.

Do not call a result Lean-ready unless you actually formalize and compile it in Lean. Numerical checks support proofs but never replace them.

## Useful reproducible inputs and commands

Use the existing scripts before implementing new ones:

```bash
python3 .ultramath/smwh8cksq/m1/lvl2b.py
python3 .ultramath/smwh8cksq/m1/probe2.py
python3 .ultramath/smwh84hiq/m1/scripts/wa_tables.py
python3 .ultramath/smwh84hiq/m1/scripts/t17.py
python3 .ultramath/smwh89pww/m1/numerics6.py
python3 .ultramath/smwh8a9it/m2/verify.py
python3 .ultramath/smwh8a9it/m1/verify_degree2.py
python3 .ultramath/smwh6nmpu/m2/work/check_m3_thm31.py
python3 .ultramath/smwh6ji5o/m1/scripts/sym_check.py
```

The CI-avg constants already corrected in m1 are
$\kappa=c_0\sigma^2/(16F^2)$, resampling denominator $2^{18}F^6$, and flip denominator $2^{17}F^6$. The worst-case threshold maximum is $\sigma^3/432$ at $\eta=\sigma/12$; its nonvacuity boundary is $\sqrt{3456}$, not64. The hybrid statement in the corrected query proof is $4T\sqrt\gamma$.

## Deliverable

Create a new technical report under `results/` with:

- an honest status line distinguishing proved results, conditional reductions, open gaps and numerical evidence;
- a self-contained statement and proof, or a sharply delimited obstruction with exact calculations;
- a comparison against the accepted special cases and a statement of what actually remains open;
- executable verification scripts where computationally useful, run with their outputs recorded;
- a short appendix listing every source you actually used.

Do not merely restate the reductions in `results/polynomial-aa-research-handoff.md`. Seek one new piece of rigorous progress: (B), a counterexample to it, a uniform (WA)/CI-avg input, a one-sided $(H_d)$ estimate, or a correctly expanded conditional product theorem.
