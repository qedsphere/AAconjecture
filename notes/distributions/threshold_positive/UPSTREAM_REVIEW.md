# Audit of upstream Task 1 against the full-AA theory

Reviewed 2026-11-14. Source: [`tasks-1-2-3-summary.md`](../../../tasks-1-2-3-summary.md), introduced by sharedwork commit `d5e4297` (`openmath-results`). The additional proof logs and scratch files listed by that summary are not present in this checkout. Therefore its **[PROJECT]** claims retain that status; they are not promoted to independently proved results here. No existing theorem text was changed by this review.

## Effect on our results

**The local-posterior, bounded-block, forest, and feedback-set proofs remain intact. General Dobrushin full AA remains open.** The upstream document principally studies flip-influence AA; our primary target is acceptance simulation with a single polynomial query bound in quantum queries and inverse error.

| Upstream result/status | Consequence for this investigation |
|---|---|
| **[OPEN]** full Dobrushin influence AA; simultaneous bounded low-degree junta; conditional path domination | No completed high-temperature theorem can be imported. These gaps support our decision to state the Dobrushin query-simulation assertion as a conjecture. |
| **[PROJECT]** fixed-degree/selected Ising regimes and mean-field results | Useful proxy evidence only, with every stated restriction retained. The summary provides no posterior source oracle or hereditary reveal-progress theorem. |
| **[FALSE/WITHDRAWN]** claimed O'Donnell–Zhao general-measure MLSI junta theorem | Must not be used. I independently checked the [primary text](https://arxiv.org/html/1512.01603v1): Corollary 3.5 concerns uniform Boolean inputs and an exponentially small influence hypothesis; Corollary 3.6 is a uniform Fourier-tail/junta result. Neither is a correlated-measure MLSI theorem. |
| **[PROVED]** star degree growth and nonlocal-gradient examples | Rule out particular influence-proof shortcuts. They do not refute our forest simulation, which implements actual quantum oracle queries and never assumes polynomial degree is preserved by a heat-bath semigroup. |
| **[PROVED]** joint-endpoint functional TV estimate | A narrow comparison under its specified source coupling. It does not supply the full-input-conditional mismatch bound or query-local posterior oracle used in our transfer proposition. |
| **[CONDITIONAL]** cumulant/MGF route; **[OPEN]** Q4 and derivative variants | Potential analytic programs, not established bridges to either polynomial-degree influence AA or full simulation. No part of our new positive proof imports them. |

The copy-triple counterexample is consistent with our arbitrary-block theorem. Majority has zero flip influences on `{000,111}`, while the actual block label is read with one coordinate query. Our full-AA block theorem makes no claim about flip influences or a single-site Glauber gap. Likewise, the upstream statement that general-degree 1D influence AA remains conditional is compatible with our independently proved full-AA simulation theorem for all Ising forests.

## Quantifiers that cannot be suppressed

Task 1A permits both the prefactor `c` and variance exponent `C` to depend arbitrarily on degree `d`. A result

$$
\max_i\operatorname{Inf}_i(p)\ge c(d)\operatorname{Var}(p)^{C(d)}
$$

is dimension-uniform **at each fixed degree**. It is weaker than a bound with polynomial dependence on degree and degree-independent exponents. Substituting `d = 2T` can give costs such as `exp(T)` or `(1/e)^{C(2T)}`, neither a polynomial in `(T,1/e)`. For correlated inputs, a separate bridge from influences to information revealed under pinnings is also required.

The weak-DFKO cutoff calculation in Task 1A is correct. Since `|p-Ep|≤1`, the normalized polynomial `f=(p-Ep)/sqrt(v)` satisfies `|f|≤1/sqrt(v)`. Applying the proposed implication at `t=2/sqrt(v)` gives

$$
\max_i\operatorname{Inf}_i(p)>
\frac{v^2}{4}\eta_0(2/\sqrt v).
$$

If `eta_0(t)≥c t^{-A}`, this is `c 2^{-A-2} v^{2+A/2}`. To obtain the polynomial-degree AA target, one must additionally control how `c` and `A` depend on `d`; the displayed cutoff does not do so. An exponentially small threshold in `t²` gives a nonpolynomial variance bound, as upstream correctly warns.

Upstream also fixes bounded degree, range, fields, and a conditional-probability margin, allowing constants to depend on those parameters. Our proposed pair-Ising conjecture is uniform over external fields and graph degrees at fixed Dobrushin contraction margin. Even a successful theorem with the upstream quantifiers would not automatically prove that stronger uniformity. Our forest theorem obtains its field uniformity directly from the kernel-column ratio bound, not from a field-independent Glauber inequality.

## Independently checked counterexamples worth retaining

1. **Degree growth already within Dobrushin.** On the three-leaf Ising star, with `u=tanh(beta)`, the cubic coefficient is
   $$
   c_3=\frac{\tanh(3\beta)-3\tanh\beta}{4}
       =-\frac{2u^3}{1+3u^2}.
   $$
   At `beta=0.2`, `c3≈-0.0137691`, while the usual Dobrushin upper bound is `3u≈0.592126<1`. Thus conditional expectation and heat-bath evolution can increase multilinear degree even in a strict high-temperature regime. The three-path is not this counterexample.
2. **Interaction locality does not localize arbitrary polynomial gradients.** On uniform `{0,1}` bits, `p=x_i x_j` gives `(p(x)-p(x^i))²=x_j`. If `j` lies outside the proposed local region, its best local mean-square approximation has error `1/4`. This refutes localization around `i`, not comparison on the actual small support `{j}`. Our posterior oracle localizes hidden edge randomness, not arbitrary gradients.
3. **A legal global-support example.** For `p=x_0 (sum_{j≠0}x_j)/(n-1)`, direct expectation gives `Var(p)=1/16+1/[8(n-1)]`, and the squared gradient at zero depends on all other coordinates. The variance was checked by exact enumeration for `n=2,5,10`. Large exact support alone does not establish a fixed local-approximation error; the distant monomial is the appropriate example for that stronger claim.
4. **Influence-error accounting.** If the flip Radon–Nikodym ratio is bounded by `C_RN`, then `(a-b)²≤2a²+2b²` and a change of variables give `E(Delta_i(p-q))²≤2(1+C_RN)||p-q||²_2`. The variance error is at most `4||p-q||_2` for `[0,1]`-valued functions. The distinction between an error and its square root is real. The supplied GMNR text independently confirms the pointwise bound `sum_i(Delta_i p)²≤4d²`; that global budget does not imply gradient locality.

## Two source formulas requiring correction or their missing proof

**Biased-product norm example: the stated witness is insufficient.** For the upstream choice `f=1+n^{-1}sum_i y_i`, the squared-norm ratio tends to `9/4`; that does not refute the existence of an arbitrary dimension-independent comparison constant. A valid bounded degree-one replacement is

$$
g_n=n^{-1}\sum_i y_i,\quad
\mathbb E_U g_n^2=1/n,\quad
\mathbb E_{\mathrm{Ber}(3/4)^{\otimes n}}g_n^2
=1/4+3/(4n).
$$

The ratio is `(n+3)/4`, which diverges. This repairs the intended warning about comparing uncentered moments across measures with different means. The map `g_n` is globally bounded in `[-1,1]`.

**The reported [PROJECT] two-bit bound has suspect atom-probability dependence.** As printed, `max Inf ≥ c delta_min^{-6} Var^8/d^12` cannot hold with a fixed positive `c` independent of the block law. Take

$$
\lambda(00)=\lambda(11)=(1-2a)/2,
\qquad\lambda(01)=\lambda(10)=a,
\qquad0<a<1/4.
$$

For `p=x_1`, `d=1`, `Var(p)=1/4`, `max Inf=1`, and `delta_min=a`. The claimed right side diverges as `a→0`. Preserve the source's **[PROJECT]** label and request its exact proof/parameter convention before quoting this formula; neither the inverse power nor a replacement positive power is imported here. This issue has no bearing on our atom-independent **query-simulation** theorem.

One further scope caution: a bounded covariance-row-sum argument cannot by itself establish a critical-tree endpoint. On a free zero-field `b`-ary tree, the root covariance contribution from level `ell` is proportional to `(b tanh(beta))^ell`; at `beta=artanh(1/b)` its sum grows with the tree depth. This does not refute an independently proved critical degree-one AA statement, but that upstream **[PROJECT]** endpoint needs an argument beyond a uniform susceptibility bound. No sharp full-AA threshold should be inferred from it.

## Recommended incorporation

Retain our four positive theorems and the open Dobrushin conjecture. Add the star and far-monomial warnings to the proof-obstruction discussion, explicitly distinguish fixed-degree evidence from a polynomial-degree theorem, and retain all upstream status labels. The concrete remaining positive task is still a conditional posterior-access construction or uniform reveal progress under pinnings; neither the withdrawn MLSI citation nor a marginal coding-tail estimate supplies it.
