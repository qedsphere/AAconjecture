# Audit of the Tasks 1–3 handoff

Reviewed 2026-11-14: [`tasks-1-2-3-summary.md`](../../../tasks-1-2-3-summary.md), supplied in commit `d5e4297`. This is an audit of the handoff and its implications for the full acceptance-simulation target. The older proof files listed at the end of that handoff are not present in this checkout, so its `[PROJECT]` labels are not promoted to independently verified theorems here. No upstream file was modified.

The most consequential findings are:

1. The stated summed-$(b')$ LP is already feasible **if the supplied established BDST antipodal-routing theorem is used**. The outstanding task is a determinant-free proof, not feasibility or the existence of a counterexample to this exact statement.
2. A literal extension of this LP from counting measure to a Gibbs-preserving transport is false even for a single biased independent bit. That is a failure of a proof mechanism, while biased-product full AA holds.
3. Several asserted counterexamples or reductions are overstated: the displayed biased-product example does not refute an arbitrary constant-factor comparison; the inverse power of the least atom probability cannot be correct with a law-independent prefactor; Boolean degree does not imply $d^2\ge n$; and uniform influences do add across homogeneous Fourier levels.
4. The valid star/localization counterexamples constrain influence-transfer approaches, while leaving our query-access approach intact. Their underlying input laws can satisfy full AA.

## 1. Targets and quantifiers must remain distinct

**Source claim.** Task 1 seeks an influence bound with constants and an exponent allowed to depend on the polynomial degree $d$.

**Verified qualification.** Such a statement can be dimension independent at each fixed degree without being polynomial AA uniformly in degree. For example, $c_d=e^{-d^2}$ or a variance exponent growing with $d$ does not provide a fixed polynomial in $(d,1/v)$. Full acceptance simulation requires a fixed polynomial in quantum query count $T$ and inverse accuracy; $d\le2T$ does not fix this quantifier issue. The hereditary restriction/reveal argument must also be supplied when the law is correlated.

**Verified calculation.** The weak-DFKO cutoff arithmetic is correct. For $p\in[0,1]$, $f=(p-\mathbb Ep)/\sqrt v$ has $|f|\le1/\sqrt v$, so its tail is zero at $t=2/\sqrt v$. Contraposition of the stated implication yields

$$
 \max_i\operatorname{Inf}_i(p)>
 \frac{v^2}{4}\eta_0(2/\sqrt v).
$$

A polynomial lower bound on $\eta_0$ gives a polynomial in $v$; an exponentially small threshold does not. The degree dependence of its constants and exponent still matters.

The handoff's Curie–Weiss threshold $\beta=1$ concerns **influence AA**. It is not a full-AA threshold: our existing exchangeable-simulation theorem covers Curie–Weiss at all temperatures. Likewise, a degree-one result cannot establish the location of the threshold for all bounded polynomials or for quantum acceptance simulation.

## 2. Counterexamples and elementary formulas independently checked

### 2.1 Valid structural counterexamples

The following calculations are sound in their stated conventions.

- **Star degree growth.** On the zero-field three-leaf Ising star,
  $$
  \tanh(\beta(x_1+x_2+x_3))
   =c_1(x_1+x_2+x_3)+c_3x_1x_2x_3,
  \qquad c_3=\frac{\tanh(3\beta)-3\tanh\beta}{4}.
  $$
  Evaluating at $(1,1,1)$ and $(1,1,-1)$ proves the coefficient formula. It is nonzero for $\beta>0$. Thus ordinary multilinear degree need not be preserved by heat-bath generators or conditional expectation. On a zero-field path with at most two neighbours, the corresponding odd conditional-mean function is affine; the stated path correction is valid.
- **Far monomial.** On the uniform $\{0,1\}$ cube, $p=x_ix_j$ gives $(p(x)-p(x^i))^2=x_j$. If $j$ is outside the permitted local sigma-field, the optimal mean-square prediction is $1/2$, with error $1/4$. This refutes localization around $i$ even under independence. It does not refute comparison on the actual support $\{j\}$, nor any classical query bound: two queries evaluate $p$ exactly.
- **Bounded global gradient.** For $p=x_0(n-1)^{-1}\sum_{j\ne0}x_j$, independence gives $\operatorname{Var}(p)=1/16+1/[8(n-1)]$ as stated. The gradient has exact support on all remaining coordinates. Exact support size is not an approximation lower bound: this particular averaged gradient concentrates and can be approximated by a constant with error tending to zero.
- **Duplicate-pair average.** Each $x_{2j-1}x_{2j}$ is Bernoulli with parameter $1/4$. Therefore $v=3/(16m)$, maximum unnormalized flip influence $1/(2m^2)$, and their ratio $8/(3m)$ are correct. This rules out a linear-in-variance bound, not polynomial AA; the influence is a constant multiple of $v^2$.
- **Three-copy block.** Under the law on $\{000,111\}$, majority has variance $1/4$ and is unchanged by every single flip starting from either support point. The influence counterexample is valid. Exact two-copy blocks instead have intersecting closed neighbourhoods, preventing a flat nonconstant block observable. Single-site heat-bath nevertheless has zero gap for the exact-copy law; it is a different quadratic form.
- **Influence error ledger.** For $r=p-q$ and $\mu(x^i)/\mu(x)\le C_{\rm RN}$,
  $$
  \mathbb E_\mu(\Delta_i r)^2
   \le2\mathbb E_\mu r(x)^2+2\mathbb E_\mu r(x^i)^2
   \le2(1+C_{\rm RN})\|r\|_{2,\mu}^2.
  $$
  The stated variance-error bound follows from Cauchy–Schwarz and boundedness. Squared approximation errors must not be substituted for their square roots.

**Direct full-AA implication.** Independent three-copy blocks still admit full acceptance simulation: encode every block by one independent fair latent bit, simulate a physical quantum query by querying that latent bit, and answer each classical latent-bit query by reading one physical representative. The failure of physical single-flip influences therefore does not obstruct full AA. This example also explains why the full-support hypothesis of an influence transfer theorem cannot be dropped merely because bounded-size block laws are query-simulable.

### 2.2 The displayed mean-square counterexample is too weak, but a correct one is immediate

**Source claim.** With $\Pr_\mu(Y_i=1)=3/4$ and $f=1+n^{-1}\sum_iY_i$, the limit $\|f\|_{2,\mu}^2\to9/4$ versus $\|f\|_{2,U}^2\to1$ refutes $\|f\|_{2,\mu}\le C\|f\|_{2,U}$.

**Correction.** That example only refutes $C<3/2$ asymptotically. It does not refute an arbitrary fixed constant $C$.

**Independently verified repair.** Take $f=M=n^{-1}\sum_iY_i$, a globally bounded degree-one polynomial. Then

$$
 \|M\|_{2,U}^2=1/n,
 \qquad \|M\|_{2,\mu}^2=1/4+3/(4n).
$$

The norm ratio diverges like $\sqrt n/2$. If a nonnegative bounded polynomial is required, $M^2\in[0,1]$ is degree two after multilinearization; $\mathbb E_U M^4=3/n^2-2/n^3$ while $\mathbb E_\mu M^4\to1/16$, giving another divergent ratio.

Even requiring the **observable's** first moment to agree does not save a universal comparison. For $k=n-2$ let

$$
 F=\frac{Y_1-Y_2}{2}\cdot\frac1k\sum_{j=3}^nY_j.
$$

It is bounded by one, has degree two, and has mean zero under both laws, but

$$
 \mathbb E_UF^2=\frac1{2k},
 \qquad\mathbb E_\mu F^2=\frac3{32}+\frac9{32k}.
$$

This does not address a different hypothesis requiring the **underlying distributions' coordinate means** to match. All these laws are product laws with full AA; their failure of a global low-degree norm comparison is a proof-method limitation.

### 2.3 The inverse least-atom factor cannot have the displayed meaning

**Source claim.** A two-bit-block theorem is reported as
$\max\operatorname{Inf}\ge c\,\delta_{\min}^{-6}v^8/d^{12}$.

**Countercheck.** On one two-bit block put

$$
 \lambda(00)=\lambda(11)=\delta,
 \qquad\lambda(01)=\lambda(10)=1/2-\delta,
 \qquad0<\delta<1/4.
$$

For $p=x_1$, $d=1$, $v=1/4$, and maximum unnormalized flip influence is exactly $1$. The asserted right side is $c\delta^{-6}4^{-8}$, which diverges as $\delta\downarrow0$. Thus the formula is false with a positive prefactor $c$ independent of the block law. A positive power of $\delta_{\min}$, an unstated dependence of $c$, or a different definition may have been intended; the exact theorem must be recovered before reuse.

### 2.4 Other scope warnings

The finite-row covariance argument does not itself cover critical susceptibility divergence. In particular, on a free zero-field $b$-ary tree with $\tanh\beta=1/b$, the root-to-level-$\ell$ sum of signed-spin covariances is $b^\ell(1/b)^\ell=1$, so the row sum grows with height. A critical degree-one result may still hold with another argument or a larger variance exponent, but it cannot be inferred from an $n$-uniform row bound that fails there. The analogous warning applies to critical two-dimensional Ising; this audit does not verify the handoff's claimed critical theorem or its boundary conditions.

Similarly, finite flatness at one mean-field minimum is not enough unless the other minima and their weights are controlled: two separated minima can retain macroscopic variance. The usual Curie–Weiss Landau expansion near $\beta=1+a$ is $-am^2/2+m^4/12+\cdots$, whose well depth is of order $a^2$. Its thermal crossover is governed by $na^2$. The handoff's separate $n\gg a^{-3/2}$ statement therefore needs an identified method-specific quantity and cannot be treated as the general finite-size thermal window.

## 3. Task 2: what the transportation problem does and does not leave open

### 3.1 The exact uniform-counting LP is feasible by the supplied determinant theorem

**Source statement.** Task 2 asks for a doubly stochastic $M$ on $A\times A$, supported on $y_i\ne x_i$ for all $i\in T(x)$, whose weighted number of coordinate agreements is at most $\sum_iw_iE_i$, where $E_i=|\{x\in A:x^i\notin A\}|$.

**Deduction from the supplied source, not a new determinant-free proof.** The accepted [Blanc–Docter–Strassle–Tan exposition](https://arxiv.org/abs/2611.11626), Lemma 3.1 and its determinant proof, yields a permutation $\pi$ of $A$ with that support condition and

$$
 \#\{x:\pi(x)_i=x_i\}\le E_i\quad\text{for every }i.
$$

The exposition explicitly notes in §2.5.4 that its proof produces a permutation. Set $M_{xy}=\mathbf1[y=\pi(x)]$. It is doubly stochastic and, for every positive weight vector, satisfies the summed inequality immediately. Thus a counterexample to the **exact stated LP** would contradict the theorem already imported into this project. What remains open in Task 2 is a proof or construction **avoiding the determinant machinery**. This audit supplies no such new construction.

Conversely, the handoff's Birkhoff implication is sound. If a supported doubly stochastic $M$ has the required average cost, its decomposition consists of supported permutations: a forbidden entry of zero cannot receive positive mass from any nonnegative component. At least one component has cost no greater than the average. This only extracts a permutation **after** an appropriate $M$ has been supplied.

The one-dimensional counterexample to the proposed wings induction is valid. Boundary submodularity is also valid: for each undirected coordinate edge, the indicator that it crosses a set is a submodular cut function, and summing gives the displayed inequality. Neither fact yields the desired new construction. Hall/support feasibility by itself controls no weighted cost.

### 3.2 A literal Gibbs-preserving extension is false already for one biased bit

**Independently verified obstruction to a natural extension, not to the stated uniform LP.** Suppose one replaces uniform row/column masses by $\mu_A$, retaining hard face support and the same zero-boundary cost requirement. Take $A=\{0,1\}$, $T(0)=T(1)=\{1\}$, and $\mu(0)=p\ne1/2$. Both faces are valid. Support forces the only possible coupling to swap $0$ and $1$:

$$
 \gamma(0,1)=p,\qquad\gamma(1,0)=1-p.
$$

Its second marginal is $(1-p,p)$, not $(p,1-p)$. No coupling preserving both Gibbs marginals exists. Even with empty faces, $A$ is the full one-bit cube so boundary mass is zero, and zero agreement cost again forces that swap.

Hence uniform-counting antipodal routing cannot be converted to a nonuniform Gibbs theorem merely by inserting Gibbs masses. This obstruction occurs for an independent external-field Hamiltonian at arbitrarily high finite temperature, although biased-product full AA holds. It cannot indicate an AA transition.

A successful nonuniform influence route would have to modify the target coupling, endpoint marginals, costs, or source representation; alternatively it can encode the product/reference law and transfer through that representation. A bound on each local likelihood ratio is not enough to make a long routing path cost dimension independent: multiplying a fixed bound over a path of length proportional to $n$ can lose an exponential factor. Our query-access and one-sided likelihood theorems avoid asserting such a transport.

### 3.3 Boolean degree does not make uniform certificates cheap

**Source claim.** Boolean-valued functions permit a uniform-certificate route because $d^2\ge n$.

**Explicit correction.** The addressing function on $m$ address bits $a$ and $2^m$ data bits $(y_s)$ is

$$
 f(a,y)=\sum_{s\in\{0,1\}^m}y_s
 \prod_{j:s_j=1}a_j\prod_{j:s_j=0}(1-a_j).
$$

It is Boolean, all $n=m+2^m$ variables are relevant, and its exact real multilinear degree is $d=m+1$. Thus $d^2\ll n$. At every input, flipping the selected data bit changes the value, so an equal-weight fractional certificate must give every coordinate weight at least one and has cost at least $n$. There may be cheap **nonuniform** certificates, but the claimed general uniform-certificate shortcut is false. This is consistent with the logarithmic degree-versus-relevant-variable scale in [Nisan–Szegedy](https://web.vu.lt/mif/s.jukna/boolean/Nisan-Szegedy.pdf).

## 4. Task 3 corrections relevant to the theory

### 4.1 Uniform influence is additive across homogeneous levels

**Source claim.** For $p=\sum_kp_k$ under uniform Boolean input, influence of the sum need not equal the sum of influences across homogeneous Fourier levels.

**Correction by orthogonality.** With normalized signed-cube derivatives,

$$
 I_i^U(p)=\sum_{S\ni i}\widehat p(S)^2
          =\sum_k I_i^U(p_k),
 \qquad \operatorname{Var}_U(p)=\sum_{k\ge1}\|p_k\|_2^2.
$$

Unnormalized flip influences multiply every term by four and preserve the identity. The alleged cancellation is absent. On a correlated law the cross terms need not vanish, but that is not Task 3's uniform setting. Applying a homogeneous fcb theorem to $p_k$ instead needs control of the **correct degree-indexed fcb norm of that component**; this cannot be assumed merely from the norm of $p$.

### 4.2 The ordinary polynomial-AA fcb target is subsumed by the accepted uniform theorem

[Escudero Gutiérrez's primary paper](https://ir.cwi.nl/pub/33545/33545.pdf), Proposition 2.3, gives $\|p\|_\infty\le\|p\|_{\mathrm{fcb},d}$. Its Conjecture 1.5 is therefore a restricted version of ordinary uniform AA. The normalization $\|p\|_{\mathrm{fcb},d}\le1$ is **stronger**, not weaker, than sup-norm boundedness; the resulting conjecture is weaker because it quantifies over fewer polynomials.

Accordingly, under the established uniform-AA theorem already imported throughout our dossier, the exact polynomial-in-$(\operatorname{Var},1/d)$ target stated in Task 3 follows immediately, including nonhomogeneous polynomials. A direct fcb proof, the degree-free $\operatorname{Var}^2$ strengthening, or the paper's specific operator construction are separate questions. The 2023 paper's open status should not be carried forward unchanged into a project accepting the November 2026 general theorem. No fractional-certificate lemma is supplied by this observation.

## 5. Remaining analytic gaps are method gaps, not thermal counterexamples

The warnings about unsupported MLSI junta citations, semigroup degree growth, clipping, simultaneous approximation under two laws, and the direction of $\max_i\mathbb E$ versus $\mathbb E\max_i$ are valid constraints. They explain why a low-degree influence-transfer proof requires more than a rapid-mixing estimate. Our forest and finite-species full-AA theorems do not assume those false steps; they use query simulation of the observed input through a reference law or posterior representation.

There is an additional caution about the handoff's conditional cumulant discussion. Its bound

$$
 |\kappa_q(f)|/q!\le(Cdq)^{C'dq}I^{q/2-1}
$$

does **not by direct summation** justify an analytic log-MGF expansion on a fixed interval: for fixed positive $I$, the majorant's $q$th root grows like $q^{C'd}\sqrt I$, so that majorant series has zero radius of convergence. A quantitative truncated-cumulant/moderate-deviation theorem or a separate remainder control is required. Such cumulant hypotheses may support a different valid moderate-deviation argument; this audit does not claim they are impossible or that every conditional route fails. The displayed simple exponential-tilt step is not proved by the displayed inequalities alone.

The practical implications for our threshold program are therefore precise:

- Keep full acceptance simulation, hereditary reveal progress, and physical flip influence as separate targets.
- Treat degree-dependent junta/DFKO estimates as proxies until the dependence is polynomial uniformly in degree and the restriction argument is justified.
- Localize **the information needed to answer queries**, not the physical support of every derivative polynomial.
- Do not identify the breakdown of a transport, moment, or cluster-counting proof with an AA threshold.
- An actual negative threshold still requires a dimension-dependent classical query lower bound at an error scale that cannot ignore the hard sector. The noisy-code and arbitrary-weight theorems in this chapter supply that requirement; the star, copy-block, and far-monomial witnesses alone do not.

These conclusions incorporate the valid new upstream constraints without promoting its unverified historical claims or reusing the corrected statements above.

## Addendum: proof companion received in commit `9312412`

On 2026-11-14, a focused follow-up reviewed [`tasks-1-2-3-proof-companion.md`](../../../tasks-1-2-3-proof-companion.md), added by upstream commit `9312412`. The preceding audit remains a historical review of `d5e4297`; this addendum records what the companion repairs and what remains unsupported. It is not a line-by-line validation of all 627 lines or of the scripts cited there.

**Corrections now acknowledged.** The companion explicitly repairs homogeneous Fourier influence additivity; changes the reported two-bit-block prefactor from $\delta_{\min}^{-6}$ to $\delta_{\min}^{6}$; withdraws the claimed every-distribution $v/(2n^2)$ floor; and distinguishes a covariance operator-norm conclusion from an absolute covariance row-sum conclusion. Its new full-support comparison lemma

$$
 \max_i\operatorname{Inf}_i^\mu(f)\ge\frac{4a}{bn}\operatorname{Var}_\mu(f),
 \qquad a=2^n\min\mu,\quad b=2^n\max\mu,
$$

is correct by uniform Poincaré and density comparison. It also properly leaves the full two-bit-block theorem, the claimed degree-two 2D-Ising result, and older small-coupling results outside its independently validated ledger. These repairs should replace the corresponding historical errors when summarizing the current upstream status.

**Curie–Weiss polynomial dependence is still not repaired by that floor.** In companion §2.4, the cutoff $N=N(\beta,d,v)$ depends on the variance and degree. The floor below $N$ contains $a_\beta(N)/b_\beta(N)$, which can be exponentially small in $N$: for even-size Curie–Weiss, $a/b=e^{-\beta n/2}$. With the companion's critical stability rate $n^{-1/4}$ and uniform bound $S_0(v,d)=c_0v^8/d^{12}$, its influence-error condition can require a cutoff of order $d^{56}v^{-32}$. A floor of scale $v\exp[-O_\beta(N)]/N$ is not a fixed polynomial in $(v,1/d)$. Calling its coefficient a constant depending on $v,d$ does not establish polynomial AA. The argument proves a positive dimension-independent modulus for each fixed $(d,v)$, rather than the claimed polynomial modulus. Its finite-flatness extension inherits this issue; a minimum away from zero also requires a suitably centered reference law rather than the unchanged unbiased comparison.

This does **not** invalidate the Curie–Weiss influence theorem already in our shared notes: [the finite-size latent/spin Poincaré proof](../curie_weiss/06_finite_size_spin_poincare_bound.tex) gives the polynomial floor $\max_i I_i\ge v/(Cn^{3/2})$, and [its assembly](../curie_weiss/08_consequence_exact_fixed_temperature_threshold.tex) tracks a polynomial cutoff to obtain $cv^4/d^{12}$. Our full-AA statement is independently supplied by the exchangeable-input simulator and holds at every temperature.

**The Boolean-degree shortcut remains false.** Companion §10.5 strengthens the erroneous sentence to “every Boolean-valued function” having degree $n$. The address-function counterexample in §3.3 above still applies, even when every variable is relevant. The all-ones certificate is a valid cost-$n$ certificate, but its cost is not generally $O(d^2)$.

**The determinant/LP distinction remains necessary.** Companion §§10.1–10.6 and its final ledger still call feasibility of the exact counting-measure summed-$(b')$ LP open. Under the established BDST antipodal-routing theorem already used in this project, the permutation-matrix deduction in §3.1 above proves feasibility. Only a new determinant-free route remains unprovided. There is also a normalization slip in companion §10.4: entries $1/N^2$ form a joint coupling with uniform marginals, whereas a doubly stochastic matrix with row and column sums one has entries $1/N$. The intended distinction between a fractional coupling and a single permutation is valid after that correction. Neither issue alters our separate one-biased-bit obstruction to a literal Gibbs-marginal extension.

**The fcb route is repaired, but its global status is not.** The companion correctly derives
$\operatorname{Inf}_i(p)=\sum_k\operatorname{Inf}_i(p_k)$ and the conditional level estimate involving $B_k=\|p_k\|_{\mathrm{fcb},k}$. For a polynomial conclusion in degree, a bound $B_k\le B_d$ must itself have polynomial degree dependence; a finite but exponential $B_d$ is insufficient. More fundamentally, its ordinary nonhomogeneous polynomial-AA target remains an immediate consequence of the uniform-AA theorem it explicitly accepts, since $\|p\|_\infty\le\|p\|_{\mathrm{fcb},d}$. The level-norm route, a direct proof, and stronger degree-free bounds can remain unresolved. The companion's derivative sentence uses a full flip difference, which preserves homogeneous degree $k$ rather than lowering it to $k-1$; orthogonality and its additivity conclusion nevertheless remain correct.

**No new threat to our full-AA theorems was identified in this focused review.** The companion's valid independent-block total-variation example reinforces our warning that global product approximation is unnecessary. Its star and support-flatness examples remain obstructions to particular influence methods. Its HC+CU section still passes from the same superfactorial cumulant majorant to an analytic MGF expansion without supplying the truncation/remainder argument identified in §5 above, so its “complete conditional proof” label is too strong as written. These unresolved upstream proof steps are not premises of our noisy-code lower bounds, temperature-independent soft-code Hamiltonian, arbitrary-weight criterion, exchangeable/finite-species simulation, or posterior-access results.
