# Polynomial-influence AA for Gibbs measures: research handoff

**Status:** 2026-11-15 consolidation of reviewed work. This is a research summary, not a new proof and not a Lean formalization.

## 0. Executive conclusion

The general polynomial-influence Aaronson–Ambainis (AA) problem for high-temperature Gibbs measures is **not solved**.

The unresolved statement is an $n$-uniform bound, for real-valued multilinear polynomials of fixed degree $d\ge 2$ with unrestricted coordinate support, under an explicitly high-temperature Gibbs family such as $\omega\le 1/8$:

$$\max_i\operatorname{Inf}_i^{\mathrm{fl}}(p)\ \ge\ S(v,d)>0
\qquad\text{whenever }\operatorname{Var}_\mu(p)\ge v,$$

with $S$ independent of $n$ and of the size of $\operatorname{supp}p$.

What **has** been proved includes:

* AA for **every product law**, with arbitrary and even degenerate one-site biases;
* the degree-one theory in essentially sharp form;
* a uniform degree-two centred-Gram estimate for **zero-field** Gibbs laws;
* AA for fixed-coordinate-support polynomials, bounded hitting sets/star forests, bounded total strength and finite interaction budgets;
* product-alphabet encodings and special Boolean-valued Gibbs results;
* precise conditional reductions that identify the remaining (WA), (B), (CI-avg), and $(H_d)$ inputs;
* several sharp obstructions showing why the natural centred-Gram, density-ratio, product-proxy and local-odds routes fail.

The accepted special cases must not be conflated with the general support-uniform theorem.

---

## 1. Target, notation and influence conventions

Let $\Omega=\{\pm1\}^n$ and

$$H(x)=-\sum_{|A|\ge2}J_A\chi_A(x)-\sum_i h_ix_i,
\qquad \chi_A(x)=\prod_{i\in A}x_i,
\qquad \mu(x)=\frac{e^{-\beta H(x)}}{Z}.$$

Define the weighted interaction strength and field size by

$$\omega:=\beta\max_i\sum_{A\ni i,\ |A|\ge2}(|A|-1)|J_A|,
\qquad \Lambda:=\max_i\beta|h_i|\quad(\text{also written $K$ in some manuscripts}).$$

The principal high-temperature regime is $\omega\le1/8$, with field bounds stated separately where needed; $\omega$ alone does not bound $\Lambda$.

For $p(x)=\sum_S\widehat p(S)\chi_S(x)$, write $\deg p=d$ and $\|p\|_\infty\le1$. Its discrete derivative is

$$\partial_i p(x_{-i}):=\frac{p(+1,x_{-i})-p(-1,x_{-i})}{2}.$$

The three real-valued influence conventions are

$$\operatorname{Inf}^{\mathrm{fl}}_i(p):=\mathbb E_\mu[(p(X)-p(X^i))^2]
=4\mathbb E_\mu[(\partial_i p)^2],$$

$$\operatorname{Inf}^{\mathrm{pv}}_i(p):=\mathbb E_\mu[\operatorname{Var}(p\mid X_{-i})]
=4\mathbb E_\mu[\theta_i(1-\theta_i)(\partial_i p)^2],$$

$$\operatorname{Inf}^{\mathrm{rs2}}_i(p):=\mathbb E_\mu[(p(X)-p(X'))^2]
=2\operatorname{Inf}^{\mathrm{pv}}_i(p)
=8\mathbb E_\mu[\theta_i(1-\theta_i)(\partial_i p)^2],$$

where $X^i$ flips coordinate $i$, $X'$ independently resamples it from $\mu(\cdot\mid X_{-i})$, and $\theta_i=\mu(X_i=1\mid X_{-i})$. Therefore

$$\boxed{\operatorname{Inf}^{\mathrm{fl}}\ \ge\ 4\operatorname{Inf}^{\mathrm{pv}}
=2\operatorname{Inf}^{\mathrm{rs2}}.}$$

If $\theta_i\in[\eta,1-\eta]$ for every $i,x_{-i}$, then more precisely

$$\eta(1-\eta)\operatorname{Inf}^{\mathrm{fl}}
\le \operatorname{Inf}^{\mathrm{pv}}\le\frac14\operatorname{Inf}^{\mathrm{fl}}.$$

m4 also uses a **TV/pivotal resampling probability**, not this squared-difference $\operatorname{Inf}^{\mathrm{rs2}}$. Keep these functionals separate.

### Current status at a glance

| Area | Accepted status |
|---|---|
| General real-valued, unrestricted-support Gibbs AA at $d\ge2$ | **Open** |
| Degree one | Proved sharply; sequence-uniform exactly when covariance norms are bounded |
| Arbitrary product measures, every degree | Proved, including degenerate biases |
| Zero-field degree-two centred Gram | Proved with $\Lambda_2\le32/9$ at $\omega\le1/8$ |
| Fixed coordinate support | Proved with explicit $n$-free constants |
| Bounded hitting sets/star forests | Proved via conditional product environments |
| Bounded total strength/finite interaction budgets | Proved with explicit tilt/routing losses |
| Unrestricted centred Gram at $d\ge3$ | **Refuted**, but this does not refute AA |
| General Boolean-valued $p$ only | Proved with balanced conditionals and a separate field bound |
| Product-alphabet/block-product special cases | Proved with fixed alphabet size/atom restrictions |
| Query-AA simulation | Completed separately; not an influence-AA proof |

---

## 2. Accepted results and proof sketches

### 2.1 Every product law: arbitrary-product AA through (WA)

**Result.** Every product law $\mu=\bigotimes_i\mu_i$, with $\mu_i^*:=\max_i\max_a\mu_i(a)\le1$, satisfies the weighted all-pairs inequality (WA) with $C_R=\mu^*$, including degenerate factors. The uniform case has the sharp dictatorship constant $C_R=1/4$.

Consequently, if $\deg p\le d$, $\|p\|_\infty\le1$ and $\operatorname{Var}_\mu(p)\ge v$, then

$$\max_i\operatorname{Inf}^{\mathrm{fl}}_i(p)
\ge \frac{(\mu^*)^{-3}v^{14}}{2^{24}\,108\,F(p)^{12}}
=\Omega\!\left(\frac{v^{14}}{(\mu^*)^3d^{24}}\right),$$

where $F(p)$ is the usual fractional-certificate complexity.

**Precise (WA) hypothesis.** For every $A\subseteq\Omega$, every Boolean certificate family $\Lambda$, and every $w>0$,

$$\sum_{x\in A,\ y\notin A}\frac{\mu(x)\mu(y)}
{\operatorname{overlap}_{w,\Lambda}(x,y)}
\ \le\ C_R\sum_i\frac{\operatorname{Inf}^{\mathrm{fl}}_i(A)}{w_i},$$

with $\operatorname{overlap}_{w,\Lambda}(x,y)=\sum_{i\in\Delta(x,y)}w_i\lambda^x_i\lambda^y_i$.

**Proof sketch.**

1. For a bichromatic pair $(x,y)$, let $\tau=\operatorname{overlap}_{w,\Lambda}(x,y)$ and define the heavy set $T=\{i:w_i\lambda^y_i>\tau\}$. Then $T$ is a monochromatic face of $x$, and any routed $z\in A\cap\operatorname{cube}(x^T,y)$ has $\operatorname{dist}_w(z,y)\ge1/\tau$.
2. Apply BDST's antipodal-with-faces routing count inside each $S$-subcube $Q$. For product laws,
   $$w_S(x):=\mu(x)\mu(x^S)$$
   is constant on $Q$: coordinates outside $S$ are fixed, while each $j\in S$ contributes the symmetric factor $\mu_j(x_j)\mu_j(\bar x_j)$.
3. Summing the weighted count and using
   $$\sum_{S\ni i}\mu(u^S)=\mu_i(\bar u_i)$$
   yields the per-direction bound $\mu_i^*B_i^+(A)\le\mu_i^*\operatorname{Inf}^{\mathrm{fl}}_i(A)$, and hence (WA).
4. (WA) implies a squared certificate inequality. Write $g=1/\|\lambda\|_1$ and $u=\mathbb E_\mu[1_Ag]$, $v=\mathbb E_\mu[1_{A^c}g]$. With
   $$\alpha_i=\mathbb E[1_A\lambda_i g^2],\qquad
   \beta_i=\mathbb E[1_{A^c}\lambda_i g^2],\qquad w_i=(\alpha_i\beta_i)^{-1/2},$$
   Cauchy–Schwarz gives
   $$M:=\max_i\operatorname{Inf}^{\mathrm{fl}}_i(A)\ \ge\ \frac1{C_R}(uv)^2.$$
5. Apply this to $A_t=\{p>t\}$. With $\sigma=\mathbb E|p-\mathbb E p|\ge v$ and $F=F(p)$, over the threshold interval $[\mathbb E p-\sigma/4,\mathbb E p+\sigma/4]$ one gets, with $c_1=1/C_R$,
   $$\kappa_1=\frac{c_1\sigma^4}{2^8F^4}.$$
   Window transfer gives $\kappa_1\le4\theta/\sigma+M/\theta^2$. Optimizing at $\theta=\kappa_1\sigma/6$ gives $M\ge\sigma^2\kappa_1^3/108$, hence the displayed $v^{14}$ bound.

The factor $108$ belongs to this **squared, flip-influence** reduction. It is not a correction to the separate resampling $v^8/F^6$ calculation below.

**Source:** `.ultramath/smwh84hiq/m1/weighted-routing-gibbs.md`.

### 2.2 Alternative arbitrary-product proof: live/dry coordinates

**Result.** Again for every product law, with no atom bound and allowing point masses, the packaged biased-product function $S_0$ gives

$$\max_i\operatorname{Inf}_i(p)
\ \ge\ S_0\!\left(\frac v2,d,\frac{v}{8d^2}\right)>0.$$

**Proof sketch.** Set $\eta=v/(8d^2)$ and $L=\{i:\epsilon_i(1-\epsilon_i)\ge\eta\}$, where $\epsilon_i=\mu_i(+1)$. Put $q=\mathbb E[p\mid x_L]$.

* Conditional on $x_L$, dry coordinates remain independent. Efron–Stein and the exact product identity
  $$\mathbb E[\operatorname{Var}(p\mid X_{-i})]
  =\epsilon_i(1-\epsilon_i)\operatorname{Inf}^{\mathrm{fl}}_i(p)$$
  give
  $$\mathbb E[\operatorname{Var}(p\mid x_L)]
  \le\eta\sum_{i\notin L}\operatorname{Inf}_i(p).$$
* The verified pointwise total-influence bound $\sum_i\operatorname{Inf}_i(p)\le4d^2$ makes the dry loss at most $v/2$. Thus $\operatorname{Var}(q)\ge v/2$.
* Remaining live biases lie in $[\eta,1-\eta]$, $\deg q\le d$, $0\le q\le1$, and conditional Jensen gives $\operatorname{Inf}_i(q)\le\operatorname{Inf}_i(p)$. Apply $E_{\rm bit}$ to $q$.

This is an alternative proof to the routing result, not evidence that interacting Gibbs measures have the same structure.

**Source:** `.ultramath/smwh8a9it/m3/results/obstruction-report.md`.

### 2.3 Degree one is settled

For affine $p=a_0+\sum_i a_ix_i$ and any law with covariance operator norm $\Lambda=\lambda_{\max}(\operatorname{Cov}_\mu)$,

$$\operatorname{Inf}^{\mathrm{fl}}_i(p)=4a_i^2,
\qquad \max_i\operatorname{Inf}_i^{\mathrm{fl}}(p)
\ge\frac{4\operatorname{Var}_\mu(p)^2}{\Lambda^2}
\quad(\|p\|_\infty\le1).$$

**Proof sketch.** Boundedness gives $\sum_i|a_i|\le1$. Therefore

$$\operatorname{Var}(p)=a^T\operatorname{Cov}a
\le\Lambda\|a\|_2^2
\le\Lambda(\max_i|a_i|)\sum_i|a_i|
\le\Lambda\max_i|a_i|.$$

Independent Ising pairs attain the constant. At fixed finite $n$, $\Lambda\le n$ is automatic, so the “iff” formulation must be for sequences: an $n$-uniform degree-one AA bound exists exactly when $\sup_n\Lambda(\mu_n)<\infty$.

For the Dobrushin coefficient defined by conditional-mean differences, $\alpha\le2\omega$, so at $\omega\le1/8$ one has $\alpha\le1/4$ and $\Lambda\le(1+\alpha)/(1-\alpha)\le5/3$.

For the [0,1]-valued normalization $\sum_i|a_i|\le1/2$, the product degree-one bound is the sharp $16\operatorname{Var}^2$; the normalization above with $\|p\|_\infty\le1$ on $[-1,1]$ gives the factor $4$ instead.

**Sources:** `.ultramath/smwh6ji5o/m1/gibbs-AA-m1.md` and `.ultramath/smwh8a9it/m3/results/obstruction-report.md`.

### 2.4 Zero-field degree-two centred Gram estimate

**An auxiliary estimate, not yet AA.** For zero-field Gibbs laws with Dobrushin coefficient $r<1$, every multilinear $p$ of degree at most $2$ satisfies

$$\operatorname{Var}_\mu(p)
\le\frac{\max\{2\Lambda_1,1\}}{1-r}\sum_S\widehat p(S)^2
\le\frac{2}{(1-r)^2}\sum_S\widehat p(S)^2.$$

Thus $\Lambda_2\le2/(1-r)^2$, and in the full zero-field $\omega\le1/8$ regime $\Lambda_2\le32/9$, uniformly in $n$, for every graph and arity.

**Proof sketch.** Write $p=\sum_i a_ix_i+\sum_{i<j}b_{ij}x_ix_j$ and $R_i=a_i+\sum_j b_{ij}x_j$. Since zero field gives $\mathbb E R_i=a_i$, level one yields

$$\mathbb E R_i^2\le\Lambda_1\sum_j b_{ij}^2+a_i^2.$$

Also $\operatorname{Inf}^{\mathrm{pv}}_i(p)\le\mathbb E R_i^2$. Sum over $i$ and insert the Dobrushin–Holley–Stroock inequality

$$\operatorname{Var}_\mu(p)\le\frac1{1-r}\sum_i\operatorname{Inf}^{\mathrm{pv}}_i(p).$$

The exact optimal constant is $\lambda_{\max}$ of the centred Gram matrix $K^{(d)}_{ST}=\mu_{S\triangle T}-\mu_S\mu_T$; the degree-one case recovers the covariance norm.

**Why “with fields” is different.** For biased independent spins of mean $m_0\ne0$, even at $\omega=r=0$, take $p=C^{-1/2}\sum_{i<j}x_ix_j$ with $C=\binom n2$. Then $\sum_S\widehat p(S)^2=1$ but

$$\operatorname{Var}(p)=\frac{2n(n-2)}{n-1}m_0^2(1-m_0^2)+O(1)\to\infty.$$

So the unrestricted centred-Gram threshold is exactly $2$ in zero field and exactly $1$ once nonzero fields are allowed. This is **not** an AA counterexample: the displayed test polynomial is unbounded and the statement is only about the auxiliary moment hypothesis.

**Source:** `.ultramath/smwh8cksq/m1/replacement-A.md`.

### 2.5 AA for fixed-coordinate-support polynomials

**Theorem.** For every Gibbs law with finite $\omega,\Lambda$, every $n$, arity and total interaction strength, if $\deg p\le d$, $\|p\|_\infty\le1$, $|\operatorname{supp}p|\le V$ and $\operatorname{Var}_\mu(p)\ge\nu$, then

$$\max_i\operatorname{Inf}^{\mathrm{fl}}_i(p)
\ge c_d e^{-(1+C(d))\kappa}\nu^{C(d)},
\qquad \kappa=(4\omega+2\Lambda)V.$$

Here $c_d,C(d)$ come only from uniform-cube product AA. At $\omega\le1/8,\Lambda=0$, $\kappa=V/2$.

**Proof sketch.** Let $K=\operatorname{supp}p$. The support marginal satisfies

$$e^{-\kappa}\le\frac{d\mu_K}{d\pi_K}\le e^\kappa,$$

where $\pi_K$ is uniform on $K$. To see the log-density bound, split interactions into internal ($A\subseteq K$) and mixed terms. Internal terms contribute at most $2\omega|K|$ and mixed terms another $2\omega|K|$ to the log-oscillation, while fields contribute $2\Lambda|K|$. The internal count is valid because, for $|A|\ge2$,

$$\beta\sum_{A\subseteq K}|J_A|
\le\beta\sum_{A\subseteq K}(|A|-1)|J_A|
\le\beta\sum_{A\subseteq K}|A|(|A|-1)|J_A|
\le\omega|K|.$$

Variance transfers by $\operatorname{Var}=\inf_c\mathbb E[(p-c)^2]$, and flip influence transfers by $\operatorname{Inf}^{\mathrm{fl}}_i=4\mathbb E_\mu[(\partial_ip)^2]$. Apply uniform-cube product AA on the $K$ coordinates.

This is a genuine $n$-free theorem for **fixed coordinate support**, and is logically distinct from both bounded total strength and bounded vertex cover.

**Source:** `.ultramath/smwh8a9it/m2/main.md`.

### 2.6 Bounded hitting sets: conditional product environments

For an interaction hypergraph with a hitting set $S$ of size $s$ (every interaction contains one of $s$ fixed sites), define

$$\eta=\sigma(-2K-2\omega),\qquad \rho=e^{2K+2\omega},\qquad
\Xi=e^{\omega^2/(\eta(1-\eta))},\qquad
\kappa_s=1+4s^2\Xi\rho^{2s-1}.$$

Then

$$\max_i\operatorname{Inf}^{\mathrm{fl}}_i(p)
\ge\min\left\{2^{-s}S_0\!\left(\frac{v}{2\kappa_s},d,\eta\right),
\frac{v}{4s^2\rho^{2(s-1)}}\right\}.$$

This covers star forests and general bounded vertex covers with arbitrary arity.

**Proof sketch.**

1. Conditional on $X_S=t$, the remaining law is exactly product, because there are no interactions involving two free coordinates. Call its within-variance $W(t)$ and write $F(t)=\mathbb E[p\mid X_S=t]$, $B=\operatorname{Var}(F)$, $W=\mathbb E W(t)$. Total variance is $V=B+W$.
2. If $W$ is large, apply biased-product AA inside environments and select one environment, losing at most $2^{-s}$ (with convexity of $S_0$).
3. If $B$ is large, use hub flips. A hybrid argument gives
   $$\sum_{j\in S}\mathbb E[(F-F^{e_j})^2]
   \ge\frac{2B}{s\rho^{2(s-1)}}.$$
   A chi-square change-of-bias estimate gives, for the environment bias shift $b_j$,
   $$b_j(t)^2\le\Xi W(t^{e_j}),
   \qquad \mathbb E[b_j^2]\le\Xi\rho W.$$
   Combining with the exact hub-flip identity yields
   $$\sum_{j\in S}\operatorname{Inf}^{\mathrm{fl}}_j(p)
   \ge\frac{B}{s\rho^{2(s-1)}}-s\Xi\rho W.$$
4. Split according to $W\ge V/(2\kappa_s)$ or $W<V/(2\kappa_s)$ to obtain the two branches.

Chains and lattices have hitting number $\Theta(n)$, so this method stops precisely there.

**Source:** `.ultramath/smwh89pww/m1/manuscript.md`.

### 2.7 Bounded total strength, tilts and finite interaction budgets

Several accepted related regimes are available.

**Bounded total strength.** For $\Theta=\beta\sum_{|A|\ge2}|J_A|$, bounded fields and $\Theta\le\kappa/2$, the accepted tilt theorem has posterior-variance influence

$$\max_i\operatorname{Inf}^{\mathrm{pv}}_i(p)
\ \ge e^{-3\kappa}S_0(e^{-\kappa}v,d,a).$$

The essential conditional-odds computation is

$$\frac{q(1-q)}{s(1-s)}=\frac{R}{(1-s+Rs)^2}
\ge\min(R,1/R),$$

not the erroneous older probability-times-$R$ formula. Flip influence follows by multiplying the posterior lower bound by $4$. A vertex cover of size $s$ gives $\Theta\le s\omega$ and the earlier bound

$$e^{-6s\omega_0}S_0(e^{-2s\omega_0}v,d,a).$$

**Source:** `.ultramath/smwh6ji5o/m2/theorem_weak_gibbs_AA.md`.

**Finite budget for the routing mechanism.** If

$$K:=\sup_S\beta\sum_{A:|A\cap S|\ge2}|J_A|<\infty,$$

then (WA) holds with $C_R=\mu^*e^{4K}$ and consequently

$$\max_i\operatorname{Inf}^{\mathrm{fl}}_i(p)
\ge\frac{(\mu^*)^{-3}e^{-12K}v^{14}}{2^{24}\,108\,F(p)^{12}}.$$

The pair-weight distortion on an $S$-cube is at most $e^{4K}$. This includes interactions on a fixed finite set with arbitrary fields and one arbitrary-arity hyperedge. It does not include the extensive chain or extensive Curie–Weiss family with $K=\Theta(n)$.

**Source:** `.ultramath/smwh84hiq/m1/weighted-routing-gibbs.md`.

### 2.8 General conditional reductions: (CI-avg), (B), and $(H_d)$

#### (CI-avg) implies the full all-degree bound

For a law satisfying the average certificate-influence inequality with constant $c_0$ in m1's squared-difference resampling convention,

$$\max_i\operatorname{Inf}^{\mathrm{rs2}}_i(p)
\ge\frac{c_0^3v^8}{2^{18}F(p)^6},
\qquad
\max_i\operatorname{Inf}^{\mathrm{fl}}_i(p)
\ge\frac{c_0^3v^8}{2^{17}F(p)^6}.$$

The interval constant is $\kappa=c_0\sigma^2/(16F^2)$. The window recursion is $M\ge2\eta^2(\kappa-4\eta/\sigma)$; at $\eta=\sigma\kappa/8$ it gives $\sigma^2\kappa^3/64$ (and optimizing gives the slightly stronger $\sigma^2\kappa^3/54$).

An independent worst-case threshold computation has nonvacuity threshold $F(p)>\sqrt{3456}=24\sqrt6\simeq58.7878$, not64. This is a necessary nonvacuity condition for that estimate, not a sufficiency theorem.

**Source:** `.ultramath/smwh6ji5o/m1/gibbs-AA-m1.md`.

#### m3's corrected conditional coefficient theorem

Assume:

1. (H1) $1-m_i(x_{-i})^2\ge c$ for every $i,x$;
2. (H2c) $\operatorname{Var}_\mu(r)\le\Lambda\sum_S\widehat r(S)^2$ for every multilinear $r$ of degree at most $d$;
3. (B) there is $\lambda_0>0$ such that every multilinear $q$ with $\deg q\le d$ and $\|q\|_\infty\le1$ satisfies
   $$\widehat q(\emptyset)^2\le\lambda_0^{-1}\|q\|_{L^2(\mu)}^2.$$

Then, with $q_{\mathrm{BH}}=2d/(d+1)$ and $C_d$ the Bohnenblust–Hille constant,

$$\max_i\operatorname{Inf}^{\mathrm{pv}}_i(p)
\ge\lambda_0c^d
\left(\frac{v}{\Lambda C_d^{\,q_{\mathrm{BH}}}}\right)^{d+1},$$

and flip influence is at least $4$ times this.

The proof uses $\operatorname{Var}(p)\le\Lambda\sum_{S\ne\emptyset}a_S^2$, Bohnenblust–Hille plus Hölder to locate a large coefficient $M$, and the coefficient-domination induction. The corrected final step is

$$\operatorname{Inf}^{\mathrm{pv}}_i
\ge c\|R_i\|^2
\ge\lambda_0c^{|S^*|}M^2
\ge\lambda_0c^dM^2,$$

not the rejected reciprocal estimate. The degree-three pair-block example prevents supplying (H2c) uniformly at $d\ge3$ inside $\omega\le1/8$. At zero-field degree 2, (H2c) is now supplied by §2.4 above, so **(B) is the only missing input in this particular conditional route**.

**Source:** `.ultramath/smwh6ji5o/m3/polynomial_AA_Gibbs_derivative_route.md`.

#### Marginal-product $L^2$ domination $(H_d)$

If $\nu=\bigotimes_i\mu_i$ is the product of one-site marginals and, for every $q$ of degree at most $d$, respectively $d-1$,

$$\mathbb E_\mu[q^2]\le A_d\mathbb E_\nu[q^2],
\qquad
\mathbb E_\mu[q^2]\le A_{d-1}\mathbb E_\nu[q^2],$$

then

$$\operatorname{Var}_\nu(p)\ge v/A_d,
\qquad
\operatorname{Inf}^{\mathrm{fl}}_i(p)\le A_{d-1}\operatorname{Inf}^{\nu,\mathrm{fl}}_i(p),$$

so arbitrary-product AA transfers with an additional factor $1/A_{d-1}$ and variance threshold $v/A_d$. This is a useful independent route, but $(H_d)$ is **unproved for $d\ge2$**.

**Source:** `.ultramath/smwh84hiq/m1/weighted-routing-gibbs.md`, Theorem 5.2.

### 2.9 Product-alphabet and Boolean-valued special cases

Accepted results outside the real-valued general target include:

* **Nonvanishing lemma.** If every coordinate conditional lies in $[\eta,1-\eta]$ and $q\not\equiv0$ is multilinear of degree at most $k$, then
  $$\mu(q\ne0)\ge\eta^k.$$
  The proof inducts on degree via a nonzero $\partial_iq$, and marginalization preserves the conditional balance.
* **Real-valued TV-resampling gap.**
  $$\max_i\operatorname{Inf}^{\mathrm{rs,TV}}_i(p)
  \ge2\eta^d(1-\eta)$$
  for nonconstant real-valued $p$ of degree at most $d$.
* **Boolean flip gap.**
  $$\max_i\operatorname{Inf}^{\mathrm{fl}}_i(p)
  \ge4\eta^d(1-\eta)$$
  for $\{0,1\}$-valued $p$. This is v-free because the relevant scale is event probability, not ordinary real-valued amplitude.
* **Gibbs corollary.** The same bound holds on the original $\{\pm1\}$ Hamiltonian basis, for Boolean-valued $p$, with separate $N$-uniform field bound $K=\beta\max_i|J_{\{i\}}|=O(1)$. It is not a general real-valued theorem, and $\{0,1\}$-monomial rewriting must not be confused with the original $\pm1$ Hamiltonian.
* **Product alphabets.** Finite-alphabet block-product encodings yield $I_{\max}\ge(\delta_0/(2t_{\max}))S_0(v,dk_{\max},\delta_0)$, improving the encoding-degree bound to $dk_{\max}$ rather than $d(2^{k_{\max}}-1)$. For arbitrary correlated full-support binary block laws,
  $$\frac{2\delta}{k}\operatorname{Var}
  \le\sum_s\operatorname{Inf}^{\mathrm{fl}}_s
  \le\frac{4k}{\delta}\operatorname{Var}.$$
  These results require fixed alphabet size and positive atom bounds and do not encompass ordinary extensive Gibbs marginals.

**Source:** `.ultramath/smwh6ji5o/m4/qary_certificate_aa.md`.

### 2.10 A new degree-two extremal example

For the five-coordinate “pentagon” polynomial, after normalization by $4$,

$$\operatorname{Var}(p)=\frac34,
\qquad \max_i\operatorname{Inf}^{\mathrm{fl}}_i(p)=1
=\frac{16}{9}\operatorname{Var}(p)^2.$$

Equivalently $V^2=(9/4)MR^2$. Hence $S(v,2)\le(16/9)v^2$ at $v=3/4$. This improves the valid but non-optimal $4v^2$ ceiling and refutes the candidate $V^2\le2MR^2$. The proposed optimal inequality $V^2\le(9/4)MR^2$ remains open. This is an **upper extremal example**, not an AA lower-bound proof.

**Source:** `.ultramath/smwh8a9it/m1/degree2-extremal.md`.

---

## 3. Important obstructions and negative results

### 3.1 The all-degree centred-Gram route fails at $d=3$

Take independent Ising pairs with $J=1/8$, $r=\tanh J$, and

$$p_m=x_{b_0,1}A_m,$$

where $A_m$ is the mean of the other $m-1$ pair products. Then $\deg p_m=3$, $\omega=1/8$, and

$$\frac{\operatorname{Var}_\mu(p_m)}{\sum_S\widehat p_m(S)^2}
=(1-r^2)+r^2(m-1)\longrightarrow\infty.$$

Moreover $\max_i\operatorname{Inf}_i^{\mathrm{fl}}(p_m)=4\operatorname{Var}(p_m)$, so this family **does not refute AA**. It refutes only a two-sided centred-Gram/product-moment bridge. A two-sided variance comparison to the uniform product fails just as badly: $\operatorname{Var}_\mu(p_m)\to r^2$ while the uniform variance is $1/(m-1)\to0$.

### 3.2 Bounded conditional odds and full support are insufficient

For $\mu_h=\tfrac12(\nu_{+h}+\nu_{-h})$, with $\nu_{\pm h}$ product laws of spin means $\pm\tanh h$ and $p=S/n$,

$$\operatorname{Var}_{\mu_h}(p)=\tanh^2h+\frac{1-\tanh^2h}{n},
\qquad
\operatorname{Inf}^{\mathrm{fl}}_i(p)=\frac4{n^2}.$$

The law has bounded flip odds and full support, but its collective Hamiltonian
$H_h=-\log(2\cosh(hS))$ has $\omega=\Theta(n)$, so it lies outside the high-temperature target regime. The couplings are $J_{ij}=+h^2+O(h^4)$; negative numbers printed by scripts are Walsh coefficients of $H_h$, not $J_{ij}$.

A related majority-on-majority example has an average certificate-influence inequality failing by an exponentially small factor. This demonstrates that CI-avg, not merely polynomial AA, can fail outside the regime.

### 3.3 Product proxies and atom floors

For the zero-field Ising chain and any product law $\pi$ with atom floor $b$,

$$\operatorname{osc}\left(\log\frac{d\mu}{d\pi}\right)
\ge2\beta J(n-1)-n|\log b|.$$

Thus global product-density comparisons generally pay $e^{-\Theta(n)}$ and are not a route to $n$-free constants. Local support marginals are different: §2.5 exploits precisely that distinction.

A full-support atom floor $\min_x\mu(x)$ is also useless uniformly in $n$, since it is always at most $2^{-n}$. The odds floor of §2.6 is a different object: it controls conditional probabilities, not global atoms.

### 3.4 Other refuted mechanisms

* **Uncentred Gram bounds** fail on extended systems through coherent nonzero means.
* **Biased degree-two centred Gram** fails even for products, as shown in §2.4.
* **Unordered general Efron–Stein** $\operatorname{Var}\le\sum_i\operatorname{Inf}^{\mathrm{pv}}_i$ is false for dependent laws; ordered prefix decompositions require explicit conditional factors.
* **One-bit posterior histories as product laws** are false: complete-trajectory independence does not imply product disintegration conditional only on the final physical configuration $X=x$.
* **Naive history composition** accumulates variance error $O(n\gamma)$ and can make composed degree grow with $n$.
* **AND-monomial influence comparisons** have ratio $(2\epsilon)^{k-1}\to0$, so failed comparisons do not remove atom floors, even though product AA survives by §2.1–§2.2.
* **Copy-law AA failure** needs a degenerate support/infinite-coupling limit. At finite coupling the three-spin Ising calculation gives
  $$\operatorname{Var}=1,
  \qquad \max_i\operatorname{Inf}^{\mathrm{fl}}_i=\frac{12e^{-4\lambda}}{1+3e^{-4\lambda}},$$
  which is not a counterexample at $\omega\le1/8$.

These are obstructions to mechanisms, not to the main conjecture.

---

## 4. What the next agent should do

### Priority A: resolve m3's base inequality (B) at zero-field degree 2

This is now the sharpest isolated gap in the conditional coefficient route. Start with

> For which zero-field Gibbs laws with $\omega\le1/8$ is there an $n$-independent $\lambda_0$ such that $\widehat q(\emptyset)^2\le\lambda_0^{-1}\|q\|_{L^2(\mu)}^2$ for every bounded multilinear $q$ of degree at most 2?

Do not assume $\mathbb E_\mu q=\widehat q(\emptyset)$; those means are taken under different measures. Test the inequality against independent Ising pairs and small cycles first, then seek a cluster-expansion proof. If (B) is established, combine it with §2.4 and m3 immediately.

### Priority B: prove an $n$-uniform (WA) or (CI-avg) constant at $\omega\le1/8$

The accepted chain makes either condition sufficient for all-degree AA. The subcube-uniform pair-weight distortion is exponential in extensive models, so the proof must use an **averaged** estimate, not $\sup_Q w_Q$ bounds. Potential approaches are weighted all-pairs transportation, boundary-averaged walk distortion, or a direct CI-avg proof that avoids facial routing.

Do not conflate (WA) with a Hamming-distance-optimal routing ratio, and do not require one global bijection of $A$; the actual routing is per pair with a face constraint.

### Priority C: pursue the $L^2$ marginal-product domination $(H_d)$ independently

The pair-block example rules out a two-sided variance bridge, but $(H_d)$ is only one-sided. Investigate a spectral bound for the moment matrix restricted to degrees $\le d$ and $\le d-1$. Test whether a weighted/centred variant can survive the pair-block family at $d=3$; the unweighted centred-Gram formulation cannot.

### Priority D: extend conditional product decompositions beyond bounded hitting sets

The hitting-set proof works almost completely, but its versions stop at unbounded hitting number. A useful extension needs multiple environments/cut sets **plus a max-versus-average selection argument**. Merely decomposing into many independent blocks can restore the old $\mathbb E[\max]$ versus $\max\mathbb E$ problem and must be avoided or explicitly charged.

### Priority E: sharpen only after proving reach

The pentagon and disjoint-character families show that the optimal exponent is not settled. The present ceiling $S(v,2)\le(16/9)v^2$ at $v=3/4$ and the conjectured $V^2\le(9/4)MR^2$ are separate questions from proving any general lower bound. Do not optimize constants before the general mechanism exists.

---

## 5. Routes not to repeat

1. Do not present query simulation as polynomial-influence AA.
2. Do not use the all-degree centred-Gram bound at $d\ge3$; it is false inside $\omega\le1/8$.
3. Do not extend the degree-two centred-Gram theorem to nonzero fields; it already fails for biased products.
4. Do not compare global Gibbs densities to product densities without addressing the $e^{-\Theta(n)}$ loss.
5. Do not treat posterior history source symbols conditional only on $X=x$ as product.
6. Do not conflate flip, posterior variance, squared-difference resampling, and TV resampling.
7. Do not use unordered dependent-measure Efron–Stein.
8. Do not rely on global atom floors or bounded conditional odds alone.
9. Do not use arXiv:1911.03748 as a theorem source; it is withdrawn/context only.
10. Do not assume a rejected report is authoritative merely because an earlier record called it accepted. The reports R2/R5 from the referee swarm were ultimately rejected for stale constants/scope; their valid ingredients are included above after independent checking.

---

## 6. Verified external inputs and citation policy

* Blanc, Docter, Strassle and Tan, *Proof of the Aaronson–Ambainis Conjecture: An Exposition*, **arXiv:2611.11626**. Use for the uniform-cube AA framework and $F(p)=O(d^2)$, not for Gibbs or arbitrary-alphabet results.
* Turturean's primary proof, **arXiv:2611.09773**, may be used only with its exact statement checked at point of use; no stronger exponent is imported in this summary.
* Girish, Mittal, Nehoran and Raz, *Distributional Variants of the Aaronson–Ambainis Conjecture*, **arXiv:2609.35327**, for the packaged biased-product $E_{\rm bit}$ and total-influence bound where explicitly noted. Verify the current version before further use.
* Huffstutler, Miloschewsky and Podder, **arXiv:2611.12795**, only for the specifically checked Boolean-box inequality in the proof of Lemma 4, equation (4).
* The antipodal routing input has constant $1/2$, and the subsequent routing lemma has constant $1/4$, not14 (the latter is a `pdftotext` flattening artefact).
* **Do not use arXiv:1911.03748 as a theorem source.**

For every import, record: source, assumptions, exact normalization, why they hold at the application, and which influence convention the output uses.

---

## 7. Source manuscripts and reproducible checks

The consolidated input file is `.ultramath/smwh6ji5o/REVIEWED-LITERATURE.md`; it contains itemized corrections and should be read alongside this handoff. Main accepted artifacts are:

| Result | Project path |
|---|---|
| Degree-one and (CI-avg) reductions | `.ultramath/smwh6ji5o/m1/gibbs-AA-m1.md` |
| Bounded total strength/vertex cover | `.ultramath/smwh6ji5o/m2/theorem_weak_gibbs_AA.md` |
| Conditional coefficient route and (B) | `.ultramath/smwh6ji5o/m3/polynomial_AA_Gibbs_derivative_route.md` |
| Alphabet/Boolean/block results | `.ultramath/smwh6ji5o/m4/qary_certificate_aa.md` |
| Zero-field degree-two Gram theorem | `.ultramath/smwh8cksq/m1/replacement-A.md` |
| Arbitrary-product WA and finite budgets | `.ultramath/smwh84hiq/m1/weighted-routing-gibbs.md` |
| Hitting-set theorem | `.ultramath/smwh89pww/m1/manuscript.md` |
| Fixed-support theorem | `.ultramath/smwh8a9it/m2/main.md` |
| Live/dry proof and obstruction report | `.ultramath/smwh8a9it/m3/results/obstruction-report.md` |
| Pentagon degree-two example | `.ultramath/smwh8a9it/m1/degree2-extremal.md` |
| Separate query-AA theorem and audit | `results/gibbs_history_aa_corrected.pdf`, `results/gibbs_history_aa_corrected_audit.md` |

Representative checks that were actually run:

```bash
python3 .ultramath/smwh8cksq/m1/lvl2b.py
python3 .ultramath/smwh8cksq/m1/probe2.py
python3 .ultramath/smwh84hiq/m1/scripts/wa_tables.py
python3 .ultramath/smwh84hiq/m1/scripts/t17.py
python3 .ultramath/smwh89pww/m1/numerics6.py
python3 .ultramath/smwh8a9it/m2/verify.py
python3 .ultramath/smwh8a9it/m3/scripts/verify_R1.py
python3 .ultramath/smwh8a9it/m1/verify_degree2.py
python3 .ultramath/smwh6nmpu/m2/work/check_m3_thm31.py
python3 .ultramath/smwh6ji5o/m1/scripts/sym_check.py
```

These checks are useful witnesses and regression tests only; they are not substitutes for proofs or formal verification.

The four genuine derivation swarms—`smwh8cksq`, `smwh84hiq`, `smwh89pww`, and `smwh8a9it`—have completed with accepted scoped deliverables. The referee-only `smwh6nmpu` R4 assembly audit remains separate from the open mathematical problem.

---

## 8. Correct minimum briefing for a new researcher

You are continuing research on a conjectured $n$-uniform polynomial-influence AA theorem for high-temperature Gibbs measures. The product case and degree-one case are solved, as are several restricted correlated classes. The general real-valued, unrestricted-support problem at $d\ge2$ remains open. Begin with §4 of this handoff, then read the source corresponding to your chosen direction. Prove every transfer from the definitions, state the field and support hypotheses explicitly, use flip influence correctly, and test each auxiliary hypothesis against the pair-block and biased-product obstructions before building on it. Do not declare the general problem solved from a special case, a conditional reduction, or numerical evidence.
