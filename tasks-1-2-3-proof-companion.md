# Proof companion for the Tasks 1–3 summary

## Purpose and reading contract

This document accompanies `results/tasks-1-2-3-summary.md`. It is intended to be self-contained enough for another model to audit the arguments without reading the swarm transcripts.

**The summary does not consist entirely of proved theorems.** Its `[PROJECT]`, `[CONDITIONAL]`, `[NUMERICAL]`, `[OPEN]`, and withdrawn entries must not be promoted to established results. This companion gives proofs for the statements marked **Proof below** or **External theorem**, conditional proofs for explicitly named hypotheses, and a final **not proof-ready** ledger for the remainder.

Four corrections emerged while preparing this document:

1. **Dobrushin gives a covariance operator-norm bound directly through Poincaré, not the absolute row-sum bound asserted in one sentence of the summary.** Both kinds of susceptibility control prove the affine result, but they must be distinguished (Theorem 4.1).
2. **Uniform-cube influence is additive across homogeneous Fourier levels.** The nonhomogeneous-fcb pigeonhole argument is blocked by lack of fcb-norm control for the levels, not by influence nonadditivity (Section 11.2).
3. **The old “every distribution has $\max\operatorname{Inf}\ge\operatorname{Var}/(2n^2)$” statement is false.** GMNR Lemma 2.12 assumes a product or fixed-slice law, and the correlated-hybrid proof does not apply unchanged. A different full-support floor is proved in Lemma 1.1 and used to repair the Curie–Weiss small-$n$ branch.
4. **The older $k=2$ routing formula has $\delta_{\min}^{6}$, not $\delta_{\min}^{-6}$, under the summary’s definition of $\delta_{\min}$ as minimum support-atom probability.** Its full proof remains outside the independently checked part of this companion.

No result from Keller–Klein arXiv:1911.03748 or from the withdrawn “OZ Theorem 3.5 with $\rho$” is used.

## Notation and external ingredients

For $p:\{0,1\}^n\to\mathbb R$, write
$$
\operatorname{Inf}_i^\lambda(p)=\mathbb E_\lambda[(p(x)-p(x^{\oplus i}))^2].
$$
This is single-bit-flip influence, not block resampling. The same notation is used on $\{\pm1\}^n$, where flipping changes the sign. Constants can therefore differ by a bounded factor $4$ between encodings.

Three external results are used as black boxes, with their scope made explicit:

- **Uniform AA.** The BDST/Turturean theorem in `papers/aa_main.txt`: there is a polynomial $S_0(v,d)>0$ such that, under uniform measure, every $[0,1]$-valued degree-$d$ multilinear $p$ with variance at least $v$ has $\max_i\operatorname{Inf}_i\ge S_0(v,d)$. The exposition supplies the explicit form $c_0v^8/d^{12}$. Its proof is not reproduced here.
- **Wu Poincaré.** Wu, *Poincaré and transportation inequalities for Gibbs measures under the Dobrushin uniqueness condition*, Theorem 2.1(2.4), locally `.scratch/papers/wu0611635.txt`: if $r=\operatorname{rsp}(C)<1$, then
  $$(1-r)\operatorname{Var}_\mu(f)\le\sum_i\mathbb E_\mu[\operatorname{Var}_{\mu_i}(f)].$$
- **Escudero’s homogeneous fcb theorem.** Escudero Gutiérrez, arXiv:2304.06713v2, Theorem 1.6: a homogeneous degree-$d$ polynomial $p$ with $\|p\|_{\mathrm{fcb},d}\le1$ has $\max_i\operatorname{Inf}_i(p)\ge\operatorname{Var}(p)^2$. The proof is in §4.2 of that paper and is not reproduced here.

GMNR Lemma 4.9 and the pointwise total-flip estimate are proved below rather than merely cited.

---

# Part I — Task 1: Gibbs and correlated input distributions

## 1. Two elementary floors used in the proofs

### 1.1 A full-support comparison floor (repairing the small-$n$ argument)

**Lemma 1.1.** Let $\mu$ have full support on $\{0,1\}^n$, and set
$$a=2^n\min_x\mu(x)>0,\qquad b=2^n\max_x\mu(x).$$
For every $f$,
$$\operatorname{Var}_\mu(f)\le\frac{b}{4a}\sum_i\operatorname{Inf}_i^\mu(f),
\qquad\text{hence}\qquad
\max_i\operatorname{Inf}_i^\mu(f)\ge\frac{4a}{bn}\operatorname{Var}_\mu(f).$$

**Proof.** Let $U$ be uniform. Since variance is the minimum squared distance to a constant,
$$
\operatorname{Var}_\mu(f)
\le \mathbb E_\mu[(f-\mathbb E_Uf)^2]
\le b\,\mathbb E_U[(f-\mathbb E_Uf)^2]
=b\operatorname{Var}_U(f).
$$
The uniform product Poincaré/Efron–Stein inequality gives
$$\operatorname{Var}_U(f)\le\frac14\sum_i\operatorname{Inf}_i^U(f).$$
Also $\operatorname{Inf}_i^U(f)\le a^{-1}\operatorname{Inf}_i^\mu(f)$, because each is an expectation of the same nonnegative function. Combining the three displays proves the first inequality; averaging over at most $n$ coordinates proves the second. ∎

This lemma is valid at critical Curie–Weiss, where Dobrushin’s $1-r$ vanishes. It gives a poor but positive constant on every fixed finite cube, which is all the small-$n$ assembly needs. It cannot be extended to degenerate support: the copy-law counterexample in §5.1 has variance $1/4$ and zero influence.

### 1.2 The binary conditional-variance identity and Wu’s limitation

**Lemma 1.2.** If $q_i=\mu_i(1\mid x_{-i})$, then
$$\mathbb E_\mu[\operatorname{Var}_{\mu_i}(p)]
=\mathbb E_\mu[q_i(1-q_i)(p-p^{\oplus i})^2]
\le\frac14\operatorname{Inf}_i^\mu(p).$$
Consequently, if $r=\operatorname{rsp}(C)<1$,
$$\operatorname{Var}_\mu(p)\le\frac{1}{4(1-r)}\sum_i\operatorname{Inf}_i^\mu(p),
\qquad
\max_i\operatorname{Inf}_i^\mu(p)\ge\frac{4(1-r)}n\operatorname{Var}_\mu(p).$$

**Proof.** With $a=p(x_{-i},0)$ and $b=p(x_{-i},1)$, conditional variance is
$$q_i(1-q_i)(a-b)^2.$$
The difference $a-b$ is, up to sign, $p(x)-p(x^{\oplus i})$ for either extension of $x_{-i}$. Taking expectations and using $q_i(1-q_i)\le1/4$ gives the display. Wu’s theorem and averaging over $i$ give the rest. ∎

This does **not** yield an $n$-independent AA bound: it loses exactly $1/n$ when passing from total to maximum influence. Nor does it construct BDST face-supported routing.

## 2. Curie–Weiss: proof including criticality and failure above it

### 2.1 Exact slice mixture and influence/variance identities

On $\{0,1\}^n$, let $S(x)=|x|$ and $M=2S-n$. For $\beta\ge0$, define
$$
\mu_\beta(x)=Z_{n,\beta}^{-1}\exp\!\left(\frac{\beta}{2n}M(x)^2\right),\qquad
p_\beta(t)=\mu_\beta(S=t).
$$
The energy depends only on $S$, so conditioning on $S=t$ gives the uniform slice $\nu_t$:
$$\mu_\beta=\sum_{t=0}^np_\beta(t)\nu_t,\qquad
p_\beta(t)=Z_{n,\beta}^{-1}\binom nt\exp\!\left(\frac{2\beta}{n}(t-n/2)^2\right).$$

The tower law immediately gives, for every $f$,
$$
\operatorname{Inf}_i^{\mu_\beta}(f)=\sum_t p_\beta(t)\operatorname{Inf}_i^{\nu_t}(f), \tag{CW-1}
$$
and the law of total variance gives
$$
\operatorname{Var}_{\mu_\beta}(f)
=\sum_t p_\beta(t)\operatorname{Var}_{\nu_t}(f)
+\operatorname{Var}_{t\sim p_\beta}(F(t)),
\quad F(t)=\mathbb E_{\nu_t}f. \tag{CW-2}
$$
No independence or low-degree hypothesis is used in (CW-1)–(CW-2). A flip may leave the slice; the definition of $\operatorname{Inf}_i^{\nu_t}$ accounts for it correctly.

### 2.2 Slice expectations are Lipschitz

First recall the pointwise total-flip estimate. For $f:\{0,1\}^n\to[0,1]$ of degree at most $D$ and any $A\subseteq[n]$, define $g(s)=\mathbb E[f(X(s))]$, where each bit in $A$ is flipped independently with probability $s$. Then $\deg g\le D$, $|g|\le1$ on $[0,1]$, and the Markov brothers inequality gives
$$
\left|\sum_{i\in A}(f(x^{\oplus i})-f(x))\right|=|g'(0)|
\le2D^2. \tag{MB}
$$
Splitting the flip differences into positive and negative parts yields, pointwise,
$$
\sum_i(f(x)-f(x^{\oplus i}))^2
\le\sum_i|f(x)-f(x^{\oplus i})|\le4D^2. \tag{TF}
$$

**Lemma 2.1 (GMNR Lemma 4.9).** If $F(t)=\mathbb E_{\nu_t}f$, then
$$|F(t)-F(t-1)|\le\frac{4D^2}{n},
\qquad |F(t)-F(u)|\le\frac{4D^2}{n}|t-u|.$$

**Proof.** Sample $X$ uniformly on slice $t$ and flip a uniformly chosen $1$-coordinate. This produces a uniform point of slice $t-1$. Hence
$$F(t-1)-F(t)=\mathbb E\!\left[\frac1t\sum_{i:X_i=1}(f(X^{\oplus i})-f(X))\right],$$
whose absolute value is at most $2D^2/t$ by (MB). Doing the same from slice $t-1$ toward $t$ gives the bound $2D^2/(n-t+1)$. Using $\max(t,n-t+1)\ge n/2$ gives $4D^2/n$. Telescope for arbitrary $t,u$. ∎

Applying Lemma 2.1 to $f$ and to the degree-$2d$ functions $f^2$ and $h_i=(f-f^{\oplus i})^2$ gives the next stability estimate.

**Lemma 2.2 (additive stability).** Put
$$D_\beta:=\sum_t|p_\beta(t)-p_0(t)|\,|t-n/2|,$$
where $p_0(t)=2^{-n}\binom nt$ is the uniform binomial law. Then, for degree $\le d$ with $f\in[0,1]$,
$$
|\operatorname{Inf}_i^{\mu_\beta}(f)-\operatorname{Inf}_i^{\mu_0}(f)|
\le\frac{16d^2}{n}D_\beta,
$$
and
$$
|\operatorname{Var}_{\mu_\beta}(f)-\operatorname{Var}_{\mu_0}(f)|
\le\frac{24d^2}{n}D_\beta
\le\frac{48d^2}{n}D_\beta.
$$

**Proof.** For influence, subtract $H_i(\lfloor n/2\rfloor)$ from the signed sum $\sum_t(p_\beta-p_0)H_i(t)$, using that the coefficients sum to zero. The degree-$2d$ Lipschitz constant is $16d^2/n$. For variance, use $\operatorname{Var}(f)=\mathbb E f^2-(\mathbb E f)^2$: the second moments differ by at most $16d^2D_\beta/n$, and the squared means differ by at most $2\cdot4d^2D_\beta/n$. ∎

Since both $p_\beta$ and $p_0$ are symmetric about $n/2$, the triangle inequality and Cauchy–Schwarz yield
$$
D_\beta\le\sigma_\beta+\sigma_0,
\qquad \sigma_\beta^2=\operatorname{Var}_{\mu_\beta}(S),
\quad \sigma_0=\sqrt n/2. \tag{D-bound}
$$

### 2.3 Magnetization fluctuations

Write $m=M/n$. Stirling’s formula and $I(m)=\frac{1+m}{2}\log(1+m)+\frac{1-m}{2}\log(1-m)$ give, away from the endpoints,
$$p_\beta(M=nm)\asymp e^{-n(I(m)-\beta m^2/2)},\qquad
I(m)=\frac{m^2}{2}+\frac{m^4}{12}+O(m^6).$$
The Laplace method therefore gives:

- for fixed $\beta<1$, $\operatorname{Var}(M)=\Theta_\beta(n)$ and $\sigma_\beta=O_\beta(\sqrt n)$;
- at $\beta=1$, after $M=n^{3/4}u$, the limiting density is proportional to $e^{-u^4/12}$, hence $\operatorname{Var}(M)=\Theta(n^{3/2})$ and $\sigma_\beta=O(n^{3/4})$.

The same scaling calculation proves the finite-flatness formula in §3. These are also the classical Curie–Weiss fluctuation theorems (Ellis–Newman/Ellis); the asymptotic numerical constants 1.164 and 0.909 in the summary are numerical diagnostics, not needed for AA.

Thus, for every fixed $\beta\le1$,
$$\sigma_\beta=o(n),\qquad D_\beta/n\to0,$$
with rates $O_{\beta}(n^{-1/2})$ for $\beta<1$ and $O(n^{-1/4})$ at $\beta=1$.

### 2.4 AA assembly, including the repaired critical small-$n$ case

**Theorem 2.3.** For each fixed $\beta\le1$, AA holds for $\mu_\beta$ with constants depending only on $\beta,d,v$ and not on $n$.

**Proof.** Let $v=\operatorname{Var}_{\mu_\beta}(f)>0$. Using Lemma 2.2 and $D_\beta/n\to0$, choose $N=N(\beta,d,v)$ such that, for all $n\ge N$,
$$\frac{48d^2D_\beta}{n}\le\frac v2,
\qquad
\frac{16d^2D_\beta}{n}\le\frac12S_0(v/2,d).$$
For such $n$, uniform variance is at least $v/2$. Uniform AA and influence stability then give
$$\max_i\operatorname{Inf}_i^{\mu_\beta}(f)
\ge S_0(v/2,d)-\frac12S_0(v/2,d)
=\frac12S_0(v/2,d).$$
For $n<N$, Lemma 1.1 applies because $\mu_\beta$ has full support. If $a_\beta(N),b_\beta(N)$ bound its normalized minimum/maximum atom probabilities over $n<N$, then
$$\max_i\operatorname{Inf}_i^{\mu_\beta}(f)
\ge \frac{4a_\beta(N)}{b_\beta(N)N}\,v.$$
Both lower bounds are positive polynomials in $v/d$, with constants depending only on $\beta,d,v$ and not on $n$. This avoids the false “every distribution” $1/(2n^2)$ floor. ∎

### 2.5 Failure for $\beta>1$

For $\beta>1$, the Curie–Weiss rate function has two minimizing phase values $\pm m_*$, $m_*>0$. Let $f=\mathbf1_{\{M>0\}}$ (with any tie convention). Phase coexistence gives $\operatorname{Var}(f)=1/4-o(1)$. A single flip changes $M$ by two, so it can change the phase label only on a bounded neighbourhood of $M=0$:
$$\operatorname{Inf}_i^{\mu_\beta}(f)\le\mu_\beta(|M|\le2)
=\exp(-\Theta_\beta(n)).$$
The one-sided threshold has exact degree $n$ (proved in §8.4). If AA held with fixed $c,C>0$ independent of $n$, it would require $\max_i\operatorname{Inf}_i\ge c(1/(4n))^C$, polynomially rather than exponentially small. Contradiction. Hence the threshold $\beta_{\rm AA}=\beta_c=1$ is sharp.

## 3. Finite-flatness mean-field scaling

Suppose $\mu_n$ depends on $x$ only through $M$, with magnetization law governed by $p_n(m)\propto e^{-nJ(m)}$ on spacing $1/n$. Assume $J$ has a unique global minimum $m_*$, and, in a neighbourhood,
$$J(m)=J(m_*)+c|m-m_*|^{2k}+o(|m-m_*|^{2k}),\qquad c>0,$$
with the usual nondegenerate Laplace-tail hypotheses. Set $u=n^{1/(2k)}(m-m_*)$. Then
$$e^{-nJ(m)}\asymp e^{-c|u|^{2k}},\qquad dm=n^{-1/(2k)}du.$$
Consequently $|m-m_*|=\Theta(n^{-1/(2k)})$ in probability and
$$\operatorname{Var}(M)=n^2\operatorname{Var}(m)=\Theta(n^{2-1/k}).$$
In particular $\operatorname{Var}(M)=o(n^2)$ for every finite $k$. The same slice-stability and small-$n$ assembly as in Theorem 2.3 therefore proves AA for exchangeable mean-field models satisfying these regularity assumptions. The cases $k=1,2,3$ give exponents $1,3/2,5/3$, respectively. Multiple global minima can produce $\operatorname{Var}(M)=\Theta(n^2)$, in which case the stability error no longer vanishes; this does not by itself prove failure for every such model.

## 4. Degree one: the two susceptibility formulations

**Theorem 4.1.** Let $p(x)=a_0+\sum_i a_ix_i$ on $\{0,1\}^n$ be $[0,1]$-valued, and let $\Sigma_{ij}=\operatorname{Cov}_\mu(X_i,X_j)$. Write $\rho=\|\Sigma\|_{\rm op}$. Then
$$\max_i\operatorname{Inf}_i^\mu(p)\ge\frac{\operatorname{Var}_\mu(p)^2}{\rho^2}.$$
The same conclusion holds with $\rho$ replaced by $R=\sup_i\sum_j|\Sigma_{ij}|$, since $\|\Sigma\|_{\rm op}\le R$ by the Schur test. Under Wu’s hypothesis $r=\operatorname{rsp}(C)<1$,
$$\rho\le\frac{1}{4(1-r)},\qquad\text{so}\qquad
\max_i\operatorname{Inf}_i^\mu(p)\ge16(1-r)^2\operatorname{Var}_\mu(p)^2.$$

**Proof.** The range condition implies $\|a\|_1=\max p-\min p\le1$. Also $\operatorname{Inf}_i^\mu(p)=a_i^2$. Put $M=\max_i|a_i|=\sqrt{\max_i\operatorname{Inf}_i}$. Then
$$
\operatorname{Var}_\mu(p)=a^{\mathsf T}\Sigma a
\le\rho\|a\|_2^2
\le\rho M\|a\|_1
\le\rho M.
$$
Thus $M\ge\operatorname{Var}_\mu(p)/\rho$; squaring gives the result.
For the Wu estimate, Lemma 1.2 applied to arbitrary affine $f$ gives
$$a^{\mathsf T}\Sigma a\le\frac{\|a\|_2^2}{4(1-r)},$$
which is precisely the operator-norm statement. ∎

The summary’s sentence “Dobrushin gives $R\le1/[4(1-\alpha)]$” for the **absolute row sum** is not what follows from this argument. The valid Dobrushin statement here is for $\|\Sigma\|_{\rm op}$. Finite absolute row sums can instead be supplied by model-specific correlation decay (for example the cited tree, 1D, and 2D results); those external decay theorems are not reproved in this companion.

For a product of $k$-bit independent blocks, $\Sigma$ is block diagonal. Every block covariance operator has norm at most $k/4$ (its trace is at most $k/4$ and it is positive semidefinite). Theorem 4.1 therefore gives
$$\max_i\operatorname{Inf}_i\ge\frac{16}{k^2}\operatorname{Var}^2$$
for affine functions under every such block law.

## 5. Block-support flatness and the basic counterexample

### 5.1 Exact criterion and the $k=3$ witness

Fix a block law $\lambda$ with support $B\subseteq\{0,1\}^k$. Construct a graph on the **whole** cube by adding an edge $\{u,u^{\oplus i}\}$ whenever $u\in B$ and $i\in[k]$. A function has zero single-bit influence at every support atom exactly when it is constant on each connected component of this graph. Hence a nonconstant flat function exists iff $B$ meets at least two components.

For two support atoms $u,v$, this happens exactly when $d_H(u,v)\ge3$: at distance $1$ the atoms are adjacent, at distance $2$ a common off-support neighbour joins them, and at distance at least $3$ their closed neighbourhoods are disjoint. This corrects the obsolete “disconnected support graph” criterion.

At $k=3$, $B=\{000,111\}$ produces two components. For $f=\operatorname{MAJ}_3$,
- $\operatorname{Var}_\lambda(f)=1/4$, since $f(000)=0$ and $f(111)=1$ with equal probabilities;
- on either support atom, every one-bit flip stays in the same majority class, so $\operatorname{Inf}_i^\lambda(f)=0$ for all $i$.
The function has degree $3$. Taking independent blocks makes $n$ arbitrarily large while preserving variance $1/4$, degree $3$, and zero influence. Thus unrestricted block-independent AA is false for $k\ge3$. At $k\le2$, every two support atoms have distance at most $2$, so this particular mechanism cannot occur.

### 5.2 Exact smoothed-copy calculation

Let $\mu_q$ be obtained by choosing $000$ or $111$ with probability $1/2$ and then flipping each bit independently with probability $q\in(0,1/2)$. Global-complement symmetry still gives $\operatorname{Var}(\operatorname{MAJ}_3)=1/4$. A coordinate flip changes majority exactly when the other two bits differ; those two bits began equal and differ after independent noise with probability $2q(1-q)$. Hence
$$\operatorname{Inf}_i^{\mu_q}(\operatorname{MAJ}_3)=2q(1-q).$$
The reported Dobrushin values were independently enumerated in `scripts/audit_smwgvdmlu.py`; they are numerical evaluations, not an impossibility proof.

### 5.3 Exact-copy heat-bath dynamics has zero gap

For the unsmoothed copy law, conditional on the other two bits, a bit is forced to equal their common value. Hence $\operatorname{Var}_{\mu_i}(f)=0$ on every support atom for every $f$. The single-site heat-bath Dirichlet form therefore vanishes identically and its spectral gap is zero. Off-support majority values used in the unweighted flip definition do not help the heat-bath form, which has zero transition rate out of each copy atom. Tensorised block resampling is a different generator; a positive unweighted flip-form constant cannot be cited as its Glauber MLSI constant.

## 6. Conditional expectations, global gradients, and influence comparisons

### 6.1 The 3-path is affine-preserving; the star raises degree

On the Ising 3-path with zero field, every conditional expectation of $x_i$ in an affine function remains affine. End sites satisfy $E[x_1\mid x_2]=x_2\tanh\beta$, and the centre satisfies
$$\tanh(\beta(x_1+x_3))=\frac{\tanh(2\beta)}2(x_1+x_3),$$
because an odd function of two bits has no quadratic term. The heat-bath generator therefore preserves the affine space.

On the star $K_{1,3}$ with centre $0$ and $S=x_1+x_2+x_3$,
$$E[x_0\mid x_{-0}]=\tanh(\beta S)
=c_1(x_1+x_2+x_3)+c_3x_1x_2x_3,$$
where oddness and symmetry give
$$c_1=\frac{\tanh(3\beta)+\tanh\beta}{4},
\qquad
c_3=\frac{\tanh(3\beta)-3\tanh\beta}{4}.$$
At $\beta=0.2$, $c_3<0$ and is nonzero. Thus
$$\mathcal Lx_0=-x_0+c_1(x_1+x_2+x_3)+c_3x_1x_2x_3$$
has exact degree $3$. The absolutely convergent expansion $P_t=I+t\mathcal L+O(t^2)$ gives a nonzero degree-$3$ coefficient $tc_3+O(t^2)$ for all sufficiently small $t>0$. Conditional expectation and Glauber semigroups therefore need not preserve multilinear degree.

### 6.2 Far monomials are not localizable around a coordinate

Under uniform product, take $p=x_ix_j$. Then
$$h_i=(p-p^{\oplus i})^2=x_j,\qquad h_j=x_i.$$
If $j\notin B(i,R)$, any $B(i,R)$-local $\ell$ is independent of $x_j$, so
$$\|h_i-\ell\|_2^2\ge\operatorname{Var}(x_j)=1/4,$$
with optimum $\ell=1/2$. Meanwhile $\sum_kh_k=x_i+x_j\le2$, comfortably below $4d^2=16$. Correlation decay therefore does not localize discrete gradients around $i$. This does not rule out expectation comparison on the small support $\{j\}$.

A legal global bounded example is
$$p_n(x)=x_{i_0}\frac1{n-1}\sum_{j\ne i_0}x_j.$$
Under uniform product it has degree $2$, range $[0,1]$, and
$$\operatorname{Var}(p_n)=\frac1{16}+\frac1{8(n-1)}.$$
Indeed, $p_n^2=x_{i_0}(n-1)^{-2}\sum_{j,k}x_jx_k$, whose mean is $[1+(n-1)/2]/(2(n-1))$, while $(\mathbb Ep_n)^2=1/16$. Its squared gradient at $i_0$ depends on all other coordinates.

### 6.3 Variance and per-coordinate influence under $L^2$ approximation

For $p,q:\{0,1\}^n\to[0,1]$,
$$|\operatorname{Var}_\mu(p)-\operatorname{Var}_\mu(q)|
\le4\|p-q\|_{2,\mu}.$$
To see this, bound the second-moment difference by $2\|p-q\|_2$ and the squared-mean difference by another $2\|p-q\|_2$.

If $\mu(x^{\oplus i})/\mu(x)\le C_{\rm RN}$ for all $x,i$, then
$$\mathbb E_\mu[(\Delta_i(p-q))^2]
\le2(1+C_{\rm RN})\|p-q\|_{2,\mu}^2,$$
where $\Delta_ir(x)=r(x)-r(x^{\oplus i})$. The proof is
$$(\Delta_ir)^2\le2r(x)^2+2r(x^{\oplus i})^2,$$
followed by the flip change of variables. Minkowski and $(u+v)^2\le2u^2+2v^2$ yield
$$\operatorname{Inf}_i^\mu(q)
\le2\operatorname{Inf}_i^\mu(p)+4(1+C_{\rm RN})\|p-q\|_2^2.$$
The same inequality applied with $p,q$ interchanged supplies the reverse comparison. Degree and pointwise boundedness are separate requirements: clipping an arbitrary $L^2$ approximant to $[0,1]$ need not preserve its multilinear degree.

### 6.4 Two independence-sensitive expectation calculations

On $\{\pm1\}^n$, let $f=1+n^{-1}\sum_i y_i$. Under uniform product $\mathbb E_Uf^2=1+1/n$. Under $\mu=\operatorname{Ber}(3/4)^{\otimes n}$ (encoding $q=(3/4,1/4)$ for $y_i=1,-1$), $\mathbb E_\mu f=1+1/2=3/2$ and
$$\mathbb E_\mu f^2=9/4+\operatorname{Var}(n^{-1}\sum y_i)=9/4+O(1/n).$$
No universal second-moment comparison without mean matching is possible.

Under uniform $\{0,1\}$ bits, put $p_m=m^{-1}\sum_{j=1}^mx_{2j-1}x_{2j}$. The transformation $q_j=y_{2j-1}y_{2j}$ with $y=2x-1$ gives independent mean-zero $q_j$, and
$$p_m=\frac14+\frac1{4m}\sum_j(y_{2j-1}+y_{2j}+q_j).$$
The three summands in each block are orthogonal, so
$$\operatorname{Var}(p_m)=\frac{3}{16m}.$$
Also $D_{2j-1}p_m=x_{2j}/m$ and $D_{2j}p_m=x_{2j-1}/m$, hence
$$\max_i\operatorname{Inf}_i(p_m)=\frac1{2m^2},
\qquad \frac{\max_i\operatorname{Inf}_i}{\operatorname{Var}}=\frac{8}{3m}.$$
This rules out an $n$-uniform linear bound $\max_i\operatorname{Inf}_i\ge c(d)\operatorname{Var}$ even for degree $2$ under uniform product.

### 6.5 The unbounded MLSI-junta obstruction, with its scope

For $\varepsilon>0$ small, let a two-bit block law be
$$\lambda_\varepsilon=(1-\varepsilon)\tfrac12(\delta_{00}+\delta_{11})
+\varepsilon\,\operatorname{Unif}_{4},$$
and let $\mu=\lambda_\varepsilon^{\otimes m}$ on $n=2m$ bits. Write $y_j=2x_{2j-1}-1$ and
$$\widetilde p_m=c\,m^{-1/2}\sum_{j=1}^m(-1)^jy_jy_{j+1},$$
with indices read cyclically and $c=1/8$. This is a degree-$2$ example. The individual block laws have positive gap, and the respective reversible block-resampling functional inequality tensorises, giving an $n$-independent constant for this product family.

Every $y_j$ has mean zero: the copy component has equal masses at $-1$ and $+1$, and the uniform component also has mean zero. The products $Z_j=y_jy_{j+1}$ are orthonormal. Indeed $E Z_j^2=1$; for distinct $j,k$, either they are independent and have mean $E Z_j\,E Z_k=0$, or they share one mean-zero bit and another independent mean-zero bit makes their product mean zero. Thus $\operatorname{Var}(\widetilde p_m)=c^2$ exactly.

Let $q$ depend on at most $M$ coordinate bits. If $Z_j$ involves a bit outside that coordinate set, then $q$ is orthogonal to $Z_j$. At most $M$ of the $m$ products can have both endpoint bits observed. Orthonormality therefore gives the exact projection bound
$$\|\widetilde p_m-q\|_{2,\mu}^2
\ge c^2\left(1-\frac Mm\right).$$
For every fixed $M$ and every $\varepsilon>0$, the error remains bounded away from zero as $m\to\infty$. This rules out an $n$-independent junta for the functional inequality alone. However,
$$\|\widetilde p_m\|_\infty=\Theta(\sqrt m),$$
so this is **not** a counterexample to the bounded $[0,1]$ Lemma J. Clipping it to $[0,1]$ generally destroys its multilinear degree. The bounded version remains open.

## 7. Endpoint coupling, hybrid identity, and conditional moment route

### 7.1 Joint endpoint functional TV

Let $(z,z^k)$ be coupled product inputs and let $x=F(z),y=F(z^k)$, with truncations $x^R=F^R(z),y^R=F^R(z^k)$. Suppose $A_S$ is an event on which both truncated endpoints agree with the untruncated ones on $S$, with
$$\Pr[A_S^c]\le\eta(M_S,R)=2C_0M_Se^{-c_0\delta R}+2L2^{-L}.$$
Then, for every $[0,1]$-valued test functional $\Phi$,
$$|\mathbb E\Phi(x_S^R,y_S^R)-\mathbb E\Phi(x_S,y_S)|
\le\Pr[A_S^c]\le\eta(M_S,R).$$
The proof is simply that the difference vanishes on $A_S$ and is at most $1$ off it. An ordered path functional defined from **both** endpoints is an admissible $\Phi$ if it depends only on the displayed coordinates.

This proves a joint-law TV comparison only. It does not show that an intermediate path value is dominated by the original squared gradient or by $\operatorname{Inf}_i^\mu$; that separate missing step cannot be inferred from the TV estimate.

### 7.2 Exact hybrid/Taylor identity

Let $X\sim\mu$, $Y\sim\nu$ independently, and define
$$Z^{(i)}=(Y_1,\ldots,Y_i,X_{i+1},\ldots,X_n),\qquad
W^{(i)}=(Y_1,\ldots,Y_{i-1},X_{i+1},\ldots,X_n).$$
For any $h$, $\mathbb E_\mu h-\mathbb E_\nu h=\sum_i\mathbb E[h(Z^{(i-1)})-h(Z^{(i)})]$ exactly. Multilinearity gives
$$f(Z^{(i-1)})-f(Z^{(i)})
=(X_i-Y_i)\,\partial_ip(W^{(i)})/\sqrt v.$$
For $\psi\in C^3$, exact Taylor expansion gives
$$\begin{aligned}
\psi(f^{(i-1)})-\psi(f^{(i)})
={}&\psi'(f^{(i)})(X_i-Y_i)\partial_ip/\sqrt v\\
&+\tfrac12\psi''(f^{(i)})(X_i-Y_i)^2(\partial_ip)^2/v+R_i,
\end{aligned}$$
with
$$|R_i|\le\frac16\|\psi^{(3)}\|_\infty
|X_i-Y_i|^3|\partial_ip|^3/v^{3/2}.$$
These are identities only. The first-order covariance bound and any subsequent exponential-tail comparison remain open. A smooth $C^3$ error polynomial in $t$ does not prove a lower tail of size $e^{-\Theta(t^2)}$.

### 7.3 Conditional HC+CU route

Assume, for standardized $f$ with mean $0$, variance $1$, and $I=\max_i\operatorname{Inf}_i(f)$, both
$$\|f\|_q\le(K_0q)^{K_1d}\quad\text{(HC)},$$
and, for $q\ge3$,
$$|\kappa_q(f)|\le(C_1dq)^{C_2dq}I^{q/2-1}q!\quad\text{(CU)}.$$
After absorbing model-dependent constants, $\log M(s)=\sum_q\kappa_qs^q/q!$ gives, on the stated geometrically small interval,
$$\log M(s)=\frac{s^2}{2}+O(s^3\sqrt I).$$
Tilting by $dP_s=e^{sf}dP/M(s)$ differentiates the cumulant function once and twice. The tilted mean is $s+O(s^2\sqrt I)$ and the tilted variance is $1+O(s\sqrt I)$. Choosing $s=t+O(1)$ and using Chebyshev on the tilted law yields, in the admissible interval,
$$\Pr[f>t]\ge c\exp(-t^2/2+O(t^3\sqrt I)).$$
Apply the same argument to $-f$. Thus, whenever $t^3\sqrt I=O(1)$, the probability is positive with an $n$-independent lower bound. If $I\le c t^{-6}$ with suitable $c$, this condition holds.

For bounded $t$, HC and $Ef^4\le K^4$ give
$$\Pr(|f|>1/2)\ge\frac{(1-1/4)^2}{K^4}=\frac9{16K^4},$$
by splitting $Ef^2$ at level $1/2$ and applying Cauchy–Schwarz on the large part.

Finally, for $p\in[0,1]$ and $f=(p-\mathbb Ep)/\sqrt v$, boundedness makes $\Pr(|f|>2/\sqrt v)=0$. Taking $t=2/\sqrt v$ in the contrapositive gives, polynomially,
$$I\gtrsim t^{-6}\asymp v^3,
\qquad \max_i\operatorname{Inf}_i(p)=vI\gtrsim v^4.$$
This is a complete **conditional** proof only. HC and CU are not established under general Dobrushin, and the moment argument does not prove them.

## 8. Counterexamples used in the latest adjudication

### 8.1 BSC damping: exact identities and the two-site coefficient

Let $Y_i=W_iX_i$, with independent $W_i$ of mean $\rho$. Then
$$\mathbb E[Y_i\mid X]=\rho X_i,\qquad
\mathbb E[Y_i\mid Y_{-i}]=\rho\mathbb E[X_i\mid Y_{-i}],$$
by the tower property. For $i\ne j$,
$$\operatorname{Cov}(Y_i,Y_j)=\rho^2\operatorname{Cov}(X_i,X_j),$$
and $\operatorname{Var}(Y_i)=1-\rho^2(\mathbb E X_i)^2$. The diagonal qualification shows why full covariance row sums do not simply scale by $\rho^2$.

For zero-field two-site Ising $\mu_J(x)\propto e^{Jx_1x_2}$,
$$\mathbb E[Y_1Y_2]=\rho^2\tanh J,
\qquad \mathbb E[Y_1\mid Y_2]=\rho^2(\tanh J)Y_2.$$
Thus $c_{12}^Y=\rho^2\tanh J$ in the binary-conditional TV normalization, not $\rho\tanh J$. Conditioning on noisy outputs requires the posterior on $X$, so the identity $C^Y=\rho C^X$ does not follow.

For any bounded $p$, total variance gives
$$\operatorname{Var}_\nu(p)=\operatorname{Var}_\mu(T_\rho p)
+\mathbb E_X\operatorname{Var}(p(Y)\mid X),\qquad T_\rho p(x)=\mathbb E[p(Y)\mid X=x].$$
If $\mu$ is uniform product then $\nu=\mu$ for every $\rho$, so $\operatorname{Var}_\nu(p)-\operatorname{Var}_\mu(p)=0$. It would be incorrect to subtract $\operatorname{Var}_\mu(T_\rho p)$ here and call that zero; the conditional-noise term is generally nonzero.

### 8.2 Full-marginal TV is not controlled by fixed weak coupling

Take $m$ independent two-site Ising blocks with $J\ne0$, and let $\pi$ be uniform product of their marginals. For one block,
$$D(\mu_J\|U_2)=J\tanh J-\log\cosh J=K_J>0,$$
so total KL divergence is $mK_J$. More elementarily, let $T=\sum_{b=1}^mX_{b,1}X_{b,2}$ and $U=T\operatorname{sgn}J$. Then $U$ has mean $m|\tanh J|$ under $\mu$ and mean $0$ under $\pi$, and variance $O(m)$ under either. Chebyshev at $m|\tanh J|/2$ gives an event with probability tending to $1$ under $\mu$ and to $0$ under $\pi$. Hence the TV distance tends to $1$ for every fixed $J\ne0$, however small. Full-marginal TV cannot serve as an $n$-uniform product proxy at fixed positive coupling; this does not refute weaker comparisons confined to low-degree tests.

### 8.3 Hadamard quadratic with growing Fourier-$\ell_1$ norm

Let $H$ be an $N\times N$ Hadamard matrix, $HH^{\mathsf T}=NI_N$, and define
$$p_H(x,y)=N^{-3/2}\sum_{i,j=1}^NH_{ij}x_iy_j.$$
Since $H/\sqrt N$ is orthogonal,
$$|p_H(x,y)|=N^{-1}|x^{\mathsf T}(H/\sqrt N)y|
\le N^{-1}\|x\|_2\|(H/\sqrt N)y\|_2\le1.$$
It has degree $2$ and $N^2$ nonzero Walsh coefficients, each of size $N^{-3/2}$. Hence its Fourier-$\ell_1$ norm is $N^2N^{-3/2}=\sqrt N$. Thus sup norm and degree do not give a dimension-independent coefficient-$\ell_1$ estimate. This example is not automatically of the restricted squared-gradient form $(p-p^{\oplus i})^2$; the bridge problem for that restricted class remains open.

### 8.4 One-sided thresholds; cancellation for two-sided thresholds

For $I_{k_0}(x)=\mathbf1_{\{|x|>k_0\}}$, $0\le k_0<n$, the top coefficient is
$$2^{-n}\sum_{t=k_0+1}^n\binom nt(-1)^t
=2^{-n}(-1)^{k_0+1}\binom{n-1}{k_0}\ne0,$$
using $\sum_{t=0}^{k_0}(-1)^t\binom nt=(-1)^{k_0}\binom{n-1}{k_0}$. Therefore $\deg I_{k_0}=n$ exactly.

No such universal statement holds for two-sided absolute-magnetization thresholds. On three bits, with $w=|x|$,
$$\mathbf1_{\{000,111\}}=1-\frac32w+\frac12w^2,$$
which has degree $2$, not $3$. Any general tail-degree proof must include support and parity/cancellation analysis.

For a specific valid example, edit only $1^n$ by flipping its first bit, and take $p=x_1$. Then
$$p(G(x))=x_1+(1-2x_1)\mathbf1_{\{1^n\}}(x),$$
whose top coefficient is $-2^{-n}(-1)^n\ne0$. Hence $\deg(p\circ G)=n$ exactly. This proves degree blow-up for this particular map, not for every tail map or every approximate implementation.

### 8.5 Influence and stability details that affect other claims

A uniform vector $\lambda_x=2/n$ is not a valid fractional certificate for Majority at a boundary 1-input: one sensitive flip of a single $1$ gives a 0-input, so every valid certificate must put at least mass $1$ on that coordinate. Consequently, the revised WAP/Majority separation based on $2/n$ certificates cannot be used.

The latest tail argument gives a TV separation at scale $n^{3/4}$. On the corresponding event it implies only
$$D\ge a n^{3/4}\,|\nu(E)-\nu_{\rm CW}(E)|=\Omega(n^{3/4}),$$
not $D=\Omega(n)$. This is compatible with $D=o(n)$ and therefore does not rule out the GMNR stability regime $D/n\to0$.

## 9. What is still open or not independently revalidated

HC, CU, Q4 and its derivative/ANOVA versions, the simultaneous bounded low-degree junta, the hybrid first-order covariance estimate, Gibbs restricted-distance routing, the general Dobrushin-to-product additive bridge, general BSC influence transfer, and universal tail-map impossibility are all **not proved**. Their conditional formulations above must not be cited without their hypotheses.

---

# Part II — Task 2: the summed-$(b')$ transportation LP

## 10.1 Birkhoff rounding is valid, but does not prove feasibility

Recall the exact target. For a fixed $A$ and monochromatic faces $T(x)$, put
$$F(x)=\{z\in A:z_i\ne x_i\ \text{for every }i\in T(x)\}.$$
Suppose $M=(M_{xy})_{x,y\in A}$ is doubly stochastic, $M_{xy}=0$ whenever $y\notin F(x)$, and
$$\sum_{x,y}M_{xy}\sum_iw_i\mathbf1[y_i=x_i]
\le B^w:=\sum_iw_i\#\{x\in A:x^{\oplus i}\notin A\}.$$

**Lemma 10.1.** Under those assumptions, there is one permutation $\pi:A\to A$ such that $\pi(x)\in F(x)$ for every $x$, and
$$\sum_x\sum_iw_i\mathbf1[\pi(x)_i=x_i]\le B^w.$$

**Proof.** Birkhoff–von Neumann writes $M=\sum_\ell\theta_\ell P_\ell$ as a convex combination of permutation matrices. If $(P_\ell)_{xy}>0$, then $M_{xy}>0$, so every positive entry of every $P_\ell$ respects $F$. Each component therefore satisfies the face constraint. The cost is linear in $M$, hence its $\theta$-average is at most $B^w$; at least one component has cost at most $B^w$. ∎

This proves only the rounding step. No explicit dual-feasible $(\alpha,\beta)$, fiberwise Hall theorem, smaller-layer saturation theorem, or Gale–Shapley projection has been supplied. Those remain the substance of the open LP.

## 10.2 Hall’s condition and the false “wings” induction

The face-allowed graph has a perfect matching exactly when, for every $S\subseteq A$,
$$\left|\bigcup_{x\in S}F(x)\right|\ge|S|.$$
This is Hall’s condition applied to $\{(x,y):y\in F(x)\}$; it is not itself an induction proof.

The proposed wings inequality fails already at $n=1$. Take
$$A=\{0,1\},\qquad T(0)=\varnothing,\qquad T(1)=\{1\}.$$
Then $F(0)=A$ and $F(1)=\{0\}$, so Hall’s condition holds. With $S=A$ in the proposed notation, $S_{0,\rm free}=\{0\}$ and $S_{1,\rm forced}=\{1\}$, but the layer-$0$ neighbourhood has size $1$, not the required $|S_{0,\rm free}|+|S_{1,\rm forced}|=2$. Any proof using that inequality is invalid. A distinct-projection/private-neighbour repair was only asserted and is not reproduced as a theorem.

## 10.3 Directed boundary submodularity

For $S\subseteq A$, let
$$B_i(S)=\{x\in S:x^{\oplus i}\notin S\}.$$

**Lemma 10.2.** For every $U,V\subseteq A$,
$$|B_i(U\cup V)|+|B_i(U\cap V)|\le|B_i(U)|+|B_i(V)|.$$

**Proof.** It suffices to prove the inequality at each $x$. Define
$$b_S(x)=\mathbf1[x\in S,\;x^{\oplus i}\notin S].$$
Then $B_i(S)=\sum_xb_S(x)$. The desired pointwise inequality is
$$b_{U\cup V}(x)+b_{U\cap V}(x)\le b_U(x)+b_V(x).$$
There are only $2^4$ choices of membership of $x$ and $x^{\oplus i}$ in $U,V$. If $x\notin U\cup V$, all terms on the left are zero. If $x$ belongs to exactly one of $U,V$, the right side is the indicator of $x^{\oplus i}$ being absent from that set, which dominates the left side. If $x\in U\cap V$, direct comparison of the three cases $x^{\oplus i}\in U\cap V$, $x^{\oplus i}\in U\triangle V$, and $x^{\oplus i}\notin U\cup V$ gives respectively $0\le0$, $1=1$, and $2=2$. Summing over $x$ proves the lemma. ∎

This structural fact does not resolve the weighted LP or its dual.

## 10.4 A doubly stochastic coupling need not be a permutation

On any finite $A$ of size $N\ge2$, the independent uniform matrix $M_{xy}=1/N^2$ is doubly stochastic. It is a nontrivial mixture of many permutation matrices; no single deterministic $\pi$ has joint distribution $(X,\pi(X))$ equal to $(X,Y)$ with $Y$ independent of $X$. Thus a fiberwise doubly stochastic coupling does not automatically furnish a fiberwise SDR. Birkhoff decomposition works only after the **global** face-supported matrix and its cost bound have been established.

## 10.5 Three elementary certificate facts (not an LP solution)

For completeness, the following claims from the $(L')$ discussion are elementary.

- On an adjacent bichromatic pair $\Delta(x,y)=\{i\}$, validity gives $\lambda_x(i)\ge|p(x)-p(y)|\ge p(x)-t$ when $p(x)>t\ge p(y)$. Thus $(L')$ holds on edges.
- The all-ones certificate family has cost $n$ and satisfies $(L')$, because overlap is $|\Delta(x,y)|$ and $|p(x)-t|\le1\le|\Delta(x,y)|$. Thus $(L')$ costs nothing beyond the trivial bound when $d^2\ge n$; this includes every Boolean-valued function since its degree is $n$.
- If $\min_{j\in\Delta}\lambda_x(j)\ge\max_{j\in\Delta}\lambda_y(j)$, certificate validity at $y$ gives
  $$
  \operatorname{overlap}(x,y)
  \ge\Big(\min_{j\in\Delta}\lambda_x(j)\Big)\lambda_y(\Delta)
  \ge\Big(\min_{j\in\Delta}\lambda_x(j)\Big)(p(x)-t).
  $$
  Since $\lambda_y(i)\le\max_{j\in\Delta}\lambda_y(j)\le\min_{j\in\Delta}\lambda_x(j)$ for every $i\in\Delta$, this proves $(L')$.

These facts do not construct an $O(d^2)$-cost family for generic nonsymmetric small $d$.

## 10.6 Numerical routing observations are not proofs

The constructive biased-product walk’s ratios, the 720 random LP instances, 2683 face examples, and small-$n$ ILP values are reproducible numerical observations using `scripts/exp9_biased_product.py` and `scripts/exp9b_biased_opt.py`. They are not proofs of boundedness in $n$, feasibility of the LP, or nonexistence of a counterexample. The $n=4,k=2,p=0.1,p=25$ infeasibility anomaly remains unexplained.

The exact summed-$(b')$ LP therefore remains open.

---

# Part III — Task 3: Escudero’s fcb conjecture

## 11.1 Established external result

Escudero Gutiérrez, arXiv:2304.06713v2, Theorem 1.6 states that if $p$ is homogeneous of degree $d$ and $\|p\|_{\mathrm{fcb},d}\le1$, then
$$\max_i\operatorname{Inf}_i(p)\ge\operatorname{Var}(p)^2.$$
The abstract and Theorem 1.6 explicitly confirm the statement. This companion does not reproduce its noncommutative-Khintchine proof. The alternative block-multilinear completely bounded result is also stated in that paper. There is no verified “Lemma 5.2: $FC_{\rm fcb}=O(d)$”; the earlier citation was fabricated and must not be used.

## 11.2 Homogeneous levels: influence does add; fcb norm is the obstruction

The summary’s claim that influence fails to add across homogeneous levels is **incorrect for the usual uniform-cube influence**. Let
$$p=\sum_{k=0}^dp_k,\qquad D_ip(x)=p(x)-p(x^{\oplus i}),$$
where $p_k$ is homogeneous of degree $k$. Under uniform measure, $D_ip_k$ is homogeneous of degree $k-1$, so terms at different levels are orthogonal. Parseval gives the exact identities
$$
\operatorname{Inf}_i(p)=\sum_{k=1}^d\operatorname{Inf}_i(p_k),
\qquad
\operatorname{Var}(p)=\sum_{k=1}^d\operatorname{Var}(p_k).
$$
Thus level decomposition itself is not the obstruction.

The obstruction is the fcb norm of the normalized levels. Put $B_k=\|p_k\|_{\mathrm{fcb},k}$. If $B_k>0$, Escudero’s theorem applied to $p_k/B_k$ gives, after rescaling,
$$\operatorname{Inf}_i(p_k)\ge B_k^{-2}\operatorname{Var}(p_k)^2$$
for some coordinate $i$ depending on $k$. Therefore, choosing $k$ with $\operatorname{Var}(p_k)\ge\operatorname{Var}(p)/d$, there is some coordinate for which
$$
\operatorname{Inf}_i(p)
\ge\operatorname{Inf}_i(p_k)
\ge\frac{\operatorname{Var}(p)^2}{d^2B_k^2}. \tag{fcb-level}
$$

**Conditional consequence.** If every nonzero level has $B_k\le B_d$, then the nonhomogeneous theorem follows immediately with $\max_i\operatorname{Inf}_i(p)\ge\operatorname{Var}(p)^2/(d^2B_d^2)$. If $B_k\le1$ for every level, the nonhomogeneous conjecture follows with no extra fcb loss. The general nonhomogeneous case remains open because no such level-norm bound has been established from $\|p\|_{\mathrm{fcb},d}\le1$.

This is the corrected statement of the level/pigeonhole route. It is not a proof of nonhomogeneous fcb.

## 11.3 Remaining tasks

A viable continuation must prove a level-uniform bound on $B_k$, a polarization preserving fcb norm and degree, or a direct operator-space argument. The summary’s candidate routes are research directions, not proved reductions. There is currently no fcb fractional-certificate theorem in the project.

---

# Part IV — Coverage ledger and items that must not be presented as proved

## 12.1 Proof status of the summary’s principal claims

| Summary item | Status in this companion |
|---|---|
| Curie–Weiss AA for $\beta\le1$ and failure for $\beta>1$ | **Proved above modulo uniform AA and standard Laplace asymptotics.** The small-$n$ branch was repaired by Lemma 1.1; the old universal $1/(2n^2)$ correlated-hybrid floor is not used. |
| Finite-flatness $\operatorname{Var}(M)=\Theta(n^{2-1/k})$ and mean-field AA | **Proved under explicitly stated Laplace regularity assumptions**, then the same external-uniform-AA assembly. Numerical constants and doubling ratios are not part of the theorem proof. |
| Degree-one AA under Dobrushin | **Proved above** with $\|\Sigma\|_{\rm op}\le1/[4(1-r)]$ from Wu. The absolute-row-sum variant is proved only when such a row bound is separately supplied. |
| Degree-one consequences on trees, 1D, and 2D up to $\beta_c$ | **External correlation-decay inputs, not reproved here.** Do not cite the absolute row bound as a consequence of Wu alone. |
| Block flatness criterion and $k=3$ counterexample | **Proved above.** |
| Full $k=2$ block-independent theorem with $\delta_{\min}^{6}\operatorname{Var}^8/d^{12}$ | **Not proof-ready here.** The older `.ultramath/smwg6ksie/m2/proof.md` contains an argument, but its single-block routing step relies on computer enumeration/asserted special matching properties and was not independently revalidated in this audit. Keep the older `[PROJECT]` label; do not present it as an independently checked theorem from this document. |
| Stronger law-independent $k=2$ variant | **Conditional/unverified** because its level-$d$ comparison was not checked. |
| 2D Ising, degree 2 at $\beta=0.35$ | **Not independently revalidated here.** Only an older project-log claim and its coarse-graining strategy are on file. |
| Small-$\kappa$ AA/cluster moment comparison | **Not revalidated by the latest submissions.** The m4/m6/m7 product-bridge arguments failed at the operator-norm/full-TV steps. Do not cite those reports as a proof. The older project-log claim remains outside this companion’s checked results. |
| Exact CW mixture, slice-Lipschitz, and mean-aligned $D$ estimates | **Proved above.** |
| Corrected $L^2$ influence ledger and joint endpoint TV lemma | **Proved above.** Their missing influence domination remains open. |
| HC+CU $\Rightarrow$ MGF/tail/AA | **Conditional proof above; HC and CU are unproved.** |
| Exact hybrid/Taylor identity | **Proved above as an identity only.** The covariance and exponential-tail steps remain open. |
| Q4, derivative/ANOVA variants, weak DFKO tail, simultaneous bounded junta | **Open; no proof supplied.** |
| Independently checked BSC, Hadamard, full-TV, threshold, smoothed-copy calculations | **Proved above;** reproduction script `scripts/audit_smwgvdmlu.py` passes. |
| General Dobrushin AA, general product bridge, general BSC damping, universal tail no-go | **Not proved.** Latest swarm ended with zero accepted solutions. |

## 12.2 Task 2 status

**Proved above:** Birkhoff rounding, directed-boundary submodularity, the $n=1$ wings counterexample, the coupling-versus-permutation distinction, and the three elementary certificate observations.

**Not proved:** summed-$(b')$ feasibility or a counterexample, fiberwise Hall, an explicit dual certificate, smaller-layer saturated matching with weighted cost, Gale–Shapley projection, determinant-free generic low-degree AA, and any nonuniform face-supported Wu routing theorem. Numerical LP/ILP observations do not change that status.

## 12.3 Task 3 status

**External theorem:** homogeneous fcb, exactly as in Escudero Theorem 1.6.

**Proved above:** influence and variance add across homogeneous levels, and the conditional estimate (fcb-level).

**Not proved:** any general bound $\|p_k\|_{\mathrm{fcb},k}\le B_d$ from $\|p\|_{\mathrm{fcb},d}\le1$, norm-preserving polarization, nonhomogeneous fcb, or an fcb fractional-certificate bound.

## 12.4 Contextual and documentary claims

The following are not proved in this companion:

- the precise 2D/tree correlation-decay estimates and their bibliographic attribution;
- numerical asymptotics such as 1.164, 0.909, and measured doubling ratios;
- the massively parallel query-complexity exponents quoted in the summary;
- the completeness of the derivation of the withdrawn early $k=2$, 2D, and small-$\kappa$ proposals;
- formal unique-versus-multi-witness and HeurP-versus-AvgP statements, which require their own model definitions.

The copy-law example does prove that an unrestricted “AA for every correlated law” statement is false. For $\operatorname{AND}_n$, every fractional certificate at $1^n$ must put mass at least $1$ on each coordinate, because changing that single coordinate gives a 0-input; hence $FC(\operatorname{AND}_n)\ge n$, and the all-ones certificate gives equality at $n$. The standard external result $\widetilde\deg(\operatorname{AND}_n)=\Theta(\sqrt n)$ is cited but not reproved, illustrating that approximate degree alone cannot bound fractional certificate cost. Other contextual comments are background, not used in any proof above.

The O’Donnell–Zhao audit is documentary rather than a theorem proof: the local v1 text contains Corollaries 3.5 and 3.6 on uniform-product inputs, not an MLSI/general-measure junta theorem. Keller–Klein’s withdrawal notice is likewise a source-status check; no mathematical result from that paper is used.

## 12.5 Safe instructions for another model

1. Use the proved sections above without restoring rejected intermediate claims.
2. Treat uniform AA, Wu, Curie–Weiss/mean-field fluctuation theory, and Escudero’s homogeneous theorem as the only external black boxes explicitly named here; check their exact hypotheses before specialization.
3. Do not label the older $k=2$, 2D-Ising, or small-$\kappa$ statements “established” without first supplying and auditing their complete proofs.
4. Do not use full-marginal TV as a necessary condition for low-degree product approximation.
5. For nonhomogeneous fcb, attack the level-norm bound in (fcb-level), not influence additivity.
6. For Curie–Weiss, use the repaired full-support floor in Lemma 1.1; do not quote the false every-distribution $1/(2n^2)$ bound.
7. Preserve the distinction between exact low-degree tests and arbitrary-set routing. None of the conditional gadget reductions supplies the missing face-supported transportation matrix.

## Verification performed

- `python3 scripts/verify_proof_companion.py`: seven finite check groups passed (full-support comparison, affine influence, thresholds, boundary submodularity, fcb level additivity, BSC damping, and junta orthogonality).
- `python3 scripts/audit_smwgvdmlu.py`: passed, including the smoothed-copy and Hadamard checks.
- Pandoc converted this Markdown file to HTML. These are consistency checks, not substitutes for the written proofs above.
