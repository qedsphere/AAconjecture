# Tasks 1–3: results, proofs, counterexamples, and open gaps

**Purpose:** a compact, context-ready handoff of work on

1. AA for high-temperature Gibbs measures / Dobrushin inputs;
2. the summed-$(b')$ transportation LP intended to remove determinant machinery;
3. Escudero Gutiérrez’s nonhomogeneous Fourier-completely-bounded (fcb) conjecture.

This document merges the proof-pipeline log and the subsequent junta/DFKO investigations and corrections. It distinguishes **proved**, **conditional**, **numerical**, **open**, and **withdrawn/false** claims. It is not a list of accepted theorem claims: many initial submissions failed audit.

## Status notation

- **[PROVED]** a theorem or lemma with a specific proof, either from a primary source or independently checked in this project.
- **[PROJECT]** accepted in an earlier project log. The statement and its hypotheses should be retained, but the full proof was not independently re-derived in the latest audit pass.
- **[CONDITIONAL]** a valid reduction only if the named unproved lemma is supplied. None of these closes the main problem.
- **[NUMERICAL]** computational evidence only; not a proof.
- **[OPEN]** no gap-free proof or counterexample currently exists.
- **[FALSE/WITHDRAWN]** the statement or proof was found false/invalid and must not be reused.

The most important caution is that the recent **4 + 2 accepted submissions were narrow partial results**, not proofs of AA, the weak DFKO tail, or the simultaneous physical junta.

---

# 1. Task 1 — AA for Gibbs and Dobrushin measures

## 1A. Formal targets

For a Boolean Gibbs measure $\mu$ with bit-level Dobrushin coefficient $\alpha\le1-\delta$, bounded range/degree/fields, and every multilinear polynomial $p:\{0,1\}^n\to[0,1]$ of degree at most $d$, the AA goal is

$$
\max_i\operatorname{Inf}_i^\mu(p)
\ge c(\delta,\delta_0,\Delta,d,R_0)
\left(\frac{\operatorname{Var}_\mu(p)}d\right)^{C(\delta,\Delta,R_0,d)},
$$

where $c,C>0$ are independent of $n$. Here

$$\operatorname{Inf}_i^\mu(p)=\mathbb E_{x\sim\mu}[(p(x)-p(x^{\oplus i}))^2].$$

A junta-free alternative is the **weak DFKO tail**. Put $v=\operatorname{Var}_\mu(p)>0$, $m=\mathbb E_\mu p$, and $f=(p-m)/\sqrt v$. If $I=\max_i\operatorname{Inf}_i^\mu(f)$, prove

$$I\le\frac{\eta_0(t)}{t^2}
\quad\Longrightarrow\quad
\Pr_\mu[|f|>t]\ge\eta_1(t)>0,$$

with $\eta_0,\eta_1$ independent of $n$, and with

$$\eta_0(t)\ge c\,t^{-A}$$

for fixed positive $c,A$. This is sufficient, not necessary in general, to obtain AA:

$$\max_i\operatorname{Inf}_i^\mu(p)
\ge \frac14v^2\eta_0(2/\sqrt v)
\ge c'v^{2+A/2}.$$

An exponentially decaying threshold $\eta_0(t)=e^{-Ct^2}$ is **not enough** for polynomial AA: it yields only $v^2e^{-\Theta(1/v)}$.

The simultaneous physical-junta version sought by an earlier route also remains open: find a single low-degree, pointwise-bounded polynomial junta $q$, on an $n$-independent support, achieving both $\|p-q\|_{L^2(\mu)}^2\le\eta$ and $\|p-q\|_{L^2(\widetilde\mu^R)}^2\le\eta$.

## 1B. Established earlier results [PROJECT]

### Curie–Weiss and mean-field models

- **Curie–Weiss, sharp threshold:** AA holds for $\beta\le1$, including $\beta_c=1$, and fails for $\beta>1$. The route uses exact mixture/slice identities, stability to uniform measure, and a small-$n$ Poincaré floor.
- **Verification of critical asymptotics:**
  $\operatorname{Var}(S)=\Theta(n^{3/2})$ at $\beta=1$;
  $\operatorname{Var}(S)/n^{1.5}\to1.164$ and the doubling ratio $\to2.838$ (predicted $2^{1.5}=2.828$).
- The weighted slice distance $D=\sum_t|p_\beta-p_{\mathrm{Bin}}||t|$ satisfies
  $D/n^{0.75}\to0.909$, hence $D/n=O(n^{-1/4})\to0$ and the stability error $O(d^2D/n)$ vanishes.
- **Finite-n warning:** the crossover is slow; small-$n$ numbers do not locate $\beta_c$. The relevant scale is $n\gg(\beta-1)^{-3/2}$.
- **General degenerate mean-field minima:** if the rate function has finite flatness $I(m)=I(m_*)+c|m|^{2k}$ at its minimum, then $\operatorname{Var}(S)=\Theta(n^{2-1/k})=o(n^2)$ and the same AA strategy applies. Measured doubling exponents $1.000,1.500,1.667$ match $2-1/k=1,1.5,1.667$.

### Degree-one bounds and tree/mean-field consequences

For affine $f$, with finite covariance row bound $R=\sup_i\sum_j|\operatorname{Cov}(i,j)|$,

$$\max_i\operatorname{Inf}_i(f)\ge \operatorname{Var}(f)^2/R^2.$$

Dobrushin gives $R\le1/[4(1-\alpha)]$, hence a degree-one bound with $n$-uniform constants. Consequences include:

- Dobrushin Gibbs at degree 1 generally;
- one-dimensional Ising at every finite $\beta$ at degree 1;
- two-dimensional Ising at degree 1 up to $\beta_c$ (using standard correlation-decay results);
- $b$-ary trees at $\beta_c=\operatorname{artanh}(1/b)$, showing the AA threshold can be **strictly above** the Dobrushin threshold $\beta_D$ (and below the KS threshold $\operatorname{artanh}(1/\sqrt b)$). Dobrushin is sufficient, not necessary, for AA.

### Block-independent special cases

Correct geometric criterion: flatness requires two support atoms whose **closed neighbourhoods are disjoint**, equivalently, for two atoms, Hamming distance at least 3. A flip landing off-support still matters because the Dirichlet/flip weight uses $\lambda(x)>0$.

- Original naive statement “disconnected support graph” is false as a criterion. For the $k=2$ copy law uniform on $\{00,11\}$, the support graph has no edges, but the two closed neighbourhoods intersect, so no flat nonconstant block function exists.
- For every $k=2$ law with at least two support atoms, closed neighbourhoods meet, giving positive finite-block Poincaré gap with the unweighted flip form.
- A $k\ge3$ counterexample remains decisive: $\lambda$ uniform on $\{000,111\}$ and $f=\operatorname{MAJ}_3$ has $\operatorname{Var}(f)=1/4$ but every single-bit flip influence is zero. Any general block-independent AA claim for unrestricted $k\ge3$ is therefore false.
- A reported full $k=2$ theorem has
  $\max\operatorname{Inf}\ge c\,\delta_{\min}^{-6}\operatorname{Var}^8/d^{12}$,
  with $\delta_{\min}$ the least block-atom probability. This is accepted in the older log but should be referenced with its exact proof, not casually generalized.
- A stronger $k=2$ result with law-independent constants was **accepted only conditionally** because its level-$d$ comparison lemma was not independently audited. Do not treat it as established.

### Ising in restricted regimes

- **2D Ising at $\beta=0.35$, degree 2:** a coarse-graining/SSM proof gives $n$-uniform AA, with a formal but practically useless constant around $10^{-300}$ from block size 100 and huge regularity factors. This reaches beyond $\beta_D=0.25$ but not $\beta_c\approx0.4407$.
- **Higher-temperature expansion:** for sufficiently small $\kappa=\beta\|J\|_{\rm row}$, connected-cluster counts compare low-degree Walsh moments to product measure. Crude animal counting gives roughly $\kappa<1/e$ and sharper lattice constants about $\kappa<1/2.3$. Crucially $\Delta$ cancels along $(e\Delta)^\ell(\kappa/\Delta)^\ell=(e\kappa)^\ell$. This does not cover the interval up to Dobrushin $\kappa<1$.
- **1D Ising, higher degrees:** only a conditional transfer-matrix/LSI route remains in the notes; do not quote it as an established general-degree theorem without the block-routing step.

## 1C. The junta citation failure and what OZ actually says

An earlier claimed full Dobrushin proof using “O’Donnell–Zhao 2016 Theorem 3.5 with modified log-Sobolev parameter $\rho$” is **withdrawn**.

Checked source: O’Donnell–Zhao, *Polynomial bounds for decoupling, with applications*, [arXiv:1512.01603v1](https://arxiv.org/html/1512.01603v1):

- There is no Theorem 3.5 and no statement of a general-measure MLSI junta theorem with $\rho$.
- **Corollary 3.5** concerns uniform Boolean inputs, assumes a small maximum influence of order $\exp(-Ct^2d^2)$, and uses Gaussian invariance.
- **Corollary 3.6** is a uniform-measure Fourier-tail theorem: if $f$ is not an $(\varepsilon,2^{O(k^2/\varepsilon)})$-junta then a high-level tail has size $>\exp(-O(k^2)/\varepsilon)$. For bounded degree $d$, this gives the usual uniform-product junta approximation.
- Ingredients include Walsh orthogonality, commuting independent noise, Gaussian one-block decoupling, and the MOO invariance principle. Glauber MLSI alone does not supply them.

**Do not revive that citation.** Junta approximation over correlated $\mu$ from a Glauber semigroup MLSI constant remains unproved. ArXiv/DOI links and the checked text are recorded in `notes/dfko-repair-outcomes.md` and `.scratch/chk/oz.txt`.

## 1D. Important proved structural facts and counterexamples

### Valid degree-growth example

Heat-bath Glauber on the 3-leaf star $K_{1,3}$ maps a degree-1 polynomial into degree 3:

$$\mathcal Lx_0=-x_0+c_1(x_1+x_2+x_3)

+c_3x_1x_2x_3,\qquad
c_3=\frac{\tanh(3\beta)-3\tanh\beta}{4}.$$

At $\beta=0.2$, $c_3\neq0$. Hence $P_tx_0$ has a nonzero degree-3 term for small $t$. Because $c_3<0$, any small-$t$ interval must use $|c_3|$ in its bound.

By contrast, the Ising 3-path preserves affine functions: there $\mathcal L V_1\subseteq V_1$ and $P_tV_1\subseteq V_1$. Thus **do not use the 3-path as a degree-growth counterexample**.

### Conditional expectations raise degree: ANOVA is not safe

The star gives
$$\mathbb E_0[x_0]=\tanh(\beta(x_1+x_2+x_3)),$$
which has a nonzero cubic component. Therefore block-Hoeffding degree, ANOVA degree, and semigroup level are not automatically bounded by original multilinear degree. Any proof claiming block-degree preservation or $P_t h=e^{-kt}h$ without proof must be rejected.

### Bounded versus unbounded MLSI obstruction

An unbounded degree-2 example, built from alternating Rademacher pair products, has constant-order variance and requires $\Omega(n)$ relevant coordinates for a small-error junta approximation. It demonstrates that a pure MLSI assumption cannot, by itself, produce the desired junta theorem. **It is not a counterexample to bounded Lemma J:** its range grows like $\sqrt m$, and clipping to $[0,1]$ destroys multilinear degree. The bounded MLSI claim and the bounded Dobrushin claim therefore remain distinct open problems.

### Far monomial kills generic gradient localization

For uniform product and $p=x_ix_j$ with $\operatorname{dist}(i,j)>R$,
$$h_i(x)=(p(x)-p(x^i))^2=x_j.$$

For every $B(i,R)$-local $\ell$,

$$\|h_i-\ell\|_2^2\ge1/4,$$

with optimum $\ell=1/2$. Moreover $\sum_kh_k=x_i+x_j\le2\le4d^2$ for $d=2$, so the GMNR total-influence budget does not rescue localization. Degree-2 monomials can have globally dispersed support. Correlation decay does not imply $R$-local approximability.

This is an obstruction to **local approximation**, not by itself a refutation of TV comparison on the actual support $\{j\}$.

### Correct Dirichlet dynamics for copy blocks

For exact copy $\lambda$ uniform on $\{00,11\}$, single-site heat-bath has zero gap: transitions leaving the copy states have rate zero. The unweighted flip form’s positive finite-block gap is **not** the reversible heat-bath MLSI constant. Tensorised block resampling dynamics is the appropriate block-MLSI object. Do not cite a positive single-site Glauber MLSI for the exact copy law.

### Bounded global-gradient witness

The legal polynomial
$$p_n=x_{i_0}\frac1{n-1}\sum_{j\ne i_0}x_j,$$
is bounded on $\{0,1\}^n$, has degree 2 and
$$\operatorname{Var}(p_n)=\frac1{16}+\frac1{8(n-1)}.$$
Its $h_{i_0}$ depends on the other $n-1$ coordinates. This provides a genuine bounded global example with $\Theta(n)$ gradient support; no need for the unbounded polynomial $(n^{-1/2}\sum x_j)^2$.

### A biased-product mean-square obstruction

A proposed universal comparison $\|f\|_{L^2(\mu)}\le C\|f\|_{L^2(U)}$ for degree-bounded polynomials is false without a matching first-moment hypothesis. Let $\mu=\operatorname{Ber}(3/4)^{\otimes n}$ on $\{\pm1\}^n$, $U$ uniform, and $f=1+n^{-1}\sum_i y_i$:
$$\|f\|_{L^2(U)}^2=1+1/n,\qquad
\mathbb E_\mu f^2\to9/4.$$
The mean-square term cannot be omitted.

### Duplicate-pair average: no linear variance-to-influence bound

For $p_m=m^{-1}\sum_{j=1}^m x_{2j-1}x_{2j}$ under uniform independent bits,
$$\operatorname{Var}(p_m)=\frac3{16m},\qquad
\max_i\operatorname{Inf}_i(p_m)=\frac1{2m^2},$$
so $\max\operatorname{Inf}/\operatorname{Var}=8/(3m)\to0$. This refutes $n$-uniform versions of $\max\operatorname{Inf}\ge c(d)\operatorname{Var}$; a polynomial in $v$, here $v^2$, is necessary.

## 1E. Accepted partial analytic steps (not AA proofs)

### Corrected $L^2$ influence ledger

For bounded $p,q$, with $C_{\rm RN}\le(1-\delta_0)/\delta_0$,

$$\mathbb E_\mu[(\Delta_i(p-q))^2]
\le2(1+C_{\rm RN})\|p-q\|_{2,\mu}^2.$$

This follows by flipping variables and using $\mu(x^i)/\mu(x)\le C_{\rm RN}$. It gives a per-coordinate influence comparison. Separately, $|\operatorname{Var}_\mu(p)-\operatorname{Var}_\mu(q)|\le4\|p-q\|_2$.

**Requirements:** preserve the distinction between $\eta$ and $\sqrt\eta$, and require $q$ to be both multilinear degree $\le d$ and pointwise bounded. Clipping a general junta to $[0,1]$ need not preserve multilinear degree and can invalidate the product-AA application.

GMNR Lemma 2.11 correctly gives $\sum_i(f(x)-f(x^i))^2\le4d^2$ pointwise for bounded degree-$d$ $f$, under any distribution. Earlier denials of that citation were themselves wrong and have been withdrawn.

### Joint endpoint functional TV lemma

For ordered pairs $(x^R,y^R)=(F^R(z),F^R(z^k))$ and $(x,y)=(F(z),F(z^k))$, on $A_S=G_S\cap G'_S$, both truncations agree with their untruncated counterparts. For bounded $\Phi$,

$$\left|\mathbb E_{\pi_k}\Phi(x_S^R,y_S^R)-\mathbb E_{\pi_k}\Phi(x_S,y_S)\right|
\le 2C_0M_Se^{-c_0\delta R}+2L2^{-L}.$$

The path functional is correctly a function of **both** endpoints; the previous definition from only $x^R$ was invalid.

**Still missing:** the additional domination/aggregation connecting that functional to $\operatorname{Inf}_i^\mu$. This is not an influence-transfer theorem or AA proof.

## 1F. Conditional cumulant/MGF reduction [CONDITIONAL]

Suppose, for suitably normalized $f$, both a hypercontractive moment and cumulant estimate hold:

$$\|f\|_q\le(K_0q)^{K_1d}\|f\|_2, \tag{HC}$$

$$|\kappa_q(f)|\le(C_1dq)^{C_2dq}I^{q/2-1}q!. \tag{CU}$$

Then over the relevant interval,
$$\log M(s)=s^2/2+O(s^3\sqrt I).$$

At $s=t+C$ for a suitable constant $C$, the tilted mean lies above $t$ with bounded tilted variance, so Chebyshev gives constant central-mass probability. Backward tilting gives

$$\Pr[f>t]\ge c\exp(-t^2/2+O(t^3\sqrt I)).$$

Using both signs and arranging $t^3\sqrt I=O(1)$ gives a weak DFKO tail with a polynomial-in-$t$ influence threshold, and hence polynomial AA conditionally via the usual cutoff.

**HC+CU remain completely unproved.** Dirichlet proofs, derivative/ANOVA versions, and the small-$\kappa$ corollary are not accepted. This is a useful sufficient package only, not a completed route.

## 1G. Exact hybrid/Taylor framework and remaining covariance gap

With $Z^{(i)}=(Y_1,\dots,Y_i,X_{i+1},\dots,X_n)$ under $\mu\otimes\nu$, the telescoping and third-order Taylor identities are exact. They define a framework for dependent replacement, not a proof of invariance. The needed first-order bound is

$$\left|\sum_i\mathbb E\!\left[\psi'(f^{(i)})(X_i-Y_i)\partial_i p/\sqrt v\right]\right|
\le C\|\psi'\|_\infty I_\mu^c,$$

with $C,c$ independent of $n$. This remains open. Even if proved, the smooth $C^3$ error $\varepsilon^{-3}I^{1/2}$ is only polynomial in $t^{-1}$ and does not beat the exponential DFKO tail for large $t$. A separate non-smooth/exponential tail comparison is required.

Upper moment bounds yield only **upper** tails, never a lower large-$t$ bound $\Pr[|f|>t]\ge ct^{-B}$.

## 1H. Q4 / fourth-moment route: status and warning

A proposed minimal lemma Q4($d$) asks whether, for degree-$\le d$ $p$ under Dobrushin,

$$\|p-\mathbb E_\mu p\|_{L^4(\mu)}
\le C_d\|p-\mathbb E_\mu p\|_{L^2(\mu)},$$
with $C_d$ independent of $n$ and $p$.

**It is unproved, as are the derivative/ANOVA variants and the general induction.** The proposed Riesz estimate $\|p-P_{t_*}p\|_4\le\frac12\|p\|_4$ was only a sketch and is not supplied. Conditional expectations can increase degree, so an induction cannot freely assume preservation.

If Q4 held at all degrees and with all derivative variants, then OZ’s algebraic sup-norm bound plus Dobrushin Poincaré and reverse Hölder would give the displayed AA bound. But this does not constitute a simplification: Q4 encapsulates a very strong hypercontractive/DFKO-type statement and may be as difficult as the main target. Bonami and nonhomogeneous OZ constants carry exponential $d$ factors, so calling the $v^2$ result “sharper” without tracking them would be misleading.

## 1I. Principal open lemmas due to current gaps

- Full Dobrushin AA, especially $d\ge2$ beyond established small-$\kappa$ regions. In particular, general degrees in the 2D Ising window $(\beta_D\approx0.25,\beta_c\approx0.4407)$ and the Dobrushin interval after the animal threshold remain open.
- The polynomial-threshold weak DFKO tail described above.
- The simultaneous low-degree bounded junta $q$ under both $\mu$ and $\widetilde\mu^R$ (“C1”).
- The intermediate path-TV comparison and subsequent influence domination (“C2”).
- HC+CU of §1F, including the Dirichlet-form control.
- The first-order hybrid covariance estimate of §1G.
- Correct block/ANOVA degree control, and the variance and argmax expressions:
  $$v=\mathbb E_\tau v_\tau+\operatorname{Var}_\tau m_\tau,\qquad
  \max_i\mathbb E_\tau\phi_i\le\mathbb E_\tau\max_i\phi_i,$$
  with no assertion of equality in the latter.
- Any smaller-scale replacement with a genuinely independent mechanism.

---

# 2. Task 2 — summed-$(b')$ LP and determinant removal

## 2A. Exact open statement

For $A\subseteq\{0,1\}^n$, a monochromatic face family $T(x)$ satisfying $x^S\in A$ for **every** $S\subseteq T(x)$, and any $w>0$, the goal is a doubly stochastic matrix $M$ on $A\times A$ with

$$M_{xy}=0\text{ unless }y\in F(x):=\{z\in A:z_i\ne x_i\ \forall i\in T(x)\},$$

and

$$\sum_{x,y}M_{xy}\sum_iw_i\mathbf1[y_i=x_i]
\le\sum_iw_i\#\{x\in A:x^i\notin A\}.$$

If this is proved, then Birkhoff–von Neumann gives a decomposition into face-allowed permutations. At least one component satisfies both face condition (a) and the same **summed** condition $(b')$. This would remove the determinant step in BDST §5–6.

The faceless case is elementary and does not require determinant machinery. Boolean-valued functions also permit uniform certificates because $d^2\ge n$; symmetric functions admit a uniform-certificate route with cost controlled by Markov symmetrisation.

## 2B. Reimer/Hall: true statement versus false induction

Reimer’s butterfly property is a genuine background theorem in the BDST account, and the face condition is exactly Hall’s hypothesis. The flawed proof attempt used

$$|N_{0\downarrow}|\ge|S_{0,\mathrm{free}}|+|S_{1,\mathrm{forced}}|,\qquad
|N_{1\downarrow}|\ge|S_{1,\mathrm{free}}|+|S_{0,\mathrm{forced}}|.$$

**Counterexample:** $n=1$, $A=\{0,1\}$, $T(0)=\varnothing$, $T(1)=\{1\}$. Hall holds: $F(0)=\{0,1\}$, $F(1)=\{0\}$ and $N(A)=\{0,1\}$. But the proposed inequality requires $|N_{0\downarrow}|\ge2$ whereas the actual set has size 1.

The two-layer overlap is essential. Distinct-projection lower bounds plus a minimal-violating-set/private-neighbour argument were proposed, but the private-neighbour step remained an assertion. **Do not quote the wings induction as a valid Reimer proof.** Random finite-instance checks cannot replace the missing proof.

## 2C. Exact remaining LP gaps

- **Fiberwise Hall:** the body–fiber partition and the required Hall property are asserted, not proved. The cube/LYM explanation “fibers partition A up to cube structure” is undefined.
- **Dual construction:** strong duality only restates the problem. No explicit dual-feasible $(\alpha,\beta)$ was constructed with cost at most the boundary mass $B^w$.
- **Cross matching:** the current layer method needs a single matching that **saturates the smaller layer**, while preserving the weighted cost bound. Full Hall does not automatically give this.
- **Gale–Shapley projection:** a $b$-matching lift still needs the required projection property.

Useful identified structure:
$$B_i(U\cup V)+B_i(U\cap V)\le B_i(U)+B_i(V),
\qquad B_i(S)=|\{x\in S:x^i\notin S\}|,$$
which follows by checking all 16 pointwise membership cases. This submodularity has not closed the saturation/cross-matching step.

**Numerical only:** hundreds/thousands of small examples, including 720 random LP tests and 2683 monochromatic-face cases, had no failures. Those experiments are not proof of general $M$.

## 2D. Weighted routing: failed constructive permutation, bounded optimum numerics

Face-free biased-product antipodal routing is highly instructive:

- At $p=1/2$, the explicit swap/greedy permutation gives ratio 1 and calibrates well.
- For $p<1/2$, that same construction blows up:
  $2^{2n-2}$ at $p=0.2$ and $3^{2n-2}$ at $p=0.1$.
- In contrast, ILP-optimal permutations looked bounded in $n$ for small $n$, especially Hamming balls, with constants increasing as $p\to0$ but not $n$.

Interpretation: the obstruction is a failed **construction**, not evidence that no good permutation exists. A proof likely needs an existence/transportation argument rather than the explicit swap walk. The anomalous infeasibility at $n=4$, $p=0.1$, Hamming ball $k=2$ has not been explained. Small-$n$ ILP data never proved uniform boundedness.

A claimed fibre SDR/lifting proof was invalid: fibre-wise doubly stochastic couplings do not automatically produce a single permutation of $A$. Hence former “product-measure determinant-free AA” claims combining different permutations for (a) and (b) were withdrawn.

## 2E. What is established versus what is open

- **Open:** a proof or explicit counterexample to the summed-$(b')$ LP exactly as formulated above, including face-support constraints and arbitrary $w>0$. Generic non-symmetric low-degree examples with $d^2\ll n$ remain the key unresolved class, where earlier LP-minimal certificate families failed $(L')$ and no cheap interpolation repair was found.
- **Face evidence to treat cautiously:** structured examples can have small measured face sizes, but this does not prove $(L')$ in general, and the older face-size experiment needs rechecking before reuse.
- **Numerical only:** truth on small random examples.
- **Conditional:** if such an $M$ or a Birkhoff-decomposable transportation solution is found, a permutation satisfying both (a) and summed $(b')$ follows.
- **Not a proof:** combining two different constructions for conditions (a) and (b'), or assuming face-free routing transfers to nonuniform $\mu$ by crude set-mass comparisons.

---

# 3. Task 3 — Escudero’s fcb conjecture

## 3A. Exact target

For $p:\{-1,1\}^n\to\mathbb R$ with

- multilinear degree $\le d$, and
- Fourier completely bounded norm $\|p\|_{\rm fcb}\le1$,

prove that some coordinate satisfies

$$\operatorname{Inf}_i(p)\ge\operatorname{poly}(\operatorname{Var}(p)/d),$$

with the polynomial independent of $n$.

## 3B. What is established

- **Homogeneous case:** if $p$ is homogeneous degree $d$ and $\|p\|_{\rm fcb}\le1$, an influential variable exists with $\operatorname{Inf}_i\ge\operatorname{Var}(p)^2$ and no $d$-degree loss. This is Escudero’s result.
- **Bansal–Sinha–de Wolf:** completely bounded block-multilinear forms have the influential-variable result; Escudero provides a randomness-free presentation with better constants.
- Their relevance is fcb’s same downstream implications as AA: classical simulation of suitable quantum query algorithms and related random-oracle consequences, using weaker hypothesis than ordinary $\|p\|_\infty$ boundedness.
- **O’Donnell–Zhao decoupling:** one-block decoupled comparisons give $C_k=O(k^2)$ and $D_k=k^{O(k)}$ for Rademacher inputs, and $C_k=D_k=O(k)$ for Gaussians. These are decoupling/tail tools, not MLSI junta theorems.

## 3C. Nonhomogeneous case: exact obstruction and routes

The open case remains open. Decompose $p=\sum_kp_k$ into homogeneous parts. Pigeonhole gives one level with variance at least $\operatorname{Var}(p)/(2d+1)$ and Escudero applies to each level, but **influence of the sum need not be the sum of influences across levels**. A viable proof needs level-uniform decoupling/Khintchine or a polarization preserving fcb norm and degree. Candidate directions, not results:

1. Level decomposition with stronger norm-preserving decoupling.
2. Polarization from a nonhomogeneous fcb polynomial into a homogeneous one with controlled degree and fcb norm.
3. Direct operator-space/free-probability methods avoiding levelwise reductions.

There is currently no fcb fractional-certificate bound established by this project.

## 3D. Explicitly withdrawn fcb-error

A previous citation “Escudero Lemma 5.2: $FC_{\rm fcb}=O(d)$” was fabricated and withdrawn. The word “certificate” occurs only incidentally in Escudero’s paper and does not supply that result. Do not resurrect it or derived degree-exponent comparisons based on it.

## 3E. Related generalization observations [PROJECT/context]

- **Unique versus multi-witness search:** a single-witness search makes $s_Q$ one bounded polynomial, so AA applies in a decision-like way; multi-witness breaks this. This explains why Yamakawa–Zhandry is not an AA counterexample.
- **HeurP vs AvgP:** uniform AA gives the HeurP setting. AvgP for arbitrary samplable distributions cannot follow without substantially different hypotheses: independent adversarial supported laws already refute a universal “every distribution” formulation. This is not a route to stronger arbitrary-measure AA.
- **Approximate degree is not enough:** $\widetilde\deg(\mathrm{AND}_n)=\Theta(\sqrt n)$ but $FC(\mathrm{AND}_n)=n$, refuting an approximate-degree shortcut to small fractional certificates or AA. If approximation must preserve variance and function behaviour essentially exactly, it collapses back to the original AA requirement.
- **Massively parallel quantum query:** existing results have depth-dependent terms like $t^{O(d^2)}$ for $d$ rounds, polynomial for constant depth and quasi-polynomial for polylog depth, rather than a general polynomial simulation of QNC.
- **Keller–Klein (arXiv:1911.03748):** later version carries a withdrawal notice because Lemma 5.3 does not support the proof. It was an elegant failed attempt, not a source of valid theorems. No result from it is used here.

---

# 4. Cross-task failed approaches — do not repeat

| Approach | Exact failure |
|---|---|
| “OZ Thm 3.5 with $\rho$” | No such theorem. OZ Cor 3.5/3.6 are uniform-product statements using independence, Fourier structure, commuting noise, and invariance. |
| MLSI $\Rightarrow$ junta by replacing a parameter | Glauber semigroup hypercontractivity is not monomial/ANOVA hypercontractivity, orthogonality, commuting noise, independent Gaussian decoupling, or invariance. |
| Degree preserved under Glauber/conditional/ANOVA | False in general; $K_{1,3}$ raises degree 1 to 3. The 3-path is affine-preserving and not a counterexample. |
| Gradients are $R$-local by correlation decay | False for $p=x_ix_j$ with $\operatorname{dist}(i,j)>R$: optimal local error $1/4$, while even the GMNR gradient budget is only 2. |
| Uniform $L^2$ sparse truncation transfers by TV on retained support | The retained set can be controlled, but the discarded residual can be globally supported and must be handled under both measures. |
| Block-ANOVA degree $\le$ original degree | Conditional mappings may generate higher-degree interactions; see the star witness. |
| Moment upper bounds give lower large-$t$ tails | Markov supplies upper tails only. A lower moderate-deviation estimate needs cumulant/tilt or independent DFKO machinery. |
| $I\lesssim t^{-2}$ implies invariance error $e^{-\Theta(t^2)}$ | Error is only polynomial in $t$. For polynomial AA at cutoff, one needs $\eta_0(t)\ge ct^{-A}$, not exponential decay. |
| $\Pr_\mu$ replaced by $\Pr_\nu$ from event inclusion | Inclusion controls only the same measure. Cross-measure tail comparison remains unsolved. |
| Copy-law unweighted flip form supplies heat-bath MLSI | Exact copy has zero single-site heat-bath gap. Use block-resampling dynamics instead. |
| Far-monomial implies failure of all support-TV transfer | It refutes localization around $i$, not direct expectation comparison on its actual small support $\{j\}$. |
| Different permutations for (a) and $(b)$ suffice | BDST needs one object satisfying constraints simultaneously; no such combination was established. |
| Birkhoff alone closes $(b')$ | It only transports a face-supported doubly stochastic solution. Feasibility of that solution is the actual open problem. |
| Wings induction for Reimer | The n=1 counterexample violates the displayed wings inequality. The overlaps require another argument. |
| Clipping a junta preserves product AA | It can make multilinear degree unbounded. Product AA needs both bounded range and degree control of the approximant. |
| Unbounded counterexample refutes bounded Lemma J | Range $\Theta(\sqrt m)$ is not $[0,1]$-bounded; clipping destroys multilinear degree. |

Other corrections to retain:

- Confusing $\max_i\mathbb E_\tau[\phi_i]$ with $\mathbb E_\tau[\max_i\phi_i]$ fails. Only $\max_i\mathbb E_\tau\phi_i\le\mathbb E_\tau\max_i\phi_i$ follows in general.
- Global variance splits as $\operatorname{Var}_\mu(p)=\mathbb E_\tau v_\tau+\operatorname{Var}_\tau m_\tau$; buffer separation does not automatically control the latter.
- A one-block expectation under product-of-marginals is identical to the original conditional marginal. It does not prove approximate independence between blocks.
- A divergent animal-count/row-sum series is a failure of that counting method, not by itself a proof that the desired theorem is false.
- Many initial AA “repairs” were invalid because full support/degree or boundedness was changed mid-proof.

---

# 5. Reference files for the next agent

Core project notes:

- `notes/proof-pipeline-log.md` — earlier round log, including corrections and withdrawn claims.
- `notes/round2-prompts.md` — formal three-task mandate and precise LP/fcb targets.
- `notes/overnight-findings.md` — earlier Gibbs/block results and generalization survey.
- `notes/dfko-repair-outcomes.md` — later junta/DFKO accepted partials, failures, and explicit assumption ledger.

Primary texts on disk:

- `papers/aa_main.txt` — BDST proof exposition (the established AA proof and routing/determinant treatment).
- `papers/aa_bhf.txt` — GMNR distributional variants, influence conventions, and bounded low-degree total-influence bounds.
- `.scratch/chk/oz.txt` — checked O’Donnell–Zhao text used to refute the claimed MLSI junta citation.

Reviewed partial proofs:

- `.ultramath/smwgqw949/m8/proof.md` — corrected influence/degree/junta ledger.
- `.ultramath/smwgqw949/m7/proof.md` — 3-path correction, star $K_{1,3}$, failed approximate filtration.
- `.ultramath/smwgqw949/m4/proof.md` — joint endpoint functional TV lemma and its remaining domination gap.
- `.ultramath/smwgqw949/m1/proof.md` — bounded/unbounded MLSI status audit.
- `.ultramath/smwgqw973/m2/proof.md` — conditional cumulant/MGF route.
- `.ultramath/smwgqw973/m1/proof.md` — exact hybrid/Taylor framework and the disjoint-pair example.

## One-sentence bottom line

For Task 1, AA remains open beyond established special regimes; the clean open ingredients are a genuine cumulant/moment comparison or a simultaneous bounded low-degree junta plus path-transfer. For Task 2, the exact face-supported summed-$(b')$ transportation LP remains unproved. For Task 3, nonhomogeneous fcb remains open, with no valid fractional-certificate shortcut.