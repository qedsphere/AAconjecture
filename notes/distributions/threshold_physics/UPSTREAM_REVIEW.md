# Audit of the new Tasks 1–3 handoff

Reviewed on 2026-11-14 against `sharedwork/tasks-1-2-3-summary.md`, received at upstream commit `d5e4297`. Scope: Task 3's Fourier-completely-bounded (fcb) claims and Task 1's physical-temperature assertions. This review does not edit the upstream handoff or upgrade its `[PROJECT]` statements into independently proved results.

## Corrections needed before synthesis

1. **The nonhomogeneous fcb polynomial-influence target is a corollary of the uniform AA theorem already imported by this project.** The historical 2023 conjecture should not be called an additional unresolved prerequisite here. A stronger bound, sharper degree dependence, a direct operator-space proof, or a Gibbs analogue can remain separate research questions; none is the same statement as Task 3A.
2. **Uniform-cube influences are additive across homogeneous Fourier levels.** Task 3C's explanation to the contrary is false. The genuine missing justification in a levelwise proof is a bound on the projected polynomial's fcb norm with the correct ambient norm index.
3. **The fcb hypothesis is stronger than supremum boundedness, so the fcb conjecture is weaker than ordinary AA.** Task 3B reverses the strength of the hypothesis.
4. **The covariance-row-sum argument does not include critical 2D Ising or the tree uniqueness point.** At those points the relevant row sums diverge. This invalidates that stated route; it does not prove failure of affine influence AA or of full acceptance simulation.
5. **Task 1A permits constants and exponents depending on degree.** Such a statement, without quantitative degree control, does not imply the polynomial-in-query-count overhead required by the present full-AA task.
6. **Neither a physical uniqueness threshold nor the Kesten–Stigum reconstruction threshold is a full-AA threshold for the finite Ising forests covered here.** Our posterior-source theorem proves full AA for every fixed finite maximum edge strength times inverse temperature, with all spins exposed as query coordinates.

## Task 3: primary-source check

Checked [Escudero Gutiérrez, arXiv:2304.06713v2](https://arxiv.org/abs/2304.06713v2), specifically Definition 2.2, Propositions 2.3, 2.5, 2.7, Theorems 1.4 and 1.6, and Remark 4.3. Its norm is indexed: `||p||_{fcb,d}`. It dominates `||p||_infinity`, decreases when its ambient degree index increases, and contracts under coordinate restrictions. Theorem 1.4 characterizes signed outputs of `T`-query quantum algorithms by degree at most `2T` and `||p||_{fcb,2T} <= 1`. The homogeneous theorem uses the matching norm index and gives maximum influence at least variance squared. Remark 4.3 describes a failed matrix-witness construction, not cancellation of uniform Fourier influences.

These facts imply the following **deductions**, independently of whether one uses an fcb-specific proof technique. For a polynomial with `||p||_{fcb,d} <= 1`, the project’s imported uniform-AA theorem applies because `||p||_infinity <= 1`. In the normalization of the existing notes, it yields

$$
 \max_i I_i^U(p)\ge c\,\operatorname{Var}_U(p)^{5/2}/d^6.
$$

Thus the literal Task 3A target is already covered **conditional on the same imported uniform-AA theorem used everywhere in this investigation**. This audit does not independently certify that theorem's provenance. It points out an inconsistency between the handoff's blanket open-status label and the project’s stated baseline assumption.

For the levelwise issue, write `p = sum_{k=0}^d p_k`, where `p_k` contains the Fourier characters of size `k`. Orthogonality gives exactly

$$
 I_i^U(p)=\sum_{S\ni i}\widehat p(S)^2
          =\sum_{k=1}^d I_i^U(p_k),
 \qquad
 \operatorname{Var}_U(p)=\sum_{k=1}^d\|p_k\|_2^2.
$$

These are elementary identities, not conjectures. A level has variance at least `Var(p)/d`. To invoke the sharp homogeneous theorem on that level, one needs control of `||p_k||_{fcb,k}`. The original assumption only controls `||p||_{fcb,d}`. Neither projection to level `k` nor changing the ambient norm index is justified by orthogonality. In particular the established monotonicity goes in the unhelpful direction `||p_k||_{fcb,d} <= ||p_k||_{fcb,k}`. No norm-preserving level projection or fcb fractional-certificate bound is supplied here.

Under a correlated Gibbs law the characters need not be orthogonal, so cross-level terms can occur in `I_i^mu`. That is a separate statement about a different measure; it does not repair Task 3C as written.

For current context, [Escudero Gutiérrez–Saucedo–Palazuelos, arXiv:2609.05201](https://arxiv.org/abs/2609.05201) improves the block-multilinear completely bounded root-influence bound to `sum_i sqrt(Inf_i) <= d ||p||_cb` and obtains nonadaptive simulation consequences for the corresponding query models. Its results are useful algorithm-sensitive structure. They are not a Gibbs-measure comparison theorem, and `cb` and degree-indexed `fcb` should not be silently identified. Its September 2026 discussion predates the uniform-AA result imported by this November project.

## What fcb contributes to the temperature theory

The useful insight is to work with **genuine quantum query outputs**, a smaller class than all bounded low-degree polynomials. For an acceptance probability `Q`, the signed output `p=2Q-1` has the appropriate degree-indexed fcb bound. Fixing queried coordinates preserves its quantum realization and the same ambient norm bound. A coherent source encoding with `a` source queries per physical query transforms a `T`-query algorithm into an `aT`-query algorithm. The local-posterior transfer theorem already uses this stronger fact directly; no arbitrary low-degree pullback is assumed to remain quantum realizable.

However, fcb does **not** turn a distributional flip-influence inequality into full acceptance simulation. There are two concrete reasons.

- The Curie–Weiss magnetization `M=n^{-1} sum_i x_i` is itself the signed output of a one-query quantum algorithm: choose a uniformly random coordinate, query it, and output its sign. Hence `||M||_{fcb,2} <= 1`. At fixed `beta>1` it has variance bounded below and flip influences `n^{-2}`, while the input laws satisfy full AA by exchangeability. Even an influence conjecture restricted to fcb/quantum outputs has this false negative.
- Replacing flip influence by singleton reveal variance is not a general cure. Under uniform input, `p=x_1 x_2` has positive variance but `Var(E[p|x_i])=0` for every single coordinate. It is nevertheless computable with two classical queries (and one quantum query for the two-bit parity decision). A useful simulation proof needs a suitable restriction potential or query procedure; immediate one-coordinate explained variance is not available for every output.

Likewise, the character-code obstruction already supplies a genuine one-query acceptance algorithm. Its lower bound survives the fcb restriction. Therefore fcb structure refines which observables deserve attention, but it does not erase the main distinction between physical correlations, flip influences, and unknown-input classical simulation.

The actual open bridge is still **Hamiltonian structure to a restriction-compatible simulation mechanism**, such as the posterior access criterion. A Gibbs-adapted fcb inequality could be useful if paired with a complete potential-decrease argument under the conditional laws. Merely proving its uniform analogue, or importing a Gibbs sampler, leaves that bridge missing.

## Task 1: critical temperatures and conventions

### Square-lattice Ising

For nearest-neighbor coupling one, the handoff's `beta_D=0.25` is the crude row-norm cutoff `4 beta<1`. The usual field-uniform coefficient bound gives the larger sufficient interval

$$
 4\tanh\beta<1,
 \qquad \beta<\operatorname{artanh}(1/4)\approx0.255413.
$$

An exact Dobrushin coefficient for a more specialized field/boundary convention can improve again. Consequently `0.25` should be described as a sufficient row-sum cutoff, not a convention-free exact Dobrushin threshold.

Below criticality, exponential correlation decay supports a finite covariance row sum in the usual zero-field ferromagnetic setting. **At** criticality this row sum is not uniformly finite. A primary reference is [Chelkak–Hongler–Izyurov, arXiv:1202.2838v3](https://arxiv.org/abs/1202.2838v3): Theorem 1.1 gives the critical two-point scaling limit, and equation (1.7) records the diagonal correlation asymptotic with exponent `1/4`. Even summing only correlations along one lattice diagonal gives a divergent series. Uniformly bounded finite-volume row sums would contradict this infinite-volume limit.

Therefore the handoff's degree-one claim “up to beta_c using standard correlation-decay results” needs its endpoint separated: the stated bounded-row-sum lemma proves the subcritical case, while the critical endpoint needs another argument. Polynomial critical decay can potentially yield a weaker polynomial variance-to-influence relation using boundedness of affine coefficients; failure of the row-sum proof is not evidence against the conclusion. No general critical-degree theorem is imported by this review.

The claimed degree-two result at `beta=0.35`, its tiny constant, and higher-temperature animal-counting constants remain handoff `[PROJECT]` claims. The detailed proof files cited by the handoff are not present in this checkout, so they have not been independently validated here and should not be promoted into full-AA threshold theorems.

### Regular rooted trees

Consider the zero-field free-boundary Ising law on the depth-`h` rooted `b`-ary tree. Its elementary independent-edge representation gives

$$
 \mathbb E[X_uX_v]=\theta^{\operatorname{dist}(u,v)},
 \qquad \theta=\tanh\beta.
$$

For the root `o`, the covariance row sum is exactly

$$
 \sum_v\operatorname{Cov}(X_o,X_v)
   =\sum_{\ell=0}^h(b\theta)^\ell.
$$

At the physical uniqueness value `theta=1/b`, it equals `h+1`; hence the finite-row-sum route again cannot justify its endpoint. This is a direct calculation and does not require an external theorem.

The reconstruction scale is a different question: for regular trees it is governed by `b theta^2=1`, as established in [Evans–Kenyon–Peres–Schulman, *Broadcasting on Trees and the Ising Model*](https://users.cms.caltech.edu/~schulman/Papers/evansKPS00Ising.pdf). That problem reveals distant boundary spins and asks about a hidden root. Our full-AA model exposes **all** coordinates and simulates an arbitrary prescribed quantum algorithm. Conflating the oracle models would change the problem.

The finite-forest theorem proved in this investigation applies on both sides of uniqueness and reconstruction at every fixed finite `beta J_max`. It uses a local posterior representation, independent of covariance-row summability. Thus the handoff cannot be read as locating a full-AA boundary between Dobrushin and Kesten–Stigum. Nor does a positive result at one temperature identify a sharp influence threshold without a matching negative result.

## Consequences for the integrated report

Retain the new handoff's warnings about nonexistent MLSI junta citations, degree growth under conditional expectation/Glauber dynamics, globally supported derivatives, and unresolved conditional-transfer steps. They strengthen the existing decision to pursue a direct query-compatible representation.

Do not add a new unresolved uniform fcb prerequisite, an exact Dobrushin value of `0.25`, or an AA boundary at tree uniqueness/reconstruction. If the handoff’s physical results are mentioned, preserve their influence-only, degree-specific, and `[PROJECT]` status. The forest, species-symmetry, and character-code results remain the decisive full-AA comparisons in the present theory.
