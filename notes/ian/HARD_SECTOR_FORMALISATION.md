# Hard-sector formalisation: split, layout and plan

Written 2026-11-15 against `main` at `cc29b4b` (PR #2 merged). It records who does
what so we don't collide; the Status table below tracks what is proved.

## Split

**Ian formalises the hard-sector material in `notes/ian/`. Everything else is
yours**, i.e. the unified-manuscript plan in `PARALLELISATION.md` and
`FORMALISATION_SEGMENTS.md` (segments 1–12) stays with you as written.

| Files in `notes/ian/` | Content | Owner |
|---|---|---|
| 13–18 | Hard-sector definitions, forward bound, calibrated-predictor extraction, full-AA characterization, rounding, transfer, instances, sampling | Ian |
| 24–34, 36–38 | Γ bridge, robust compilation, transcript hiding, Simon / period / HSP / Forrelation / Hadamard sectors, adversary certificates, thermal realization and robustness, inverse question | Ian |
| 19–21, 26–27 | Phase labels and hidden-label admissibility (built on sectors) | Ian |
| 22–23 | Product-alphabet degree, product OSSS, influence-form uniform AA | **To agree**: overlaps your segment 9 (manuscript Lemmas 3.5–3.8). Proposal: you own the product-alphabet definitions and certificate inequality; I import them for 22–23. |
| 03–10 | Generalized influence, spectral high temperature, Γ-sets | Not hard-sector; not claimed by either of us yet |

## Layout

- No branches: everything goes straight to `main`, in small commits that only
  add files under my folders.
- Code: new files only, in `formalisation/UnifiedAA/HardSector/`, modules
  `UnifiedAA.HardSector.*`, namespace `UnifiedAA.HardSector`. They sit inside
  your `UnifiedAA` lib, so `lake build UnifiedAA.HardSector.<Module>` works with
  **no lakefile change**. Nothing imports them from `UnifiedAA.lean`, so your
  default `lake build` is unaffected. Hook them into the aggregate whenever you like.
- I do not edit any existing module, `UnifiedAA.lean`, `checks/`, `scripts/`,
  `lakefile.toml`, dependency pins or `lake-manifest.json`.
- Every commit passes a gate first: module builds; no `sorry` / `admit` /
  `axiom` / `native_decide`; statements unchanged from the reviewed skeleton;
  `#print axioms` shows only `propext`, `Classical.choice`, `Quot.sound`;
  no file outside `HardSector/` and this note touched.

## What I use from your code

Please keep these signatures stable, or tell me before changing them:

- `FiniteLaw` (`FiniteProbability.lean`), `variance` (`ProbabilityBounds.lean`).
- `DecisionTree`, `eval`, `depth`, `queries` (`DecisionTree.lean`).
- `QAlg` and its acceptance probability (vendored `Quantum/Algorithm.lean`) to
  realise the class $\mathcal Q_{n,T}$.
- `walsh` (`WalshConvolution.lean`) and `conditionOn` (`ParityUpdate.lean`) once your current fixes land.
- Later, for files 36 and 38: your Gibbs law / pinning definitions (segments 8
  and 10). I wait for those rather than define competing ones.

`ConditionalMeans.withMeans` averages under the **uniform** law only. Hard
sectors need conditional means under an arbitrary law μ, so I will write a
μ-general version inside `HardSector/`. If you'd rather generalise yours and
have me use it, say so.

## Conventions

- The notes use $\Omega_n=\{-1,1\}^n$; the Lean code uses `I → Bool`. For files
  13–16 this is pure relabelling (no influence appears).
- Influence: the notes use $\tfrac14\mathbb E(f(X)-f(X^i))^2$, your code uses
  $\mathbb E[(f(x)-f(\mathrm{flip}_i x))^2]$ with no factor $1/4$. This only
  matters for 22–23; I convert with an explicit lemma, I don't change yours.
- $\mathcal D_t$ / $\mathcal F_t$ become predicates on `DecisionTree`
  (depth ≤ t, leaves in $[0,1]$ resp. $[-1,1]$).
- In the full-AA characterization (file 13), the quantum class enters only as
  a parameter. I state the theorem for an arbitrary class family
  $\mathcal Q : \mathbb N\to\mathbb N\to$ `Set ((I → Bool) → ℝ)` and instantiate
  with `QAlg` acceptance functions as a corollary.

## Milestones

1. **HS1 (file 13).** `Hard`, smooth and set sectors, tree aggregation, the
   forward bound, attainment of $\ell_\mu$ via conditional-mean leaves, the
   one-calibrated-predictor theorem, explicit extraction at depth
   $\lceil 32\varepsilon^{-5}\eta^{-2}\rceil t$, and the full-AA ⇔ polynomially
   weighted hard sectors equivalence. Self-contained.
2. **HS2 (15–16).** Smooth-to-set rounding, bounded-density transfer.
3. **HS3.** One concrete instance end to end: Forrelation (33) or Hadamard rows
   (34) first, since their $Q$ needs a single quantum query; Simon (30) after.
4. **HS4.** Robust compilation and transcript hiding (28–29), adversary
   certificates (32, literature theorems as hypotheses), then the thermal files
   (36, 38) once your Gibbs modules land.

## Status (updated by each commit)

| TeX label (`notes/ian/`) | Lean declaration | Module |
|---|---|---|
| 13, `ian:hard-sector-definition` (Hard, smooth/set sectors, $\mathcal D_t$, $\mathcal F_t$, $\mu(\cdot\mid H)$) | `Hard`, `CovCondition`, `IsSmoothSector`, `IsSetSector`, `DepthTrees`, `SignTrees`, `condLaw`, `cov` | `UnifiedAA.HardSector.Basic` |
| 13, opening paragraph ($\mathcal D_t$, $\mathcal F_t$ monotone in $t$) | `depthTrees_mono`, `signTrees_mono` | `UnifiedAA.HardSector.Basic` |
| 13, after `ian:hard-sector-definition` ($\mathcal F_t=2\mathcal D_t-1$, covariance form, Hard antitone in $t$) | `exists_depthTree_of_signTree`, `exists_signTree_of_depthTree`, `expect_centered_mul_eq_cov`, `covCondition_iff`, `hard_of_le` | `UnifiedAA.HardSector.Basic` |
| 13, `ian:hard-sector-definition` (set sector ⇒ smooth sector, $\mu(\cdot\mid H)\le\mu/\mu(H)$) | `isSmoothSector_of_isSetSector`, `condLaw_weight_le` | `UnifiedAA.HardSector.Basic` |
| 13, `ian:hard-sector-tree-closure` (sequential composition ≤ s+t, function of k trees ≤ kt, extremal ±1 tests; count $N(n,t)$ not formalised) | `graft`, `leafPath`, `ExtremalTrees`, `eval_graft`, `leafPath_graft`, `graft_depth_le_and_leavesIn`, `exists_tree_of_function`, `extremalTrees_subset_signTrees`, `covCondition_iff_extremal` | `UnifiedAA.HardSector.TreeOps` |
| 13, `ian:hard-sector-forward` (H1-forward, per tree $D\in\mathcal D_t$: $\E_\mu\lvert Q-D\rvert\ge w(a-\gamma)$; first step $\E_\nu(Q-D)^2\ge a-\gamma$) | `forward_bound`, `sq_loss_ge_of_hard` | `UnifiedAA.HardSector.Forward` |
| 13, `ian:hard-sector-aa-definition` ((AA) for a law family and an abstract class family $\mathcal Q_{n,T}$; condition (3)) | `AAWith`, `FullAA`, `SmoothSectorWitnesses` | `UnifiedAA.HardSector.Exclusion` |
| 13, `ian:hard-sector-aa-exclusion` (sector exclusion under full AA) | `depth_lt_of_aa` | `UnifiedAA.HardSector.Exclusion` |
| 13, `ian:hard-sector-aa-equivalence` ((3) ⇒ (1)) | `not_fullAA_of_smoothSectorWitnesses` | `UnifiedAA.HardSector.Exclusion` |
| 13, lines 8–11 ($\ell_\mu(t,Q)$ and the squared-loss minimum exist; $\ell_\mu(\cdot,Q)$ nonincreasing) | `ell`, `l1Loss`, `sqLoss`, `ell_attained`, `ell_antitone`, `ell_le_iff`, `exists_sqLoss_min` | `UnifiedAA.HardSector.Optimal` |
| 13, proof of `ian:hard-sector-regularity` (conditional-mean leaves, calibration, Pythagoras, nested leaf partitions) | `cellMean`, `condMeanTree`, `eval_condMeanTree`, `condMeanTree_mem_depthTrees`, `expect_resid_mul_eq_zero`, `sq_pythagoras`, `exists_factor_leafPath_graft`, `exists_eval_eq_comp_leafPath`, `leafPath_condMeanTree`, `expect_condLaw` | `UnifiedAA.HardSector.Optimal` |
| 13, `ian:hard-sector-regularity` (one calibrated predictor; $K=\lceil1/(w\gamma^2)\rceil$ form; Cauchy–Schwarz and $\E\lvert Y-m\rvert$ bounds from the proof) | `regularity`, `regularity_of_K_eq`, `expect_mul_sq_le`, `expect_abs_sub_mean_le_half`, `expect_abs_sub_mean_le_sqrt_variance` | `UnifiedAA.HardSector.Regularity` |
| 13, `ian:hard-sector-explicit` (set extraction at depth $L_\dagger$, the $L_*$ form, smooth sector $\nu\le16\mu/(\eta\varepsilon^3)$; constants as in the note) | `extraction`, `extraction_of_Lstar`, `extraction_smooth` | `UnifiedAA.HardSector.Extraction` |
| 13, `ian:hard-sector-aa-equivalence` (condition (2); reduction to $r>8$; (1) ⇒ (2) ⇒ (3); (1) ⇔ (2) ⇔ (3), for an abstract $[0,1]$-valued class family) | `SetSectorWitnesses`, `exists_large_r_of_not_fullAA`, `setSectorWitnesses_of_not_fullAA`, `smoothSectorWitnesses_of_setSectorWitnesses`, `not_fullAA_iff_setSectorWitnesses`, `not_fullAA_iff_smoothSectorWitnesses` | `UnifiedAA.HardSector.Equivalence` |
| 13, $\mathcal Q_{n,T}$ (acceptance functions of `QAlg (Fin n) Bool Bool W` with ≤ T value-oracle queries) and `ian:hard-sector-aa-equivalence` for it | `QuantumClass`, `quantumClass_mem_unit`, `quantum_not_fullAA_iff_setSectorWitnesses`, `quantum_not_fullAA_iff_smoothSectorWitnesses` | `UnifiedAA.HardSector.Quantum` |
| 15, `ian:hard-sector-polynomial-quantifiers` (property (P); ¬FullAA ⇔ (P), smooth and set) | `SectorKind`, `HasHardSector`, `PolynomialSectorProperty`, `not_fullAA_iff_polynomialSectorProperty`, `quantum_not_fullAA_iff_polynomialSectorProperty` | `UnifiedAA.HardSector.Quantifiers` |
| 15, `ian:hard-sector-resource-equivalence` (FullAA ⇔ 𝖱(μ), smooth and set) | `ResourceProperty`, `fullAA_iff_resourceProperty`, `quantum_fullAA_iff_resourceProperty` | `UnifiedAA.HardSector.Quantifiers` |

## Questions for you

1. OK with the 22–23 split above?
2. `withMeans`: should I write my own μ-general version, or will you generalise yours?
