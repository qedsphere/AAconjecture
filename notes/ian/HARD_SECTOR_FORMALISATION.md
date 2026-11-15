# Hard-sector formalisation: split, layout and plan

Written 2026-11-15 against `main` at `cc29b4b` (PR #2 merged). Nothing in this
note is formalised yet; it records who does what so we don't collide.

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
- Code: `formalisation/HardSector/`, namespace `HardSector`, as a **separate
  `lean_lib`**. It imports `UnifiedAA` and the vendored
  `QuantumQueryComplexity` read-only.
- I do not edit any existing module, `UnifiedAA.lean`, `checks/Axioms.lean`,
  `scripts/`, dependency pins or `lake-manifest.json`. My own axiom audit lives
  under `formalisation/HardSector/checks/`.
- **One request:** add this stanza to `lakefile.toml` (your file), so my
  modules build without touching the aggregate:

  ```toml
  [[lean_lib]]
  name = "HardSector"
  ```

Same rules as your plan: Lean 4.33.0, no `sorry` / `admit` / `axiom` /
`native_decide`, literature inputs stated as explicit hypotheses, one bounded
result per PR with the note's label, hypotheses and audit output.

## What I use from your code

Please keep these signatures stable, or tell me before changing them:

- `FiniteLaw` (`FiniteProbability.lean`) and `conditionOn` (`ParityUpdate.lean`).
- `DecisionTree`, `eval`, `depth`, `queries` (`DecisionTree.lean`).
- `walsh` (`WalshConvolution.lean`) for the character-based sectors.
- `QAlg` and its acceptance probability (vendored `Quantum/Algorithm.lean`) to
  realise the class $\mathcal Q_{n,T}$.
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

## Questions for you

1. OK with the 22–23 split above?
2. OK to add the `HardSector` lean_lib stanza?
3. `withMeans`: should I write my own μ-general version, or will you generalise yours?
