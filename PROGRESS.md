# Full-AA temperature structure

## 2026-11-14 — investigation started

The primary target is dimension-independent polynomial classical **query acceptance simulation** for quantum algorithms under Gibbs input laws. Flip-influence AA and transverse-field Ising models are supporting probes, not substitutes for this target. Computational running time and the cost of generating a fresh Gibbs sample are separate resources.

The existing `notes/distributions/` organization is retained: new results will be split into numbered LaTeX sections, with chapter wrappers included by the shared master. Existing results are used as inputs and not silently promoted beyond their stated scope.

| Work stream | Assigned scope | Working directory |
|---|---|---|
| Main synthesis | Full-AA criterion, closure results, structural threshold theory, integration and review | `notes/distributions/threshold_theory/` |
| Positive theory agent | Query simulation transfer, local encodings, product/block models, pinning obstacles | `notes/distributions/threshold_positive/` |
| Obstruction theory agent | Genuine query separations, energy–entropy thresholds, robustness and locality | `notes/distributions/threshold_obstructions/` |
| Physical theory agent | Quantum measurement basis, transverse-field Ising, primary-source research, physical conjectures | `notes/distributions/threshold_physics/` |

Initial constraint from the existing work: the Curie–Weiss influence transition is **not** a full-AA transition, because the exchangeable-input theorem supplies acceptance simulation at every temperature. The nonlocal character-code family supplies a genuine full-AA threshold. Any proposed structural theory must explain both.

## Completed theory and deductions

The synthesis is [here](notes/distributions/threshold_theory/README.md), with proofs integrated as Sections 11–14 of [the shared LaTeX master](notes/main.tex).

1. **Positive structure:** proved a forward-oracle plus conditional-source transfer criterion, uniform full AA for arbitrary bounded-block products (including hard constraints), and full AA for Ising forests at every fixed finite temperature with bounded edge strengths and arbitrary fields/degrees. The forest result is uniform under pinnings and extends to bounded feedback vertex sets.
2. **Symmetry:** proved one simulator simultaneously works on every product of a fixed number of Hamming slices. Thus fixed-species permutation-invariant Hamiltonians, including noncommuting collective transverse-field models, have full AA at all temperatures and temperature schedules.
3. **Genuine negative structure:** upgraded the noisy affine-character example to a one-query versus Ω(log n) classical separation. Proved that one fixed log-sum-exp Hamiltonian is exponentially close to such a noisy law at every fixed β > 0. It has bounded one-spin energy changes, extensive energy range, exact three-wise independence and high entropy, but unbounded interaction order. Its limiting pressure is analytic throughout β > 0.
4. **Threshold refinement:** proved an exact criterion for character-code mixtures: full AA holds iff log n is bounded by a fixed polynomial in the inverse hard-sector weight. This distinguishes a thermodynamic crossover window from the property quantified over approximation accuracy.
5. **General criteria:** proved a reveal-progress characterization on classes closed under pinning and a one-sided Lᵖ likelihood-transfer theorem, including a free-energy sufficient condition.
6. **Research program:** formulated explicit classical Dobrushin and quantum local high-temperature conjectures. General mixing, separability, forward sampling, or a physical transition is not promoted to a full-AA theorem. The source audit accounts for the 2025 quantum-CMI erratum.

## Independent review and verification

- Main agent reviewed all new proof streams.
- Positive agent independently reviewed the noisy-code fixed-H theorem and the species extension.
- Physics agent independently reviewed the forest, posterior-transfer and block-product arguments.
- Obstruction agent independently reviewed the reveal-progress and likelihood-transfer propositions.
- All 18 block-rounding cases and 12 exact finite-forest checks passed. Noisy-code identities and powered-Gibbs properties passed exhaustive enumeration for n = 4 and 16 at three inverse temperatures. Scripts and JSON results are kept with their chapters.
- Integrated LuaLaTeX compilation and page-layout inspection are recorded in [verification](notes/distributions/threshold_theory/VERIFICATION.md).

## Scope at completion

The requested structural theory, supporting deductions, counterexamples, and literature audit are complete and recorded. A necessary-and-sufficient classification of arbitrary Hamiltonians, a proof of general Dobrushin-to-full-AA transfer, and sharp thresholds for bounded-degree finite-range Ising models remain research questions. All positive results import uniform-input AA; none of the new arguments is claimed to be formally verified or novel in the priority sense. No general monotonicity of full AA in temperature is assumed.

## 2026-11-14 — latest GitHub results incorporated

At the user's request, fetched and fast-forwarded this checkout from `ff4afe4` to `d5e429763b9f0234f5dd02c3fe03925c78b4306c` on `qedsphere/AAconjecture/main`. The local `structured_inputs/` directory is not a Git checkout; `sharedwork/` is the connected repository. The pull added [tasks-1-2-3-summary.md](tasks-1-2-3-summary.md), preserving all local research changes.

The three theory agents reviewed the handoff against the full-AA target and primary or supplied sources. The resulting [integrated audit](notes/distributions/threshold_theory/05_upstream_audit.tex) adds:

- Explicit degree-uniform quantifier requirements, the high-temperature Ising-star degree-growth obstruction, and the distinction between geometric locality of input representations and arbitrary query observables.
- A correction to the transportation status: its exact LP is feasible using the BDST determinant theorem; finding a determinant-free proof remains the intended open task.
- A one-biased-bit obstruction to a literal Gibbs-preserving antipodal transport, even on an independent-field law that satisfies full AA.
- Corrections to uniform Fourier influence additivity and the fcb target's status relative to the already imported uniform-AA theorem.
- Repaired mean-square comparison evidence and cautions about the reported inverse-atom prefactor, Boolean degree shortcut, critical covariance row sums, and physical versus query thresholds.
- A direct example showing that quantum query realizability itself does not turn correlated flip-influence failure into a simulation obstruction.

The upstream handoff is unchanged. Its `[PROJECT]` and `[CONDITIONAL]` claims are not promoted to established full-AA results. Companion reviews are stored as `UPSTREAM_REVIEW.md` in each theory agent's chapter directory. The established forest, symmetry, code-mixture, and noisy-code temperature classifications remain unchanged.

## 2026-11-14 — publication and generalized influence

The user authorized publishing the critical campaign results. Before preparing the commit, this checkout was fast-forwarded to `9312412`, which adds the [proof companion](tasks-1-2-3-proof-companion.md). The publication acknowledges its repairs to Fourier influence additivity, the minimum-atom exponent, and covariance-norm conventions; the original source audit remains explicitly tied to `d5e4297`.

The repository landing page now links the main results, full PDF, proof chapters, and verification. A focused note on generalized influence distinguishes physical perturbations from information revealed by queries and from influences in recoverable latent coordinates. It identifies an obstruction to any influence based only on changing a bounded number of physical spins, and states the polynomial-reveal and source-transfer routes with their existing hypotheses.
