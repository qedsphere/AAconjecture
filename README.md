# Hamiltonian structure and distributional AA

This repository studies when quantum query acceptance probabilities on Gibbs-distributed inputs admit classical approximation with a number of queries polynomial in the quantum query count and inverse accuracy, independent of system size. We call this **full AA**. Computation time and the cost of generating a fresh thermal sample are separate resources.

Start with the [campaign synthesis](notes/distributions/threshold_theory/README.md), [complete PDF](notes/main.pdf), or [progress and review record](PROGRESS.md). The new full-AA results are in Sections 11–14 of the PDF. Positive results import the uniform-input AA theorem; the new deductions have analytical proofs, independent agent reviews, and finite checks, but are not claimed to be formally verified or novel in the research-priority sense.

| Hamiltonian or input structure | Full-AA conclusion |
|---|---|
| Independent bounded-size components | All temperatures, including hard-constraint limits |
| A fixed number of permutation-exchangeable species | All temperatures and temperature schedules; includes collective transverse-field Ising |
| Classical Ising forests with bounded edge strengths | Every fixed finite inverse temperature; arbitrary fields, degrees and pinnings |
| A bounded feedback vertex set | Reduces to the forest case after revealing that set |
| Global character-code penalty | Exact normalized threshold: holds for fixed β < 1, fails for β ≥ 1 |
| Fixed global noisy-code Hamiltonian | Fails for every fixed β > 0; holds at β = 0 |

The negative constructions have global interactions. No general negative threshold for bounded-degree finite-range Ising models is claimed. General local high-temperature full AA remains a stated conjecture.

The organizing idea is that energy–entropy competition determines which sectors become occupied, while their query-accessible information determines whether AA fails. Magnetic order alone is insufficient. Symmetry and local access to hidden randomness conditional on the observed input can preserve simulation even when physical flip-influence inequalities fail.

Generalized influence is still a useful research direction. Changing at most k physical spins changes normalized magnetization by at most 2k/n, so bounded-size perturbations cannot detect its ordered-phase variance. Revealing a spin can nevertheless reveal phase information. The [focused note](notes/distributions/threshold_theory/06_generalized_influence.tex) develops adaptive reveal gain and recoverable latent-source influences, including why singleton reveal gain and inaccessible latent variables are insufficient. Deriving these mechanisms from general high-temperature local Hamiltonians remains open.

## Proofs and reproducibility

- [Positive mechanisms](notes/distributions/threshold_positive/threshold_positive.tex): local posterior transfer, arbitrary block products, forests and feedback sets.
- [Actual query obstructions](notes/distributions/threshold_obstructions/threshold_obstructions.tex): noisy-code separation, the fixed Hamiltonian, and an exact criterion for arbitrary code-mixture weights.
- [Physical models and sources](notes/distributions/threshold_physics/threshold_physics.tex): species symmetry, quantum measurement conventions, and high-temperature conjectures.
- [General criteria](notes/distributions/threshold_theory/threshold_theory.tex): reveal progress, likelihood transfer, upstream audit and generalized influence.
- [Verification and build instructions](notes/distributions/threshold_theory/VERIFICATION.md), including reproducible finite checks and their limitations.

The upstream [Tasks 1–3 summary](tasks-1-2-3-summary.md) and [proof companion](tasks-1-2-3-proof-companion.md) are retained as received. Their claims have separate [audits](notes/distributions/threshold_theory/05_upstream_audit.tex); historical open-status labels and conditional results should be read with those qualifications.
