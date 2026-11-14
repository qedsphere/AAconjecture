# Hamiltonian structure and full-AA temperature thresholds

Research record, 14 November 2026. The primary target is polynomial classical **query acceptance simulation**, with a bound independent of the number of spins. The influence formulation is a proxy. All positive results import uniform-input AA; new deductions are proved in the numbered LaTeX sections and the three companion chapters.

**Main theory:** a full-AA transition requires thermal weight on information that coherent queries can extract but classical coordinate queries cannot efficiently infer. Thermodynamic ordering alone does not supply that information gap. The positive mechanisms established here are symmetry, independent bounded blocks, and local access to the latent randomness **conditional on the actual observed input**.

For a two-level Hamiltonian with a preferred sector Cₙ and energy gap Δₙ, the exact sector mass is

$$
p_{\beta,n}=\frac{1}{1+\exp(S_n-\beta\Delta_n)},\qquad
S_n=\log\frac{2^n-|C_n|}{|C_n|}.
$$

This identifies the energy–entropy crossover at βΔₙ ≈ Sₙ. It becomes a full-AA obstruction only when the conditional sector law has a quantum/classical query separation at the relevant accuracy. A ferromagnetic phase label can be learned by sampling spins; a hidden-character bent label cannot. For general Hamiltonians, restricted partition functions replace this two-level formula. This is a structural research framework supported by the examples below, rather than a classification theorem for all interactions.

| Hamiltonian structure | Full-AA result | What controls the result |
|---|---|---|
| Fixed number of exchangeable species, including noncommuting collective transverse-field models | Holds at every temperature, uniformly even for temperature schedules and canonical zero temperature | One tree simultaneously simulates all products of Hamming slices |
| Independent bounded-size components | Holds uniformly at every temperature, including hard constraints | Blockwise conditional source sampling; no lower atom-probability bound |
| Classical Ising forest, arbitrary fields/degrees, bounded edge strengths | Holds at every fixed finite inverse temperature, uniformly over pinnings | Independent latent edge variables have an edge-local posterior and exponentially decaying conditional ancestor tails |
| Graph with a bounded feedback vertex set | Same finite-temperature conclusion | Reveal that set, then use the forest theorem |
| Global character-code penalty | Exact fixed-temperature threshold at normalized inverse temperature **β = 1** | Hard-sector weight crosses from exponentially small to constant |
| Global noisy-character log-sum-exp Hamiltonian | Holds at β = 0; fails at every fixed β > 0 | A hidden code label survives thermal noise despite weak single-spin energy changes |
| General bounded-order local models in a Dobrushin or quantum high-temperature regime | **Conjectural** sufficient regime | Missing bridge from mixing/locality to conditional query access or reveal progress |

The last two negative constructions have global interactions. They do **not** establish failure for bounded-degree finite-range Ising models.

The strongest new negative example fixes one Hamiltonian family, rather than changing the Hamiltonian when temperature changes:

$$
H_{n,L}(x)=-\log\!\sum_{v\in\mathcal C_n}\exp(Lx\cdot v),
\qquad \mathcal C_n=\{\text{signed binary characters}\}.
$$

For every fixed β,L > 0, its Gibbs law is exponentially close in total variation to a noisy character law with signal $\rho=\tanh(\beta L)$. One quantum query then needs Ω(log n) classical queries at an accuracy depending only on β,L. Yet the Hamiltonian has energy oscillation at most Ln, single-spin energy changes at most 2L, identity spin covariance, and exact three-wise independence. For fixed β, choosing L sufficiently small makes its entropy density arbitrarily close to maximal. Its interaction order is unbounded. These are genuine full-AA counterexamples, beyond the earlier influence-only results for noisy codes.

A second refinement separates a thermodynamic window from a query threshold. For a character-code mixture with weight wₙ, full AA holds **if and only if** log n is bounded by a fixed polynomial in 1/wₙ. Thus a hard-sector weight tending to zero can still defeat a polynomial-in-accuracy simulator. The proof includes a matching classical algorithm that identifies and verifies a candidate character.

The positive forest theorem is independent of degree and external-field bounds. Its constants depend on β times the largest **edge** strength, through a posterior continuation probability bounded by $1-e^{-4\beta J_{\rm edge}}<1$. This is different from a Dobrushin bound on the **sum** of incident strengths. The theorem concerns classical Gibbs laws; it does not automatically extend to transverse-field models on the same graph.

Two general criteria complement these examples:

- **Polynomial reveal progress:** on a class closed under all pinnings, full AA is equivalent to a polynomial-size adaptive transcript revealing an inverse-polynomial amount of the variance of every nonconstant quantum acceptance function. A martingale argument proves sufficiency. This targets the query problem directly, without equating flip derivatives and revealed information.
- **One-sided likelihood transfer:** if a law has a dimension-uniform Lᵖ density bound, p > 1, relative to an already simulable reference, then full AA transfers. The corresponding sufficient thermal condition is a bounded free-energy difference $\log Z(p\beta)-p\log Z(\beta)$. Failure of this condition is not an obstruction: independent edges already show that it is not necessary.

## Read the proofs

- [Synthesis and scope](01_target_and_conclusions.tex), [reveal criterion](02_reveal_criterion.tex), [likelihood/free-energy transfer](03_density_and_free_energy.tex), [structural research program](04_structural_program.tex).
- [Positive simulation mechanisms](../threshold_positive/threshold_positive.tex): posterior access, arbitrary blocks, forests, feedback vertex sets.
- [Genuine obstructions](../threshold_obstructions/threshold_obstructions.tex): robust query lower bound, fixed noisy-code Hamiltonian, energy–entropy balance and exact schedule criterion.
- [Physical models and literature](../threshold_physics/threshold_physics.tex): species symmetry, collective transverse-field models, normalization, source audit and conjectures.
- [Progress and review record](../../../PROGRESS.md).
- [Generalized influence](06_generalized_influence.tex): a no-go for physically local updates, adaptive reveal gain, and recoverable latent-source influences.

The [compiled full dossier](../../main.pdf) is assembled by [the shared master](../../main.tex); the new investigation is in Sections 11–14. No general monotonicity in temperature, necessary-and-sufficient coupling-matrix criterion, or sharp threshold for general local Hamiltonians is claimed. Gibbs sampling, thermal-state preparation, ground-energy computation, and approximation of a function on a particular unknown oracle input are distinct tasks.

## Latest GitHub material incorporated

Reviewed [Tasks 1–3](../../../tasks-1-2-3-summary.md) from commit `d5e4297`, then pulled the [proof companion](../../../tasks-1-2-3-proof-companion.md) at `9312412` before publication. The integrated [upstream audit](05_upstream_audit.tex) preserves the source's status distinctions and records corrections separately; the upstream documents are unchanged. The companion acknowledges the Fourier-additivity and inverse-atom-sign corrections and distinguishes covariance operator norm from absolute row sums.

The new material strengthens the conditional-access research program: Gibbs averaging can raise degree even under Dobrushin contraction, and spatial mixing does not localize arbitrary query gradients. Its degree-dependent influence bounds do not supply the uniform polynomial in quantum query count required here. Our forest and other full-AA classifications remain intact.

Two status corrections are especially consequential. The literal polynomial fcb target follows from the uniform-AA theorem already imported in this study; uniform Fourier-level influences are additive. Also, the stated face-supported transportation LP is feasible by the supplied BDST determinant theorem: the unresolved challenge is a **determinant-free proof**, rather than feasibility itself. Further repairs concern the mean-square comparison witness, inverse-atom prefactor, Boolean degree shortcut, and critical covariance arguments.

A new one-bit check shows that a literal Gibbs-preserving version of that antipodal transport is impossible under nonzero bias, even though independent-field full AA holds. This gives another concrete reason to transfer through a query-accessible representation instead of treating failure of a uniform-measure proof mechanism as a thermal obstruction.

The reviews are [positive mechanisms](../threshold_positive/UPSTREAM_REVIEW.md), [obstructions and routing](../threshold_obstructions/UPSTREAM_REVIEW.md), and [fcb and physical scales](../threshold_physics/UPSTREAM_REVIEW.md). Detailed `[PROJECT]` claims whose cited proofs are absent remain unverified proxy evidence.
