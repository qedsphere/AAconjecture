# Positive mechanisms for full AA

Started and completed 2026-11-14 as a parallel theory stream of the Hamiltonian threshold investigation. The primary target is polynomial classical approximation of quantum acceptance probabilities; local flip influences are a separate proxy.

The chapter wrapper is `threshold_positive.tex`; it follows the shared `notes/distributions/<topic>/NN_topic.tex` organization.

## Completed deductions

1. **Local posterior transfer.** A representation from an already simulable source law transfers full AA when a virtual output query has bounded source-query cost, the hidden source can be sampled conditionally on the actual input with bounded query cost, and approximation error has a bound conditional on the full observed input. This avoids global-total-variation and `log n` losses.
2. **Arbitrary bounded-block products.** Every product of distributions on blocks of bounded size has full AA, with a bound uniform over atom probabilities, including zero atoms and dimension-dependent biases. The proof rounds each block law upward in a multiplicative dyadic envelope, couples through independent block replacement, and samples gadget randomness conditionally on the observed block. No finite-energy assumption is needed.
3. **Ising forests.** Every finite-temperature Ising forest with bounded absolute edge couplings has full AA, uniformly over graph size, maximum degree, arbitrary external fields, and all pinnings. A binary tree kernel decomposes into a common reset law plus deterministic copy/flip. Given the full spin configuration, source pairs remain edge-independent, and their posterior continuation probability is at most `1 - exp(-4 beta J*)`. Truncating ancestor histories at `O(exp(4 beta J*) log(T/e))` gives a dimension-independent quantum hybrid error and a local posterior oracle.
4. **Bounded feedback vertex sets.** Querying a fixed-size set whose deletion leaves a forest reduces to the preceding theorem; couplings incident to the queried set may be arbitrary because they become external fields.

All positive statements import uniform-input AA simulation. These are deductions recorded here; no priority or novelty claim is made.

## Review and verification

- The physical-theory agent independently reviewed all four proof sections and found no substantive issue, including coherent-query costs, conditional source independence, arbitrary-field uniformity, and error constants.
- The root agent independently checked the tree reset decomposition, the endpoint-conditioned continuation formula, the `exp(-4 beta J*)` ratio bound, and the locality of the posterior. The text explicitly handles `lambda = 0` and notes that finite parameters imply positive reset mass.
- `python3 verify_positive.py` passed 18 dyadic-block rounding cases and 12 exact five-spin forest enumerations. The latter include paths, stars, branching trees, disconnected forests, signed and zero couplings, arbitrary fields, and beta zero. The script checks Gibbs/Markov factorization, the independent-source output law, full posterior factorization, and the conditional truncation bounds for lengths one and two. Results are saved in `verification.json`.
- This agent separately reviewed `../threshold_obstructions/03_fixed_hamiltonian_all_temperatures.tex`: the Gibbs-power comparison, beta-below-one inequalities, score-gap probability, total-variation normalization, symmetry, entropy, and finite-energy claims were consistent.
- This agent separately reviewed `../threshold_physics/01_species_exchangeability.tex`: the simultaneous product-slice simulator and its parameter arithmetic were consistent. In particular the endpoint hybrid uses conditioning in the correct direction and the number of species enters the sampling/union-bound cost rather than the quantum hybrid factor.

## Literature used and limits

The shared uniform-input simulation assumption and quantum hybrid estimate are reused. Girish–Mittal–Nehoran–Raz's conditional gadget-sampling idea is available in the supplied source and [paper listing](https://arxiv.org/abs/2609.35327).

Internet-assisted research checked Yinon Spinka, [Finitary codings for spatial mixing Markov random fields](https://arxiv.org/abs/1803.10578), also available as the [author's manuscript](https://www.math.tau.ac.il/~yinonspi/files/finitary-coding-mrf.pdf). Its strong-mixing-to-forward-coding theorem motivates the general-graph direction; the needed posterior oracle and full-input-conditional tail estimates do not follow merely from the quoted result.

The forest theorem is for classical diagonal Ising Gibbs laws. A measured noncommuting transverse Ising thermal state need not have the binary tree factorization used in the proof. The temperature-dependent constants diverge as beta tends to infinity; no uniform assertion over arbitrary beta(n) is inferred. General bounded-degree graphs remain open within this stream: a rapidly mixing sampler alone has not supplied the query-local posterior needed for the transfer theorem.

Notation was harmonized after review: the LaTeX forest theorem uses `J_edge` for the maximum absolute edge coupling, distinct from incident-row-sum norms in the physics chapter. Positivity of the kernels and therefore `q_e > 0` are explicit.
