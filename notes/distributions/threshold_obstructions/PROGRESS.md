# Full-AA obstruction workstream

Date: 2026-11-14. Scope: actual polynomial classical query simulation of quantum acceptance probabilities. Files follow the numbered-LaTeX-section organization of `sharedwork/notes/distributions`.

Completed deductions:

1. Hard-component and total-variation transfer lemmas, with explicit error accounting.
2. Upgraded the existing noisy affine-code influence counterexample to a one-quantum-query versus Ω(log n) classical-query separation. The lower bound loses only O(n^-1/2) from fluctuations around the hidden binary target and tolerates every fixed noise bias rho > 0.
3. Constructed one temperature-independent Hamiltonian H = -log sum_v exp(L x·v), over signed character modes. For every fixed beta > 0, its Gibbs law is exponentially close in total variation to the noisy-code law with bias tanh(beta L), and therefore full AA fails. At beta = 0 uniform AA applies.
4. Proved exact three-wise independence, covariance identity, finite site randomness, entropy and maximum-atom estimates, O(n) energy range, and single-flip energy bound 2L for that same powered Gibbs family. No bounded-arity/local-interaction claim is made.
5. Derived the energy–entropy sector-mass identity and an exact criterion for arbitrary character-code mixture weights: full AA iff log n is bounded by some fixed power of 1/w_n. Included the near-critical schedule consequences.

Source check: primary Bernstein–Vazirani paper and Aaronson–Ambainis Forrelation paper were found online. Forrelation is background only. The lower bounds and Gibbs estimates used here are explicitly proved in the notes; no novelty claim is made.

Review checkpoints: the noise is quenched as part of the input; Gibbs powering does not equal rescaling L except at the proved asymptotic comparison; both beta < 1 and beta > 1 are covered by the global power-sum ratio bounds; full-AA statements are separated from influence-only counterexamples. Parent-agent independent review found the noisy posterior argument, power-sum comparison, and arbitrary-weight necessity/sufficiency sound.

Verification completed:

- `verify_small.py` exhaustively enumerated n = 4 and n = 16 at L = 0.4 and beta = 0.3, 1, 2. It checked the exact noisy-law mean, variance and conditional mean of the one-query acceptance function; exact powered-Gibbs moments through degree three; energy-range and one-flip bounds; global power-sum ratio bounds; and equality of the two laws at beta = 1. All assertions passed, with moment errors below 9e-16. Results are in `verification.json`.
- The small-n total-variation values are diagnostics only and need not decrease at these sizes. They are not numerical evidence for the asymptotic comparison; its proof is the explicit exponential estimate in section 03.
- A standalone LuaLaTeX build of the chapter produced six pages without overflow warnings. References to the earlier shared chapters are unresolved in that isolated build and are resolved by the shared master.
- Independently reviewed `threshold_theory/02_reveal_criterion.tex` and `03_density_and_free_energy.tex`: hereditary closure is used at the appropriate pinned leaves; the expected variance decrement, round count and 3a/4 converse are correct; the one-sided likelihood exponent, tail truncation, partition-function identity and sub-Gaussian constant are correct. The distinction between hereditary and unconditioned full AA is stated explicitly. No mathematical correction was needed.
