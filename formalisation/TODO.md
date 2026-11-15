# Formalization tasks

Work on one stated result at a time. AA is proved and should be imported,
not reintroduced as an axiom. Do not use placeholders to claim completion.

## First checkpoint

- [x] Inspect project research state and relevant report derivations.
- [x] Read supplied wrapper and recover statements from matching PDF.
- [x] Visually inspect Theorem 4.1 and its formulas on PDF p. 26.
- [x] Pin Lean, Mathlib, and the supplied upstream AA repository.
- [x] Compile all local proof modules; record exact results.
- [x] Audit the 11 core results and record standard Lean axiom dependencies.
- [x] Finish the extended 13-theorem audit, including the two AA statement adapters.
- [x] Record the theorem coverage and remaining formalization boundary.

## Next dependency: scalar simulation (§2.4)

- [x] Define deterministic Boolean-oracle trees, physical query cost, depth,
  truncation, finite potential telescoping, and uniform-table fairness for
  fresh coordinates; prove the uniform truncation-failure bound.
- [x] Construct exact conditional-mean summaries for any given fresh tree,
  preserving its coordinates and physical query counts.
- [x] Construct the polynomial tree from a restriction-stable influence rule;
  prove termination, freshness and the potential-based expected cost.
- [x] Define Boolean-function and multivariate-polynomial restrictions; prove
  one-bit and simultaneous partial-assignment pointwise correspondence and
  boundedness/total-degree preservation.
- [x] Prove the Boolean flip-influence potential identity under restriction,
  Phi(f) - E_b Phi(f|i=b) = Inf_i(f), for arbitrary finite Boolean cubes.
- [x] Prove Phi(p) ≤ d for degree-d [0,1] polynomials, and bridge the new
  generic finite-cube normalization to `Influence.lean`'s `Fin N` interface.
- [x] Prove one-coordinate conditional means, exact squared-error splitting,
  finite-law variance decomposition, Chebyshev, and tablewise Markov bounds.
- [x] Apply the squared-error split recursively to a fresh decision tree with
  exact conditional-mean leaves and aggregate the leaf-variance error.
- [x] Use the imported AA statement as an explicit parameter to construct the
  influence-guided tree, then prove deterministic truncation and Chebyshev error
  with query cap ceil(512*d^13/(e^16*delta^9)).
- [ ] Instantiate the explicit AA parameter with the upstream proved theorem
  from `AaronsonAmbainis.Main`; check its full dependency graph locally.
- [x] Connect native-value and padded Boolean XOR quantum query algorithms to
  degree-2Q acceptance polynomials with [0,1] range; construct scalar estimators
  under `hAA`, using the vendored operational quantum polynomial method.

## Complete Theorem 4.1 and Corollary 4.2

- [x] Construct finite affine parity hashes; prove exact pair-collision
  probability `1/2^k` for k output bits (B = 2^k buckets).
- [ ] Round the bucket count to a power of two and wire the affine family
  into the operational decoder/verifier construction.
- [x] Assemble scalar estimators for all B(L+1) fixed native-quantum predicates,
  selected before sampling the table, and derive aggregate failure.
- [x] Construct and cost an oracle-query decoder/verifier algorithm, proving
  C(t,rho) = B(L+1)F(Q,t/16,rho/(4B(L+1))) + BV under `hAA` and an explicit
  pair-collision hypothesis (`exists_quantum_extractor`).
- [ ] Extend the assembled extraction theorem to the padded XOR semantics;
  the XOR acceptance-polynomial and scalar-estimator bridges are already proved.
- [ ] Prove the sparse-heavy implication tablewise, Markov exceptional set,
  and independent repetition bound with r = ceil(log2(1/eta)).
  Independent finite products and the exact repeated-failure formula
  `(1 - success_probability)^r` are proved; operational/tablewise assembly
  and logarithmic rounding remain.

## Later results, after extraction

- [ ] Theorem 4.3: formal min-entropy definition, accepted-law heavy atom,
  soundness contradiction, and strict exceptional-oracle bound.
- [ ] Seeded leftover hashing and global acceptance reweighting (PDF p. 27).
- [ ] Gibbs Lemmas 3.1–3.9, then Theorem 3.10; keep product-resampling
  influence distinct from Boolean flip influence.
- [ ] YZ coding inputs and Lemma 5.1/Theorems 5.2–5.3.
- [ ] Quantum state preparation Lemma 5.4 and Theorem 5.5.
- [ ] Appendix B sparse sampling and remaining comparison statements.
- [ ] Obtain the nine included TeX sources and maintain a stable label-to-Lean map.
