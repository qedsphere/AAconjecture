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
- [ ] Construct the tree whose stored summaries are exact conditional means
  of the target polynomial and verify its drift hypothesis.
- [ ] Define restrictions and prove boundedness/degree preservation.
- [ ] Prove the Boolean flip-influence potential identity under restriction,
  Phi(p) - E_b Phi(p|i=b) = Inf_i(p), and Phi(p) ≤ d for [0,1] functions.
- [ ] Use imported AA to construct the influence-guided tree. Bound expected
  depth, then prove deterministic truncation and conditional Chebyshev error.
- [ ] Connect a quantum query algorithm's acceptance function to a degree-2Q
  polynomial. Keep this as an explicit hypothesis until that model is proved.

## Complete Theorem 4.1 and Corollary 4.2

- [ ] Instantiate the collision hypothesis by a uniform finite affine hash.
- [ ] Assemble scalar estimators for all B(L+1) predicates, selected before
  sampling the table, and derive the existing aggregate failure hypothesis.
- [ ] Construct and cost an oracle-query decoder/verifier algorithm, proving
  C(t,rho) = B(L+1)F(Q,t/16,rho/(4B(L+1))) + BV.
- [ ] Prove the sparse-heavy implication tablewise, Markov exceptional set,
  and independent repetition bound with r = ceil(log2(1/eta)).

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
