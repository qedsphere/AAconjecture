# Formalisation coverage and remaining segments

Reviewed 2026-11-15 at upstream commit `38ccd9363153775f46ab1344f6077500cef8e82a`.
Scope: the unified manuscript, with the weighted-interaction report as supporting material. This is a source review, dependency map, and record of the local Lean verification boundary.

## What is already implemented

The twenty-six modules in `formalisation/UnifiedAA/` contain finite probability, bucket reconstruction and isolation, AA statement adapters, deterministic query trees and typed query programs, uniform fresh-query fairness, potential-based truncation, conditional means, squared-error probability bounds, polynomial restrictions, independent repetition, affine hashing, Fourier/Parseval influence bounds, AA-conditional polynomial and quantum scalar simulation, and one-round operational quantum extraction. Twelve vendored modules supply the quantum semantics and polynomial method. Their important boundaries are explicit:

- `Extraction.lean:99`, `heavy_output_list_success`, assumes pair collisions and simultaneous estimator accuracy. It establishes list membership probability, not a bounded-query search algorithm.
- `DecisionTreeUniform.lean:69`, `uniform_truncation_failure_bound`, assumes freshness and `HasDrift`; tree summaries are arbitrary reals.
- `Influence.lean` and `ScalarSimulation.lean` take `hAA : AaronsonAmbainis.PrintedConjecture`. Instantiate this with the pinned upstream proof; the adapters and simulator do not discharge that assumption.
- `QuantumSimulation.lean` covers native value and padded Boolean XOR queries. `QuantumExtraction.lean` assembles the native-value extractor with an explicit `hAA`, pair-collision bound, heavy witness, and correct bounded-query verifier. It constructs the scalar estimators and their accuracy guarantees.

## Segments to formalise

| Priority / segment | Manuscript target | Concrete missing proof obligations | Completion boundary |
|---|---|---|---|
| 1. Restrictions and influence potential | §2.4, Theorem 2.4, pp. 8–9 | **Proved:** one-bit and simultaneous partial-assignment restrictions, boundedness and total-degree preservation, exact pointwise correspondence, expected potential drop, nonnegativity, Fourier/Parseval bound Phi(p) ≤ d, and normalization adapter to the AA interface | Complete polynomial potential infrastructure; direct induction supplies the constructed tree's expected-cost bound |
| 2. Scalar tree and error | Theorem 2.4 | **Proved conditional on hAA:** terminating fresh tree, exact leaf means, small terminal variance, potential-based expected cost, truncation and Chebyshev error, explicit rounded budget ceil(512*d^13/(e^16*delta^9)) for d≥1 and 0<e,delta≤1. **Open:** instantiate hAA with the upstream proved theorem | Actual bounded-query polynomial estimator; quantum bridge remains separate |
| 3. Quantum-to-polynomial bridge | Theorem 2.4 and fixed predicates in §4 | **Proved:** operational finite quantum models for native value and padded Boolean XOR queries; acceptance in [0,1]; degree ≤2q; fixed output postprocessing and bucket/bit-mass identities | Quantum scalar theorem with explicit rounded F(q,e,delta), conditional on `hAA`; vendored polynomial method checked unchanged on the pinned toolchain |
| 4. Conditional-mean restriction | §2.5, Proposition 2.6, pp. 9–10 | L2/L1 estimator error; existence of a leaf whose conditional mean differs from the global mean by ≥3v/4; query bound with factor 2^93 and v^-34 | Formal biased restriction statement, using genuine conditional means |
| 5. Affine hashing and operational extraction | §4, Theorem 4.1, p. 26 | **Proved:** affine parity family and exact `1/2^k` collisions; fixed native-quantum predicates; construction of all B(L+1) scalar estimators; typed decoder/verifier composition and full query cost. **Open:** power-of-two bucket rounding and plugging the affine family into the final theorem; XOR extractor assembly | Concrete native-value extractor with cost B(L+1)F(Q,t/16,rho/(4B(L+1)))+BV and success ≥rho/2, conditional on `hAA`, pair-collision, heavy-witness and verifier hypotheses |
| 6. Sparse-witness amplification | Corollary 4.2 | **Proved:** generic joint-to-tablewise Markov bound, independent finite products and exact repeated-failure formula `(1-success_probability)^r`. **Open:** sparse-heavy implication and per-table operational assembly, logarithmic repetition rounding | Stated per-table search success and repetition/query bounds |
| 7. Entropy and extraction | Theorem 4.3 and p. 27 | Accepted conditional law; heavy atom from low min-entropy; unconditional mass a0*2^-h; soundness contradiction; strict exceptional-set bound; seeded leftover hashing and global acceptance reweighting | Certified accepted-output entropy and extraction with all acceptance/exception hypotheses explicit |
| 8. Exact Gibbs histories and posterior access | §3, Lemmas 3.1–3.4 | Finite Gibbs laws and pinnings; signed-parity/constant update maps; analytic norm bounds and constants; stationary history disintegration; forward path counting; lazy reverse/posterior sampling; typed physical-spin work | Exact source/physical joint law, conditional discrepancy, and posterior expected-work bounds |
| 9. Product-alphabet simulation | Lemmas 3.5–3.8 | Product certificate inequality; alphabet-independent quantum adversary weights; influence-guided product trees; real-valued approximation | Symbol-query simulator with stated quantitative bounds, using resampling influence rather than Boolean flip influence |
| 10. Quantum hybrid and Gibbs assembly | Lemma 3.9 and Theorem 3.10 | Recursive hybrid norm estimate; coherent source evaluation and compute/uncompute cost; forward and work truncation; deterministic seed selection; parameter arithmetic | O(T^18 e^-28) physical-spin queries at weighted interaction strength ≤1/8, uniform under positive-probability pinnings |
| 11. Coding and honest generation | §5, Lemma 5.1, Theorems 5.2–5.3, Lemma 5.4, Theorem 5.5 | Exact YZ coding/list-recovery inputs; retuned adaptive classical soundness; entropy asymptotics; quantum preimage preparation and propagation of state error | Refined entropy and honest n_c-query, one-parallel-layer generation claims |
| 12. Sparse sampling and quantitative comparisons | Appendix B, Theorem B.1; Appendix A | Two independent hash banks; candidate deduplication; weight accuracy and normalization; zero-weight fallback; total variation and exceptional-table conversion; comparison exponents | Full sparse-output sampling guarantee and explicit comparison bounds |

## Recommended sequence

Segments 1–3 now connect the tree infrastructure to actual polynomial and quantum estimators, conditional on the imported AA statement. Import the upstream proof to discharge that parameter. Segment 5 now constructs and costs a native-value quantum extractor; connect its pair-collision hypothesis to the affine family with bucket rounding, then finish amplification and entropy through segments 6–7. Segment 4 is a downstream branch using exact leaf means. Segments 8–10 form the independent Gibbs branch, sharing quantum foundations with segment 3. Finish coding/preparation and sparse sampling through segments 11–12.

Completed first mathematical deliverable: Boolean function restriction definitions plus the exact identity

    Phi(p) - (Phi(p restricted i=0) + Phi(p restricted i=1))/2 = Inf_i(p)

using the current squared-flip influence normalization. The degree bound `Phi(p) ≤ d` and a degree-preserving restriction tree are now proved, together with the explicit-budget polynomial scalar theorem under `hAA`.

## Proof-sensitive interfaces

- Keep oracle-table randomness, hash randomness, and repeated-run randomness distinct. Estimators for fixed predicates must be chosen before sampling the oracle; a decoded oracle-dependent candidate does not justify a fresh scalar-AA application to its singleton predicate.
- Uniform fair branches require fresh coordinates. Conditional means require averaging all unread completions. Proposition 2.6's prose also mentions setting unread bits to zero: that is not generally the same operation on the current 0/1 cube representation. Formalise the displayed conditional expectation and resolve the prose/representation convention before using a zero-evaluation shortcut.
- Gibbs mean-error simulation is a different conclusion from polynomial-influence AA under a Gibbs measure. The weighted-interaction report's “Full AA” title must not obscure this distinction.
- An abstract theorem conditional on a simulator, drift, collision bound, or external coding input is useful infrastructure, but does not discharge that input.
- `weighted_interaction_full_proof.tex` covers overlapping Gibbs/product-alphabet material. Reuse the same formal definitions and lemmas rather than treating it as a separate independent proof target. The wider research notes and cubic/quadratic reports need a separate coverage inventory if they are to be included beyond the unified manuscript.

## Source and verification limitations

The root unified TeX wrapper still references nine absent files under `results/unified_aa_sections/`. The matching 36-page PDF is present in `formalisation/sources/unified_aa_simulation.pdf`; its text was inspected for the theorem map above. Recover the section sources for stable statement-level source links and reproducible manuscript compilation.

The full local `lake build` passed with pinned Lean 4.33.0. The combined `checks/Axioms.lean` audit passed all 101 selected declarations, with only `propext`, `Classical.choice`, and `Quot.sound`; `scripts/check_axioms.py` verifies both the exact declaration set and the allowed axioms. Logs are `formalisation/artifacts/build-complete.log` and `formalisation/artifacts/axioms-complete.log`. No local or vendored module contains `sorry`, `admit`, a custom axiom declaration, or `native_decide`.

The earlier disk blocker for the local aggregate was resolved by the recorded `formalisation/patches/aa-conjecture-imports.patch`: it replaces only the broad import in the upstream statement file with three targeted Mathlib imports, preserving every AA proposition. Targeted caches were downloaded. `scripts/build_serial.py` orders local and vendored modules by their imports and checks them sequentially. The upstream `AaronsonAmbainis.Main` proof is still not imported or rechecked locally; the scalar and extractor theorems retain their explicit `hAA` parameter. This build and audit do not certify the unformalized manuscript segments or translations from arbitrary quantum programming languages into the formal query model.

Primary local references: `formalisation/README.md`, `formalisation/TODO.md`, `formalisation/RESEARCH.md`, `PARALLELISATION.md`, the twenty-six local Lean modules, the vendored quantum library's provenance, and the frozen manuscript PDF.
