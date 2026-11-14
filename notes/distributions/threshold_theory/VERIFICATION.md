# Verification and provenance

Date: 2026-11-14.

The proof status is **analytical deductions with independent agent review and finite checks**, conditional on the uniform-input AA simulation theorem imported throughout the dossier. Finite enumeration does not establish asymptotic claims, and formal verification or research priority is not claimed.

## Mathematical review

| Argument | Review |
|---|---|
| Local posterior transfer and arbitrary blocks | Main agent; physical theory agent |
| Ising forests and feedback vertex sets | Main agent; physical theory agent |
| Noisy-code query lower bound | Main agent |
| Fixed log-sum-exp Hamiltonian at every fixed β > 0 | Main agent; positive theory agent |
| Exact character-mixture weight criterion | Main agent |
| Simultaneous products-of-slices simulation | Main agent; positive theory agent |
| Reveal progress and one-sided likelihood transfer | Obstruction theory agent |

The reviews specifically checked conditional versus marginal coupling errors; posterior source independence after observing the entire input; arbitrary external fields; the β < 1 power-sum inequality; normalization in total variation; the accuracy quantifier for shrinking hard-sector weights; and closure under rare pinnings.

The final limiting-pressure observation follows directly from the reviewed normalization identity: Zₙ(β) = 2n [2 cosh(βL)]ⁿ E_q R with E_q R = 1 + O(exp(−cn)) for each fixed β,L > 0.

## Reproducible finite checks

- [Positive checks](../threshold_positive/verify_positive.py), [results](../threshold_positive/verification.json): 18 dyadic block-rounding cases and 12 five-spin forest cases. Forests include paths, stars, branching trees and disconnected components, signed couplings, zero/nonzero interactions, and external fields. Maximum Gibbs/source-law discrepancy was about 1.1 × 10⁻¹⁶; maximum posterior factorization discrepancy was about 2.0 × 10⁻¹⁵.
- [Obstruction checks](../threshold_obstructions/verify_small.py), [results](../threshold_obstructions/verification.json): exhaustive configurations for n = 4 and 16, L = 0.4 and β = 0.3, 1, 2. Exact moment formulas, conditional means, three-wise symmetry, energy bounds, and power-sum directions passed. Small-size total variation need not decrease monotonically in n; the asymptotic comparison is proved analytically.

Run either Python script from any directory. It writes its JSON beside the script. The obstruction checks require NumPy; the positive checks use the Python standard library.

## Document checks

The integrated master includes all four new chapter wrappers. Build with LuaLaTeX; on this host a writable TeX cache was needed:

```sh
cd notes
aa_build_dir="$(mktemp -d)"
mkdir -p "$aa_build_dir/cache"
TEXMFVAR="$aa_build_dir/cache" TEXMFCACHE="$aa_build_dir/cache" latexmk -lualatex -interaction=nonstopmode -halt-on-error -outdir="$aa_build_dir" main.tex
cp "$aa_build_dir/main.pdf" main.pdf
```

The current PDF is [main.pdf](../../main.pdf), 80 pages; the new chapters occupy pages 54–80. The build has no LaTeX warnings, undefined references, or overflowing boxes. Before the upstream update, all 22 new chapter pages were rendered and inspected in contact sheets, with proof pages 55, 61, 66, and 68 inspected individually. After that update, the added audit on pages 58–61 was rendered and inspected. The final generalized-influence note on pages 61–63 was inspected before publication. Relative links were checked to resolve within the repository or to explicit external sources, and Markdown math delimiters were made compatible with GitHub. Temporary cache, auxiliary TeX files, and page renders are kept outside the repository.

## Source audit

The [physics literature audit](../threshold_physics/04_literature_audit.tex) and [paper index](../../../papers/README.md) record primary sources consulted. The source claims distinguish efficient preparation, correlation decay, and conditional mutual information from unknown-input query simulation. In particular, the original unrestricted 2020 CMI argument is not used after the 2025 erratum.

## Upstream update at d5e4297

All three theory agents audited the new Tasks 1–3 handoff. Their `UPSTREAM_REVIEW.md` files record checked calculations, source references, and scope qualifications. The root agent checked the supplied BDST antipodal-routing statement and its permutation-producing proof directly before recording that the uniform summed LP is feasible. The one-bit Gibbs-transport obstruction, Fourier additivity, star coefficients, mean-square repair, addressing example, and tree covariance sum are elementary analytical checks. The fcb norm domination was checked against Escudero's primary paper. Historical `[PROJECT]` claims with missing detailed proofs were not promoted into theorems.

This update changes the source audit and research program, not the earlier numerical models. The finite checks above were therefore not rerun. The integrated LaTeX and newly added pages were rebuilt and checked separately.

## Publication update at 9312412

The new proof companion was pulled before preparing the campaign commit. Its acknowledged corrections are reflected in the integrated audit, and the obstruction agent's review records the remaining parameter-dependence and proof-status gaps. A separate theory agent wrote the generalized-influence note; the root agent checked the local-update bound, reveal-gain identity, parity example, and source-influence formula. No new unproved implication from mixing to full AA is asserted. Publication checks cover the root landing page, portable build instructions, source references, generated PDF, and the intentionally selected staged files.
