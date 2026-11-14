# Physical structure and full AA

Date: 2026-11-14. This stream follows the numbered LaTeX-section organization of `sharedwork/notes/distributions` and does not edit shared masters.

## Completed deductions

- Proved a simultaneous deterministic acceptance simulator for every product of `r` Hamming slices, using `poly(T,r,1/epsilon)` coordinate queries. Arbitrary mixtures are therefore covered, including correlated block weights. The proof extends the already recorded one-slice simulator with vector-biased product gadgets and per-block hypergeometric estimates.
- Proved that measured Gibbs states of Hamiltonians invariant under permutations within a fixed number of species satisfy full AA at every temperature. Noncommutativity and dimension-dependent coefficients/temperatures cause no exception. The zero-temperature statement concerns the canonical normalized ground-space projector.
- Applied this to collective transverse-field Ising and general collective-spin Hamiltonians. The genuine physical boundary `J tanh(beta Gamma)/Gamma = 1` does not become a full-AA boundary.
- Derived normalized classical conditional-influence bounds and explained why stability under pinning is a useful proof target.

## Literature audit

Primary sources checked online on 2026-11-14:

- Chayes, Crawford, Ioffe, Levit, [arXiv:0804.1605](https://arxiv.org/abs/0804.1605), Theorem 3.2 and equation (3.7).
- Bakshi, Liu, Moitra, Tang, [arXiv:2403.16850v2](https://arxiv.org/abs/2403.16850v2), updated quantitative regime; v1 figures are not silently substituted.
- Putterman, Zlokapa, Cotler, [arXiv:2607.28536v2](https://arxiv.org/abs/2607.28536v2), locality/per-site-strength scales and distinction between thermal properties.
- Chen, Chen, Yin, Zhang, [arXiv:2411.03413](https://arxiv.org/abs/2411.03413), critical mixing.
- Kuwahara, Kato, Brandao, [2025 erratum](https://journals.aps.org/prl/abstract/10.1103/PhysRevLett.134.199901), read including PDF; the original unrestricted 2020 CMI proof is not used.
- Kato, Kuwahara, [arXiv:2504.02235v2](https://arxiv.org/abs/2504.02235v2), replacement belief-propagation framework.
- Chen, Rouze, [arXiv:2504.02208](https://arxiv.org/abs/2504.02208), local Markovianity with specified region qualifications.

## Status and checks

The fixed-species proof was checked algebraically: prefix failure is at most epsilon/4; endpoint replacement costs less than epsilon/8; central simulation and coupling cost at most epsilon/4. The hybrid discrepancy is bounded conditionally on an entire input, so adaptivity introduces no hidden factor of dimension. All query bounds use polynomially many queries for fixed `r`; growth of `r` with dimension is explicitly charged.

The `positive_full_aa` theory agent independently reviewed `01_species_exchangeability.tex`: it checked the endpoint conditioning, vector-biased-product reduction, union bound, constants, and one-tree-for-all-weight-vectors quantifier. No substantive correction was requested.

This stream independently reviewed `threshold_positive/03_ising_forests.tex`, its local-posterior transfer lemma, block-product lemma, and feedback-set corollary. The review checked binary-kernel decomposition, factorization of the conditional source law, the field-uniform likelihood-ratio bound, conditional geometric tails, coherent query count, and error constants. No substantive issue was found. The maximum edge strength in that theorem is distinct from the incident row-sum normalization used in this section.

A standalone LuaLaTeX build of these sections succeeded (six pages, no overfull boxes). The build used a writable temporary font cache; references to other sections are resolved in the shared master build.

Classical Dobrushin and quantum high-temperature full-AA claims are stated as conjectures only. Forward sampling, separability, thermodynamic transitions, and quantum CMI do not by themselves close the conditional-query simulation gap. No claim of novelty or formal verification is made.
