# Papers

| File | Paper | arXiv | Licence | In repo |
|---|---|---|---|---|
| `AA_Exposition.pdf` | Blanc, Docter, Strassle, Tan — *Proof of the Aaronson–Ambainis Conjecture: An Exposition* | [2611.11626](https://arxiv.org/abs/2611.11626) | arXiv non-exclusive | No, download from arXiv |
| `2611.12795v1.pdf` | Huffstutler, Miloschewsky, Podder — *A short proof of the Aaronson–Ambainis Conjecture via the completion framework* | [2611.12795](https://arxiv.org/abs/2611.12795) | CC BY 4.0 | Yes |
| `2609.35327v1.pdf` | Girish, Mittal, Nehoran, Raz — *Distributional Variants of the Aaronson–Ambainis Conjecture* | [2609.35327](https://arxiv.org/abs/2609.35327) | arXiv non-exclusive | No, download from arXiv |
| `2604.13026v1.pdf` | Marwaha, Sud — *A complexity phase transition at the EPR Hamiltonian* | [2604.13026](https://arxiv.org/abs/2604.13026) | CC BY 4.0 | Yes |
| `2204.02063v3.pdf` | Yamakawa, Zhandry — *Verifiable Quantum Advantage without Structure* | [2204.02063](https://arxiv.org/abs/2204.02063) | arXiv non-exclusive | No, download from arXiv |

Not held here: Turturean, *A proof of the Aaronson–Ambainis conjecture*, [2611.09773](https://arxiv.org/abs/2611.09773), the source of the uniform bound every positive result imports.

The three files marked "No" are listed in `.gitignore` because their licence does not allow redistribution. Save them into this folder under the file names above and the links in the notes will resolve.

## Additional sources consulted for the full-AA threshold theory

Primary records checked on 2026-11-14; these PDFs are not added to this repository. See the [detailed scope audit](../notes/synthesis/physical_models/04_literature_audit.tex).

- [Spinka, *Finitary codings for spatial mixing Markov random fields*](https://arxiv.org/abs/1803.10578): forward local coding; no automatic conditional-source query access.
- [Chayes, Crawford, Ioffe, Levit, *The Phase Diagram of the Quantum Curie–Weiss Model*](https://arxiv.org/abs/0804.1605): physical phase boundary for the collective transverse-field model.
- [Bakshi, Liu, Moitra, Tang, *High-Temperature Gibbs States are Unentangled and Efficiently Preparable*, v2](https://arxiv.org/abs/2403.16850v2): separability and preparation, separate from unknown-input query simulation.
- [Putterman, Zlokapa, Cotler, *When quantum thermal states look classical*, v2](https://arxiv.org/abs/2607.28536v2): locality and per-site-strength temperature scales.
- [Chen, Chen, Yin, Zhang, *Rapid Mixing at the Uniqueness Threshold*](https://arxiv.org/abs/2411.03413): critical mixing and spectral independence.
- [Kuwahara, Kato, Brandão, 2025 erratum](https://journals.aps.org/prl/abstract/10.1103/PhysRevLett.134.199901): limitations of the earlier CMI cluster-expansion argument.
- [Kato, Kuwahara, v2](https://arxiv.org/abs/2504.02235v2) and [Chen, Rouzé](https://arxiv.org/abs/2504.02208): qualified quantum Markov/recovery results; their conditions are not promoted to a full-AA theorem.

For the upstream Tasks 1–3 audit at commit `d5e4297`, also checked:

- [Escudero Gutiérrez, *Influences of Fourier completely bounded polynomials and classical simulation of quantum algorithms*, v2](https://arxiv.org/abs/2304.06713v2): indexed fcb norm, supremum-norm domination, restrictions, and the distinction between the homogeneous bound and the historical conjecture.
- [O'Donnell, Zhao, *Polynomial bounds for decoupling, with applications*](https://arxiv.org/abs/1512.01603): uniform-product decoupling/tail statements, not a general Gibbs MLSI junta theorem.
- The supplied Blanc–Docter–Strassle–Tan exposition, Lemma 3.1 and Section 2.5.4: its determinant proof already gives a permutation that certifies feasibility of the stated summed transportation LP. A determinant-free proof is a different task.
