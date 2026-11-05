# affine_quadric_lean 0.1.0 — Initial selective formalization

Version 0.1.0 provides a selective Lean 4 companion formalization for Adrián Henríquez-Tamargo's *Hamiltonian Desingularization, Collision Asymptotics, and Exact Critical Modes for Cohomogeneity-One IIB Solitons on the Affine Quadric*. Exact statements, hypotheses and external dependencies are documented in `FORMALIZATION_SCOPE.md`. This development does not certify the entire paper.

## Mathematical scope

- Scalar Hamiltonian identities, differential momentum balance under the stated canonical equations, weighted rational identities, scalar positivity and scalar energy laws. The numerical positivity example does not establish the existence of a physical solution.
- Conservation of the variational pairing and scalar endpoint bounds under the declared solution, variation, comparison and normalization data.
- Exclusion of nonconstant quadratic first integrals for every β>0, with C∞ coefficients on a nonempty connected open time interval, a **given regular inverse mechanical clock**, and the specified physical transport equation. The determining equations and temporal obstruction are derived within these hypotheses.
- Construction of a local C∞ canonical continuation through collision, local uniqueness, and one-sided matching to an incoming trajectory with the required terminal limits.
- Finite-order Taylor remainders, distance estimates and leading collision laws. Analytic distance inversion and convergent Puiseux profiles remain **conditional on analytic solution data**. Analyticity of the constructed C∞ continuation has not been proved.
- Metric, connection and curvature calculations for an auxiliary two-dimensional model, with leading term 2/(9ρ²) and remainder O(ρ^(-4/3)). Identification with the ambient six-dimensional sectional curvature remains outside the formalized result.

The development also leaves external the construction of the inverse mechanical clock, the geometric Stenzel identification, full 6D/7D/8D tensor reconstruction, global physical branch and comparison theory, the global diffeomorphism of Corollary 6.3, and the exact critical modes and sensitivity of Section 7. The selected results do not constitute complete formalizations of Propositions 4.2, 6.2 or 6.4.

## Fixed environment and accepted evidence

- Lean: `leanprover/lean4:v4.24.0`.
- Mathlib: `f897ebcf72cd16f89ab4577d0c826cd14afaafc7`.
- All nine dependency revisions are pinned in `lake-manifest.json`.

The accepted corpus contains **54 mathematical modules, 56 Lean files in total, 377 explicitly written theorems and 614 inventoried declarations**. The 614 declarations are not a theorem count or a count of every automatically generated declaration in Lean's environment.

The preserved clean source build and direct axiom audit completed on **30 October 2026** and each covered exactly the 614 inventoried declarations. Axiom dependencies are restricted to `propext`, `Classical.choice` and `Quot.sound`. The delivered proofs contain no `sorry`, `admit`, `native_decide` or custom axioms. The 59 accepted source/configuration files retain their accepted SHA-256 values.

These are preserved validation results for the accepted mathematical corpus. The prior reproduction was performed by the same executor and is not presented as independent human review. Reproduction instructions and evidence are described in `README.md` and `docs/VALIDATION.md`.

## Companion paper and citation

Author: **Adrián Henríquez-Tamargo**. ORCID: https://orcid.org/0009-0003-1452-1632.

Source repository: https://github.com/adrianht85/affine_quadric_lean.

The **paper's DOI**, `10.5281/zenodo.23956688`, is reserved in a Zenodo draft and has not yet been definitively registered; the paper is not yet published. This is not the software's DOI. The **software DOI remains pending**.

The intended archival relationship is **software `isSupplementTo` paper**.

## License

The software is licensed under MIT. This license does not assign a license to the companion paper.
