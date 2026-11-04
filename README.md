# Affine quadric: selective Lean 4 formalization

## Purpose and paper

Companion formalization for [Adrián Henríquez-Tamargo](https://orcid.org/0009-0003-1452-1632), *Hamiltonian Desingularization, Collision Asymptotics, and Exact Critical Modes for Cohomogeneity-One IIB Solitons on the Affine Quadric*. This is a selective formalization; it does not certify the whole paper. Begin with [AffineQuadric/](AffineQuadric/) and the scope table below.

## Fixed environment and reproduction

With elan installed and this repository as the working directory, run:

```sh
lean --version
lake exe cache get
lake build
```

Required Lean: `leanprover/lean4:v4.24.0`. Mathlib: `f897ebcf72cd16f89ab4577d0c826cd14afaafc7`; all nine package revisions are pinned in `lake-manifest.json`. Keep the toolchain, lakefile and manifest unchanged. The accepted corpus has 54 mathematical modules, 56 Lean files including the root and audit, 377 written theorems and 614 inventoried declarations. Its sources contain no incomplete proofs (`sorry`, `admit`, `sorryAx`), `native_decide`, or custom axioms. Audited axiom dependencies are limited to `propext`, `Classical.choice` and `Quot.sound`.

For a direct axiom audit, run `lake env lean -DwarningAsError=true AffineQuadric/Audit.lean`. [Reproduction and validation](docs/VALIDATION.md) explains independent name coverage and how to check captured output. The source-integrity check is `python3 tools/verify_public.py` (`python` on some Windows installations).

## Exact scope

| Paper target | Certified part and retained inputs |
| --- | --- |
| Proposition 3.1 | Canonical scalar Hamiltonian partials and momentum balance, under the displayed canonical equations. |
| Proposition 4.3 | Conserved variational pairing for a supplied radial solution and its two variations. |
| Theorem 4.1; quadratic clause of Proposition 4.2 | Nonconstant quadratic first integrals excluded for every β>0, with C∞ coefficients on any nonempty connected open time interval, a **given regular inverse mechanical clock**, and the specified physical transport equation. The determining equations are derived. |
| Scalar energy clause of Proposition 4.2 | Energy/free-motion laws at β=0 and strict energy decrease at β>0 for the supplied scalar/Newtonian systems. The Stenzel geometric identification is external. |
| Proposition 6.2, local continuation | Constructed C∞ canonical continuation through collision, local uniqueness and one-sided matching to an incoming trajectory with the declared terminal limits; differential configuration fold and crossing. |
| Collision asymptotics; Proposition 6.4 | Uniform finite-order collision remainders; analytic distance inversion and convergent Puiseux profiles **conditional on analytic solution data**. Analyticity of the constructed C∞ ODE solution is not proved. |
| Radial-vertical curvature model | Metric, connection and curvature calculated for the auxiliary two-dimensional model, with 2/(9ρ²) leading term and O(ρ^(-4/3)) remainder. Equality with the ambient six-dimensional sectional curvature is not formalized. |
| Propositions 6.4 and 6.5, scalar clauses | Weighted rational identities, terminal positivity and quantitative endpoint bounds **from explicit comparison and endpoint data**. Global comparison is external. |
| Outside the delivered scope | Geometric Stenzel identification; inverse mechanical clock construction; analytic ODE regularity of the constructed continuation; full 6D/7D/8D tensor reconstruction; global physical branch/comparison theory and global diffeomorphism S(φ₀) (Corollary 6.3); exact critical modes and sensitivity (Section 7). |

## Detailed map

[FORMALIZATION_SCOPE.md](FORMALIZATION_SCOPE.md) gives theorem anchors, mathematical input hypotheses, external dependencies and an inventory of all 56 Lean files. [Development method](docs/DEVELOPMENT_METHOD.md) records the assisted workflow and its limits. Project code is under the [MIT license](LICENSE); use [CITATION.cff](CITATION.cff) for citation metadata. The source repository is [https://github.com/adrianht85/affine_quadric_lean](https://github.com/adrianht85/affine_quadric_lean). Software DOI, article DOI/URL, release URL and actual publication date remain pending. The software MIT license does not assign a license to the article.

This preparation phase keeps the GitHub repository **private**. Opening is planned for **5 November 2026**; this is a plan, not a completed publication, release or Zenodo deposit.
