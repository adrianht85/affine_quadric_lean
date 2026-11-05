# Selective formalization scope — PE V8

This is a statement-and-dependency map of the selective Lean development, not a claim that the whole article is formalized. Names belong to AffineQuadric. Hito9 accepted 53 mathematical modules, 367 written theorems and 602 inventoried declarations. Hito10 preserves those sources and adds one module (10 theorems, 2 definitions): current inventory 54 mathematical modules, 377 written theorems and 614 declarations. [Validation](docs/VALIDATION.md) records the accepted validation and the status of this public packaging.

The reference is the accepted manuscript source `PE_V8_English.tex`, SHA-256 `f40d7898470a34b8320d316b8420c1ad9badd5b244719ffb14c3ee3165e0dfc7`. Labels below identify the exact statements/equations in that source.

**Entry types:** **H** = explicit mathematical hypothesis of a Lean theorem; **D** = definition; **R** = proved result; **E** = dependency still external to the delivered formalization. An H is neither an added kernel axiom nor a conclusion already proved. The axiom audit checks declarations under their stated hypotheses; permitted dependencies are `propext`, `Classical.choice`, `Quot.sound`.

Notation: Lean `q` is V8's canonical `q`/`u`; geometric velocity `v=u'` in Pairing is distinct from Newtonian velocity `U=dZ/dτ`. Coordinate definitions alone do not establish the geometric dictionary. The effective endpoint distance is the actual scalar integral `terminalDistance`, not an assumed asymptotic substitute.

## Coverage map

| Selected V8 target | Lean anchors | Inputs and certified scope |
| --- | --- | --- |
| `prop:ham`, `eq:ham`, `eq:balance`, `eq:general-div` | [Canonical.lean](AffineQuadric/Canonical.lean): `hamiltonian_partial_p`, `hamiltonian_partial_q`, `momentum_square_balance` | **D:** scalar Hamiltonian and canonical vector field. **H:** p≠0 for the p-partial; the displayed canonical p-ODE and nonzero momentum for the differential balance. **R:** the state partial derivatives and `(p²)'=8uV²`. **E:** geometric/Legendre coordinate dictionary and equivalence with the full geometric equations. These identities alone construct no trajectory. |
| `prop:weighted-block`, `eq:weighted-factors`, `eq:weighted-terminal` | [Weighted.lean](AffineQuadric/Weighted.lean): `weighted_vertical_identity`, `weighted_horizontal_identity`, `weighted_horizontal_product`, `weighted_product`, `collision_scalar_positivity` | **D:** rational representatives V²/p and p/(u+a). **H:** vertical cancellation uses p≠0 and X=u²−a²≠0; horizontal cancellation uses u−a≠0 and u+a≠0; each product has its stated nonzero denominator. Terminal positivity uses V≠0, a>0, p>0. **R:** rational scalar identities and positive terminal values. **E:** full weighted tensor, analytic horizontal bundles/splitting, reference metric and reconstructed tensor extension. The numerical positivity example does not establish existence of a physical solution. |
| `prop:pairing`, `eq:pairing` | [Pairing.lean](AffineQuadric/Pairing.lean): `radialF_partial_x`, `radialF_partial_y`, `radialPairing_hasDerivAt_zero`, `radialPairing_constant` | **H:** `RadialSolutionOn` supplies V>0, X>0, v>0, actual a,V,u,v derivatives and the scalar ODE; two `RadialVariationOn` inputs supply the linearized equations. Constancy uses an open preconnected interval and two points in it. **R:** the coefficients are genuine state partial derivatives; pairing derivative is zero and the pairing is constant. **E:** existence of that radial solution, its variations/physical family, and geometric reconstruction are not consequences of conservation. |
| `prop:zero-flux`, `eq:hatODE`, `eq:hatH`, `eq:hatenergy`; `eq:newtonH` | [ScalarMechanical.lean](AffineQuadric/ScalarMechanical.lean): `scalar_to_newtonian`, `hyperbolicScalarEnergy_strictAntiOn`; [MechanicalEnergy.lean](AffineQuadric/MechanicalEnergy.lean): `newtonianEnergy_hasDerivAt`, `zero_flux_energy_constant`, `zero_flux_velocity_constant`; [MechanicalClock.lean](AffineQuadric/MechanicalClock.lean): `hyperbolicEnergy_strictAntiOn` | **H:** positive position and the scalar/Newtonian equations are given as `ScalarMechanicalSolutionOn`/`NewtonianSolutionOn`; K has the indicated derivative. For the hyperbolic profile, the regular inverse clock is given. **R:** the f→Z=f^(3/4), U=3u f^(−1/4) scalar transformation; the energy law with arbitrary real β; strict decrease for β>0 on an open preconnected time interval; zero-flux free motion, constant energy/velocity and explicit affine solutions. **E:** construction of the mechanical inverse clock and the full canonical/geometric-to-mechanical dictionary; Stenzel reconstruction is not supplied by these scalar statements. |
| `thm:quadratic`, `eq:coefficients`, `eq:obstruction` | [QuadraticDetermining.lean](AffineQuadric/QuadraticDetermining.lean): `quadratic_determining_from_transport`; [QuadraticTemporal.lean](AffineQuadric/QuadraticTemporal.lean): `quadratic_temporal_obstruction`; [QuadraticIntegral.lean](AffineQuadric/QuadraticIntegral.lean): `quadratic_first_integral_coefficients`, `quadratic_first_integral_constant` | **H:** nonempty open preconnected I, `RegularMechanicalClockOn I t`, `SmoothQuadraticOn I A₂ A₁ A₀`, and transport equal to zero for every z>0 and every v above the admissible threshold. **R:** determining equations and temporal obstruction are derived, not assumed in the final theorem; A₂=A₁=0 and A₀ is one constant, hence J is constant even for all velocities. **D:** the transport force is explicitly `newtonianForce 1`; K=`hyperbolicTimeCoefficient t`. **R (Hito10):** QuadraticPositiveBeta.lean transfers the exclusion to every β>0, with the exact physical threshold and force, while preserving these normalized theorems. **E:** the regular clock is still received; see the boundary below. |
| `eq:average`, `eq:Qtransport`, `eq:p-integral` | [CanonicalAverage.lean](AffineQuadric/CanonicalAverage.lean): `canonical_square_integral`, `canonical_endpoint_average_normalization`, `canonical_relative_momentum_terminal`; [CriticalMomentum.lean](AffineQuadric/CriticalMomentum.lean): `criticalMomentum_formula`, `critical_transport_terminal` | **H:** β,κ>0; `CanonicalMomentumOn` gives continuity on [0,T], u(0)=p(0)=0, p>0 on (0,T] and the canonical p-equation; R=u/(3βs) at positive times. Terminal derivative additionally uses S<T and the stated comparison/transport data. **R:** p² equals its actual integral, the physical-weight average equals normalized p², critical scalar formulas and the total terminal derivative/sign are proved under these data. The average normalization can thus be discharged by these results; it is not universally assumed. **E:** construction of the global regular physical family and its strict comparison remain separate. |
| `prop:endpoint-bounds`, `eq:terminal-bounds`, `eq:radius-bound`, `eq:hyperbolic-lower` | [WeightedTransport.lean](AffineQuadric/WeightedTransport.lean): `transportAverage_bounds`, `transportAverage_strictAntiOn`; [QuantitativeEndpoint.lean](AffineQuadric/QuantitativeEndpoint.lean): `quantitative_endpoint_bounds`, `physical_weight_endpoint_bounds`; [RadialLength.lean](AffineQuadric/RadialLength.lean): `radialLength_bound`, `radialLength_strict_bound` | **H:** `WeightedTransportOn` includes continuity, strictly decreasing R, nonnegative weight and positive weight away from zero. Endpoint bounds use S>0, C>1, positive terminal constants, R(0)=1/C, the stated average/momentum normalization, endpoint profile R(S)=coth(3S)−1/(3S), contact, and `RadialLengthData` (u(0)=0, continuous u,v, v≥0 and u'=v in the interior). The physical-weight version also receives R=u/(As) and κ,A>0. **R:** average inequalities, radius bound, terminal momentum/acceleration bounds and the actual integral length estimate follow from these hypotheses. **E:** existence of a finite physical endpoint and strict ordering/comparison for its global family are not proved here. |
| `prop:transverse` and its continuation/uniqueness argument; `eq:transverse-derivatives` | [CanonicalLocalExistence.lean](AffineQuadric/CanonicalLocalExistence.lean): `canonical_smooth_extension_exists`; [CanonicalIncoming.lean](AffineQuadric/CanonicalIncoming.lean): `canonical_continuation_exists`, `canonical_incoming_match`, `canonical_smooth_extension_unique`; [ODETerminalMatching.lean](AffineQuadric/ODETerminalMatching.lean): `autonomous_terminal_deriv`, `autonomous_terminal_match` | **H:** `CanonicalTerminalData` and `IncomingCanonicalTrajectory`, detailed below. **R:** local solution constructed, C∞ established, pbar>0 on a smaller open interval through S, canonical interface constructed, local uniqueness, and equality with the given incoming q,p on an explicit left interval. The terminal one-sided derivative is proved before applying uniqueness. **E:** global physical incoming-trajectory existence and analytic solution regularity are not supplied by this local theorem. |
| `eq:endprofile`, `eq:moving-barrier`, scalar part of `eq:length-scales`; differential fold in `prop:transverse` | [TransverseTaylor.lean](AffineQuadric/TransverseTaylor.lean), [TransverseRemainders.lean](AffineQuadric/TransverseRemainders.lean); [CanonicalContinuationResults.lean](AffineQuadric/CanonicalContinuationResults.lean): `canonicalContinuation_fold`, `canonicalContinuation_crossing`, `canonicalContinuation_taylor`, `canonicalContinuation_curvature_remainder` | **H:** `LocalTransverseSolutionOn` on an open neighborhood is sufficient for the older scalar results; it is now an **R**, constructed from terminal data and an incoming canonical trajectory by Hito7. **R:** q'(S)=0, q''(S)=−2η<0, nonzero phase velocity, crossing of X, finite-order Taylor remainders, effective-distance and scalar radial length/curvature errors. **E:** full symplectic/Lagrangian or horizontal geometric reconstruction and the complete endpoint theorem are not claimed. |
| `prop:weighted-block` scalar convergent profile, `eq:distance-inverse`, `eq:Puiseux` | [AnalyticDistanceFactor.lean](AffineQuadric/AnalyticDistanceFactor.lean): `transverse_analytic_distance_factor`; [EffectiveDistanceChart.lean](AffineQuadric/EffectiveDistanceChart.lean): `transverse_analyticDistanceChart_exists`, `independentDistance_identity`, `independentDistance_inverse`; [ConvergentCollisionProfiles.lean](AffineQuadric/ConvergentCollisionProfiles.lean): `transverse_convergent_profiles` | **H:** the canonical local solution, `AnalyticAt ℝ q S`; for X and the combined theorem, also `AnalyticAt ℝ a S`. **R:** analytic factor F of the actual distance integral, analytic regular coordinate/inverse D, positive independent r with ρ(s(r))=r and the inverse identity, convergence of U and Xtilde in z=r^(2/3), exact V8 coefficients and remainders. Neither F nor D is assumed by the final theorem. **E:** analyticity of the solution constructed in Hito7 remains an additional unproved input; C∞ alone does not discharge it. Geodesic interpretation of the scalar distance needs reconstruction. |
| `eq:curvature`, radial-vertical part of `thm:endpoint` | [CollisionRadialCurvature.lean](AffineQuadric/CollisionRadialCurvature.lean): `radialScalarCurvature_eq`; [TransverseRemainders.lean](AffineQuadric/TransverseRemainders.lean): `transverse_curvature_remainders`; [ConvergentCollisionProfiles.lean](AffineQuadric/ConvergentCollisionProfiles.lean): `transverse_curvature_r_remainder` | **D:** λ=√w, radialDerivative=−(d/ds)/λ and Kscalar=−Dρ(Dρλ)/λ. **H:** smooth w and w>0 for the differential identity; canonical transverse data for the endpoint errors; the constructed analytic chart for the independent-r version. **R:** Kscalar=(w'²−ww'')/(2w³), leading 2/9 and the O(ρ^(−4/3)) error, including independent r under the analytic hypotheses. **E:** identification with sectional curvature of a reconstructed Riemannian metric, horizontal geometry and the full nonextension conclusion. |

## Two boundaries that must remain visible

**Mechanical normalization, transferred in Hito10.** The energy law already retains arbitrary real β and strict decrease covers β>0. The preserved quadraticTransport uses newtonianForce 1 with generic K; beta_quadratic_first_integral_coefficients and beta_quadratic_first_integral_constant now instantiate it at Kβ=β²h(t(τ))². quadratic_scaled_force and quadratic_scaled_threshold prove the exact physical force and velocity domain. The determining equations, integrated coefficients and temporal obstruction are derived from half-line transport; β² is cancelled using β>0. Thus the positive-β transfer of the quadratic clause of prop:zero-flux is delivered under the given regular clock and transport PDE. It does not construct the inverse clock or a flow, prove general equivalence with invariance along all flows, or cover β=0 with this exclusion.

`RegularMechanicalClockOn I t` supplies t>0, differentiability and T(t(τ))=τ for T(t)=(sinh(t)cosh(t)−t)/2. Its derivative and positivity consequences are proved; existence of this regular inverse clock is not constructed. This received clock must not be confused with the effective-distance inverse D, which is constructed.

**Smooth continuation versus analytic continuation.** `CanonicalTerminalData J S pS a V` receives J open, S∈J, S>0, a,V C∞ on J, a(S)>0, V(S)>0, a'(S)>0, pS>0. `IncomingCanonicalTrajectory` receives ε0>0, the two canonical equations on (S−ε0,S), and left limits q→a(S), p→pS. It does not assume endpoint values or differentiability of the original functions. `canonical_continuation_exists` constructs an open I⊆J through S and a C∞ canonical extension with those terminal values; it proves coincidence on (S−ε,S), ε>0, ε≤ε0. No local solution across S is an input of that theorem.

`canonicalLiftedField_analytic_terminal` proves analyticity of G when a,V are analytic in S. It does not prove analyticity of its integral curve. The analytic-ODE regularity goal remains unproved in the delivered corpus. Consequently the Hito7 smooth continuation is not automatically an input satisfying the additional analytic hypotheses of Hito6C.

For the analytic branch, c=(2/3)√η and d=c^(−2/3)=(3/(2√η))^(2/3) are certified. With positive independent r:

```
q(s(r)) = a(S) − (3/2)^(4/3)η^(1/3) r^(4/3) + O(r²),
X(s(r)) = 2a(S)a'(S)(3/(2√η))^(2/3) r^(2/3) + O(r^(4/3)),
Kscalar(s(r)) = 2/(9r²) + O(r^(−4/3)).
```

AnalyticAt of the profiles in z supplies convergence, not merely finite-order errors. The scalar integral factor and inverse are proved for the actual effective distance, on its positive branch. These are conditional mathematical theorems, not assertions that analytic solution construction or Riemannian reconstruction has been completed.

## Reproduction and provenance

Lean 4.24.0, Mathlib f897ebcf72cd16f89ab4577d0c826cd14afaafc7 and all nine package revisions are fixed. REPRODUCIBLE_SOURCES_SHA256.txt covers all 56 active Lean files and the three configurations. Those 59 files are byte-identical to the accepted Hito10 corpus. The independent accepted declaration inventory is tools/expected-declarations.txt (614 names).

See [docs/VALIDATION.md](docs/VALIDATION.md) for the accepted original and clean-run evidence, the limitations of that evidence, and fresh reproduction instructions. Historical iteration dossiers and execution environments are not required for compiling this public source tree.

## Hito9: two-dimensional model, not ambient identification

This accepted model remains unchanged in Hito10; its analytic and ambient
geometric dependencies below remain open.

The model's coordinates are `x : Fin 2 → ℝ`, with `s=x 0`, `θ=x 1` and standard coordinate vectors `model2DBasis`. `model2DPartial` is the real derivative at zero along `x+t eᵢ`. Thus the derivative terms below are derivatives of functions, not independently assigned symbols.

| V8 reference and status | New Lean anchors | H → R, with external boundary |
| --- | --- | --- |
| `prop:transverse`, `prop:weighted-block`, `eq:Puiseux`: A **DEFERRED** | No new analytic-continuation theorem; see the boundary discussion above | The one additional route inspected uses complex states in real-time Picard–Lindelöf. It supplies no holomorphic time extension. Analyticity of the constructed solution and its unconditional link to the convergent profiles remain unproved. All previous analytic hypotheses remain explicit. |
| Auxiliary surface suggested by `eq:radialmetric`: B0 metric/connection | [Model2DMetric.lean](AffineQuadric/Model2DMetric.lean): `model2DMetric_bilinear`, `model2DMetric_positive`, `model2DMetric_basis`, `model2DMetric_inverse`, `model2DMetricCoeff_partial`, `model2DChristoffel_eq`, `model2DChristoffel_torsion_free`, `model2DChristoffel_metric_compatible` | **D:** gₓ(u,v)=w(s)(u₀v₀+u₁v₁); inverse coefficient matrix; Christoffel from the standard inverse-metric/partial-derivative formula. **H:** w differentiable at s for coefficients; w(s)>0 for positivity, w(s)≠0 for inverse/compatibility. **R:** symmetric bilinearity, positive definiteness, actual coefficient derivatives, Γ⁰₀₀=b, Γ⁰₁₁=−b, Γ¹₀₁=Γ¹₁₀=b, all others zero, b=w'/(2w); zero coordinate torsion and metric compatibility. **E:** no ambient metric/immersion is constructed. |
| `eq:curvature` auxiliary 2D calculation | [Model2DCurvature.lean](AffineQuadric/Model2DCurvature.lean): `model2DB_hasDerivAt`, `model2DChristoffel_partial`, `model2DRiemann_radial_vertical`, `model2DGram_positive`, `model2DSectional_eq_quotient`, `model2DSectional_eq_radialScalarCurvature` | **H:** open I, w C∞ on I, s∈I, w(s)>0. **D:** coordinate Riemann formula from the connection and its real partials, with R(X,Y)Z=∇X∇Y Z−∇Y∇X Z−∇[X,Y]Z; sectional normalization by the actual metric Gram determinant. **R:** R(∂s,∂θ)∂θ=−b'∂s; Gram=w²>0; the model's sectional curvature equals −b'/w=(w'²−ww'')/(2w³)=Kscalar. **E:** equality with the six-dimensional paper metric has not been proved or assumed. |
| `eq:curvature`, applied to the constructed continuation in the **model** | [Model2DCanonical.lean](AffineQuadric/Model2DCanonical.lean): `canonicalContinuation_model2D_near`, `canonicalContinuation_model2D_radial_limit`, `canonicalContinuation_model2D_curvature_remainder`, `canonical_model2D_continuation_exists` | **H:** `CanonicalTerminalData` and `IncomingCanonicalTrajectory` as above. **R:** a matching C∞ continuation exists; for w=qbar'/2 the model is positive sufficiently close on the incoming side, its curvature equals Kscalar, ρ²Kmodel→2/9 and Kmodel=2/(9ρ²)+O(ρ^(−4/3)). θ can be any function of δ, because the coefficients are θ-independent. The distance here is the existing scalar integral along the radial coordinate. Neither solution analyticity nor a curvature identity is assumed. **E:** ambient radial-vertical identification, horizontal geometry, global physical family and the full Riemannian nonextension conclusion. |

B0 establishes a genuine metric/connection/curvature calculation in a local coordinate surface. It does not establish B1: no equality between its sectional curvature and that of the six-dimensional reconstructed metric is delivered. The scalar integral has a radial-length meaning in this model (radial speed has norm √w); a full Riemannian distance/ambient reconstruction is not claimed. The old scalar-only row above still describes the preserved baseline; the new bridge is exactly this model calculation.

## Hito10: physical positive-beta quadratic exclusion

New module: [QuadraticPositiveBeta.lean](AffineQuadric/QuadraticPositiveBeta.lean).

| V8 target | New anchors | H → R; external boundary |
| --- | --- | --- |
| `prop:zero-flux`, `eq:hatODE`, `eq:hatH` | betaTimeCoefficient_hasDerivAt, betaTimeCoefficient_pos, quadratic_scaled_force, quadratic_scaled_threshold, betaQuadraticTransport_eq | **D:** Kβ=β²K and transport by actual time, position and velocity partials of the polynomial candidate. **H:** positive β, given regular clock, K=h(t)²>0 on I. **R:** Kβ positive/differentiable, force −3β²Kz^(−5/3), and exactly v>3β√Kz^(−1/3). The force identity holds for all real parameters; the threshold identity holds for every z, and the final domain restricts z>0. **E:** construction of the clock/flow and the full geometric dictionary. |
| Positive-beta exclusion clause of `prop:zero-flux`; generic stages of `thm:quadratic` | beta_quadratic_determining_from_transport, beta_quadratic_obstruction_cancel, beta_quadratic_first_integral_coefficients, beta_quadratic_first_integral_constant | **H:** β>0, I nonempty open preconnected, RegularMechanicalClockOn I t, SmoothQuadraticOn I A₂ A₁ A₀, physical transport zero only on the admissible velocity half-line for each τ∈I,z>0. **R:** determining equations derived, generic integration/separation reused at Kβ, β² cancelled from the derived obstruction, original temporal theorem applied. A₂=A₁=0 and A₀=D for one D on all I×(0,∞); the candidate equals D for all real velocities. No determining/temporal conclusion is an input of the final theorem. **E:** inverse-clock existence, physical flow/dictionary; no extension of this exclusion to β=0. |

betaTimeCoefficient_one verifies the direct specialization β=1. All accepted
normalized proofs are preserved. No fractional beta powers or coordinate
rescaling are introduced. This closes the previously explicit normalization
gap, with the regular-clock and transport hypotheses retained. It makes no
progress on analytic solution regularity or ambient curvature identification.
The Hito10 original build and clean rebuild by the same executor passed on 30 October 2026: 56 project modules, 377 written theorems and 614 inventoried axiom reports. The current public packaging preserves the 59 accepted source/configuration files exactly. See [validation and reproduction instructions](docs/VALIDATION.md) for the completed clean validation and its evidence.

Historical source comments are preserved with the accepted bytes. This scope map uses the accepted V8 and actual declaration signatures. Package status does not certify all of Propositions 6.2/6.4, tensor reconstruction, global branch classification, or the whole article.

## Complete active Lean file inventory

The file-level table is a navigation aid; exact input hypotheses are stated in the Lean signatures and the theorem map above. Counts refer to explicitly written `theorem` commands. Audit and the root contain no new mathematical theorems.

| Lean file | Written theorems | Project imports |
| --- | ---: | --- |
| [AffineQuadric.lean](AffineQuadric.lean) | 0 | `AffineQuadric.Canonical`, `AffineQuadric.Weighted`, `AffineQuadric.Audit` |
| [AffineQuadric/AnalyticCollisionFactor.lean](AffineQuadric/AnalyticCollisionFactor.lean) | 7 | `AffineQuadric.TransverseRadialLaw` |
| [AffineQuadric/AnalyticDistanceFactor.lean](AffineQuadric/AnalyticDistanceFactor.lean) | 3 | `AffineQuadric.AnalyticDistanceSeries` |
| [AffineQuadric/AnalyticDistanceInverse.lean](AffineQuadric/AnalyticDistanceInverse.lean) | 4 | `AffineQuadric.AnalyticDistanceFactor` |
| [AffineQuadric/AnalyticDistanceSeries.lean](AffineQuadric/AnalyticDistanceSeries.lean) | 3 | `AffineQuadric.AnalyticCollisionFactor` |
| [AffineQuadric/AnalyticProfileTaylor.lean](AffineQuadric/AnalyticProfileTaylor.lean) | 7 | `AffineQuadric.EffectiveDistanceChart`, `AffineQuadric.TransverseRemainders` |
| [AffineQuadric/Audit.lean](AffineQuadric/Audit.lean) | 0 | `AffineQuadric.QuadraticPositiveBeta`, `AffineQuadric.Model2DCanonical`, `AffineQuadric.Canonical`, `AffineQuadric.Weighted`, `AffineQuadric.Pairing`, `AffineQuadric.Profiles`, `AffineQuadric.Examples`, `AffineQuadric.MechanicalProfile`, `AffineQuadric.MechanicalEnergy`, `AffineQuadric.MechanicalClock`, `AffineQuadric.ScalarMechanical`, `AffineQuadric.RadiusBounds`, `AffineQuadric.TerminalBounds`, `AffineQuadric.WeightedTransport`, `AffineQuadric.RadialLength`, `AffineQuadric.QuantitativeEndpoint`, `AffineQuadric.TerminalTransport`, `AffineQuadric.CriticalMomentum`, `AffineQuadric.CanonicalAverage`, `AffineQuadric.QuadraticDetermining`, `AffineQuadric.QuadraticTemporal`, `AffineQuadric.QuadraticIntegration`, `AffineQuadric.QuadraticPowers`, `AffineQuadric.QuadraticIntegral`, `AffineQuadric.TransverseCollision`, `AffineQuadric.EndpointRates`, `AffineQuadric.TransverseProfile`, `AffineQuadric.CollisionDistance`, `AffineQuadric.CollisionRadialCurvature`, `AffineQuadric.TransverseRadialLaw`, `AffineQuadric.LocalTaylorRemainder`, `AffineQuadric.TransverseTaylor`, `AffineQuadric.RemainderAlgebra`, `AffineQuadric.SimpleZeroRemainders`, `AffineQuadric.DistanceScaleBounds`, `AffineQuadric.CollisionCurvatureRemainder`, `AffineQuadric.CollisionLengthRemainder`, `AffineQuadric.TransverseRemainders`, `AffineQuadric.AnalyticCollisionFactor`, `AffineQuadric.AnalyticDistanceSeries`, `AffineQuadric.AnalyticDistanceFactor`, `AffineQuadric.AnalyticDistanceInverse`, `AffineQuadric.EffectiveDistanceChart`, `AffineQuadric.AnalyticProfileTaylor`, `AffineQuadric.PuiseuxCoefficients`, `AffineQuadric.ConvergentCollisionProfiles`, `AffineQuadric.CanonicalLocalField`, `AffineQuadric.CanonicalLocalExistence`, `AffineQuadric.ODETerminalMatching`, `AffineQuadric.CanonicalIncoming`, `AffineQuadric.CanonicalContinuationResults`, `AffineQuadric.CanonicalFieldAnalytic` |
| [AffineQuadric/Canonical.lean](AffineQuadric/Canonical.lean) | 3 | Mathlib / no project imports |
| [AffineQuadric/CanonicalAverage.lean](AffineQuadric/CanonicalAverage.lean) | 8 | `AffineQuadric.CriticalMomentum` |
| [AffineQuadric/CanonicalContinuationResults.lean](AffineQuadric/CanonicalContinuationResults.lean) | 6 | `AffineQuadric.CanonicalIncoming` |
| [AffineQuadric/CanonicalFieldAnalytic.lean](AffineQuadric/CanonicalFieldAnalytic.lean) | 2 | `AffineQuadric.CanonicalLocalField`, `AffineQuadric.AnalyticCollisionFactor` |
| [AffineQuadric/CanonicalIncoming.lean](AffineQuadric/CanonicalIncoming.lean) | 6 | `AffineQuadric.CanonicalLocalExistence`, `AffineQuadric.ODETerminalMatching` |
| [AffineQuadric/CanonicalLocalExistence.lean](AffineQuadric/CanonicalLocalExistence.lean) | 3 | `AffineQuadric.CanonicalLocalField` |
| [AffineQuadric/CanonicalLocalField.lean](AffineQuadric/CanonicalLocalField.lean) | 4 | `AffineQuadric.TransverseRemainders` |
| [AffineQuadric/CollisionCurvatureRemainder.lean](AffineQuadric/CollisionCurvatureRemainder.lean) | 5 | `AffineQuadric.DistanceScaleBounds` |
| [AffineQuadric/CollisionDistance.lean](AffineQuadric/CollisionDistance.lean) | 6 | `AffineQuadric.EndpointRates` |
| [AffineQuadric/CollisionLengthRemainder.lean](AffineQuadric/CollisionLengthRemainder.lean) | 5 | `AffineQuadric.DistanceScaleBounds` |
| [AffineQuadric/CollisionRadialCurvature.lean](AffineQuadric/CollisionRadialCurvature.lean) | 8 | `AffineQuadric.CollisionDistance` |
| [AffineQuadric/ConvergentCollisionProfiles.lean](AffineQuadric/ConvergentCollisionProfiles.lean) | 9 | `AffineQuadric.AnalyticProfileTaylor`, `AffineQuadric.PuiseuxCoefficients` |
| [AffineQuadric/CriticalMomentum.lean](AffineQuadric/CriticalMomentum.lean) | 20 | `AffineQuadric.TerminalTransport` |
| [AffineQuadric/DistanceScaleBounds.lean](AffineQuadric/DistanceScaleBounds.lean) | 5 | `AffineQuadric.SimpleZeroRemainders` |
| [AffineQuadric/EffectiveDistanceChart.lean](AffineQuadric/EffectiveDistanceChart.lean) | 10 | `AffineQuadric.AnalyticDistanceInverse` |
| [AffineQuadric/EndpointRates.lean](AffineQuadric/EndpointRates.lean) | 5 | `AffineQuadric.QuadraticIntegration` |
| [AffineQuadric/Examples.lean](AffineQuadric/Examples.lean) | 4 | `AffineQuadric.Pairing` |
| [AffineQuadric/LocalTaylorRemainder.lean](AffineQuadric/LocalTaylorRemainder.lean) | 4 | `AffineQuadric.TransverseRadialLaw` |
| [AffineQuadric/MechanicalClock.lean](AffineQuadric/MechanicalClock.lean) | 9 | `AffineQuadric.MechanicalEnergy` |
| [AffineQuadric/MechanicalEnergy.lean](AffineQuadric/MechanicalEnergy.lean) | 7 | `AffineQuadric.MechanicalProfile` |
| [AffineQuadric/MechanicalProfile.lean](AffineQuadric/MechanicalProfile.lean) | 11 | Mathlib / no project imports |
| [AffineQuadric/Model2DCanonical.lean](AffineQuadric/Model2DCanonical.lean) | 4 | `AffineQuadric.Model2DCurvature`, `AffineQuadric.CanonicalContinuationResults` |
| [AffineQuadric/Model2DCurvature.lean](AffineQuadric/Model2DCurvature.lean) | 10 | `AffineQuadric.Model2DMetric` |
| [AffineQuadric/Model2DMetric.lean](AffineQuadric/Model2DMetric.lean) | 9 | `AffineQuadric.CollisionRadialCurvature` |
| [AffineQuadric/ODETerminalMatching.lean](AffineQuadric/ODETerminalMatching.lean) | 6 | `AffineQuadric.CanonicalLocalField` |
| [AffineQuadric/Pairing.lean](AffineQuadric/Pairing.lean) | 12 | Mathlib / no project imports |
| [AffineQuadric/Profiles.lean](AffineQuadric/Profiles.lean) | 12 | `AffineQuadric.Pairing` |
| [AffineQuadric/PuiseuxCoefficients.lean](AffineQuadric/PuiseuxCoefficients.lean) | 4 | `AffineQuadric.AnalyticCollisionFactor` |
| [AffineQuadric/QuadraticDetermining.lean](AffineQuadric/QuadraticDetermining.lean) | 7 | `AffineQuadric.MechanicalClock` |
| [AffineQuadric/QuadraticIntegral.lean](AffineQuadric/QuadraticIntegral.lean) | 3 | `AffineQuadric.QuadraticIntegration`, `AffineQuadric.QuadraticPowers` |
| [AffineQuadric/QuadraticIntegration.lean](AffineQuadric/QuadraticIntegration.lean) | 11 | `AffineQuadric.QuadraticDetermining`, `AffineQuadric.QuadraticTemporal` |
| [AffineQuadric/QuadraticPositiveBeta.lean](AffineQuadric/QuadraticPositiveBeta.lean) | 10 | `AffineQuadric.QuadraticIntegral` |
| [AffineQuadric/QuadraticPowers.lean](AffineQuadric/QuadraticPowers.lean) | 4 | Mathlib / no project imports |
| [AffineQuadric/QuadraticTemporal.lean](AffineQuadric/QuadraticTemporal.lean) | 15 | `AffineQuadric.MechanicalClock`, `AffineQuadric.RadiusBounds` |
| [AffineQuadric/QuantitativeEndpoint.lean](AffineQuadric/QuantitativeEndpoint.lean) | 3 | `AffineQuadric.RadiusBounds`, `AffineQuadric.TerminalBounds`, `AffineQuadric.WeightedTransport`, `AffineQuadric.RadialLength`, `AffineQuadric.Profiles` |
| [AffineQuadric/RadialLength.lean](AffineQuadric/RadialLength.lean) | 5 | Mathlib / no project imports |
| [AffineQuadric/RadiusBounds.lean](AffineQuadric/RadiusBounds.lean) | 14 | `AffineQuadric.MechanicalProfile` |
| [AffineQuadric/RemainderAlgebra.lean](AffineQuadric/RemainderAlgebra.lean) | 13 | `AffineQuadric.LocalTaylorRemainder` |
| [AffineQuadric/ScalarMechanical.lean](AffineQuadric/ScalarMechanical.lean) | 9 | `AffineQuadric.MechanicalClock` |
| [AffineQuadric/SimpleZeroRemainders.lean](AffineQuadric/SimpleZeroRemainders.lean) | 9 | `AffineQuadric.RemainderAlgebra` |
| [AffineQuadric/TerminalBounds.lean](AffineQuadric/TerminalBounds.lean) | 7 | `AffineQuadric.Canonical` |
| [AffineQuadric/TerminalTransport.lean](AffineQuadric/TerminalTransport.lean) | 5 | `AffineQuadric.QuantitativeEndpoint` |
| [AffineQuadric/TransverseCollision.lean](AffineQuadric/TransverseCollision.lean) | 7 | `AffineQuadric.Canonical`, `AffineQuadric.QuadraticIntegration` |
| [AffineQuadric/TransverseProfile.lean](AffineQuadric/TransverseProfile.lean) | 4 | `AffineQuadric.TransverseCollision`, `AffineQuadric.EndpointRates` |
| [AffineQuadric/TransverseRadialLaw.lean](AffineQuadric/TransverseRadialLaw.lean) | 3 | `AffineQuadric.TransverseProfile`, `AffineQuadric.CollisionRadialCurvature` |
| [AffineQuadric/TransverseRemainders.lean](AffineQuadric/TransverseRemainders.lean) | 6 | `AffineQuadric.TransverseTaylor`, `AffineQuadric.CollisionCurvatureRemainder`, `AffineQuadric.CollisionLengthRemainder` |
| [AffineQuadric/TransverseTaylor.lean](AffineQuadric/TransverseTaylor.lean) | 5 | `AffineQuadric.LocalTaylorRemainder` |
| [AffineQuadric/Weighted.lean](AffineQuadric/Weighted.lean) | 11 | Mathlib / no project imports |
| [AffineQuadric/WeightedTransport.lean](AffineQuadric/WeightedTransport.lean) | 5 | Mathlib / no project imports |

## Explicit exclusions

The delivered corpus does not construct the regular inverse mechanical clock,
identify free motion with the Stenzel geometry, prove analyticity of the
constructed C-infinity ODE solution, reconstruct the full 6D/7D/8D tensors, or
identify the model's two-dimensional sectional curvature with the ambient one.
Global construction/classification of the physical family and strict comparison,
the global diffeomorphism S(phi_0) of Corollary 6.3, and the exact critical modes
and sensitivity of Section 7 remain outside this formalization. The scalar
critical-momentum identities in this repository do not close those Section 7
claims. Propositions 4.2, 6.2 and 6.4 are not asserted complete.

These external dependencies are mathematical boundaries of the accepted corpus.
The author-confirmed repository is [https://github.com/adrianht85/affine_quadric_lean](https://github.com/adrianht85/affine_quadric_lean)
and the author ORCID is [https://orcid.org/0009-0003-1452-1632](https://orcid.org/0009-0003-1452-1632).
The paper DOI `10.5281/zenodo.23956688` is reserved in a Zenodo draft;
the paper is not yet published and its DOI has not yet been definitively
registered. This is the paper DOI, not the software DOI. The software DOI,
software release URL and software release/archival publication dates remain pending metadata.
The repository was made public on 5 November 2026. The first software release
and archiving of the software in Zenodo remain pending.
This documentary preparation does not publish a release or a Zenodo record.
