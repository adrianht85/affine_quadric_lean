import AffineQuadric.TransverseTaylor
import AffineQuadric.CollisionCurvatureRemainder
import AffineQuadric.CollisionLengthRemainder

/-! Final 6B results linked to the unchanged local canonical solution. Every
distance estimate is parameterized by delta; no analytic inversion is claimed. -/
noncomputable section
open Set Filter Asymptotics
open scoped Topology
namespace AffineQuadric

theorem transverse_w_remainders {I : Set ℝ} (hI : IsOpen I) {S : ℝ} {a V q p : ℝ → ℝ}
    (h : LocalTransverseSolutionOn I S a V q p) :
    ((fun δ => collisionRadialW q (S - δ) - collisionEta a V p S * δ)
      =O[𝓝[>] (0 : ℝ)] (fun δ => δ ^ 2)) ∧
    ((fun δ => deriv (collisionRadialW q) (S - δ) + collisionEta a V p S)
      =O[𝓝[>] (0 : ℝ)] (fun δ => δ)) ∧
    ((fun δ => deriv (deriv (collisionRadialW q)) (S - δ))
      =O[𝓝[>] (0 : ℝ)] (fun _ => (1 : ℝ))) := by
  have hz := transverse_simple_radial_zero hI h
  exact ⟨simple_zero_w_bigO hI hz,
    by simpa [FirstOrderAtZero] using simple_zero_wprime_firstOrder hI hz,
    simple_zero_wsecond_bounded hI hz⟩

theorem transverse_lambda_remainder {I : Set ℝ} (hI : IsOpen I) {S : ℝ} {a V q p : ℝ → ℝ}
    (h : LocalTransverseSolutionOn I S a V q p) :
    (fun δ => radialLambda (collisionRadialW q) (S - δ) - Real.sqrt (collisionEta a V p S) * δ ^ (1 / 2 : ℝ))
      =O[𝓝[>] (0 : ℝ)] (fun δ => δ ^ (3 / 2 : ℝ)) :=
  simple_zero_lambda_bigO hI (transverse_simple_radial_zero hI h)

theorem transverse_distance_remainder {I : Set ℝ} (hI : IsOpen I) {S : ℝ} {a V q p : ℝ → ℝ}
    (h : LocalTransverseSolutionOn I S a V q p) :
    (fun δ => terminalDistance (collisionRadialW q) S (S - δ) -
      distanceLeadingCoefficient (collisionEta a V p S) * δ ^ (3 / 2 : ℝ))
      =O[𝓝[>] (0 : ℝ)] (fun δ => δ ^ (5 / 2 : ℝ)) :=
  simple_zero_distance_bigO hI (transverse_simple_radial_zero hI h)

theorem transverse_distance_comparisons {I : Set ℝ} (hI : IsOpen I) {S : ℝ} {a V q p : ℝ → ℝ}
    (h : LocalTransverseSolutionOn I S a V q p) :
    (∃ L U : ℝ, 0 < L ∧ 0 < U ∧ ∀ᶠ δ in 𝓝[>] (0 : ℝ),
      L * δ ^ (3 / 2 : ℝ) ≤ terminalDistance (collisionRadialW q) S (S - δ) ∧
      terminalDistance (collisionRadialW q) S (S - δ) ≤ U * δ ^ (3 / 2 : ℝ)) ∧
    (∃ A B : ℝ, 0 < A ∧ 0 < B ∧ ∀ᶠ δ in 𝓝[>] (0 : ℝ),
      A * terminalDistance (collisionRadialW q) S (S - δ) ^ (2 / 3 : ℝ) ≤ δ ∧
      δ ≤ B * terminalDistance (collisionRadialW q) S (S - δ) ^ (2 / 3 : ℝ)) :=
  simple_zero_distance_scale_bounds hI (transverse_simple_radial_zero hI h)

theorem transverse_curvature_remainders {I : Set ℝ} (hI : IsOpen I) {S : ℝ} {a V q p : ℝ → ℝ}
    (h : LocalTransverseSolutionOn I S a V q p) :
    ((fun δ => radialScalarCurvature (collisionRadialW q) (S - δ) -
      (1 / (2 * collisionEta a V p S)) * δ ^ (-3 : ℝ))
      =O[𝓝[>] (0 : ℝ)] (fun δ => δ ^ (-2 : ℝ))) ∧
    ((fun δ => radialScalarCurvature (collisionRadialW q) (S - δ) -
      (2 / 9 : ℝ) * terminalDistance (collisionRadialW q) S (S - δ) ^ (-2 : ℝ))
      =O[𝓝[>] (0 : ℝ)] (fun δ => terminalDistance (collisionRadialW q) S (S - δ) ^ (-4 / 3 : ℝ))) := by
  have hz := transverse_simple_radial_zero hI h
  exact ⟨simple_zero_curvature_parameter_bigO hI hz, simple_zero_curvature_distance_bigO hI hz⟩

theorem transverse_length_profile_remainder {I : Set ℝ} (hI : IsOpen I) {S : ℝ} {a V q p : ℝ → ℝ}
    (h : LocalTransverseSolutionOn I S a V q p) :
    Tendsto (fun δ => radialLambda (collisionRadialW q) (S - δ) /
      terminalDistance (collisionRadialW q) S (S - δ) ^ (1 / 3 : ℝ))
      (𝓝[>] (0 : ℝ)) (𝓝 (collisionLengthCoefficient (collisionEta a V p S))) ∧
    ((fun δ => radialLambda (collisionRadialW q) (S - δ) - collisionLengthCoefficient (collisionEta a V p S) *
      terminalDistance (collisionRadialW q) S (S - δ) ^ (1 / 3 : ℝ))
      =O[𝓝[>] (0 : ℝ)] (fun δ => terminalDistance (collisionRadialW q) S (S - δ))) := by
  have hz := transverse_simple_radial_zero hI h
  exact ⟨simple_zero_length_ratio_tendsto hI hz, simple_zero_length_distance_bigO hI hz⟩

end AffineQuadric
