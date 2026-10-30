import AffineQuadric.TransverseProfile
import AffineQuadric.CollisionRadialCurvature

/-! The scalar radial law is linked to the given local canonical solution.
Neither the simple zero nor the distance rate is a hypothesis of this result. -/
noncomputable section
open Set Filter
open scoped Topology
namespace AffineQuadric

theorem transverse_simple_radial_zero {I : Set ℝ} (hI : IsOpen I)
    {S : ℝ} {a V q p : ℝ → ℝ} (h : LocalTransverseSolutionOn I S a V q p) :
    SimpleRadialZeroOn I S (collisionRadialW q) (collisionEta a V p S) :=
  ⟨h.S_mem, collisionRadialW_smooth hI h, (collisionRadialW_terminal hI h).1,
    (collisionRadialW_terminal hI h).2.1, collisionEta_pos h⟩

theorem transverse_distance_law {I : Set ℝ} (hI : IsOpen I)
    {S : ℝ} {a V q p : ℝ → ℝ} (h : LocalTransverseSolutionOn I S a V q p) :
    (∀ᶠ δ in 𝓝[>] (0 : ℝ), 0 < terminalDistance (collisionRadialW q) S (S - δ)) ∧
    Tendsto (fun δ => terminalDistance (collisionRadialW q) S (S - δ) / δ ^ (3 / 2 : ℝ))
      (𝓝[>] (0 : ℝ)) (𝓝 ((2 / 3 : ℝ) * Real.sqrt (collisionEta a V p S))) := by
  have hp := transverse_simple_radial_zero hI h
  exact ⟨simple_zero_distance_pos hI hp, simple_zero_distance_rate hI hp⟩

/-- Leading scalar radial singularity for a given local canonical collision.
The identification of Kscalar with sectional curvature of a reconstructed
metric, analytic continuation, big-O remainders and Puiseux are not concluded. -/
theorem transverse_scalar_radial_law {I : Set ℝ} (hI : IsOpen I)
    {S : ℝ} {a V q p : ℝ → ℝ} (h : LocalTransverseSolutionOn I S a V q p) :
    Tendsto (fun δ => terminalDistance (collisionRadialW q) S (S - δ) ^ 2 *
      radialScalarCurvature (collisionRadialW q) (S - δ))
      (𝓝[>] (0 : ℝ)) (𝓝 (2 / 9 : ℝ)) ∧
    Tendsto (fun δ => radialScalarCurvature (collisionRadialW q) (S - δ))
      (𝓝[>] (0 : ℝ)) atTop := by
  have hp := transverse_simple_radial_zero hI h
  exact ⟨simple_zero_curvature_coefficient hI hp, simple_zero_curvature_tendsto_atTop hI hp⟩

end AffineQuadric
