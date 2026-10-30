import AffineQuadric.AnalyticDistanceFactor
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv

/-! The regular distance coordinate and its analytic inverse. The inverse
function theorem constructs the local homeomorphism; it is not an input. -/
noncomputable section
open Set Filter
open scoped Topology
namespace AffineQuadric

def regularDistanceCoordinate (F : ℝ → ℝ) (δ : ℝ) : ℝ := δ * (F δ) ^ (2 / 3 : ℝ)

theorem regularDistanceCoordinate_analytic {F : ℝ → ℝ} (hF : AnalyticAt ℝ F 0)
    (hc : 0 < F 0) : AnalyticAt ℝ (regularDistanceCoordinate F) 0 :=
  analyticAt_id.mul (analyticAt_positive_rpow hF hc _)

theorem regularDistanceCoordinate_deriv {F : ℝ → ℝ} (hF : AnalyticAt ℝ F 0)
    (hc : 0 < F 0) :
    HasDerivAt (regularDistanceCoordinate F) ((F 0) ^ (2 / 3 : ℝ)) 0 := by
  have hp := (analyticAt_positive_rpow hF hc (2 / 3 : ℝ)).differentiableAt.hasDerivAt
  simpa [regularDistanceCoordinate] using (hasDerivAt_id (0 : ℝ)).mul hp

theorem analytic_local_inverse_zero {Z : ℝ → ℝ} {k : ℝ} (hZ : AnalyticAt ℝ Z 0)
    (h0 : Z 0 = 0) (hd : HasDerivAt Z k 0) (hk : k ≠ 0) :
    ∃ D : ℝ → ℝ, AnalyticAt ℝ D 0 ∧ D 0 = 0 ∧ HasDerivAt D k⁻¹ 0 ∧
      (∀ᶠ z in 𝓝 (0 : ℝ), Z (D z) = z) ∧ (∀ᶠ δ in 𝓝 (0 : ℝ), D (Z δ) = δ) := by
  have hs : HasStrictDerivAt Z k 0 := by
    obtain ⟨p, hp⟩ := hZ
    convert hp.hasStrictDerivAt using 1
    exact hd.deriv.symm.trans hp.deriv
  let hf := hs.hasStrictFDerivAt_equiv hk
  let e := hf.toOpenPartialHomeomorph Z
  have he : AnalyticAt ℝ e 0 := hZ
  have ha := e.analyticAt_symm' hf.mem_toOpenPartialHomeomorph_source he
    hf.hasFDerivAt.fderiv
  refine ⟨hf.localInverse Z _ _, ?_, ?_, ?_, ?_, hf.eventually_left_inverse⟩
  · simpa [e, ← hf.localInverse_def, h0] using ha
  · simpa [h0] using hf.localInverse_apply_image
  · simpa [HasStrictDerivAt.localInverse, hf, h0] using (hs.to_localInverse hk).hasDerivAt
  · simpa [h0] using hf.eventually_right_inverse

theorem analytic_distance_inverse {F : ℝ → ℝ} (hF : AnalyticAt ℝ F 0)
    (hc : 0 < F 0) :
    ∃ D : ℝ → ℝ, AnalyticAt ℝ D 0 ∧ D 0 = 0 ∧
      HasDerivAt D ((F 0) ^ (2 / 3 : ℝ))⁻¹ 0 ∧
      (∀ᶠ z in 𝓝 (0 : ℝ), regularDistanceCoordinate F (D z) = z) ∧
      (∀ᶠ δ in 𝓝 (0 : ℝ), D (regularDistanceCoordinate F δ) = δ) := by
  exact analytic_local_inverse_zero (regularDistanceCoordinate_analytic hF hc)
    (by simp [regularDistanceCoordinate]) (regularDistanceCoordinate_deriv hF hc)
    (Real.rpow_pos_of_pos hc _).ne'

end AffineQuadric
