import AffineQuadric.AnalyticCollisionFactor

/-! Exact positive-real coefficients in V8 eq:distance-inverse and eq:Puiseux. -/
noncomputable section
namespace AffineQuadric

def distanceInverseCoefficient (η : ℝ) : ℝ :=
  (((2 / 3 : ℝ) * Real.sqrt η) ^ (2 / 3 : ℝ))⁻¹

theorem distanceInverseCoefficient_pos {η : ℝ} (hη : 0 < η) :
    0 < distanceInverseCoefficient η := by
  dsimp [distanceInverseCoefficient]
  positivity

theorem distanceInverseCoefficient_rpow {η : ℝ} (hη : 0 < η) :
    distanceInverseCoefficient η = ((2 / 3 : ℝ) * Real.sqrt η) ^ (-2 / 3 : ℝ) := by
  simpa only [distanceInverseCoefficient, neg_div] using
    (Real.rpow_neg (by positivity : (0 : ℝ) ≤ (2 / 3) * Real.sqrt η) (2 / 3 : ℝ)).symm

theorem distanceInverseCoefficient_exact {η : ℝ} (hη : 0 < η) :
    distanceInverseCoefficient η = (3 / (2 * Real.sqrt η)) ^ (2 / 3 : ℝ) := by
  rw [distanceInverseCoefficient, ← Real.inv_rpow (by positivity : (0 : ℝ) ≤ (2 / 3) * Real.sqrt η)]
  congr 1
  have hs := (Real.sqrt_pos.mpr hη).ne'
  field_simp

theorem puiseux_quadratic_coefficient {η : ℝ} (hη : 0 < η) :
    η * distanceInverseCoefficient η ^ 2 = (3 / 2 : ℝ) ^ (4 / 3 : ℝ) * η ^ (1 / 3 : ℝ) := by
  have hc : 0 < (2 / 3 : ℝ) * Real.sqrt η := by positivity
  have hd := distanceInverseCoefficient_pos hη
  apply Real.log_injOn_pos (show 0 < η * distanceInverseCoefficient η ^ 2 by positivity)
    (show 0 < (3 / 2 : ℝ) ^ (4 / 3 : ℝ) * η ^ (1 / 3 : ℝ) by positivity)
  rw [Real.log_mul hη.ne' (pow_ne_zero 2 hd.ne'), Real.log_pow,
    Real.log_mul (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 3 / 2) _).ne'
      (Real.rpow_pos_of_pos hη _).ne', Real.log_rpow (by norm_num : (0 : ℝ) < 3 / 2),
    Real.log_rpow hη]
  dsimp [distanceInverseCoefficient]
  rw [Real.log_inv, Real.log_rpow hc, Real.log_mul (by norm_num) (Real.sqrt_pos.mpr hη).ne',
    Real.log_sqrt hη.le]
  have hlog : Real.log (2 / 3 : ℝ) = -Real.log (3 / 2 : ℝ) := by
    rw [show (2 / 3 : ℝ) = (3 / 2 : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [hlog]
  ring

end AffineQuadric
