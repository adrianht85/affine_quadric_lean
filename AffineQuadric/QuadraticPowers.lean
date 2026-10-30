import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Tactic

/-! Exact power conversion and separation of the scalar residual. -/
noncomputable section
open Set Polynomial
namespace AffineQuadric

theorem cubic_rpow_neg_two_thirds {r : ℝ} (hr : 0 < r) :
    (r ^ 3) ^ (-2 / 3 : ℝ) = (r ^ 2)⁻¹ := by
  calc
    (r ^ 3) ^ (-2 / 3 : ℝ) = r ^ ((3 : ℕ) * (-2 / 3 : ℝ)) :=
      (Real.rpow_natCast_mul hr.le 3 _).symm
    _ = r ^ (-((2 : ℕ) : ℝ)) := by congr 1; norm_num
    _ = (r ^ ((2 : ℕ) : ℝ))⁻¹ := Real.rpow_neg hr.le _
    _ = (r ^ 2)⁻¹ := congrArg Inv.inv (Real.rpow_natCast r 2)

theorem cubic_rpow_neg_five_thirds {r : ℝ} (hr : 0 < r) :
    (r ^ 3) ^ (-5 / 3 : ℝ) = (r ^ 5)⁻¹ := by
  calc
    (r ^ 3) ^ (-5 / 3 : ℝ) = r ^ ((3 : ℕ) * (-5 / 3 : ℝ)) :=
      (Real.rpow_natCast_mul hr.le 3 _).symm
    _ = r ^ (-((5 : ℕ) : ℝ)) := by congr 1; norm_num
    _ = (r ^ ((5 : ℕ) : ℝ))⁻¹ := Real.rpow_neg hr.le _
    _ = (r ^ 5)⁻¹ := congrArg Inv.inv (Real.rpow_natCast r 5)

theorem sparse_polynomial_coefficients (u w q e f : ℝ)
    (h : ∀ r : ℝ, 0 < r → u * r ^ 11 - w * r ^ 8 + q * r ^ 5 - e * r ^ 3 - f = 0) :
    u = 0 ∧ w = 0 ∧ q = 0 ∧ e = 0 ∧ f = 0 := by
  let p : Polynomial ℝ := C u * X ^ 11 - C w * X ^ 8 + C q * X ^ 5 - C e * X ^ 3 - C f
  have hp : p = 0 := by
    apply Polynomial.eq_zero_of_infinite_isRoot
    apply (Ioi_infinite (0 : ℝ)).mono
    intro r hr
    change p.eval r = 0
    simpa [p] using h r hr
  have h11 := congrArg (fun p : Polynomial ℝ => p.coeff 11) hp
  have h8 := congrArg (fun p : Polynomial ℝ => p.coeff 8) hp
  have h5 := congrArg (fun p : Polynomial ℝ => p.coeff 5) hp
  have h3 := congrArg (fun p : Polynomial ℝ => p.coeff 3) hp
  have h0 := congrArg (fun p : Polynomial ℝ => p.coeff 0) hp
  simp [p] at h11 h8 h5 h3 h0
  exact ⟨h11, h8, h5, h3, h0⟩

theorem quadratic_residual_separation (a₃ b₂ d₁ e f : ℝ)
    (h : ∀ z : ℝ, 0 < z → a₃ * z ^ 2 / 2 - b₂ * z + d₁ -
      e * z ^ (-2 / 3 : ℝ) - f * z ^ (-5 / 3 : ℝ) = 0) :
    a₃ = 0 ∧ b₂ = 0 ∧ d₁ = 0 ∧ e = 0 ∧ f = 0 := by
  have hh := sparse_polynomial_coefficients (a₃ / 2) b₂ d₁ e f (by
    intro r hr
    have he := h (r ^ 3) (pow_pos hr 3)
    rw [cubic_rpow_neg_two_thirds hr, cubic_rpow_neg_five_thirds hr] at he
    have hn : r ≠ 0 := ne_of_gt hr
    field_simp at he
    nlinarith [he])
  exact ⟨by linarith [hh.1], hh.2⟩

end AffineQuadric
