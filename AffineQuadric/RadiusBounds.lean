import AffineQuadric.MechanicalProfile

/-! PE V8 eq:hyperbolic-lower and its conditional collision-radius consequence. -/
noncomputable section
namespace AffineQuadric

def radiusProfile (t : ℝ) : ℝ := Real.cosh t / Real.sinh t - 1 / t
def radiusAux (t : ℝ) : ℝ := (2 * t - 3) * Real.exp (2 * t) + 2 * t ^ 2 + 4 * t + 3
def radiusAuxOne (t : ℝ) : ℝ := (4 * t - 4) * Real.exp (2 * t) + 4 * t + 4
def radiusAuxTwo (t : ℝ) : ℝ := (8 * t - 4) * Real.exp (2 * t) + 4

theorem positive_from_zero_derivative {f d : ℝ → ℝ} (h0 : f 0 = 0)
    (hd : ∀ t, HasDerivAt f (d t) t) (hpos : ∀ t, 0 < t → 0 < d t)
    {t : ℝ} (ht : 0 < t) : 0 < f t := by
  have hm : StrictMonoOn f (Set.Ici 0) := by
    apply strictMonoOn_of_deriv_pos (convex_Ici 0)
    · exact fun x _ => (hd x).continuousAt.continuousWithinAt
    · intro x hx
      rw [interior_Ici] at hx
      rw [(hd x).deriv]
      exact hpos x hx
  have hh := hm (by simp : (0 : ℝ) ∈ Set.Ici 0) (le_of_lt ht) ht
  simpa [h0] using hh

theorem radiusAux_hasDerivAt (t : ℝ) : HasDerivAt radiusAux (radiusAuxOne t) t := by
  have he := (Real.hasDerivAt_exp (2 * t)).comp t ((hasDerivAt_id t).const_mul 2)
  convert (((((hasDerivAt_id t).const_mul 2).sub_const 3).mul he).add
    (((hasDerivAt_id t).pow 2).const_mul 2)).add ((hasDerivAt_id t).const_mul 4) |>.add_const 3 using 1
  dsimp [radiusAuxOne]
  ring

theorem radiusAuxOne_hasDerivAt (t : ℝ) : HasDerivAt radiusAuxOne (radiusAuxTwo t) t := by
  have he := (Real.hasDerivAt_exp (2 * t)).comp t ((hasDerivAt_id t).const_mul 2)
  convert (((((hasDerivAt_id t).const_mul 4).sub_const 4).mul he).add
    ((hasDerivAt_id t).const_mul 4)).add_const 4 using 1
  dsimp [radiusAuxTwo]
  ring

theorem radiusAuxTwo_hasDerivAt (t : ℝ) :
    HasDerivAt radiusAuxTwo (16 * t * Real.exp (2 * t)) t := by
  have he := (Real.hasDerivAt_exp (2 * t)).comp t ((hasDerivAt_id t).const_mul 2)
  convert ((((hasDerivAt_id t).const_mul 8).sub_const 4).mul he).add_const 4 using 1
  dsimp
  ring

theorem radiusAux_initial : radiusAux 0 = 0 ∧ radiusAuxOne 0 = 0 ∧ radiusAuxTwo 0 = 0 := by
  norm_num [radiusAux, radiusAuxOne, radiusAuxTwo]

theorem radiusAuxTwo_pos {t : ℝ} (ht : 0 < t) : 0 < radiusAuxTwo t := by
  exact positive_from_zero_derivative radiusAux_initial.2.2 radiusAuxTwo_hasDerivAt
    (fun x hx => mul_pos (mul_pos (by norm_num) hx) (Real.exp_pos _)) ht

theorem radiusAuxOne_pos {t : ℝ} (ht : 0 < t) : 0 < radiusAuxOne t := by
  exact positive_from_zero_derivative radiusAux_initial.2.1 radiusAuxOne_hasDerivAt
    (fun _ hx => radiusAuxTwo_pos hx) ht

theorem radiusAux_pos {t : ℝ} (ht : 0 < t) : 0 < radiusAux t := by
  exact positive_from_zero_derivative radiusAux_initial.1 radiusAux_hasDerivAt
    (fun _ hx => radiusAuxOne_pos hx) ht

theorem radius_exponential_denominator_pos {t : ℝ} (ht : 0 < t) :
    0 < t * (t + 3) * (Real.exp (2 * t) - 1) := by
  exact mul_pos (mul_pos ht (by linarith)) (sub_pos.2 (Real.one_lt_exp_iff.2 (by linarith)))

theorem coth_exp_identity {t : ℝ} (ht : 0 < t) :
    Real.cosh t / Real.sinh t = (Real.exp (2 * t) + 1) / (Real.exp (2 * t) - 1) := by
  have hn : Real.sinh t ≠ 0 := ne_of_gt (Real.sinh_pos_iff.2 ht)
  have he : Real.exp t ≠ 0 := ne_of_gt (Real.exp_pos t)
  have htwo : Real.exp (2 * t) = Real.exp t ^ 2 := by
    rw [show 2 * t = t + t by ring, Real.exp_add]
    ring
  have hd : Real.exp (2 * t) - 1 ≠ 0 := ne_of_gt (sub_pos.2 (Real.one_lt_exp_iff.2 (by linarith)))
  apply (div_eq_div_iff hn hd).2
  rw [Real.cosh_eq, Real.sinh_eq, Real.exp_neg, htwo]
  field_simp

theorem radiusProfile_difference {t : ℝ} (ht : 0 < t) :
    radiusProfile t - t / (t + 3) = radiusAux t /
      (t * (t + 3) * (Real.exp (2 * t) - 1)) := by
  have hn := ne_of_gt (radius_exponential_denominator_pos ht)
  have ht0 := ne_of_gt ht
  have ht3 : t + 3 ≠ 0 := by linarith
  have he : Real.exp (2 * t) - 1 ≠ 0 := ne_of_gt (sub_pos.2 (Real.one_lt_exp_iff.2 (by linarith)))
  dsimp [radiusProfile, radiusAux]
  rw [coth_exp_identity ht]
  field_simp
  ring

theorem radiusProfile_lower_one {t : ℝ} (ht : 0 < t) : 1 - 1 / t < radiusProfile t := by
  have hh : 1 < Real.cosh t / Real.sinh t :=
    (one_lt_div (Real.sinh_pos_iff.2 ht)).2 (Real.sinh_lt_cosh t)
  dsimp [radiusProfile]
  linarith

theorem radiusProfile_lower_fraction {t : ℝ} (ht : 0 < t) : t / (t + 3) < radiusProfile t := by
  have hh := div_pos (radiusAux_pos ht) (radius_exponential_denominator_pos ht)
  rw [← radiusProfile_difference ht] at hh
  linarith

theorem endpoint_radius_bound {S C : ℝ} (hS : 0 < S) (hC : 1 < C)
    (hr : radiusProfile (3 * S) < 1 / C) :
    S < min (1 / (C - 1)) (C / (3 * (C - 1))) := by
  have hCp : 0 < C := by linarith
  have hcm : 0 < C - 1 := by linarith
  have ht : 0 < 3 * S := by positivity
  have hlow := lt_trans (radiusProfile_lower_one ht) hr
  have hfrac := lt_trans (radiusProfile_lower_fraction ht) hr
  have hcross := (div_lt_div_iff₀ (show 0 < 3 * S + 3 by linarith) hCp).mp hfrac
  have hs1 : S < 1 / (C - 1) := (lt_div_iff₀ hcm).2 (by nlinarith)
  have hh := (lt_div_iff₀ hCp).mp hlow
  have hmul := mul_lt_mul_of_pos_right hh ht
  have heq : (1 - 1 / (3 * S)) * C * (3 * S) = 3 * S * C - C := by field_simp
  rw [heq, one_mul] at hmul
  have hs2 : S < C / (3 * (C - 1)) :=
    (lt_div_iff₀ (mul_pos (by norm_num) hcm)).2 (by nlinarith)
  exact lt_min hs1 hs2

end AffineQuadric
