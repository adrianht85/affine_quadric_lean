import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic

/-! The radial length is an actual interval integral. Its square estimate is proved by
integrating a nonnegative square and the fundamental theorem of calculus. -/
noncomputable section
open Set MeasureTheory
namespace AffineQuadric

def radialLength (v : ℝ → ℝ) (S : ℝ) : ℝ := ∫ s in 0..S, Real.sqrt (v s / 2)

structure RadialLengthData (S : ℝ) (u v : ℝ → ℝ) : Prop where
  u_cont : ContinuousOn u (Icc 0 S)
  v_cont : ContinuousOn v (Icc 0 S)
  v_nonneg : ∀ s ∈ Icc 0 S, 0 ≤ v s
  du : ∀ s ∈ Ioo 0 S, HasDerivAt u (v s) s
  initial : u 0 = 0

theorem radialLength_nonneg {S : ℝ} (hS : 0 ≤ S) (v : ℝ → ℝ) : 0 ≤ radialLength v S := by
  exact intervalIntegral.integral_nonneg_of_forall hS (fun _ => Real.sqrt_nonneg _)

theorem radial_velocity_integral {S a : ℝ} {u v : ℝ → ℝ} (hS : 0 < S)
    (h : RadialLengthData S u v) (hterminal : u S = a) : (∫ s in 0..S, v s) = a := by
  have hh := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hS.le h.u_cont h.du
    (h.v_cont.intervalIntegrable_of_Icc hS.le)
  simpa [h.initial, hterminal] using hh

theorem radialLength_sq_bound {S a : ℝ} {u v : ℝ → ℝ} (hS : 0 < S)
    (h : RadialLengthData S u v) (hterminal : u S = a) : radialLength v S ^ 2 ≤ S * a / 2 := by
  let f : ℝ → ℝ := fun x => Real.sqrt (v x / 2)
  let L : ℝ := radialLength v S
  have hfc : ContinuousOn f (Icc 0 S) := Real.continuous_sqrt.comp_continuousOn (h.v_cont.div_const 2)
  have hfi : IntervalIntegrable f volume 0 S := hfc.intervalIntegrable_of_Icc hS.le
  have hfsq : IntervalIntegrable (fun x => f x ^ 2) volume 0 S :=
    (hfc.pow 2).intervalIntegrable_of_Icc hS.le
  have hvint := radial_velocity_integral hS h hterminal
  have hsqint : (∫ x in 0..S, f x ^ 2) = a / 2 := by
    calc
      _ = ∫ x in 0..S, v x / 2 := intervalIntegral.integral_congr
        (fun x hx => Real.sq_sqrt (div_nonneg (h.v_nonneg x (by simpa [uIcc_of_le hS.le] using hx)) (by norm_num)))
      _ = a / 2 := by rw [intervalIntegral.integral_div, hvint]
  have hnonneg : 0 ≤ ∫ x in 0..S, (f x - L / S) ^ 2 :=
    intervalIntegral.integral_nonneg_of_forall hS.le (fun x => sq_nonneg _)
  have hexpand : (∫ x in 0..S, (f x - L / S) ^ 2) =
      (∫ x in 0..S, f x ^ 2) - 2 * (L / S) * L + S * (L / S) ^ 2 := by
    calc
      _ = ∫ x in 0..S, (f x ^ 2 - (2 * (L / S)) * f x + (L / S) ^ 2) :=
        intervalIntegral.integral_congr (fun x _ => by ring)
      _ = _ := by
        rw [intervalIntegral.integral_add (hfsq.sub (hfi.const_mul _)) intervalIntegrable_const,
          intervalIntegral.integral_sub hfsq (hfi.const_mul _), intervalIntegral.integral_const_mul,
          intervalIntegral.integral_const]
        simp only [sub_zero, smul_eq_mul]
        rfl
  rw [hexpand, hsqint] at hnonneg
  have hSne := ne_of_gt hS
  have heq : a / 2 - 2 * (L / S) * L + S * (L / S) ^ 2 = (S * a / 2 - L ^ 2) / S := by
    field_simp
    ring
  rw [heq] at hnonneg
  have hh := mul_nonneg hnonneg hS.le
  rw [div_mul_cancel₀ _ hSne] at hh
  exact sub_nonneg.1 hh

theorem radialLength_bound {S a : ℝ} {u v : ℝ → ℝ} (hS : 0 < S)
    (h : RadialLengthData S u v) (hterminal : u S = a) :
    radialLength v S ≤ Real.sqrt (S * a / 2) := by
  exact Real.le_sqrt_of_sq_le (radialLength_sq_bound hS h hterminal)

theorem radialLength_strict_bound {S a A C : ℝ} {u v : ℝ → ℝ}
    (hS : 0 < S) (hA : 0 < A) (hC : 0 < C)
    (h : RadialLengthData S u v) (hterminal : u S = a) (ha : a < A * S / C) :
    radialLength v S < Real.sqrt (A / (2 * C)) * S := by
  have hsq := radialLength_sq_bound hS h hterminal
  have hh := mul_lt_mul_of_pos_left ha (show 0 < S / 2 by positivity)
  have heq : S / 2 * (A * S / C) = A / (2 * C) * S ^ 2 := by ring
  rw [heq] at hh
  have hx : 0 ≤ A / (2 * C) := (div_pos hA (mul_pos (by norm_num) hC)).le
  have hr : (Real.sqrt (A / (2 * C)) * S) ^ 2 = A / (2 * C) * S ^ 2 := by
    rw [mul_pow, Real.sq_sqrt hx]
  have hsquare : radialLength v S ^ 2 < (Real.sqrt (A / (2 * C)) * S) ^ 2 := by
    rw [hr]
    nlinarith
  exact (sq_lt_sq₀ (radialLength_nonneg hS.le v)
    (mul_nonneg (Real.sqrt_nonneg _) hS.le)).1 hsquare

end AffineQuadric
