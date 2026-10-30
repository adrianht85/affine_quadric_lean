import AffineQuadric.RemainderAlgebra
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-! Stage 2: error bounds for the genuine square root and distance integral. -/
noncomputable section
open Set Filter Asymptotics MeasureTheory
open scoped Topology ContDiff
namespace AffineQuadric

def distanceLeadingCoefficient (η : ℝ) : ℝ := (2 / 3 : ℝ) * Real.sqrt η

theorem simple_zero_w_bigO {I : Set ℝ} (hI : IsOpen I) {S η : ℝ} {w : ℝ → ℝ}
    (h : SimpleRadialZeroOn I S w η) :
    (fun δ => w (S - δ) - η * δ) =O[𝓝[>] (0 : ℝ)] (fun δ => δ ^ 2) := by
  simpa only [h.zero, h.rate.deriv, neg_mul, zero_sub, neg_neg] using
    terminal_taylor_first_bigO hI h.smooth_w h.S_mem

theorem simple_zero_normalized_firstOrder {I : Set ℝ} (hI : IsOpen I) {S η : ℝ} {w : ℝ → ℝ}
    (h : SimpleRadialZeroOn I S w η) : FirstOrderAtZero (fun δ => w (S - δ) / δ) η := by
  have hh := rpow_error_normalize (a := 1) (b := 1) (c := η)
    (f := fun δ => w (S - δ)) (by
      simpa only [Real.rpow_one, show (1 : ℝ) + 1 = 2 by norm_num, Real.rpow_two] using simple_zero_w_bigO hI h)
  simpa [FirstOrderAtZero] using hh

theorem simple_zero_wprime_firstOrder {I : Set ℝ} (hI : IsOpen I) {S η : ℝ} {w : ℝ → ℝ}
    (h : SimpleRadialZeroOn I S w η) : FirstOrderAtZero (fun δ => deriv w (S - δ)) (-η) := by
  simpa only [FirstOrderAtZero, h.rate.deriv] using
    terminal_constant_bigO hI (smooth_deriv_on_open hI h.smooth_w) h.S_mem

theorem simple_zero_wsecond_bounded {I : Set ℝ} (hI : IsOpen I) {S η : ℝ} {w : ℝ → ℝ}
    (h : SimpleRadialZeroOn I S w η) :
    (fun δ => deriv (deriv w) (S - δ)) =O[𝓝[>] (0 : ℝ)] (fun _ => (1 : ℝ)) :=
  ((smooth_hasDerivAt_on_open hI
    (smooth_deriv_on_open hI (smooth_deriv_on_open hI h.smooth_w)) h.S_mem).continuousAt.tendsto.comp
      (endpoint_parameter_tendsto S)).isBigO_one ℝ

theorem simple_zero_lambda_bigO {I : Set ℝ} (hI : IsOpen I) {S η : ℝ} {w : ℝ → ℝ}
    (h : SimpleRadialZeroOn I S w η) :
    (fun δ => radialLambda w (S - δ) - Real.sqrt η * δ ^ (1 / 2 : ℝ))
      =O[𝓝[>] (0 : ℝ)] (fun δ => δ ^ (3 / 2 : ℝ)) := by
  have hf := firstOrder_sqrt (simple_zero_normalized_firstOrder hI h) h.eta_pos
  have hf' : (fun δ => Real.sqrt (w (S - δ) / δ) - Real.sqrt η)
      =O[𝓝[>] (0 : ℝ)] (fun δ => δ ^ (1 : ℝ)) := by simpa [FirstOrderAtZero] using hf
  apply (bigO_mul_rpow hf' (1 / 2 : ℝ)).congr'
  · filter_upwards [eventually_mem_nhdsWithin] with δ hδ
    have hp : 0 < δ := hδ
    rw [← Real.sqrt_eq_rpow, Real.sqrt_div' _ hp.le]
    dsimp [radialLambda]
    field_simp [ne_of_gt (Real.sqrt_pos.mpr hp)]
  · exact Eventually.of_forall (fun δ => by norm_num)

theorem integral_bigO_rpow {f : ℝ → ℝ} {r : ℝ} (hr : 0 ≤ r)
    (hf : f =O[𝓝[>] (0 : ℝ)] (fun x => x ^ r)) :
    (fun δ => ∫ x in 0..δ, f x) =O[𝓝[>] (0 : ℝ)] (fun δ => δ ^ (r + 1)) := by
  obtain ⟨C, hC, hb⟩ := hf.exists_pos
  obtain ⟨ε, hε, he⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp hb.bound
  apply IsBigO.of_bound (C / (r + 1))
  filter_upwards [Ioo_mem_nhdsGT hε] with δ hδ
  have hp : 0 < δ := hδ.1
  have hbound : IntervalIntegrable (fun x : ℝ => C * x ^ r) volume 0 δ :=
    (continuous_const.mul (Real.continuous_rpow_const hr)).intervalIntegrable _ _
  have hh := intervalIntegral.norm_integral_le_of_norm_le (f := f) hp.le
    (Eventually.of_forall (fun x hx => by
      have hh : ‖f x‖ ≤ C * ‖x ^ r‖ := he (show x ∈ Ioo 0 ε from ⟨hx.1, lt_of_le_of_lt hx.2 hδ.2⟩)
      simpa only [Real.norm_eq_abs, abs_of_pos (Real.rpow_pos_of_pos hx.1 r)] using hh)) hbound
  rw [intervalIntegral.integral_const_mul, integral_rpow (Or.inl (by linarith : (-1 : ℝ) < r))] at hh
  have hr1 : 0 < r + 1 := by linarith
  simpa only [Real.zero_rpow (ne_of_gt hr1), sub_zero, Real.norm_eq_abs,
    abs_of_pos (Real.rpow_pos_of_pos hp (r + 1)), mul_div_assoc, div_mul_eq_mul_div] using hh

theorem local_intervalIntegrable_near_zero {U : Set ℝ} (hU : IsOpen U) {g : ℝ → ℝ}
    (hg : ContinuousOn g U) (h0 : (0 : ℝ) ∈ U) :
    ∀ᶠ δ in 𝓝 (0 : ℝ), IntervalIntegrable g volume 0 δ := by
  obtain ⟨b, c, hz, hbc, hsub⟩ := exists_Icc_mem_subset_of_mem_nhds (hU.mem_nhds h0)
  filter_upwards [hbc] with δ hδ
  exact (hg.mono (Subset.trans (uIcc_subset_Icc hz hδ) hsub)).intervalIntegrable

theorem simple_zero_distance_bigO {I : Set ℝ} (hI : IsOpen I) {S η : ℝ} {w : ℝ → ℝ}
    (h : SimpleRadialZeroOn I S w η) :
    (fun δ => terminalDistance w S (S - δ) - distanceLeadingCoefficient η * δ ^ (3 / 2 : ℝ))
      =O[𝓝[>] (0 : ℝ)] (fun δ => δ ^ (5 / 2 : ℝ)) := by
  let g := fun x => Real.sqrt (w (S - x))
  let U : Set ℝ := (fun x => S - x) ⁻¹' I
  have hU : IsOpen U := hI.preimage (continuous_const.sub continuous_id)
  have h0 : (0 : ℝ) ∈ U := by simpa [U] using h.S_mem
  have hg : ContinuousOn g U := Real.continuous_sqrt.comp_continuousOn
    (h.smooth_w.continuousOn.comp (continuous_const.sub continuous_id).continuousOn (fun _ hx => hx))
  have hi := (local_intervalIntegrable_near_zero hU hg h0).filter_mono (inf_le_left : 𝓝[>] (0 : ℝ) ≤ 𝓝 0)
  have he := integral_bigO_rpow (by norm_num : (0 : ℝ) ≤ 3 / 2) (simple_zero_lambda_bigO hI h)
  apply he.congr'
  · filter_upwards [hi] with δ hδ
    change (∫ x in 0..δ, g x - Real.sqrt η * x ^ (1 / 2 : ℝ)) =
      terminalDistance w S (S - δ) - distanceLeadingCoefficient η * δ ^ (3 / 2 : ℝ)
    rw [intervalIntegral.integral_sub hδ
      ((continuous_const.mul (Real.continuous_rpow_const (by norm_num : (0 : ℝ) ≤ 1 / 2))).intervalIntegrable 0 δ),
      intervalIntegral.integral_const_mul, integral_rpow (Or.inl (by norm_num : (-1 : ℝ) < 1 / 2))]
    rw [terminalDistance_change_variable]
    norm_num [distanceLeadingCoefficient]
    ring
  · exact Eventually.of_forall (fun δ => by norm_num)

theorem simple_zero_distance_firstOrder {I : Set ℝ} (hI : IsOpen I) {S η : ℝ} {w : ℝ → ℝ}
    (h : SimpleRadialZeroOn I S w η) :
    FirstOrderAtZero (fun δ => terminalDistance w S (S - δ) / δ ^ (3 / 2 : ℝ)) (distanceLeadingCoefficient η) := by
  have hh := rpow_error_normalize (a := 3 / 2) (b := 1) (c := distanceLeadingCoefficient η)
    (f := fun δ => terminalDistance w S (S - δ)) (by
      simpa only [show (3 / 2 : ℝ) + 1 = 5 / 2 by norm_num] using simple_zero_distance_bigO hI h)
  simpa [FirstOrderAtZero] using hh

end AffineQuadric
