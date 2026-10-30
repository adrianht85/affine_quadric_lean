import AffineQuadric.EndpointRates
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-! The actual distance integral and its leading rate at a simple zero of w.
The simple-zero data will be supplied by the local canonical collision theorem. -/
noncomputable section
open Set Filter MeasureTheory
open scoped Topology ContDiff
namespace AffineQuadric

def radialLambda (w : ℝ → ℝ) (s : ℝ) : ℝ := Real.sqrt (w s)
def terminalDistance (w : ℝ → ℝ) (S s : ℝ) : ℝ :=
  ∫ σ in s..S, radialLambda w σ

structure SimpleRadialZeroOn (I : Set ℝ) (S : ℝ) (w : ℝ → ℝ) (η : ℝ) : Prop where
  S_mem : S ∈ I
  smooth_w : ContDiffOn ℝ ∞ w I
  zero : w S = 0
  rate : HasDerivAt w (-η) S
  eta_pos : 0 < η

theorem local_integral_hasDerivAt {U : Set ℝ} (hU : IsOpen U) {g : ℝ → ℝ}
    (hg : ContinuousOn g U) (h0 : (0 : ℝ) ∈ U) :
    ∀ᶠ δ in 𝓝 (0 : ℝ), HasDerivAt (fun x => ∫ t in 0..x, g t) (g δ) δ := by
  obtain ⟨b, c, hz, hbc, hsub⟩ := exists_Icc_mem_subset_of_mem_nhds (hU.mem_nhds h0)
  filter_upwards [hbc] with δ hδ
  have hint : IntervalIntegrable g volume 0 δ :=
    (hg.mono (Subset.trans (uIcc_subset_Icc hz hδ) hsub)).intervalIntegrable
  exact intervalIntegral.integral_hasDerivAt_right hint
    (hg.stronglyMeasurableAtFilter hU δ (hsub hδ)) (hg.continuousAt (hU.mem_nhds (hsub hδ)))

theorem local_integral_zero_hasDerivAt {U : Set ℝ} (hU : IsOpen U) {g : ℝ → ℝ}
    (hg : ContinuousOn g U) (h0 : (0 : ℝ) ∈ U) :
    HasDerivAt (fun x => ∫ t in 0..x, g t) (g 0) 0 :=
  intervalIntegral.integral_hasDerivAt_right (by simp)
    (hg.stronglyMeasurableAtFilter hU 0 h0) (hg.continuousAt (hU.mem_nhds h0))

theorem terminalDistance_change_variable (w : ℝ → ℝ) (S δ : ℝ) :
    terminalDistance w S (S - δ) = ∫ x in 0..δ, Real.sqrt (w (S - x)) := by
  simpa [terminalDistance, radialLambda] using
    (intervalIntegral.integral_comp_sub_left (fun σ => Real.sqrt (w σ)) (a := 0) (b := δ) S).symm

theorem simple_zero_lambda_rate {I : Set ℝ} {S η : ℝ} {w : ℝ → ℝ}
    (h : SimpleRadialZeroOn I S w η) :
    Tendsto (fun δ => radialLambda w (S - δ) / δ ^ (1 / 2 : ℝ))
      (𝓝[>] (0 : ℝ)) (𝓝 (Real.sqrt η)) := by
  have hr : Tendsto (fun δ => w (S - δ) / δ) (𝓝[>] (0 : ℝ)) (𝓝 η) := by
    simpa using terminal_linear_rate h.rate h.zero
  have hh := Real.continuous_sqrt.continuousAt.tendsto.comp hr
  apply hh.congr'
  filter_upwards [eventually_mem_nhdsWithin] with δ hδ
  have hδpos : 0 < δ := hδ
  dsimp only [Function.comp_def]
  rw [radialLambda, ← Real.sqrt_eq_rpow, Real.sqrt_div' (w (S - δ)) hδpos.le]

theorem simple_zero_distance_rate {I : Set ℝ} (hI : IsOpen I)
    {S η : ℝ} {w : ℝ → ℝ} (h : SimpleRadialZeroOn I S w η) :
    Tendsto (fun δ => terminalDistance w S (S - δ) / δ ^ (3 / 2 : ℝ))
      (𝓝[>] (0 : ℝ)) (𝓝 ((2 / 3 : ℝ) * Real.sqrt η)) := by
  let U : Set ℝ := (fun δ => S - δ) ⁻¹' I
  have hU : IsOpen U := hI.preimage (continuous_const.sub continuous_id)
  have h0 : (0 : ℝ) ∈ U := by simpa [U] using h.S_mem
  let g := fun δ => Real.sqrt (w (S - δ))
  have hg : ContinuousOn g U := Real.continuous_sqrt.comp_continuousOn
    (h.smooth_w.continuousOn.comp (continuous_const.sub continuous_id).continuousOn (fun _ hx => hx))
  have hF := local_integral_hasDerivAt hU hg h0
  have hF0 := local_integral_zero_hasDerivAt hU hg h0
  have hdiv : Tendsto (fun δ => g δ / ((3 / 2 : ℝ) * δ ^ (1 / 2 : ℝ)))
      (𝓝[>] (0 : ℝ)) (𝓝 ((2 / 3 : ℝ) * Real.sqrt η)) := by
    convert (simple_zero_lambda_rate h).const_mul (2 / 3 : ℝ) using 1
    funext δ
    dsimp [g, radialLambda]
    ring
  have hlim : Tendsto (fun δ => (∫ x in 0..δ, g x) / δ ^ (3 / 2 : ℝ))
      (𝓝[>] (0 : ℝ)) (𝓝 ((2 / 3 : ℝ) * Real.sqrt η)) := by
    apply HasDerivAt.lhopital_zero_nhdsGT (f' := g)
      (g' := fun δ => (3 / 2 : ℝ) * δ ^ (1 / 2 : ℝ))
      (hF.filter_mono inf_le_left) _ _ _ _ hdiv
    · filter_upwards [eventually_mem_nhdsWithin] with δ hδ
      have hδpos : 0 < δ := hδ
      apply ((hasDerivAt_id δ).rpow_const (p := (3 / 2 : ℝ)) (Or.inl (ne_of_gt hδpos))).congr_deriv
      dsimp
      rw [show (3 / 2 : ℝ) - 1 = (1 / 2 : ℝ) by norm_num]
      ring
    · filter_upwards [eventually_mem_nhdsWithin] with δ hδ
      exact ne_of_gt (mul_pos (by norm_num) (Real.rpow_pos_of_pos (show 0 < δ from hδ) _))
    · simpa using hF0.continuousAt.tendsto.mono_left (inf_le_left : 𝓝[>] (0 : ℝ) ≤ 𝓝 0)
    · simpa using (tendsto_id.mono_left (inf_le_left : 𝓝[>] (0 : ℝ) ≤ 𝓝 0)).rpow_const
        (Or.inr (by norm_num : (0 : ℝ) ≤ 3 / 2))
  simpa only [g, terminalDistance_change_variable] using hlim

theorem simple_zero_distance_pos {I : Set ℝ} (hI : IsOpen I)
    {S η : ℝ} {w : ℝ → ℝ} (h : SimpleRadialZeroOn I S w η) :
    ∀ᶠ δ in 𝓝[>] (0 : ℝ), 0 < terminalDistance w S (S - δ) := by
  have hrate := simple_zero_distance_rate hI h
  have hc : 0 < (2 / 3 : ℝ) * Real.sqrt η := mul_pos (by norm_num) (Real.sqrt_pos.mpr h.eta_pos)
  filter_upwards [hrate.eventually (Ioi_mem_nhds hc), eventually_mem_nhdsWithin] with δ hr hδ
  exact (div_pos_iff_of_pos_right (Real.rpow_pos_of_pos (show 0 < δ from hδ) _)).mp hr

end AffineQuadric
