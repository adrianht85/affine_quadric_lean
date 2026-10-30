import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Tactic

/-! The weighted average is used only at positive times, never as a physical value at zero. -/
noncomputable section
open Set MeasureTheory
namespace AffineQuadric

def transportMass (w : ℝ → ℝ) (s : ℝ) : ℝ := ∫ t in 0..s, w t
def transportNumerator (R w : ℝ → ℝ) (s : ℝ) : ℝ := ∫ t in 0..s, R t * w t
def transportAverage (R w : ℝ → ℝ) (s : ℝ) : ℝ := transportNumerator R w s / transportMass w s

structure WeightedTransportOn (S : ℝ) (R w : ℝ → ℝ) : Prop where
  R_cont : ContinuousOn R (Icc 0 S)
  w_cont : ContinuousOn w (Icc 0 S)
  R_decreasing : StrictAntiOn R (Icc 0 S)
  w_nonneg : ∀ t ∈ Icc 0 S, 0 ≤ w t
  w_pos : ∀ t ∈ Ioc 0 S, 0 < w t

theorem transportMass_pos {S s : ℝ} {R w : ℝ → ℝ}
    (h : WeightedTransportOn S R w) (hs : 0 < s) (hsS : s ≤ S) : 0 < transportMass w s := by
  apply intervalIntegral.integral_pos hs (h.w_cont.mono (Icc_subset_Icc le_rfl hsS))
  · exact fun x hx => h.w_nonneg x ⟨le_of_lt hx.1, hx.2.trans hsS⟩
  · refine ⟨s, ⟨hs.le, le_rfl⟩, h.w_pos s ⟨hs, hsS⟩⟩

theorem transportAverage_bounds {S s : ℝ} {R w : ℝ → ℝ}
    (h : WeightedTransportOn S R w) (hs : 0 < s) (hsS : s ≤ S) :
    R s < transportAverage R w s ∧ transportAverage R w s < R 0 := by
  have hw := h.w_cont.mono (Icc_subset_Icc (le_refl 0) hsS)
  have hR := h.R_cont.mono (Icc_subset_Icc (le_refl 0) hsS)
  have hmid : s / 2 ∈ Icc 0 S := ⟨by linarith, by linarith⟩
  have hmidw := h.w_pos (s / 2) ⟨by linarith, by linarith⟩
  have hlow : R s * transportMass w s < transportNumerator R w s := by
    dsimp [transportMass, transportNumerator]
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_lt_integral_of_continuousOn_of_le_of_exists_lt hs
      (continuousOn_const.mul hw) (hR.mul hw)
    · intro x hx
      have hxS : x ∈ Icc 0 S := ⟨hx.1.le, hx.2.trans hsS⟩
      exact mul_le_mul_of_nonneg_right (h.R_decreasing.antitoneOn hxS ⟨hs.le, hsS⟩ hx.2)
        (h.w_nonneg x hxS)
    · refine ⟨s / 2, ⟨by linarith, by linarith⟩, ?_⟩
      exact mul_lt_mul_of_pos_right (h.R_decreasing hmid ⟨hs.le, hsS⟩ (by linarith)) hmidw
  have hhigh : transportNumerator R w s < R 0 * transportMass w s := by
    dsimp [transportMass, transportNumerator]
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_lt_integral_of_continuousOn_of_le_of_exists_lt hs
      (hR.mul hw) (continuousOn_const.mul hw)
    · intro x hx
      have hxS : x ∈ Icc 0 S := ⟨hx.1.le, hx.2.trans hsS⟩
      exact mul_le_mul_of_nonneg_right (h.R_decreasing.antitoneOn ⟨le_rfl, le_trans hs.le hsS⟩ hxS hx.1.le)
        (h.w_nonneg x hxS)
    · refine ⟨s / 2, ⟨by linarith, by linarith⟩, ?_⟩
      exact mul_lt_mul_of_pos_right
        (h.R_decreasing ⟨le_rfl, le_trans hs.le hsS⟩ hmid (by linarith)) hmidw
  have hJ := transportMass_pos h hs hsS
  exact ⟨(lt_div_iff₀ hJ).2 hlow, (div_lt_iff₀ hJ).2 hhigh⟩

theorem transportAverage_hasDerivAt {S s : ℝ} {R w : ℝ → ℝ}
    (h : WeightedTransportOn S R w) (hs : s ∈ Ioo 0 S) :
    HasDerivAt (transportAverage R w)
      (w s / transportMass w s * (R s - transportAverage R w s)) s := by
  have hw := h.w_cont.continuousAt (Icc_mem_nhds hs.1 hs.2)
  have hRw := (h.R_cont.mul h.w_cont).continuousAt (Icc_mem_nhds hs.1 hs.2)
  have hwint : IntervalIntegrable w volume 0 s := (h.w_cont.mono (Icc_subset_Icc (le_refl 0) hs.2.le)).intervalIntegrable_of_Icc hs.1.le
  have hRwint : IntervalIntegrable (fun x => R x * w x) volume 0 s := ((h.R_cont.mul h.w_cont).mono
    (Icc_subset_Icc (le_refl 0) hs.2.le)).intervalIntegrable_of_Icc hs.1.le
  have hJ := intervalIntegral.integral_hasDerivAt_right hwint (ContinuousOn.stronglyMeasurableAtFilter isOpen_Ioo
    (h.w_cont.mono Ioo_subset_Icc_self) s hs) hw
  have hN := intervalIntegral.integral_hasDerivAt_right hRwint (ContinuousOn.stronglyMeasurableAtFilter isOpen_Ioo
    ((h.R_cont.mul h.w_cont).mono Ioo_subset_Icc_self) s hs) hRw
  have hn := ne_of_gt (transportMass_pos h hs.1 hs.2.le)
  convert hN.div hJ hn using 1
  dsimp [transportAverage, transportMass, transportNumerator]
  dsimp [transportMass] at hn
  field_simp

theorem transportAverage_deriv_neg {S s : ℝ} {R w : ℝ → ℝ}
    (h : WeightedTransportOn S R w) (hs : s ∈ Ioo 0 S) :
    deriv (transportAverage R w) s < 0 := by
  rw [(transportAverage_hasDerivAt h hs).deriv]
  exact mul_neg_of_pos_of_neg (div_pos (h.w_pos s ⟨hs.1, hs.2.le⟩)
    (transportMass_pos h hs.1 hs.2.le)) (sub_neg.2 (transportAverage_bounds h hs.1 hs.2.le).1)

theorem transportAverage_strictAntiOn {S : ℝ} {R w : ℝ → ℝ}
    (h : WeightedTransportOn S R w) : StrictAntiOn (transportAverage R w) (Ioo 0 S) := by
  apply strictAntiOn_of_deriv_neg (convex_Ioo 0 S)
  · exact fun x hx => (transportAverage_hasDerivAt h hx).continuousAt.continuousWithinAt
  · intro x hx
    rw [interior_Ioo] at hx
    exact transportAverage_deriv_neg h hx

end AffineQuadric
