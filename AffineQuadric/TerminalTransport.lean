import AffineQuadric.QuantitativeEndpoint

/-! A regular extension at S supplies local continuity and measurability for the FTC.
No decrease or physical admissibility beyond S is required. -/
noncomputable section
open Set MeasureTheory Filter
open scoped Topology
namespace AffineQuadric

theorem physicalTransportWeight_continuous (A κ : ℝ) : Continuous (physicalTransportWeight A κ) := by
  have hc : Continuous (v8Volume κ) :=
    continuous_iff_continuousAt.2 (fun s => (v8Volume_hasDerivAt κ s).continuousAt)
  exact (continuous_const.mul continuous_id).mul (hc.pow 2)

theorem relativePosition_continuousAt {R u : ℝ → ℝ} {A S : ℝ}
    (hA : A ≠ 0) (hS : 0 < S) (hu : DifferentiableAt ℝ u S)
    (hEq : R =ᶠ[𝓝 S] (fun s => u s / (A * s))) : ContinuousAt R S := by
  exact (hu.continuousAt.div (continuous_const.mul continuous_id).continuousAt
    (mul_ne_zero hA (ne_of_gt hS))).congr_of_eventuallyEq hEq

theorem transportAverage_terminal_hasDerivAt {S T : ℝ} {R w : ℝ → ℝ}
    (h : WeightedTransportOn S R w) (hS : 0 < S) (hST : S < T)
    (hRc : ContinuousOn R (Ioo 0 T)) (hwc : ContinuousOn w (Ioo 0 T)) :
    HasDerivAt (transportAverage R w)
      (w S / transportMass w S * (R S - transportAverage R w S)) S := by
  have hs : S ∈ Ioo 0 T := ⟨hS, hST⟩
  have hw := hwc.continuousAt (Ioo_mem_nhds hS hST)
  have hRw := (hRc.mul hwc).continuousAt (Ioo_mem_nhds hS hST)
  have hwint : IntervalIntegrable w volume 0 S := h.w_cont.intervalIntegrable_of_Icc hS.le
  have hRwint : IntervalIntegrable (fun x => R x * w x) volume 0 S :=
    (h.R_cont.mul h.w_cont).intervalIntegrable_of_Icc hS.le
  have hJ := intervalIntegral.integral_hasDerivAt_right hwint
    (ContinuousOn.stronglyMeasurableAtFilter isOpen_Ioo hwc S hs) hw
  have hN := intervalIntegral.integral_hasDerivAt_right hRwint
    (ContinuousOn.stronglyMeasurableAtFilter isOpen_Ioo (hRc.mul hwc) S hs) hRw
  have hn := ne_of_gt (transportMass_pos h hS le_rfl)
  convert hN.div hJ hn using 1
  dsimp [transportAverage, transportMass, transportNumerator]
  dsimp [transportMass] at hn
  field_simp

theorem transportAverage_terminal_deriv_neg {S T : ℝ} {R w : ℝ → ℝ}
    (h : WeightedTransportOn S R w) (hS : 0 < S) (hST : S < T)
    (hRc : ContinuousOn R (Ioo 0 T)) (hwc : ContinuousOn w (Ioo 0 T)) :
    deriv (transportAverage R w) S < 0 := by
  rw [(transportAverage_terminal_hasDerivAt h hS hST hRc hwc).deriv]
  exact mul_neg_of_pos_of_neg (div_pos (h.w_pos S ⟨hS, le_rfl⟩)
    (transportMass_pos h hS le_rfl)) (sub_neg.2 (transportAverage_bounds h hS le_rfl).1)

theorem physical_average_terminal_hasDerivAt {S T A κ : ℝ} {R : ℝ → ℝ}
    (h : WeightedTransportOn S R (physicalTransportWeight A κ))
    (hS : 0 < S) (hST : S < T) (hRc : ContinuousOn R (Ioo 0 T)) :
    HasDerivAt (transportAverage R (physicalTransportWeight A κ))
      (physicalTransportWeight A κ S / transportMass (physicalTransportWeight A κ) S *
        (R S - transportAverage R (physicalTransportWeight A κ) S)) S := by
  exact transportAverage_terminal_hasDerivAt h hS hST hRc
    (physicalTransportWeight_continuous A κ).continuousOn

end AffineQuadric
