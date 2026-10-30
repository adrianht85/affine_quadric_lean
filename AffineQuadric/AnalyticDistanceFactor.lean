import AffineQuadric.AnalyticDistanceSeries

/-! Identification of the analytic series factor with the effective distance
integral. The real fractional power is only used on the positive side. -/
noncomputable section
open Set Filter MeasureTheory
open scoped Topology
namespace AffineQuadric

theorem distance_factor_integral {g F : ℝ → ℝ}
    (hg : AnalyticAt ℝ g 0) (hF : AnalyticAt ℝ F 0)
    (he : ∀ᶠ x in 𝓝 (0 : ℝ), (3 / 2 : ℝ) * F x + x * deriv F x = Real.sqrt (g x)) :
    ∀ᶠ δ in 𝓝[>] (0 : ℝ),
      (∫ x in 0..δ, Real.sqrt (x * g x)) = δ ^ (3 / 2 : ℝ) * F δ := by
  have hall : ∀ᶠ x in 𝓝 (0 : ℝ),
      AnalyticAt ℝ g x ∧ AnalyticAt ℝ F x ∧
        (3 / 2 : ℝ) * F x + x * deriv F x = Real.sqrt (g x) :=
    hg.eventually_analyticAt.and (hF.eventually_analyticAt.and he)
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.mp hall
  filter_upwards [Ioo_mem_nhdsGT hε] with δ hδ
  have hin : ∀ x ∈ Icc (0 : ℝ) δ, dist x 0 < ε := by
    intro x hx
    simpa [Real.dist_eq, abs_of_nonneg hx.1] using lt_of_le_of_lt hx.2 hδ.2
  have hcF : ContinuousOn F (Icc 0 δ) := fun x hx =>
    (hball (hin x hx)).2.1.continuousAt.continuousWithinAt
  have hcg : ContinuousOn (fun x => Real.sqrt (x * g x)) (Icc 0 δ) :=
    Real.continuous_sqrt.comp_continuousOn (continuousOn_id.mul (fun x hx =>
      (hball (hin x hx)).1.continuousAt.continuousWithinAt))
  have hc : ContinuousOn (fun x => x ^ (3 / 2 : ℝ) * F x) (Icc 0 δ) :=
    (Real.continuous_rpow_const (by norm_num : (0 : ℝ) ≤ 3 / 2)).continuousOn.mul hcF
  have hd : ∀ x ∈ Ioo (0 : ℝ) δ,
      HasDerivAt (fun x => x ^ (3 / 2 : ℝ) * F x) (Real.sqrt (x * g x)) x := by
    intro x hx
    have hxε := hin x ⟨hx.1.le, hx.2.le⟩
    have hf := (hball hxε).2.1.differentiableAt.hasDerivAt
    have hp := (hasDerivAt_id x).rpow_const (p := (3 / 2 : ℝ)) (Or.inl hx.1.ne')
    apply (hp.mul hf).congr_deriv
    dsimp
    rw [show (3 / 2 : ℝ) - 1 = 1 / 2 by norm_num]
    have hpow : x ^ (3 / 2 : ℝ) = x ^ (1 / 2 : ℝ) * x := by
      rw [show (3 / 2 : ℝ) = 1 / 2 + 1 by norm_num, Real.rpow_add hx.1, Real.rpow_one]
    rw [hpow]
    calc
      1 * (3 / 2 : ℝ) * x ^ (1 / 2 : ℝ) * F x + x ^ (1 / 2 : ℝ) * x * deriv F x =
          x ^ (1 / 2 : ℝ) * ((3 / 2 : ℝ) * F x + x * deriv F x) := by ring
      _ = Real.sqrt x * Real.sqrt (g x) := by
        rw [(hball hxε).2.2]
        simp only [Real.sqrt_eq_rpow]
      _ = Real.sqrt (x * g x) := (Real.sqrt_mul hx.1.le _).symm
  have hint : IntervalIntegrable (fun x => Real.sqrt (x * g x)) volume 0 δ :=
    (hcg.mono (by rw [uIcc_of_le hδ.1.le])).intervalIntegrable
  simpa using intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hδ.1.le hc hd hint

theorem analytic_simple_zero_distance_factor {w : ℝ → ℝ} {S η : ℝ}
    (hw : AnalyticAt ℝ w S) (hz : w S = 0) (hd : HasDerivAt w (-η) S) (hη : 0 < η) :
    ∃ F : ℝ → ℝ, AnalyticAt ℝ F 0 ∧ F 0 = (2 / 3 : ℝ) * Real.sqrt η ∧
      (∀ᶠ δ in 𝓝[>] (0 : ℝ), terminalDistance w S (S - δ) = δ ^ (3 / 2 : ℝ) * F δ) := by
  obtain ⟨F, hF, hF0, he⟩ := analytic_distance_euler (analyticRadialFactor_sqrt hw hd hη)
  refine ⟨F, hF, ?_, ?_⟩
  · simpa only [analyticRadialFactor_zero hd] using hF0
  · have hh := distance_factor_integral (analyticRadialFactor_analytic hw) hF he
    simpa only [terminalDistance_change_variable, ← analyticRadialFactor_identity hz] using hh

theorem transverse_analytic_distance_factor {I : Set ℝ} (hI : IsOpen I)
    {S : ℝ} {a V q p : ℝ → ℝ} (h : LocalTransverseSolutionOn I S a V q p)
    (hq : AnalyticAt ℝ q S) :
    ∃ F : ℝ → ℝ, AnalyticAt ℝ F 0 ∧
      F 0 = (2 / 3 : ℝ) * Real.sqrt (collisionEta a V p S) ∧
      (∀ᶠ δ in 𝓝[>] (0 : ℝ), terminalDistance (collisionRadialW q) S (S - δ) =
        δ ^ (3 / 2 : ℝ) * F δ) := by
  have ht := collisionRadialW_terminal hI h
  exact analytic_simple_zero_distance_factor (transverse_radial_analytic h hq) ht.1 ht.2.1
    (collisionEta_pos h)

end AffineQuadric
