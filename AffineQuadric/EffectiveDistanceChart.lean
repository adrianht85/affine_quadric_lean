import AffineQuadric.AnalyticDistanceInverse

/-! A chart constructed from the integral distance, with a positive independent
distance parameter. All identities are local; no global inverse is claimed. -/
noncomputable section
open Set Filter
open scoped Topology
namespace AffineQuadric

structure AnalyticDistanceChart (w : ℝ → ℝ) (S η : ℝ) where
  F : ℝ → ℝ
  D : ℝ → ℝ
  analyticF : AnalyticAt ℝ F 0
  Fzero : F 0 = (2 / 3 : ℝ) * Real.sqrt η
  Fpos : 0 < F 0
  factor : ∀ᶠ δ in 𝓝[>] (0 : ℝ), terminalDistance w S (S - δ) = δ ^ (3 / 2 : ℝ) * F δ
  analyticD : AnalyticAt ℝ D 0
  Dzero : D 0 = 0
  Dderiv : HasDerivAt D ((F 0) ^ (2 / 3 : ℝ))⁻¹ 0
  right_inverse : ∀ᶠ z in 𝓝 (0 : ℝ), regularDistanceCoordinate F (D z) = z
  left_inverse : ∀ᶠ δ in 𝓝 (0 : ℝ), D (regularDistanceCoordinate F δ) = δ

theorem analyticDistanceChart_exists {w : ℝ → ℝ} {S η : ℝ}
    (hw : AnalyticAt ℝ w S) (hz : w S = 0) (hd : HasDerivAt w (-η) S) (hη : 0 < η) :
    Nonempty (AnalyticDistanceChart w S η) := by
  obtain ⟨F, hF, hF0, hfactor⟩ := analytic_simple_zero_distance_factor hw hz hd hη
  have hc : 0 < F 0 := by rw [hF0]; positivity
  obtain ⟨D, hD, hD0, hdD, hright, hleft⟩ := analytic_distance_inverse hF hc
  exact ⟨⟨F, D, hF, hF0, hc, hfactor, hD, hD0, hdD, hright, hleft⟩⟩

def independentDistanceDelta {w : ℝ → ℝ} {S η : ℝ}
    (C : AnalyticDistanceChart w S η) (r : ℝ) : ℝ := C.D (r ^ (2 / 3 : ℝ))

def independentDistancePoint {w : ℝ → ℝ} {S η : ℝ}
    (C : AnalyticDistanceChart w S η) (r : ℝ) : ℝ := S - independentDistanceDelta C r

theorem positive_rpow_tendsto {b : ℝ} (hb : 0 < b) :
    Tendsto (fun r : ℝ => r ^ b) (𝓝[>] (0 : ℝ)) (𝓝[>] (0 : ℝ)) := by
  apply tendsto_nhdsWithin_iff.mpr
  constructor
  · simpa [Real.zero_rpow hb.ne'] using
      (Real.continuous_rpow_const hb.le).continuousAt.tendsto.mono_left
        (inf_le_left : 𝓝[>] (0 : ℝ) ≤ 𝓝 0)
  · filter_upwards [eventually_mem_nhdsWithin] with r hr
    exact Real.rpow_pos_of_pos hr _

theorem distanceChart_D_tendsto {w : ℝ → ℝ} {S η : ℝ} (C : AnalyticDistanceChart w S η) :
    Tendsto C.D (𝓝[>] (0 : ℝ)) (𝓝[>] (0 : ℝ)) := by
  apply tendsto_nhdsWithin_iff.mpr
  constructor
  · simpa [C.Dzero] using C.analyticD.continuousAt.tendsto.mono_left
      (inf_le_left : 𝓝[>] (0 : ℝ) ≤ 𝓝 0)
  · have hd : 0 < ((C.F 0) ^ (2 / 3 : ℝ))⁻¹ := inv_pos.mpr (Real.rpow_pos_of_pos C.Fpos _)
    filter_upwards [(right_linear_rate C.Dderiv C.Dzero).eventually (Ioi_mem_nhds hd),
      eventually_mem_nhdsWithin] with z hz hp
    exact (div_pos_iff_of_pos_right hp).mp hz

theorem independentDistanceDelta_tendsto {w : ℝ → ℝ} {S η : ℝ}
    (C : AnalyticDistanceChart w S η) :
    Tendsto (independentDistanceDelta C) (𝓝[>] (0 : ℝ)) (𝓝[>] (0 : ℝ)) :=
  (distanceChart_D_tendsto C).comp (positive_rpow_tendsto (by norm_num : (0 : ℝ) < 2 / 3))

theorem independentDistancePoint_tendsto {w : ℝ → ℝ} {S η : ℝ}
    (C : AnalyticDistanceChart w S η) :
    Tendsto (independentDistancePoint C) (𝓝[>] (0 : ℝ)) (𝓝 S) :=
  (endpoint_parameter_tendsto S).comp (independentDistanceDelta_tendsto C)

theorem distanceChart_power_identity {F : ℝ → ℝ} {δ : ℝ} (hδ : 0 < δ) (hF : 0 < F δ) :
    (δ ^ (3 / 2 : ℝ) * F δ) ^ (2 / 3 : ℝ) = regularDistanceCoordinate F δ := by
  rw [Real.mul_rpow (Real.rpow_nonneg hδ.le _) hF.le, ← Real.rpow_mul hδ.le]
  norm_num [regularDistanceCoordinate]

theorem independentDistance_identity {w : ℝ → ℝ} {S η : ℝ} (C : AnalyticDistanceChart w S η) :
    ∀ᶠ r in 𝓝[>] (0 : ℝ), 0 < independentDistanceDelta C r ∧
      terminalDistance w S (independentDistancePoint C r) = r := by
  have ht := independentDistanceDelta_tendsto C
  have hz := positive_rpow_tendsto (by norm_num : (0 : ℝ) < 2 / 3)
  have hright := (hz.mono_right inf_le_left).eventually C.right_inverse
  have hpos := C.analyticF.continuousAt.eventually (Ioi_mem_nhds C.Fpos)
  filter_upwards [ht.eventually eventually_mem_nhdsWithin, ht.eventually C.factor,
    (ht.mono_right inf_le_left).eventually hpos, hright, eventually_mem_nhdsWithin]
      with r hδ hf hp hi hr
  refine ⟨hδ, ?_⟩
  have he : (terminalDistance w S (independentDistancePoint C r)) ^ (2 / 3 : ℝ) =
      r ^ (2 / 3 : ℝ) := by
    rw [independentDistancePoint, hf, distanceChart_power_identity hδ hp]
    exact hi
  have hρ : 0 < terminalDistance w S (independentDistancePoint C r) := by
    rw [independentDistancePoint, hf]; exact mul_pos (Real.rpow_pos_of_pos hδ _) hp
  have hh := congrArg (fun x : ℝ => x ^ (3 / 2 : ℝ)) he
  simpa only [← Real.rpow_mul hρ.le, ← Real.rpow_mul (show 0 ≤ r from le_of_lt hr),
    show (2 / 3 : ℝ) * (3 / 2) = 1 by norm_num, Real.rpow_one] using hh

theorem independentDistance_inverse {w : ℝ → ℝ} {S η : ℝ} (C : AnalyticDistanceChart w S η) :
    ∀ᶠ δ in 𝓝[>] (0 : ℝ),
      independentDistancePoint C (terminalDistance w S (S - δ)) = S - δ := by
  have hp := C.analyticF.continuousAt.eventually (Ioi_mem_nhds C.Fpos)
  filter_upwards [C.factor, C.left_inverse.filter_mono inf_le_left,
    hp.filter_mono inf_le_left, eventually_mem_nhdsWithin] with δ hf hi hp hδ
  simp only [independentDistancePoint, independentDistanceDelta, hf,
    distanceChart_power_identity hδ hp, hi]

theorem independentDistance_interval {I : Set ℝ} (hI : IsOpen I) {w : ℝ → ℝ} {S η : ℝ}
    (hS : S ∈ I) (C : AnalyticDistanceChart w S η) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ r ∈ Ioo (0 : ℝ) ε,
      0 < independentDistanceDelta C r ∧ independentDistancePoint C r ∈ I ∧
        terminalDistance w S (independentDistancePoint C r) = r := by
  have hm := (independentDistancePoint_tendsto C).eventually (hI.mem_nhds hS)
  have hh : ∀ᶠ r in 𝓝[>] (0 : ℝ), 0 < independentDistanceDelta C r ∧
      independentDistancePoint C r ∈ I ∧ terminalDistance w S (independentDistancePoint C r) = r := by
    filter_upwards [independentDistance_identity C, hm] with r hr hmem
    exact ⟨hr.1, hmem, hr.2⟩
  exact mem_nhdsGT_iff_exists_Ioo_subset.mp hh

theorem transverse_analyticDistanceChart_exists {I : Set ℝ} (hI : IsOpen I)
    {S : ℝ} {a V q p : ℝ → ℝ} (h : LocalTransverseSolutionOn I S a V q p)
    (hq : AnalyticAt ℝ q S) :
    Nonempty (AnalyticDistanceChart (collisionRadialW q) S (collisionEta a V p S)) := by
  have ht := collisionRadialW_terminal hI h
  exact analyticDistanceChart_exists (transverse_radial_analytic h hq) ht.1 ht.2.1 (collisionEta_pos h)

end AffineQuadric
