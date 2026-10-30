import AffineQuadric.AnalyticProfileTaylor
import AffineQuadric.PuiseuxCoefficients

/-! Scalar convergent profiles in z = r^(2/3), for the given local canonical
solution. Real analyticity of a and q at the endpoint is explicit. No tensor
geometry or existence of analytic continuation is inferred. -/
noncomputable section
open Set Filter Asymptotics
open scoped Topology
namespace AffineQuadric

theorem distanceChart_inverse_deriv {w : ℝ → ℝ} {S η : ℝ} (C : AnalyticDistanceChart w S η) :
    HasDerivAt C.D (distanceInverseCoefficient η) 0 := by
  simpa only [C.Fzero, distanceInverseCoefficient] using C.Dderiv

theorem independentDistanceDelta_remainder {w : ℝ → ℝ} {S η : ℝ}
    (C : AnalyticDistanceChart w S η) :
    (fun r => independentDistanceDelta C r - distanceInverseCoefficient η * r ^ (2 / 3 : ℝ))
      =O[𝓝[>] (0 : ℝ)] (fun r => r ^ (4 / 3 : ℝ)) := by
  have hz := (positive_rpow_tendsto (by norm_num : (0 : ℝ) < 2 / 3)).mono_right inf_le_left
  have ht := (analytic_taylor_first_bigO C.analyticD).comp_tendsto hz
  apply ht.congr'
  · exact Eventually.of_forall (fun r => by
      simp only [Function.comp_def, C.Dzero, (distanceChart_inverse_deriv C).deriv,
        zero_add, independentDistanceDelta])
  · filter_upwards [eventually_mem_nhdsWithin] with r hr
    dsimp
    rw [← Real.rpow_natCast, ← Real.rpow_mul (show 0 ≤ r from le_of_lt hr)]
    norm_num

theorem transverse_U_z_remainder {I : Set ℝ} (hI : IsOpen I) {S : ℝ} {a V q p : ℝ → ℝ}
    (h : LocalTransverseSolutionOn I S a V q p) (hq : AnalyticAt ℝ q S)
    (C : AnalyticDistanceChart (collisionRadialW q) S (collisionEta a V p S)) :
    (fun z => collisionUProfile q C.D S z -
      (a S - collisionEta a V p S * distanceInverseCoefficient (collisionEta a V p S) ^ 2 * z ^ 2))
      =O[𝓝 (0 : ℝ)] (fun z => z ^ 3) := by
  have hd := distanceChart_inverse_deriv C
  have hU := collisionUProfile_analytic hq C.analyticD C.Dzero
  have h1 := collisionUProfile_first (transverse_q_hasDerivAt_zero h) hd C.Dzero
  have h2 := collisionUProfile_second hq C.analyticD C.Dzero hd
    (transverse_q_hasDerivAt_zero h) (transverse_q_second_hasDerivAt hI h)
  apply (analytic_taylor_second_bigO hU).congr_left
  intro z
  rw [h1.deriv, h2.deriv]
  simp only [collisionUProfile, C.Dzero, sub_zero, h.contact]
  ring

theorem transverse_X_z_remainder {I : Set ℝ} (hI : IsOpen I) {S : ℝ} {a V q p : ℝ → ℝ}
    (h : LocalTransverseSolutionOn I S a V q p) (ha : AnalyticAt ℝ a S) (hq : AnalyticAt ℝ q S)
    (C : AnalyticDistanceChart (collisionRadialW q) S (collisionEta a V p S)) :
    (fun z => collisionXProfile a q C.D S z -
      2 * a S * deriv a S * distanceInverseCoefficient (collisionEta a V p S) * z)
      =O[𝓝 (0 : ℝ)] (fun z => z ^ 2) := by
  have hX := collisionXProfile_analytic ha hq C.analyticD C.Dzero
  have h1 := collisionXProfile_first hI h (distanceChart_inverse_deriv C) C.Dzero
  apply (analytic_taylor_first_bigO hX).congr_left
  intro z
  rw [h1.deriv]
  simp only [collisionXProfile, collisionGap, C.Dzero, sub_zero, h.contact, sub_self, zero_add]

theorem distance_profiles_effective_link {w : ℝ → ℝ} {S η : ℝ}
    (C : AnalyticDistanceChart w S η) (a q : ℝ → ℝ) (r : ℝ) :
    q (independentDistancePoint C r) = collisionUProfile q C.D S (r ^ (2 / 3 : ℝ)) ∧
    collisionGap a q (independentDistancePoint C r) =
      collisionXProfile a q C.D S (r ^ (2 / 3 : ℝ)) := ⟨rfl, rfl⟩

theorem transverse_U_r_remainder {I : Set ℝ} (hI : IsOpen I) {S : ℝ} {a V q p : ℝ → ℝ}
    (h : LocalTransverseSolutionOn I S a V q p) (hq : AnalyticAt ℝ q S)
    (C : AnalyticDistanceChart (collisionRadialW q) S (collisionEta a V p S)) :
    (fun r => q (independentDistancePoint C r) - (a S -
      (3 / 2 : ℝ) ^ (4 / 3 : ℝ) * (collisionEta a V p S) ^ (1 / 3 : ℝ) * r ^ (4 / 3 : ℝ)))
      =O[𝓝[>] (0 : ℝ)] (fun r => r ^ 2) := by
  have hz := (positive_rpow_tendsto (by norm_num : (0 : ℝ) < 2 / 3)).mono_right inf_le_left
  have ht := (transverse_U_z_remainder hI h hq C).comp_tendsto hz
  apply ht.congr'
  · filter_upwards [eventually_mem_nhdsWithin] with r hr
    dsimp [collisionUProfile, independentDistancePoint, independentDistanceDelta]
    rw [puiseux_quadratic_coefficient (collisionEta_pos h), ← Real.rpow_natCast,
      ← Real.rpow_mul (show 0 ≤ r from le_of_lt hr)]
    norm_num
  · filter_upwards [eventually_mem_nhdsWithin] with r hr
    dsimp
    rw [← Real.rpow_natCast, ← Real.rpow_mul (show 0 ≤ r from le_of_lt hr)]
    norm_num

theorem transverse_X_r_remainder {I : Set ℝ} (hI : IsOpen I) {S : ℝ} {a V q p : ℝ → ℝ}
    (h : LocalTransverseSolutionOn I S a V q p) (ha : AnalyticAt ℝ a S) (hq : AnalyticAt ℝ q S)
    (C : AnalyticDistanceChart (collisionRadialW q) S (collisionEta a V p S)) :
    (fun r => collisionGap a q (independentDistancePoint C r) -
      2 * a S * deriv a S * (3 / (2 * Real.sqrt (collisionEta a V p S))) ^ (2 / 3 : ℝ) *
        r ^ (2 / 3 : ℝ)) =O[𝓝[>] (0 : ℝ)] (fun r => r ^ (4 / 3 : ℝ)) := by
  have hz := (positive_rpow_tendsto (by norm_num : (0 : ℝ) < 2 / 3)).mono_right inf_le_left
  have ht := (transverse_X_z_remainder hI h ha hq C).comp_tendsto hz
  apply ht.congr'
  · exact Eventually.of_forall (fun r => by
      simp only [Function.comp_def, collisionXProfile, independentDistancePoint,
        independentDistanceDelta, distanceInverseCoefficient_exact (collisionEta_pos h)])
  · filter_upwards [eventually_mem_nhdsWithin] with r hr
    dsimp
    rw [← Real.rpow_natCast, ← Real.rpow_mul (show 0 ≤ r from le_of_lt hr)]
    norm_num

theorem transverse_curvature_r_remainder {I : Set ℝ} (hI : IsOpen I) {S : ℝ} {a V q p : ℝ → ℝ}
    (h : LocalTransverseSolutionOn I S a V q p)
    (C : AnalyticDistanceChart (collisionRadialW q) S (collisionEta a V p S)) :
    (fun r => radialScalarCurvature (collisionRadialW q) (independentDistancePoint C r) -
      (2 / 9 : ℝ) * r ^ (-2 : ℝ)) =O[𝓝[>] (0 : ℝ)] (fun r => r ^ (-4 / 3 : ℝ)) := by
  have ht := (transverse_curvature_remainders hI h).2.comp_tendsto (independentDistanceDelta_tendsto C)
  apply ht.congr'
  · filter_upwards [independentDistance_identity C] with r hr
    change radialScalarCurvature (collisionRadialW q) (independentDistancePoint C r) -
      (2 / 9 : ℝ) * terminalDistance (collisionRadialW q) S (independentDistancePoint C r) ^ (-2 : ℝ) = _
    rw [hr.2]
  · filter_upwards [independentDistance_identity C] with r hr
    change terminalDistance (collisionRadialW q) S (independentDistancePoint C r) ^ (-4 / 3 : ℝ) = _
    rw [hr.2]

/-- Existence of the convergent profiles uses only endpoint analyticity of a
and q in addition to the unchanged given canonical solution. -/
theorem transverse_convergent_profiles {I : Set ℝ} (hI : IsOpen I) {S : ℝ} {a V q p : ℝ → ℝ}
    (h : LocalTransverseSolutionOn I S a V q p) (ha : AnalyticAt ℝ a S) (hq : AnalyticAt ℝ q S) :
    ∃ C : AnalyticDistanceChart (collisionRadialW q) S (collisionEta a V p S),
      AnalyticAt ℝ (collisionUProfile q C.D S) 0 ∧
      AnalyticAt ℝ (collisionXProfile a q C.D S) 0 ∧
      (∃ ε : ℝ, 0 < ε ∧ ∀ r ∈ Ioo (0 : ℝ) ε,
        0 < independentDistanceDelta C r ∧ independentDistancePoint C r ∈ I ∧
          terminalDistance (collisionRadialW q) S (independentDistancePoint C r) = r) ∧
      ((fun r => q (independentDistancePoint C r) - (a S -
        (3 / 2 : ℝ) ^ (4 / 3 : ℝ) * (collisionEta a V p S) ^ (1 / 3 : ℝ) * r ^ (4 / 3 : ℝ)))
        =O[𝓝[>] (0 : ℝ)] (fun r => r ^ 2)) ∧
      ((fun r => collisionGap a q (independentDistancePoint C r) -
        2 * a S * deriv a S * (3 / (2 * Real.sqrt (collisionEta a V p S))) ^ (2 / 3 : ℝ) *
          r ^ (2 / 3 : ℝ)) =O[𝓝[>] (0 : ℝ)] (fun r => r ^ (4 / 3 : ℝ))) ∧
      ((fun r => radialScalarCurvature (collisionRadialW q) (independentDistancePoint C r) -
        (2 / 9 : ℝ) * r ^ (-2 : ℝ)) =O[𝓝[>] (0 : ℝ)] (fun r => r ^ (-4 / 3 : ℝ))) := by
  obtain ⟨C⟩ := transverse_analyticDistanceChart_exists hI h hq
  exact ⟨C, collisionUProfile_analytic hq C.analyticD C.Dzero,
    collisionXProfile_analytic ha hq C.analyticD C.Dzero,
    independentDistance_interval hI h.S_mem C, transverse_U_r_remainder hI h hq C,
    transverse_X_r_remainder hI h ha hq C, transverse_curvature_r_remainder hI h C⟩

end AffineQuadric
