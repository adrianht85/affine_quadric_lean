import AffineQuadric.DistanceScaleBounds

/-! Stage 3: precise scalar curvature error, using the previously proved
radial-derivative identity and the actual distance integral. -/
noncomputable section
open Set Filter Asymptotics
open scoped Topology
namespace AffineQuadric

theorem simple_zero_normalized_curvature_firstOrder {I : Set ℝ} (hI : IsOpen I)
    {S η : ℝ} {w : ℝ → ℝ} (h : SimpleRadialZeroOn I S w η) :
    FirstOrderAtZero (fun δ => δ ^ 3 * radialScalarCurvature w (S - δ)) (1 / (2 * η)) := by
  have hη : 0 < η := h.eta_pos
  have hW := simple_zero_normalized_firstOrder hI h
  have hP := simple_zero_wprime_firstOrder hI h
  have hQ : FirstOrderAtZero (fun δ => δ * deriv (deriv w) (S - δ)) 0 := by
    have hh := (isBigO_refl (fun δ : ℝ => δ) (𝓝[>] (0 : ℝ))).mul (simple_zero_wsecond_bounded hI h)
    simpa [FirstOrderAtZero] using hh
  have hN := firstOrder_sub (firstOrder_pow hP 2) (firstOrder_mul hW hQ)
  have hD := firstOrder_inv (firstOrder_mul (firstOrder_const (2 : ℝ)) (firstOrder_pow hW 3))
    (by positivity : (2 : ℝ) * η ^ 3 ≠ 0)
  have hF := firstOrder_mul hN hD
  have hc : ((-η) ^ 2 - η * 0) * (2 * η ^ 3)⁻¹ = 1 / (2 * η) := by
    field_simp [ne_of_gt hη]
    ring
  rw [hc] at hF
  apply hF.congr' _ (Eventually.of_forall (fun _ => rfl))
  have hwpos := simple_zero_sign_crossing h.rate h.zero (neg_neg_of_pos hη)
  filter_upwards [hwpos, (endpoint_parameter_tendsto S).eventually (hI.mem_nhds h.S_mem),
    eventually_mem_nhdsWithin] with δ hw hδI hδ
  rw [radialScalarCurvature_eq hI h.smooth_w hδI hw.1]
  dsimp [radialCurvatureQuotient]
  have hp : 0 < δ := hδ
  field_simp [ne_of_gt hp, ne_of_gt hw.1]

theorem simple_zero_curvature_parameter_bigO {I : Set ℝ} (hI : IsOpen I)
    {S η : ℝ} {w : ℝ → ℝ} (h : SimpleRadialZeroOn I S w η) :
    (fun δ => radialScalarCurvature w (S - δ) - (1 / (2 * η)) * δ ^ (-3 : ℝ))
      =O[𝓝[>] (0 : ℝ)] (fun δ => δ ^ (-2 : ℝ)) := by
  have hf : (fun δ => radialScalarCurvature w (S - δ) / δ ^ (-3 : ℝ) - 1 / (2 * η))
      =O[𝓝[>] (0 : ℝ)] (fun δ => δ ^ (1 : ℝ)) := by
    apply (simple_zero_normalized_curvature_firstOrder hI h).congr'
    · filter_upwards [eventually_mem_nhdsWithin] with δ hδ
      have hp : 0 < δ := hδ
      rw [show (-3 : ℝ) = -(3 : ℝ) by norm_num, Real.rpow_neg hp.le]
      norm_num [Real.rpow_natCast]
      ring
    · exact Eventually.of_forall (fun δ => (Real.rpow_one δ).symm)
  have hh := rpow_error_denormalize (a := (-3 : ℝ)) (b := (1 : ℝ)) hf
  simpa only [show (-3 : ℝ) + 1 = -2 by norm_num] using hh

theorem simple_zero_distance_inverse_square_bigO {I : Set ℝ} (hI : IsOpen I)
    {S η : ℝ} {w : ℝ → ℝ} (h : SimpleRadialZeroOn I S w η) :
    (fun δ => terminalDistance w S (S - δ) ^ (-2 : ℝ) -
      distanceLeadingCoefficient η ^ (-2 : ℝ) * δ ^ (-3 : ℝ))
      =O[𝓝[>] (0 : ℝ)] (fun δ => δ ^ (-2 : ℝ)) := by
  have hc := distanceLeadingCoefficient_pos h.eta_pos
  have hR := firstOrder_rpow (simple_zero_distance_firstOrder hI h) (ne_of_gt hc) (-2 : ℝ)
  have hf : (fun δ => terminalDistance w S (S - δ) ^ (-2 : ℝ) / δ ^ (-3 : ℝ) -
      distanceLeadingCoefficient η ^ (-2 : ℝ)) =O[𝓝[>] (0 : ℝ)] (fun δ => δ ^ (1 : ℝ)) := by
    apply hR.congr'
    · filter_upwards [simple_zero_distance_pos hI h, eventually_mem_nhdsWithin] with δ hρ hδ
      rw [normalized_rpow_identity (show 0 < δ from hδ) hρ.le,
        show (3 / 2 : ℝ) * -2 = -3 by norm_num]
    · exact Eventually.of_forall (fun δ => (Real.rpow_one δ).symm)
  have hh := rpow_error_denormalize (a := (-3 : ℝ)) (b := (1 : ℝ)) hf
  simpa only [show (-3 : ℝ) + 1 = -2 by norm_num] using hh

theorem distance_curvature_coefficient_identity {η : ℝ} (hη : 0 < η) :
    (2 / 9 : ℝ) * distanceLeadingCoefficient η ^ (-2 : ℝ) = 1 / (2 * η) := by
  have hc := distanceLeadingCoefficient_pos hη
  rw [show (-2 : ℝ) = -(2 : ℝ) by norm_num, Real.rpow_neg hc.le, Real.rpow_two]
  dsimp [distanceLeadingCoefficient]
  rw [mul_pow, Real.sq_sqrt hη.le]
  field_simp [ne_of_gt hη]
  ring

theorem simple_zero_curvature_distance_bigO {I : Set ℝ} (hI : IsOpen I)
    {S η : ℝ} {w : ℝ → ℝ} (h : SimpleRadialZeroOn I S w η) :
    (fun δ => radialScalarCurvature w (S - δ) -
      (2 / 9 : ℝ) * terminalDistance w S (S - δ) ^ (-2 : ℝ))
      =O[𝓝[>] (0 : ℝ)] (fun δ => terminalDistance w S (S - δ) ^ (-4 / 3 : ℝ)) := by
  have he := (simple_zero_curvature_parameter_bigO hI h).sub
    ((simple_zero_distance_inverse_square_bigO hI h).const_mul_left (2 / 9 : ℝ))
  have hp : (fun δ => radialScalarCurvature w (S - δ) -
      (2 / 9 : ℝ) * terminalDistance w S (S - δ) ^ (-2 : ℝ))
      =O[𝓝[>] (0 : ℝ)] (fun δ => δ ^ (-2 : ℝ)) := by
    apply he.congr_left
    intro δ
    have hc := distance_curvature_coefficient_identity h.eta_pos
    linear_combination (δ ^ (-3 : ℝ)) * hc
  have hs := simple_zero_parameter_scale_bigO hI h (-4 / 3 : ℝ)
  have hs' : (fun δ : ℝ => δ ^ (-2 : ℝ)) =O[𝓝[>] (0 : ℝ)]
      (fun δ => terminalDistance w S (S - δ) ^ (-4 / 3 : ℝ)) := by
    simpa only [show (3 / 2 : ℝ) * (-4 / 3) = -2 by norm_num] using hs
  exact hp.trans hs'

end AffineQuadric
