import AffineQuadric.DistanceScaleBounds

/-! The length-factor profile and its error, parameterized by delta. This does
not construct an independent distance variable or an analytic inverse. -/
noncomputable section
open Set Filter Asymptotics
open scoped Topology
namespace AffineQuadric

def collisionLengthCoefficient (η : ℝ) : ℝ := ((3 / 2 : ℝ) * η) ^ (1 / 3 : ℝ)

theorem positive_cuberoot_cube {x : ℝ} (hx : 0 < x) :
    (x ^ (1 / 3 : ℝ)) ^ 3 = x := by
  calc
    (x ^ (1 / 3 : ℝ)) ^ 3 = x ^ ((1 / 3 : ℝ) * (3 : ℕ)) :=
      (Real.rpow_mul_natCast hx.le _ 3).symm
    _ = x ^ (1 : ℝ) := by congr 1; norm_num
    _ = x := Real.rpow_one x

theorem collisionLengthCoefficient_identity {η : ℝ} (hη : 0 < η) :
    Real.sqrt η / distanceLeadingCoefficient η ^ (1 / 3 : ℝ) = collisionLengthCoefficient η := by
  have hs : 0 < Real.sqrt η := Real.sqrt_pos.mpr hη
  have hc := distanceLeadingCoefficient_pos hη
  have hp : 0 < (3 / 2 : ℝ) * η := mul_pos (by norm_num) hη
  apply (pow_left_inj₀ (div_pos hs (Real.rpow_pos_of_pos hc _)).le
    (Real.rpow_pos_of_pos hp _).le (by decide : (3 : ℕ) ≠ 0)).mp
  rw [div_pow, positive_cuberoot_cube hc]
  rw [positive_cuberoot_cube hp]
  calc
    Real.sqrt η ^ 3 / distanceLeadingCoefficient η =
        (Real.sqrt η ^ 2 * Real.sqrt η) / ((2 / 3 : ℝ) * Real.sqrt η) := by
      dsimp [distanceLeadingCoefficient]
      ring
    _ = (3 / 2 : ℝ) * η := by
      rw [Real.sq_sqrt hη.le]
      field_simp [ne_of_gt hs]

theorem simple_zero_length_ratio_firstOrder {I : Set ℝ} (hI : IsOpen I)
    {S η : ℝ} {w : ℝ → ℝ} (h : SimpleRadialZeroOn I S w η) :
    FirstOrderAtZero (fun δ => radialLambda w (S - δ) /
      terminalDistance w S (S - δ) ^ (1 / 3 : ℝ)) (collisionLengthCoefficient η) := by
  have hc := distanceLeadingCoefficient_pos h.eta_pos
  have hA := firstOrder_sqrt (simple_zero_normalized_firstOrder hI h) h.eta_pos
  have hB := firstOrder_rpow (simple_zero_distance_firstOrder hI h) (ne_of_gt hc) (1 / 3 : ℝ)
  have hF := firstOrder_mul hA (firstOrder_inv hB (ne_of_gt (Real.rpow_pos_of_pos hc _)))
  have hconst : Real.sqrt η * (distanceLeadingCoefficient η ^ (1 / 3 : ℝ))⁻¹ = collisionLengthCoefficient η := by
    simpa only [← div_eq_mul_inv] using collisionLengthCoefficient_identity h.eta_pos
  rw [hconst] at hF
  apply hF.congr' _ (Eventually.of_forall (fun _ => rfl))
  filter_upwards [simple_zero_distance_pos hI h, eventually_mem_nhdsWithin] with δ hρ hδ
  have hp : 0 < δ := hδ
  rw [Real.sqrt_div' _ hp.le, normalized_rpow_identity hp hρ.le,
    show (3 / 2 : ℝ) * (1 / 3) = 1 / 2 by norm_num, ← Real.sqrt_eq_rpow]
  dsimp [radialLambda]
  field_simp [ne_of_gt (Real.sqrt_pos.mpr hp), ne_of_gt (Real.rpow_pos_of_pos hρ (1 / 3 : ℝ))]

theorem simple_zero_length_ratio_tendsto {I : Set ℝ} (hI : IsOpen I)
    {S η : ℝ} {w : ℝ → ℝ} (h : SimpleRadialZeroOn I S w η) :
    Tendsto (fun δ => radialLambda w (S - δ) / terminalDistance w S (S - δ) ^ (1 / 3 : ℝ))
      (𝓝[>] (0 : ℝ)) (𝓝 (collisionLengthCoefficient η)) :=
  firstOrder_tendsto (simple_zero_length_ratio_firstOrder hI h)

theorem simple_zero_length_distance_bigO {I : Set ℝ} (hI : IsOpen I)
    {S η : ℝ} {w : ℝ → ℝ} (h : SimpleRadialZeroOn I S w η) :
    (fun δ => radialLambda w (S - δ) - collisionLengthCoefficient η *
      terminalDistance w S (S - δ) ^ (1 / 3 : ℝ))
      =O[𝓝[>] (0 : ℝ)] (fun δ => terminalDistance w S (S - δ)) := by
  have hR := simple_zero_length_ratio_firstOrder hI h
  have hρhalf : (fun δ => terminalDistance w S (S - δ) ^ (1 / 3 : ℝ))
      =O[𝓝[>] (0 : ℝ)] (fun δ => δ ^ (1 / 2 : ℝ)) := by
    have hb := ((firstOrder_tendsto (simple_zero_distance_firstOrder hI h)).rpow_const
      (p := (1 / 3 : ℝ)) (Or.inl (ne_of_gt (distanceLeadingCoefficient_pos h.eta_pos)))).isBigO_one ℝ
    have hh := hb.mul (isBigO_refl (fun δ : ℝ => δ ^ (1 / 2 : ℝ)) (𝓝[>] (0 : ℝ)))
    apply hh.congr'
    · filter_upwards [simple_zero_distance_pos hI h, eventually_mem_nhdsWithin] with δ hρ hδ
      have hδpos : 0 < δ := hδ
      rw [normalized_rpow_identity hδpos hρ.le, show (3 / 2 : ℝ) * (1 / 3) = 1 / 2 by norm_num]
      exact div_mul_cancel₀ _ (ne_of_gt (Real.rpow_pos_of_pos hδpos (1 / 2 : ℝ)))
    · exact Eventually.of_forall (fun _ => one_mul _)
  have he := hR.mul hρhalf
  have he' : (fun δ => radialLambda w (S - δ) - collisionLengthCoefficient η *
      terminalDistance w S (S - δ) ^ (1 / 3 : ℝ)) =O[𝓝[>] (0 : ℝ)] (fun δ => δ ^ (3 / 2 : ℝ)) := by
    apply he.congr'
    · filter_upwards [simple_zero_distance_pos hI h] with δ hρ
      field_simp [ne_of_gt (Real.rpow_pos_of_pos hρ (1 / 3 : ℝ))]
    · filter_upwards [eventually_mem_nhdsWithin] with δ hδ
      calc
        δ * δ ^ (1 / 2 : ℝ) = δ ^ (1 : ℝ) * δ ^ (1 / 2 : ℝ) := by rw [Real.rpow_one]
        _ = δ ^ ((1 : ℝ) + 1 / 2) := (Real.rpow_add (show 0 < δ from hδ) _ _).symm
        _ = δ ^ (3 / 2 : ℝ) := by congr 1; norm_num
  have hs : (fun δ : ℝ => δ ^ (3 / 2 : ℝ)) =O[𝓝[>] (0 : ℝ)]
      (fun δ => terminalDistance w S (S - δ)) := by
    simpa using simple_zero_parameter_scale_bigO hI h (1 : ℝ)
  exact he'.trans hs

end AffineQuadric
