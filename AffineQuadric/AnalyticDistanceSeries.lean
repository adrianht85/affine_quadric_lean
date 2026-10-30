import AffineQuadric.AnalyticCollisionFactor

/-! The only series multiplier needed for the distance factor. Its coefficients
are divided by n + 3/2; the convergence radius does not decrease. -/
noncomputable section
open Set Filter
open scoped Topology
namespace AffineQuadric

def distanceFactorSeries (p : FormalMultilinearSeries ℝ ℝ ℝ) :
    FormalMultilinearSeries ℝ ℝ ℝ :=
  fun n => ((n : ℝ) + 3 / 2)⁻¹ • p n

theorem distanceFactorSeries_radius (p : FormalMultilinearSeries ℝ ℝ ℝ) :
    p.radius ≤ (distanceFactorSeries p).radius := by
  apply FormalMultilinearSeries.radius_le_of_le
  intro n
  dsimp [distanceFactorSeries]
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity : 0 < ((n : ℝ) + 3 / 2)⁻¹)]
  exact mul_le_of_le_one_left (norm_nonneg _)
    (inv_le_one_of_one_le₀ (by have := Nat.cast_nonneg (α := ℝ) n; linarith))

theorem distanceFactorSeries_coeff (p : FormalMultilinearSeries ℝ ℝ ℝ) (n : ℕ) :
    (distanceFactorSeries p).coeff n = ((n : ℝ) + 3 / 2)⁻¹ * p.coeff n := by
  rfl

theorem analytic_distance_euler {B : ℝ → ℝ} (hB : AnalyticAt ℝ B 0) :
    ∃ F : ℝ → ℝ, AnalyticAt ℝ F 0 ∧ F 0 = (2 / 3 : ℝ) * B 0 ∧
      ∀ᶠ x in 𝓝 (0 : ℝ), (3 / 2 : ℝ) * F x + x * deriv F x = B x := by
  obtain ⟨p, r, hp⟩ := hB
  let q := distanceFactorSeries p
  have hqpos : 0 < q.radius := lt_of_lt_of_le hp.r_pos (hp.r_le.trans (distanceFactorSeries_radius p))
  have hq := q.hasFPowerSeriesOnBall hqpos
  refine ⟨q.sum, hq.analyticAt, ?_, ?_⟩
  · have hc := hq.coeff_zero (fun _ => (1 : ℝ))
    have hb := hp.coeff_zero (fun _ => (1 : ℝ))
    change q.coeff 0 = q.sum 0 at hc
    change p.coeff 0 = B 0 at hb
    rw [← hc, distanceFactorSeries_coeff, hb]
    norm_num
  · have hsF := hasFPowerSeriesAt_iff.mp hq.hasFPowerSeriesAt
    have hsB := hasFPowerSeriesAt_iff.mp hp.hasFPowerSeriesAt
    have hsD := hasFPowerSeriesAt_iff.mp hq.fderiv.hasFPowerSeriesAt
    filter_upwards [hsF, hsB, hsD] with x hF hB hD
    simp only [zero_add, smul_eq_mul] at hF hB
    have hd : HasSum (fun n : ℕ => x ^ n * ((n + 1 : ℕ) : ℝ) * q.coeff (n + 1))
        (deriv q.sum x) := by
      have hh := (ContinuousLinearMap.apply ℝ ℝ (1 : ℝ)).hasSum hD
      simpa only [ContinuousLinearMap.apply_apply, map_smul, zero_add,
        FormalMultilinearSeries.derivSeries_coeff_one, deriv, nsmul_eq_mul,
        smul_eq_mul, mul_assoc] using hh
    have hx : HasSum (fun n : ℕ => (n : ℝ) * x ^ n * q.coeff n) (x * deriv q.sum x) := by
      have hh := hd.mul_left x
      have ht : HasSum (fun n : ℕ => ((n + 1 : ℕ) : ℝ) * x ^ (n + 1) * q.coeff (n + 1))
          (x * deriv q.sum x) := by
        convert hh using 1
        funext n
        ring
      apply (hasSum_nat_add_iff' (f := fun n : ℕ => (n : ℝ) * x ^ n * q.coeff n) 1).mp
      simpa only [Finset.sum_range_one, Nat.cast_zero, zero_mul, sub_zero] using ht
    have he := (hF.mul_left (3 / 2 : ℝ)).add hx
    have hterms : (fun n : ℕ => (3 / 2 : ℝ) * (x ^ n * q.coeff n) +
        (n : ℝ) * x ^ n * q.coeff n) = (fun n => x ^ n * p.coeff n) := by
      funext n
      dsimp [q]
      rw [distanceFactorSeries_coeff]
      have hn : (n : ℝ) + 3 / 2 ≠ 0 := by positivity
      field_simp
      ring
    rw [hterms] at he
    exact he.unique hB

end AffineQuadric
