import AffineQuadric.SimpleZeroRemainders

/-! Positive two-sided scale comparisons along the endpoint parameter.
No inverse function of distance is asserted. -/
noncomputable section
open Set Filter Asymptotics
open scoped Topology
namespace AffineQuadric

theorem normalized_rpow_identity {x δ : ℝ} (hδ : 0 < δ) (hx : 0 ≤ x) (p r : ℝ) :
    (x / δ ^ p) ^ r = x ^ r / δ ^ (p * r) := by
  rw [Real.div_rpow hx (Real.rpow_nonneg hδ.le p), ← Real.rpow_mul hδ.le]

theorem positive_ratio_bounds {f g : ℝ → ℝ} {c : ℝ} (hc : 0 < c)
    (hlim : Tendsto (fun δ => f δ / g δ) (𝓝[>] (0 : ℝ)) (𝓝 c))
    (hg : ∀ᶠ δ in 𝓝[>] (0 : ℝ), 0 < g δ) :
    ∃ L U : ℝ, 0 < L ∧ 0 < U ∧ ∀ᶠ δ in 𝓝[>] (0 : ℝ), L * g δ ≤ f δ ∧ f δ ≤ U * g δ := by
  refine ⟨c / 2, 2 * c, by positivity, by positivity, ?_⟩
  have he := hlim.eventually (Ioo_mem_nhds (by linarith : c / 2 < c) (by linarith : c < 2 * c))
  filter_upwards [he, hg] with δ hδ hp
  exact ⟨((lt_div_iff₀ hp).mp hδ.1).le, ((div_lt_iff₀ hp).mp hδ.2).le⟩

theorem distanceLeadingCoefficient_pos {η : ℝ} (hη : 0 < η) : 0 < distanceLeadingCoefficient η :=
  mul_pos (by norm_num) (Real.sqrt_pos.mpr hη)

theorem simple_zero_distance_scale_bounds {I : Set ℝ} (hI : IsOpen I) {S η : ℝ} {w : ℝ → ℝ}
    (h : SimpleRadialZeroOn I S w η) :
    (∃ L U : ℝ, 0 < L ∧ 0 < U ∧ ∀ᶠ δ in 𝓝[>] (0 : ℝ),
      L * δ ^ (3 / 2 : ℝ) ≤ terminalDistance w S (S - δ) ∧
      terminalDistance w S (S - δ) ≤ U * δ ^ (3 / 2 : ℝ)) ∧
    (∃ A B : ℝ, 0 < A ∧ 0 < B ∧ ∀ᶠ δ in 𝓝[>] (0 : ℝ),
      A * terminalDistance w S (S - δ) ^ (2 / 3 : ℝ) ≤ δ ∧
      δ ≤ B * terminalDistance w S (S - δ) ^ (2 / 3 : ℝ)) := by
  have hc := distanceLeadingCoefficient_pos h.eta_pos
  have hr := firstOrder_tendsto (simple_zero_distance_firstOrder hI h)
  refine ⟨positive_ratio_bounds hc hr ?_, ?_⟩
  · exact eventually_mem_nhdsWithin.mono (fun δ hδ => Real.rpow_pos_of_pos (show 0 < δ from hδ) _)
  · have hp := hr.rpow_const (p := (2 / 3 : ℝ)) (Or.inl (ne_of_gt hc))
    have hp' : Tendsto (fun δ => terminalDistance w S (S - δ) ^ (2 / 3 : ℝ) / δ)
        (𝓝[>] (0 : ℝ)) (𝓝 (distanceLeadingCoefficient η ^ (2 / 3 : ℝ))) := by
      apply hp.congr'
      filter_upwards [simple_zero_distance_pos hI h, eventually_mem_nhdsWithin] with δ hρ hδ
      rw [normalized_rpow_identity (show 0 < δ from hδ) hρ.le,
        show (3 / 2 : ℝ) * (2 / 3) = 1 by norm_num, Real.rpow_one]
    have hi : Tendsto (fun δ => δ / terminalDistance w S (S - δ) ^ (2 / 3 : ℝ))
        (𝓝[>] (0 : ℝ)) (𝓝 ((distanceLeadingCoefficient η ^ (2 / 3 : ℝ))⁻¹)) := by
      simpa only [inv_div] using hp'.inv₀ (ne_of_gt (Real.rpow_pos_of_pos hc _))
    apply positive_ratio_bounds (inv_pos.mpr (Real.rpow_pos_of_pos hc _)) hi
    exact (simple_zero_distance_pos hI h).mono (fun δ hδ => Real.rpow_pos_of_pos hδ _)

theorem simple_zero_parameter_scale_bigO {I : Set ℝ} (hI : IsOpen I) {S η : ℝ} {w : ℝ → ℝ}
    (h : SimpleRadialZeroOn I S w η) (r : ℝ) :
    (fun δ => δ ^ ((3 / 2 : ℝ) * r)) =O[𝓝[>] (0 : ℝ)]
      (fun δ => terminalDistance w S (S - δ) ^ r) := by
  have hc := distanceLeadingCoefficient_pos h.eta_pos
  have hb := ((firstOrder_tendsto (simple_zero_distance_firstOrder hI h)).rpow_const
    (p := -r) (Or.inl (ne_of_gt hc))).isBigO_one ℝ
  have hh := hb.mul (isBigO_refl (fun δ => terminalDistance w S (S - δ) ^ r) (𝓝[>] (0 : ℝ)))
  apply hh.congr'
  · filter_upwards [simple_zero_distance_pos hI h, eventually_mem_nhdsWithin] with δ hρ hδ
    have hδpos : 0 < δ := hδ
    rw [Real.rpow_neg (div_pos hρ (Real.rpow_pos_of_pos hδpos _)).le,
      normalized_rpow_identity hδpos hρ.le]
    field_simp [ne_of_gt (Real.rpow_pos_of_pos hρ r)]
  · exact Eventually.of_forall (fun δ => one_mul _)

end AffineQuadric
