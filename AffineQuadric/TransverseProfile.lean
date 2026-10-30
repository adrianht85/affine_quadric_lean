import AffineQuadric.TransverseCollision
import AffineQuadric.EndpointRates

/-! Principal transverse rates and the admissible side of a given local solution.
No Taylor big-O estimate or analytic continuation is asserted. -/
noncomputable section
open Set Filter
open scoped Topology ContDiff
namespace AffineQuadric

theorem transverse_terminal_rates {I : Set ℝ} (hI : IsOpen I)
    {S : ℝ} {a V q p : ℝ → ℝ} (h : LocalTransverseSolutionOn I S a V q p) :
    Tendsto (fun δ => (a S - q (S - δ)) / δ ^ 2) (𝓝[>] (0 : ℝ)) (𝓝 (collisionEta a V p S)) ∧
    Tendsto (fun δ => deriv q (S - δ) / δ) (𝓝[>] (0 : ℝ)) (𝓝 (2 * collisionEta a V p S)) ∧
    Tendsto (fun δ => collisionGap a q (S - δ) / δ) (𝓝[>] (0 : ℝ)) (𝓝 (2 * a S * deriv a S)) := by
  have hq := transverse_q_hasDerivAt_zero h
  have hq2 := transverse_q_second_hasDerivAt hI h
  refine ⟨?_, ?_, ?_⟩
  · have hh := terminal_quadratic_rate hI h.smooth_q h.S_mem hq.deriv hq2
    simpa [h.contact] using hh
  · simpa using terminal_linear_rate hq2 hq.deriv
  · simpa using terminal_linear_rate (collisionGap_hasDerivAt hI h)
      (by simp [collisionGap, h.contact])

theorem transverse_side_neighborhood {I : Set ℝ} (hI : IsOpen I)
    {S : ℝ} {a V q p : ℝ → ℝ} (h : LocalTransverseSolutionOn I S a V q p) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ δ ∈ Ioo 0 ε,
      S - δ ∈ I ∧ S + δ ∈ I ∧
      0 < p (S - δ) ∧ 0 < p (S + δ) ∧ 0 < V (S - δ) ∧ 0 < V (S + δ) ∧
      0 < collisionGap a q (S - δ) ∧ collisionGap a q (S + δ) < 0 ∧ q (S - δ) > a (S - δ) := by
  have hp := (smooth_hasDerivAt_on_open hI h.smooth_p h.S_mem).continuousAt
  have hV := (smooth_hasDerivAt_on_open hI h.smooth_V h.S_mem).continuousAt
  have hsum := ((smooth_hasDerivAt_on_open hI h.smooth_q h.S_mem).continuousAt.add
    (smooth_hasDerivAt_on_open hI h.smooth_a h.S_mem).continuousAt)
  have hsumpos : 0 < q S + a S := by rw [h.contact]; linarith [h.a_pos]
  have hleft := endpoint_parameter_tendsto S
  have hright : Tendsto (fun δ : ℝ => S + δ) (𝓝[>] (0 : ℝ)) (𝓝 S) := by
    simpa using (tendsto_const_nhds (x := S)).add
      (tendsto_id.mono_left (inf_le_left : 𝓝[>] (0 : ℝ) ≤ 𝓝 0))
  have hevent : ∀ᶠ δ in 𝓝[>] (0 : ℝ),
      S - δ ∈ I ∧ S + δ ∈ I ∧
      0 < p (S - δ) ∧ 0 < p (S + δ) ∧ 0 < V (S - δ) ∧ 0 < V (S + δ) ∧
      0 < collisionGap a q (S - δ) ∧ collisionGap a q (S + δ) < 0 ∧ q (S - δ) > a (S - δ) := by
    have hcross := simple_zero_sign_crossing (collisionGap_hasDerivAt hI h)
      (by simp [collisionGap, h.contact]) (by nlinarith [h.a_pos, h.a_rate_pos])
    filter_upwards [hleft.eventually (hI.mem_nhds h.S_mem), hright.eventually (hI.mem_nhds h.S_mem),
      (hp.tendsto.comp hleft).eventually (Ioi_mem_nhds h.p_pos),
      (hp.tendsto.comp hright).eventually (Ioi_mem_nhds h.p_pos),
      (hV.tendsto.comp hleft).eventually (Ioi_mem_nhds h.V_pos),
      (hV.tendsto.comp hright).eventually (Ioi_mem_nhds h.V_pos),
      (hsum.tendsto.comp hleft).eventually (Ioi_mem_nhds hsumpos), hcross] with δ hl hr hpl hpr hVl hVr hsumδ hx
    refine ⟨hl, hr, hpl, hpr, hVl, hVr, hx.1, hx.2, ?_⟩
    have hprod : 0 < (q (S - δ) - a (S - δ)) * (q (S - δ) + a (S - δ)) := by
      dsimp [collisionGap] at hx
      nlinarith [hx.1]
    have hh := (mul_pos_iff_of_pos_right hsumδ).mp hprod
    linarith
  rcases mem_nhdsGT_iff_exists_Ioo_subset.mp hevent with ⟨ε, hε, he⟩
  exact ⟨ε, hε, fun δ hδ => he hδ⟩

def collisionRadialW (q : ℝ → ℝ) (s : ℝ) : ℝ := deriv q s / 2

theorem collisionRadialW_smooth {I : Set ℝ} (hI : IsOpen I)
    {S : ℝ} {a V q p : ℝ → ℝ} (h : LocalTransverseSolutionOn I S a V q p) :
    ContDiffOn ℝ ∞ (collisionRadialW q) I :=
  (smooth_deriv_on_open hI h.smooth_q).div_const 2

theorem collisionRadialW_terminal {I : Set ℝ} (hI : IsOpen I)
    {S : ℝ} {a V q p : ℝ → ℝ} (h : LocalTransverseSolutionOn I S a V q p) :
    collisionRadialW q S = 0 ∧
    HasDerivAt (collisionRadialW q) (-collisionEta a V p S) S ∧
    Tendsto (fun δ => collisionRadialW q (S - δ) / δ) (𝓝[>] (0 : ℝ)) (𝓝 (collisionEta a V p S)) := by
  have hz : collisionRadialW q S = 0 := by simp [collisionRadialW, (transverse_q_hasDerivAt_zero h).deriv]
  have hd : HasDerivAt (collisionRadialW q) (-collisionEta a V p S) S := by
    convert (transverse_q_second_hasDerivAt hI h).div_const 2 using 1; ring
  exact ⟨hz, hd, by simpa using terminal_linear_rate hd hz⟩

end AffineQuadric
