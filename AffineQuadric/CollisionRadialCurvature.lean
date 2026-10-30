import AffineQuadric.CollisionDistance
import Mathlib.Topology.Algebra.Order.Field

/-! Scalar radial derivative and leading singularity. Identification with
Riemannian sectional curvature is a separate geometric input. -/
noncomputable section
open Set Filter
open scoped Topology ContDiff
namespace AffineQuadric

def radialDerivative (w f : ℝ → ℝ) (s : ℝ) : ℝ := -deriv f s / radialLambda w s
def radialScalarCurvature (w : ℝ → ℝ) (s : ℝ) : ℝ :=
  -radialDerivative w (radialDerivative w (radialLambda w)) s / radialLambda w s
def radialCurvatureQuotient (w : ℝ → ℝ) (s : ℝ) : ℝ :=
  (deriv w s ^ 2 - w s * deriv (deriv w) s) / (2 * w s ^ 3)

theorem radialLambda_hasDerivAt {I : Set ℝ} (hI : IsOpen I) {w : ℝ → ℝ}
    (hw : ContDiffOn ℝ ∞ w I) {s : ℝ} (hs : s ∈ I) (hpos : 0 < w s) :
    HasDerivAt (radialLambda w) (deriv w s / (2 * Real.sqrt (w s))) s :=
  (smooth_hasDerivAt_on_open hI hw hs).sqrt (ne_of_gt hpos)

theorem radialDerivative_lambda_eq {I : Set ℝ} (hI : IsOpen I) {w : ℝ → ℝ}
    (hw : ContDiffOn ℝ ∞ w I) {s : ℝ} (hs : s ∈ I) (hpos : 0 < w s) :
    radialDerivative w (radialLambda w) s = -deriv w s / (2 * w s) := by
  unfold radialDerivative
  rw [(radialLambda_hasDerivAt hI hw hs hpos).deriv]
  dsimp [radialLambda]
  have hn := ne_of_gt hpos
  have hr := ne_of_gt (Real.sqrt_pos.mpr hpos)
  field_simp
  ring_nf
  rw [Real.sq_sqrt hpos.le]

theorem radialDerivative_lambda_hasDerivAt {I : Set ℝ} (hI : IsOpen I) {w : ℝ → ℝ}
    (hw : ContDiffOn ℝ ∞ w I) {s : ℝ} (hs : s ∈ I) (hpos : 0 < w s) :
    HasDerivAt (radialDerivative w (radialLambda w))
      ((-deriv (deriv w) s * (2 * w s) - -deriv w s * (2 * deriv w s)) / (2 * w s) ^ 2) s := by
  have hd := (smooth_hasDerivAt_on_open hI (smooth_deriv_on_open hI hw) hs).neg.div
    ((smooth_hasDerivAt_on_open hI hw hs).const_mul 2) (mul_ne_zero (by norm_num) (ne_of_gt hpos))
  have he : radialDerivative w (radialLambda w) =ᶠ[𝓝 s] (fun x => -deriv w x / (2 * w x)) := by
    filter_upwards [hI.mem_nhds hs, (smooth_hasDerivAt_on_open hI hw hs).continuousAt.eventually
      (Ioi_mem_nhds hpos)] with x hx hp
    exact radialDerivative_lambda_eq hI hw hx hp
  exact hd.congr_of_eventuallyEq he

theorem radialScalarCurvature_eq {I : Set ℝ} (hI : IsOpen I) {w : ℝ → ℝ}
    (hw : ContDiffOn ℝ ∞ w I) {s : ℝ} (hs : s ∈ I) (hpos : 0 < w s) :
    radialScalarCurvature w s = radialCurvatureQuotient w s := by
  change -(-deriv (radialDerivative w (radialLambda w)) s / radialLambda w s) /
    radialLambda w s = radialCurvatureQuotient w s
  rw [(radialDerivative_lambda_hasDerivAt hI hw hs hpos).deriv]
  dsimp [radialLambda, radialCurvatureQuotient]
  have hn := ne_of_gt hpos
  have hr := ne_of_gt (Real.sqrt_pos.mpr hpos)
  field_simp
  ring_nf
  rw [Real.sq_sqrt hpos.le]
  ring

theorem three_halves_square {δ : ℝ} (hδ : 0 < δ) :
    (δ ^ (3 / 2 : ℝ)) ^ 2 = δ ^ 3 := by
  calc
    (δ ^ (3 / 2 : ℝ)) ^ 2 = δ ^ ((3 / 2 : ℝ) * (2 : ℕ)) :=
      (Real.rpow_mul_natCast hδ.le _ 2).symm
    _ = δ ^ ((3 : ℕ) : ℝ) := by congr 1; norm_num
    _ = δ ^ 3 := Real.rpow_natCast _ _

theorem simple_zero_curvature_coefficient {I : Set ℝ} (hI : IsOpen I)
    {S η : ℝ} {w : ℝ → ℝ} (h : SimpleRadialZeroOn I S w η) :
    Tendsto (fun δ => terminalDistance w S (S - δ) ^ 2 * radialScalarCurvature w (S - δ))
      (𝓝[>] (0 : ℝ)) (𝓝 (2 / 9 : ℝ)) := by
  have hη : 0 < η := h.eta_pos
  have hw0 : Tendsto (fun δ => w (S - δ)) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    simpa [h.zero] using h.rate.continuousAt.tendsto.comp (endpoint_parameter_tendsto S)
  have hw1 : Tendsto (fun δ => deriv w (S - δ)) (𝓝[>] (0 : ℝ)) (𝓝 (-η)) := by
    simpa only [h.rate.deriv] using
      (smooth_hasDerivAt_on_open hI (smooth_deriv_on_open hI h.smooth_w) h.S_mem).continuousAt.tendsto.comp
        (endpoint_parameter_tendsto S)
  have hw2 := (smooth_hasDerivAt_on_open hI
    (smooth_deriv_on_open hI (smooth_deriv_on_open hI h.smooth_w)) h.S_mem).continuousAt.tendsto.comp
      (endpoint_parameter_tendsto S)
  have hwr : Tendsto (fun δ => w (S - δ) / δ) (𝓝[>] (0 : ℝ)) (𝓝 η) := by
    simpa using terminal_linear_rate h.rate h.zero
  have hnum := (hw1.pow 2).sub (hw0.mul hw2)
  have hnorm := ((simple_zero_distance_rate hI h).pow 2).mul
    (hnum.div ((hwr.pow 3).const_mul 2) (by positivity : (2 : ℝ) * η ^ 3 ≠ 0))
  have hc : ((2 / 3 : ℝ) * Real.sqrt η) ^ 2 *
      ((-η) ^ 2 - 0 * deriv (deriv w) S) / (2 * η ^ 3) = (2 / 9 : ℝ) := by
    rw [mul_pow, Real.sq_sqrt h.eta_pos.le]
    field_simp [ne_of_gt hη]
    ring
  have hlim : Tendsto
      (fun δ => (terminalDistance w S (S - δ) / δ ^ (3 / 2 : ℝ)) ^ 2 *
        ((deriv w (S - δ) ^ 2 - w (S - δ) * deriv (deriv w) (S - δ)) /
          (2 * (w (S - δ) / δ) ^ 3))) (𝓝[>] (0 : ℝ)) (𝓝 (2 / 9 : ℝ)) := by
    convert hnorm using 1
    congr 1
    simpa only [mul_div_assoc] using hc.symm
  apply hlim.congr'
  have hcross := simple_zero_sign_crossing h.rate h.zero (neg_neg_of_pos h.eta_pos)
  filter_upwards [hcross, (endpoint_parameter_tendsto S).eventually (hI.mem_nhds h.S_mem),
    eventually_mem_nhdsWithin] with δ hwpos hδI hδ
  have hδpos : 0 < δ := hδ
  rw [radialScalarCurvature_eq hI h.smooth_w hδI hwpos.1]
  dsimp [radialCurvatureQuotient]
  rw [div_pow, three_halves_square hδpos, div_pow]
  field_simp [ne_of_gt hδpos, ne_of_gt hwpos.1]

theorem simple_zero_distance_tendsto_zero {I : Set ℝ} (hI : IsOpen I)
    {S η : ℝ} {w : ℝ → ℝ} (h : SimpleRadialZeroOn I S w η) :
    Tendsto (fun δ => terminalDistance w S (S - δ)) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  have hp : Tendsto (fun δ : ℝ => δ ^ (3 / 2 : ℝ)) (𝓝[>] 0) (𝓝 0) := by
    simpa using (tendsto_id.mono_left (inf_le_left : 𝓝[>] (0 : ℝ) ≤ 𝓝 0)).rpow_const
      (Or.inr (by norm_num : (0 : ℝ) ≤ 3 / 2))
  have hh := (simple_zero_distance_rate hI h).mul hp
  have hh' : Tendsto (fun δ => terminalDistance w S (S - δ) / δ ^ (3 / 2 : ℝ) * δ ^ (3 / 2 : ℝ))
      (𝓝[>] 0) (𝓝 (0 : ℝ)) := by simpa using hh
  apply hh'.congr'
  filter_upwards [eventually_mem_nhdsWithin] with δ hδ
  exact div_mul_cancel₀ _ (ne_of_gt (Real.rpow_pos_of_pos (show 0 < δ from hδ) _))

theorem simple_zero_curvature_tendsto_atTop {I : Set ℝ} (hI : IsOpen I)
    {S η : ℝ} {w : ℝ → ℝ} (h : SimpleRadialZeroOn I S w η) :
    Tendsto (fun δ => radialScalarCurvature w (S - δ)) (𝓝[>] (0 : ℝ)) atTop := by
  have hρ2 : Tendsto (fun δ => terminalDistance w S (S - δ) ^ 2)
      (𝓝[>] (0 : ℝ)) (𝓝[>] (0 : ℝ)) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨by simpa using (simple_zero_distance_tendsto_zero hI h).pow 2, ?_⟩
    exact (simple_zero_distance_pos hI h).mono (fun _ hx => sq_pos_of_pos hx)
  have hh := (simple_zero_curvature_coefficient hI h).pos_mul_atTop (by norm_num : (0 : ℝ) < 2 / 9)
    hρ2.inv_tendsto_nhdsGT_zero
  apply hh.congr'
  filter_upwards [simple_zero_distance_pos hI h] with δ hδ
  change terminalDistance w S (S - δ) ^ 2 * radialScalarCurvature w (S - δ) *
    (terminalDistance w S (S - δ) ^ 2)⁻¹ = radialScalarCurvature w (S - δ)
  field_simp [ne_of_gt hδ]

end AffineQuadric
