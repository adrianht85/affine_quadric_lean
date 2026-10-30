import AffineQuadric.QuadraticIntegration
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.LHopital

/-! Principal one-sided rates. These are limits, not estimates for Taylor remainders. -/
noncomputable section
open Set Filter
open scoped Topology ContDiff
namespace AffineQuadric

theorem right_linear_rate {f : ℝ → ℝ} {d : ℝ} (hf : HasDerivAt f d 0) (h0 : f 0 = 0) :
    Tendsto (fun δ => f δ / δ) (𝓝[>] (0 : ℝ)) (𝓝 d) := by
  simpa [h0, smul_eq_mul, div_eq_mul_inv, mul_comm] using hf.tendsto_slope_zero_right

theorem endpoint_parameter_tendsto (S : ℝ) :
    Tendsto (fun δ : ℝ => S - δ) (𝓝[>] (0 : ℝ)) (𝓝 S) := by
  simpa using (tendsto_const_nhds (x := S)).sub
    (tendsto_id.mono_left (inf_le_left : 𝓝[>] (0 : ℝ) ≤ 𝓝 0))

theorem terminal_linear_rate {f : ℝ → ℝ} {S d : ℝ}
    (hf : HasDerivAt f d S) (h0 : f S = 0) :
    Tendsto (fun δ => f (S - δ) / δ) (𝓝[>] (0 : ℝ)) (𝓝 (-d)) := by
  have hd : HasDerivAt (fun δ => f (S - δ)) (-d) 0 := by
    have hf' : HasDerivAt f d (S - (0 : ℝ)) := by simpa using hf
    convert hf'.comp 0 ((hasDerivAt_const 0 S).sub (hasDerivAt_id 0)) using 1; simp
  exact right_linear_rate hd (by simpa using h0)

theorem terminal_quadratic_rate {I : Set ℝ} (hI : IsOpen I) {f : ℝ → ℝ}
    (hf : ContDiffOn ℝ ∞ f I) {S d : ℝ} (hS : S ∈ I)
    (h1 : deriv f S = 0) (h2 : HasDerivAt (deriv f) d S) :
    Tendsto (fun δ => (f S - f (S - δ)) / δ ^ 2) (𝓝[>] (0 : ℝ)) (𝓝 (-d / 2)) := by
  have hrate := terminal_linear_rate h2 h1
  have hdiv : Tendsto (fun δ => deriv f (S - δ) / (2 * δ)) (𝓝[>] (0 : ℝ)) (𝓝 (-d / 2)) := by
    convert hrate.div_const 2 using 1
    funext δ
    ring
  have hin : ∀ᶠ δ in 𝓝[>] (0 : ℝ), S - δ ∈ I :=
    (endpoint_parameter_tendsto S).eventually (hI.mem_nhds hS)
  apply HasDerivAt.lhopital_zero_nhdsGT (f' := fun δ => deriv f (S - δ))
    (g' := fun δ => 2 * δ) _ _ _ _ _ hdiv
  · filter_upwards [hin] with δ hδ
    convert (hasDerivAt_const δ (f S)).sub
      ((smooth_hasDerivAt_on_open hI hf hδ).comp δ
        ((hasDerivAt_const δ S).sub (hasDerivAt_id δ))) using 1; simp
  · exact Eventually.of_forall (fun δ => by convert (hasDerivAt_id δ).pow 2 using 1; simp)
  · filter_upwards [eventually_mem_nhdsWithin] with δ hδ
    exact mul_ne_zero (by norm_num) (ne_of_gt hδ)
  · have hh := (tendsto_const_nhds (x := f S)).sub
      ((smooth_hasDerivAt_on_open hI hf hS).continuousAt.tendsto.comp (endpoint_parameter_tendsto S))
    simpa using hh
  · simpa using (tendsto_id.mono_left (inf_le_left : 𝓝[>] (0 : ℝ) ≤ 𝓝 0)).pow 2

theorem simple_zero_sign_crossing {f : ℝ → ℝ} {S d : ℝ}
    (hf : HasDerivAt f d S) (h0 : f S = 0) (hd : d < 0) :
    ∀ᶠ δ in 𝓝[>] (0 : ℝ), 0 < f (S - δ) ∧ f (S + δ) < 0 := by
  have hl := terminal_linear_rate hf h0
  have hr : Tendsto (fun δ => f (S + δ) / δ) (𝓝[>] (0 : ℝ)) (𝓝 d) := by
    have hh : HasDerivAt (fun δ => f (S + δ)) d 0 := by
      have hf' : HasDerivAt f d (S + (0 : ℝ)) := by simpa using hf
      convert hf'.comp 0 ((hasDerivAt_const 0 S).add (hasDerivAt_id 0)) using 1; simp
    exact right_linear_rate hh (by simpa using h0)
  have hlpos := hl.eventually (Ioi_mem_nhds (neg_pos.mpr hd))
  have hrneg := hr.eventually (Iio_mem_nhds hd)
  filter_upwards [hlpos, hrneg, eventually_mem_nhdsWithin] with δ hδl hδr hδ
  have hδpos : 0 < δ := hδ
  refine ⟨(div_pos_iff_of_pos_right hδpos).mp hδl, ?_⟩
  have hh := mul_neg_of_neg_of_pos hδr hδpos
  simpa only [div_mul_cancel₀ _ (ne_of_gt hδpos)] using hh

end AffineQuadric
