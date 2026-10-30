import AffineQuadric.LocalTaylorRemainder
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-! First-order uniform errors and positive-parameter scaling. Every inverse or
real-power cancellation below is restricted to the positive side. -/
noncomputable section
open Set Filter Asymptotics
open scoped Topology
namespace AffineQuadric

def FirstOrderAtZero (f : ℝ → ℝ) (c : ℝ) : Prop :=
  (fun δ => f δ - c) =O[𝓝[>] (0 : ℝ)] (fun δ => δ)

theorem firstOrder_tendsto {f : ℝ → ℝ} {c : ℝ} (hf : FirstOrderAtZero f c) :
    Tendsto f (𝓝[>] (0 : ℝ)) (𝓝 c) := by
  have hh := hf.trans_tendsto (tendsto_id.mono_left (inf_le_left : 𝓝[>] (0 : ℝ) ≤ 𝓝 0))
  simpa only [sub_add_cancel, zero_add] using hh.add (tendsto_const_nhds (x := c))

theorem firstOrder_const (c : ℝ) : FirstOrderAtZero (fun _ => c) c := by
  simpa [FirstOrderAtZero] using (isBigO_zero (fun δ : ℝ => δ) (𝓝[>] (0 : ℝ)))

theorem firstOrder_add {f g : ℝ → ℝ} {a b : ℝ}
    (hf : FirstOrderAtZero f a) (hg : FirstOrderAtZero g b) :
    FirstOrderAtZero (fun δ => f δ + g δ) (a + b) :=
  (hf.add hg).congr_left (fun δ => by ring)

theorem firstOrder_sub {f g : ℝ → ℝ} {a b : ℝ}
    (hf : FirstOrderAtZero f a) (hg : FirstOrderAtZero g b) :
    FirstOrderAtZero (fun δ => f δ - g δ) (a - b) :=
  (hf.sub hg).congr_left (fun δ => by ring)

theorem firstOrder_mul {f g : ℝ → ℝ} {a b : ℝ}
    (hf : FirstOrderAtZero f a) (hg : FirstOrderAtZero g b) :
    FirstOrderAtZero (fun δ => f δ * g δ) (a * b) := by
  have hb := (firstOrder_tendsto hf).isBigO_one ℝ
  have hh : (fun δ => f δ * (g δ - b)) =O[𝓝[>] (0 : ℝ)] (fun δ => δ) := by
    simpa only [one_mul] using hb.mul hg
  exact (hh.add (hf.const_mul_left b)).congr_left (fun δ => by ring)

theorem firstOrder_comp_hasDerivAt {f φ : ℝ → ℝ} {a d : ℝ}
    (hf : FirstOrderAtZero f a) (hφ : HasDerivAt φ d a) :
    FirstOrderAtZero (fun δ => φ (f δ)) (φ a) :=
  (hφ.isBigO_sub.comp_tendsto (firstOrder_tendsto hf)).trans hf

theorem firstOrder_inv {f : ℝ → ℝ} {a : ℝ} (hf : FirstOrderAtZero f a) (ha : a ≠ 0) :
    FirstOrderAtZero (fun δ => (f δ)⁻¹) a⁻¹ :=
  firstOrder_comp_hasDerivAt hf ((hasDerivAt_id a).inv ha)

theorem firstOrder_rpow {f : ℝ → ℝ} {a : ℝ} (hf : FirstOrderAtZero f a) (ha : a ≠ 0) (r : ℝ) :
    FirstOrderAtZero (fun δ => (f δ) ^ r) (a ^ r) :=
  firstOrder_comp_hasDerivAt hf ((hasDerivAt_id a).rpow_const (Or.inl ha))

theorem firstOrder_pow {f : ℝ → ℝ} {a : ℝ} (hf : FirstOrderAtZero f a) (n : ℕ) :
    FirstOrderAtZero (fun δ => (f δ) ^ n) (a ^ n) :=
  firstOrder_comp_hasDerivAt hf ((hasDerivAt_id a).pow n)

theorem firstOrder_sqrt {f : ℝ → ℝ} {a : ℝ} (hf : FirstOrderAtZero f a) (ha : 0 < a) :
    FirstOrderAtZero (fun δ => Real.sqrt (f δ)) (Real.sqrt a) :=
  firstOrder_comp_hasDerivAt hf ((hasDerivAt_id a).sqrt (ne_of_gt ha))

theorem bigO_mul_rpow {f : ℝ → ℝ} {a : ℝ}
    (hf : f =O[𝓝[>] (0 : ℝ)] (fun δ => δ ^ a)) (b : ℝ) :
    (fun δ => f δ * δ ^ b) =O[𝓝[>] (0 : ℝ)] (fun δ => δ ^ (a + b)) := by
  apply (hf.mul (isBigO_refl (fun δ : ℝ => δ ^ b) (𝓝[>] (0 : ℝ)))).congr' (Eventually.of_forall (fun _ => rfl))
  filter_upwards [eventually_mem_nhdsWithin] with δ hδ
  exact (Real.rpow_add (show 0 < δ from hδ) a b).symm

theorem rpow_error_normalize {f : ℝ → ℝ} {c a b : ℝ}
    (hf : (fun δ => f δ - c * δ ^ a) =O[𝓝[>] (0 : ℝ)] (fun δ => δ ^ (a + b))) :
    (fun δ => f δ / δ ^ a - c) =O[𝓝[>] (0 : ℝ)] (fun δ => δ ^ b) := by
  have hh := bigO_mul_rpow hf (-a)
  apply hh.congr'
  · filter_upwards [eventually_mem_nhdsWithin] with δ hδ
    have hp : 0 < δ := hδ
    rw [Real.rpow_neg hp.le]
    field_simp [ne_of_gt (Real.rpow_pos_of_pos hp a)]
  · exact Eventually.of_forall (fun δ => by
      change δ ^ (a + b + -a) = δ ^ b
      rw [show a + b + -a = b by ring])

theorem rpow_error_denormalize {f : ℝ → ℝ} {c a b : ℝ}
    (hf : (fun δ => f δ / δ ^ a - c) =O[𝓝[>] (0 : ℝ)] (fun δ => δ ^ b)) :
    (fun δ => f δ - c * δ ^ a) =O[𝓝[>] (0 : ℝ)] (fun δ => δ ^ (a + b)) := by
  have hh := bigO_mul_rpow hf a
  apply hh.congr'
  · filter_upwards [eventually_mem_nhdsWithin] with δ hδ
    have hp : 0 < δ := hδ
    field_simp [ne_of_gt (Real.rpow_pos_of_pos hp a)]
  · exact Eventually.of_forall (fun δ => by
      change δ ^ (b + a) = δ ^ (a + b)
      rw [add_comm b a])

end AffineQuadric
