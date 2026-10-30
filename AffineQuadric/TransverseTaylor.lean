import AffineQuadric.LocalTaylorRemainder

/-! Stage 1: Taylor remainders deduced from the unchanged canonical local data. -/
noncomputable section
open Set Filter Asymptotics
open scoped Topology ContDiff
namespace AffineQuadric

theorem transverse_q_taylor_bigO {I : Set ℝ} (hI : IsOpen I) {S : ℝ} {a V q p : ℝ → ℝ}
    (h : LocalTransverseSolutionOn I S a V q p) :
    (fun δ => q (S - δ) - (a S - collisionEta a V p S * δ ^ 2))
      =O[𝓝[>] (0 : ℝ)] (fun δ => δ ^ 3) := by
  have ht := terminal_taylor_second_bigO hI h.smooth_q h.S_mem
  simpa only [h.contact, (transverse_q_hasDerivAt_zero h).deriv,
    (transverse_q_second_hasDerivAt hI h).deriv, zero_mul, sub_zero, neg_mul, neg_div,
    mul_div_cancel_left₀ _ (by norm_num : (2 : ℝ) ≠ 0), add_neg_cancel_right] using ht

theorem transverse_qprime_taylor_bigO {I : Set ℝ} (hI : IsOpen I) {S : ℝ} {a V q p : ℝ → ℝ}
    (h : LocalTransverseSolutionOn I S a V q p) :
    (fun δ => deriv q (S - δ) - 2 * collisionEta a V p S * δ)
      =O[𝓝[>] (0 : ℝ)] (fun δ => δ ^ 2) := by
  have ht := terminal_taylor_first_bigO hI (smooth_deriv_on_open hI h.smooth_q) h.S_mem
  simpa only [(transverse_q_hasDerivAt_zero h).deriv, (transverse_q_second_hasDerivAt hI h).deriv,
    neg_mul, zero_sub, neg_neg] using ht

theorem transverse_gap_taylor_bigO {I : Set ℝ} (hI : IsOpen I) {S : ℝ} {a V q p : ℝ → ℝ}
    (h : LocalTransverseSolutionOn I S a V q p) :
    (fun δ => collisionGap a q (S - δ) - 2 * a S * deriv a S * δ)
      =O[𝓝[>] (0 : ℝ)] (fun δ => δ ^ 2) := by
  have hg : ContDiffOn ℝ ∞ (collisionGap a q) I := (h.smooth_q.pow 2).sub (h.smooth_a.pow 2)
  have ht := terminal_taylor_first_bigO hI hg h.S_mem
  simpa only [(collisionGap_hasDerivAt hI h).deriv, show collisionGap a q S = 0 by simp [collisionGap, h.contact],
    neg_mul, zero_sub, neg_neg] using ht

theorem transverse_moving_barrier_bigO {I : Set ℝ} (hI : IsOpen I) {S : ℝ} {a V q p : ℝ → ℝ}
    (h : LocalTransverseSolutionOn I S a V q p) :
    (fun δ => q (S - δ) - a (S - δ) -
      (deriv a S * δ - (collisionEta a V p S + deriv (deriv a) S / 2) * δ ^ 2))
      =O[𝓝[>] (0 : ℝ)] (fun δ => δ ^ 3) := by
  apply ((transverse_q_taylor_bigO hI h).sub (terminal_taylor_second_bigO hI h.smooth_a h.S_mem)).congr_left
  intro δ
  ring

theorem transverse_sum_barrier_bigO {I : Set ℝ} (hI : IsOpen I) {S : ℝ} {a V q p : ℝ → ℝ}
    (h : LocalTransverseSolutionOn I S a V q p) :
    (fun δ => q (S - δ) + a (S - δ) - (2 * a S - deriv a S * δ))
      =O[𝓝[>] (0 : ℝ)] (fun δ => δ ^ 2) := by
  have hq := terminal_taylor_first_bigO hI h.smooth_q h.S_mem
  rw [(transverse_q_hasDerivAt_zero h).deriv, h.contact] at hq
  apply (hq.add (terminal_taylor_first_bigO hI h.smooth_a h.S_mem)).congr_left
  intro δ
  ring

end AffineQuadric
