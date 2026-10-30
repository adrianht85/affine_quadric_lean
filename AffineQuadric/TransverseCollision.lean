import AffineQuadric.Canonical
import AffineQuadric.QuadraticIntegration

/-! Local scalar collision core for V8 prop:transverse. A smooth solution on an
open neighborhood is an input; no analytic continuation is constructed here. -/
noncomputable section
open Set Filter
open scoped Topology ContDiff
namespace AffineQuadric

def collisionGap (a q : ℝ → ℝ) (s : ℝ) : ℝ := q s ^ 2 - a s ^ 2
def collisionEta (a V p : ℝ → ℝ) (S : ℝ) : ℝ :=
  2 * V S ^ 2 * a S * deriv a S / p S ^ 2

structure LocalTransverseSolutionOn (I : Set ℝ) (S : ℝ) (a V q p : ℝ → ℝ) : Prop where
  S_mem : S ∈ I
  S_pos : 0 < S
  smooth_a : ContDiffOn ℝ ∞ a I
  smooth_V : ContDiffOn ℝ ∞ V I
  smooth_q : ContDiffOn ℝ ∞ q I
  smooth_p : ContDiffOn ℝ ∞ p I
  contact : q S = a S
  a_pos : 0 < a S
  V_pos : 0 < V S
  p_pos : 0 < p S
  a_rate_pos : 0 < deriv a S
  dq : ∀ s ∈ I, HasDerivAt q (qdot (V s) (a s) (q s) (p s)) s
  dp : ∀ s ∈ I, HasDerivAt p (pdot (V s) (q s) (p s)) s

theorem collisionEta_pos {I : Set ℝ} {S : ℝ} {a V q p : ℝ → ℝ}
    (h : LocalTransverseSolutionOn I S a V q p) : 0 < collisionEta a V p S := by
  exact div_pos (mul_pos (mul_pos (mul_pos (by norm_num) (sq_pos_of_pos h.V_pos)) h.a_pos)
    h.a_rate_pos) (sq_pos_of_pos h.p_pos)

theorem transverse_q_hasDerivAt_zero {I : Set ℝ} {S : ℝ} {a V q p : ℝ → ℝ}
    (h : LocalTransverseSolutionOn I S a V q p) : HasDerivAt q 0 S := by
  simpa [qdot, h.contact] using h.dq S h.S_mem

theorem transverse_p_hasDerivAt {I : Set ℝ} {S : ℝ} {a V q p : ℝ → ℝ}
    (h : LocalTransverseSolutionOn I S a V q p) :
    HasDerivAt p (4 * V S ^ 2 * a S / p S) S := by
  simpa [pdot, h.contact] using h.dp S h.S_mem

theorem transverse_p_deriv_pos {I : Set ℝ} {S : ℝ} {a V q p : ℝ → ℝ}
    (h : LocalTransverseSolutionOn I S a V q p) : 0 < deriv p S := by
  rw [(transverse_p_hasDerivAt h).deriv]
  exact div_pos (mul_pos (mul_pos (by norm_num) (sq_pos_of_pos h.V_pos)) h.a_pos) h.p_pos

theorem collisionGap_hasDerivAt {I : Set ℝ} (hI : IsOpen I) {S : ℝ} {a V q p : ℝ → ℝ}
    (h : LocalTransverseSolutionOn I S a V q p) :
    HasDerivAt (collisionGap a q) (-2 * a S * deriv a S) S := by
  convert ((transverse_q_hasDerivAt_zero h).pow 2).sub
    ((smooth_hasDerivAt_on_open hI h.smooth_a h.S_mem).pow 2) using 1
  dsimp
  ring

theorem transverse_q_second_hasDerivAt {I : Set ℝ} (hI : IsOpen I)
    {S : ℝ} {a V q p : ℝ → ℝ} (h : LocalTransverseSolutionOn I S a V q p) :
    HasDerivAt (deriv q) (-2 * collisionEta a V p S) S := by
  have hV := smooth_hasDerivAt_on_open hI h.smooth_V h.S_mem
  have hX := collisionGap_hasDerivAt hI h
  have hp := transverse_p_hasDerivAt h
  have hg := (((hV.pow 2).mul hX).const_mul 2).div (hp.pow 2)
    (pow_ne_zero 2 (ne_of_gt h.p_pos))
  have he : deriv q =ᶠ[𝓝 S] (fun s => 2 * (V s ^ 2 * collisionGap a q s) / p s ^ 2) :=
    Filter.eventually_of_mem (hI.mem_nhds h.S_mem) (fun s hs => by
      rw [(h.dq s hs).deriv]; dsimp [qdot, collisionGap]; ring)
  apply (hg.congr_of_eventuallyEq he).congr_deriv
  dsimp [collisionGap, collisionEta]
  rw [h.contact]
  have hn := ne_of_gt h.p_pos
  field_simp
  ring

theorem transverse_differential_fold {I : Set ℝ} (hI : IsOpen I)
    {S : ℝ} {a V q p : ℝ → ℝ} (h : LocalTransverseSolutionOn I S a V q p) :
    HasDerivAt (fun s => (q s, p s)) (0, 4 * V S ^ 2 * a S / p S) S ∧
    (0, 4 * V S ^ 2 * a S / p S) ≠ (0, (0 : ℝ)) ∧
    deriv q S = 0 ∧ deriv (deriv q) S = -2 * collisionEta a V p S ∧
    deriv (deriv q) S < 0 := by
  have hη := collisionEta_pos h
  have hpd : 0 < 4 * V S ^ 2 * a S / p S := by
    rw [← (transverse_p_hasDerivAt h).deriv]
    exact transverse_p_deriv_pos h
  refine ⟨(transverse_q_hasDerivAt_zero h).prodMk (transverse_p_hasDerivAt h), ?_,
    (transverse_q_hasDerivAt_zero h).deriv, (transverse_q_second_hasDerivAt hI h).deriv, ?_⟩
  · intro heq
    have hh := congrArg Prod.snd heq
    exact (ne_of_gt hpd) hh
  · rw [(transverse_q_second_hasDerivAt hI h).deriv]
    linarith

end AffineQuadric
