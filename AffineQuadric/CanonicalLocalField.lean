import AffineQuadric.TransverseRemainders
import Mathlib.Analysis.ODE.PicardLindelof

/-! The nonautonomous canonical equations are lifted to three autonomous
coordinates. Smoothness is proved only on the domain with nonzero momentum. -/
noncomputable section
open Set Filter
open scoped Topology ContDiff
namespace AffineQuadric

def canonicalLiftedField (a V : ℝ → ℝ) (x : ℝ × ℝ × ℝ) : ℝ × ℝ × ℝ :=
  (1, qdot (V x.1) (a x.1) x.2.1 x.2.2, pdot (V x.1) x.2.1 x.2.2)

def canonicalRegularDomain (J : Set ℝ) : Set (ℝ × ℝ × ℝ) :=
  {x | x.1 ∈ J ∧ x.2.2 ≠ 0}

structure CanonicalTerminalData (J : Set ℝ) (S pS : ℝ) (a V : ℝ → ℝ) : Prop where
  open_J : IsOpen J
  S_mem : S ∈ J
  S_pos : 0 < S
  smooth_a : ContDiffOn ℝ ∞ a J
  smooth_V : ContDiffOn ℝ ∞ V J
  a_pos : 0 < a S
  V_pos : 0 < V S
  a_rate_pos : 0 < deriv a S
  p_pos : 0 < pS

theorem canonicalLiftedField_contDiffAt {a V : ℝ → ℝ} {x : ℝ × ℝ × ℝ}
    {n : WithTop ℕ∞} (ha : ContDiffAt ℝ n a x.1) (hV : ContDiffAt ℝ n V x.1)
    (hp : x.2.2 ≠ 0) : ContDiffAt ℝ n (canonicalLiftedField a V) x := by
  have ht : ContDiffAt ℝ n (fun y : ℝ × ℝ × ℝ => y.1) x := contDiffAt_fst
  have hq : ContDiffAt ℝ n (fun y : ℝ × ℝ × ℝ => y.2.1) x := contDiffAt_snd.fst
  have hP : ContDiffAt ℝ n (fun y : ℝ × ℝ × ℝ => y.2.2) x := contDiffAt_snd.snd
  have hAv := ha.comp x ht
  have hVv := hV.comp x ht
  have hQ := (((contDiffAt_const (c := (2 : ℝ))).mul (hVv.pow 2)).mul
    ((hq.pow 2).sub (hAv.pow 2))).div (hP.pow 2) (pow_ne_zero 2 hp)
  have hR := (((contDiffAt_const (c := (4 : ℝ))).mul (hVv.pow 2)).mul hq).div hP hp
  exact contDiffAt_const.prodMk (hQ.prodMk hR)

theorem canonicalLiftedField_smooth {J : Set ℝ} (hJ : IsOpen J) {a V : ℝ → ℝ}
    (ha : ContDiffOn ℝ ∞ a J) (hV : ContDiffOn ℝ ∞ V J) :
    ContDiffOn ℝ ∞ (canonicalLiftedField a V) (canonicalRegularDomain J) := by
  intro x hx
  exact (canonicalLiftedField_contDiffAt (ha.contDiffAt (hJ.mem_nhds hx.1))
    (hV.contDiffAt (hJ.mem_nhds hx.1)) hx.2).contDiffWithinAt

theorem canonicalLiftedField_terminal {J : Set ℝ} {S pS : ℝ} {a V : ℝ → ℝ}
    (h : CanonicalTerminalData J S pS a V) :
    ContDiffAt ℝ 1 (canonicalLiftedField a V) (S, a S, pS) := by
  exact canonicalLiftedField_contDiffAt
    ((h.smooth_a.contDiffAt (h.open_J.mem_nhds h.S_mem)).of_le (by simp))
    ((h.smooth_V.contDiffAt (h.open_J.mem_nhds h.S_mem)).of_le (by simp)) h.p_pos.ne'

theorem autonomous_solution_smooth {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {I : Set ℝ} {U : Set E} (hI : IsOpen I) {G : E → E} {γ : ℝ → E}
    (hG : ContDiffOn ℝ ∞ G U) (hγ : ∀ t ∈ I, HasDerivAt γ (G (γ t)) t)
    (hU : MapsTo γ I U) : ContDiffOn ℝ ∞ γ I := by
  have hd : DifferentiableOn ℝ γ I := fun t ht => (hγ t ht).differentiableAt.differentiableWithinAt
  rw [contDiffOn_infty]
  intro n
  induction n with
  | zero => exact contDiffOn_zero.mpr hd.continuousOn
  | succ n ih =>
    rw [show ((n + 1 : ℕ) : WithTop ℕ∞) = (n : WithTop ℕ∞) + 1 by simp,
      contDiffOn_succ_iff_deriv_of_isOpen hI]
    refine ⟨hd, by simp, ?_⟩
    have hc := (hG.of_le (show (n : WithTop ℕ∞) ≤ ∞ by
      exact_mod_cast (le_top : (n : ℕ∞) ≤ ⊤))).comp ih hU
    exact hc.congr (fun t ht => (hγ t ht).deriv)

end AffineQuadric
