import AffineQuadric.CanonicalLocalField
import AffineQuadric.AnalyticCollisionFactor

/-! Analyticity of the lifted field is separate from analyticity of its
integral curves. This module proves only the former. -/
noncomputable section
namespace AffineQuadric

theorem canonicalLiftedField_analyticAt {a V : ℝ → ℝ} {x : ℝ × ℝ × ℝ}
    (ha : AnalyticAt ℝ a x.1) (hV : AnalyticAt ℝ V x.1) (hp : x.2.2 ≠ 0) :
    AnalyticAt ℝ (canonicalLiftedField a V) x := by
  have ht : AnalyticAt ℝ (fun y : ℝ × ℝ × ℝ => y.1) x := analyticAt_fst
  have hq : AnalyticAt ℝ (fun y : ℝ × ℝ × ℝ => y.2.1) x :=
    ((ContinuousLinearMap.fst ℝ ℝ ℝ).comp (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ))).analyticAt x
  have hP : AnalyticAt ℝ (fun y : ℝ × ℝ × ℝ => y.2.2) x :=
    ((ContinuousLinearMap.snd ℝ ℝ ℝ).comp (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ))).analyticAt x
  have hAv := ha.comp ht
  have hVv := hV.comp ht
  have hQ := (((analyticAt_const (v := (2 : ℝ))).mul (hVv.pow 2)).mul
    ((hq.pow 2).sub (hAv.pow 2))).div (hP.pow 2) (pow_ne_zero 2 hp)
  have hR := (((analyticAt_const (v := (4 : ℝ))).mul (hVv.pow 2)).mul hq).div hP hp
  exact analyticAt_const.prod (hQ.prod hR)

theorem canonicalLiftedField_analytic_terminal {J : Set ℝ} {S pS : ℝ} {a V : ℝ → ℝ}
    (h : CanonicalTerminalData J S pS a V) (ha : AnalyticAt ℝ a S) (hV : AnalyticAt ℝ V S) :
    AnalyticAt ℝ (canonicalLiftedField a V) (S, a S, pS) :=
  canonicalLiftedField_analyticAt ha hV h.p_pos.ne'

end AffineQuadric
