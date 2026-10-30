import AffineQuadric.TransverseRadialLaw
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-! Analytic regularization of the simple radial zero. Analyticity is an
additional input on the given solution; no analytic solution is constructed. -/
noncomputable section
open Set Filter
open scoped Topology
namespace AffineQuadric

def analyticRadialFactor (w : ℝ → ℝ) (S : ℝ) : ℝ → ℝ :=
  dslope (fun δ => w (S - δ)) 0

theorem analyticRadialFactor_analytic {w : ℝ → ℝ} {S : ℝ}
    (hw : AnalyticAt ℝ w S) : AnalyticAt ℝ (analyticRadialFactor w S) 0 := by
  have hg : AnalyticAt ℝ (fun δ : ℝ => w (S - δ)) 0 := by
    exact (show AnalyticAt ℝ w (S - (0 : ℝ)) by simpa using hw).comp
      (analyticAt_const.sub analyticAt_id)
  obtain ⟨p, hp⟩ := hg
  exact hp.has_fpower_series_dslope_fslope.analyticAt

theorem analyticRadialFactor_identity {w : ℝ → ℝ} {S : ℝ} (hz : w S = 0) (δ : ℝ) :
    w (S - δ) = δ * analyticRadialFactor w S δ := by
  simpa [analyticRadialFactor, hz] using
    (sub_smul_dslope (fun x => w (S - x)) 0 δ).symm

theorem analyticRadialFactor_zero {w : ℝ → ℝ} {S η : ℝ}
    (hd : HasDerivAt w (-η) S) : analyticRadialFactor w S 0 = η := by
  have hg : HasDerivAt (fun δ : ℝ => w (S - δ)) η 0 := by
    convert (show HasDerivAt w (-η) (S - (0 : ℝ)) by simpa using hd).comp 0
      ((hasDerivAt_const 0 S).sub (hasDerivAt_id 0)) using 1
    simp
  simpa [analyticRadialFactor, dslope_same] using hg.deriv

theorem analyticAt_positive_rpow {f : ℝ → ℝ} {x : ℝ}
    (hf : AnalyticAt ℝ f x) (hp : 0 < f x) (r : ℝ) :
    AnalyticAt ℝ (fun t => (f t) ^ r) x := by
  have hg : AnalyticAt ℝ (fun t => Real.exp (Real.log (f t) * r)) x :=
    ((hf.log hp).mul (analyticAt_const (v := r))).rexp'
  apply hg.congr
  filter_upwards [hf.continuousAt.eventually (Ioi_mem_nhds hp)] with t ht
  exact (Real.rpow_def_of_pos ht r).symm

theorem analyticRadialFactor_sqrt {w : ℝ → ℝ} {S η : ℝ}
    (hw : AnalyticAt ℝ w S) (hd : HasDerivAt w (-η) S) (hη : 0 < η) :
    AnalyticAt ℝ (fun δ => Real.sqrt (analyticRadialFactor w S δ)) 0 := by
  simpa only [Real.sqrt_eq_rpow] using
    analyticAt_positive_rpow (analyticRadialFactor_analytic hw)
      (by rw [analyticRadialFactor_zero hd]; exact hη) (1 / 2 : ℝ)

theorem transverse_radial_analytic {I : Set ℝ} {S : ℝ} {a V q p : ℝ → ℝ}
    (_h : LocalTransverseSolutionOn I S a V q p) (hq : AnalyticAt ℝ q S) :
    AnalyticAt ℝ (collisionRadialW q) S := by
  exact hq.deriv.div analyticAt_const (by norm_num)

theorem transverse_analytic_radial_factor {I : Set ℝ} (hI : IsOpen I)
    {S : ℝ} {a V q p : ℝ → ℝ} (h : LocalTransverseSolutionOn I S a V q p)
    (hq : AnalyticAt ℝ q S) :
    AnalyticAt ℝ (analyticRadialFactor (collisionRadialW q) S) 0 ∧
    analyticRadialFactor (collisionRadialW q) S 0 = collisionEta a V p S ∧
    (∀ δ, collisionRadialW q (S - δ) =
      δ * analyticRadialFactor (collisionRadialW q) S δ) ∧
    AnalyticAt ℝ (fun δ => Real.sqrt (analyticRadialFactor (collisionRadialW q) S δ)) 0 := by
  have hw := transverse_radial_analytic h hq
  have ht := collisionRadialW_terminal hI h
  exact ⟨analyticRadialFactor_analytic hw, analyticRadialFactor_zero ht.2.1,
    analyticRadialFactor_identity ht.1,
    analyticRadialFactor_sqrt hw ht.2.1 (collisionEta_pos h)⟩

end AffineQuadric
