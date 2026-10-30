import AffineQuadric.EffectiveDistanceChart
import AffineQuadric.TransverseRemainders
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs

/-! Taylor estimates for the analytic profiles in the regular coordinate z. -/
noncomputable section
open Set Filter Asymptotics
open scoped Topology
namespace AffineQuadric

theorem analytic_taylor_first_bigO {f : ℝ → ℝ} (hf : AnalyticAt ℝ f 0) :
    (fun z => f z - (f 0 + deriv f 0 * z)) =O[𝓝 (0 : ℝ)] (fun z => z ^ 2) := by
  have ht := hf.hasFPowerSeriesAt.isBigO_sub_partialSum_pow 2
  have hr : (fun z : ℝ => ‖z‖ ^ 2) =O[𝓝 (0 : ℝ)] (fun z => z ^ 2) :=
    isBigO_of_le _ (fun z => by simp only [norm_pow, norm_norm]; exact le_rfl)
  convert ht.trans hr using 1
  funext z
  norm_num [FormalMultilinearSeries.partialSum, FormalMultilinearSeries.ofScalars_apply_eq,
    Finset.sum_range_succ, iteratedDeriv_succ, iteratedDeriv_zero]
  ring

theorem analytic_taylor_second_bigO {f : ℝ → ℝ} (hf : AnalyticAt ℝ f 0) :
    (fun z => f z - (f 0 + deriv f 0 * z + deriv (deriv f) 0 / 2 * z ^ 2))
      =O[𝓝 (0 : ℝ)] (fun z => z ^ 3) := by
  have ht := hf.hasFPowerSeriesAt.isBigO_sub_partialSum_pow 3
  have hr : (fun z : ℝ => ‖z‖ ^ 3) =O[𝓝 (0 : ℝ)] (fun z => z ^ 3) :=
    isBigO_of_le _ (fun z => by simp only [norm_pow, norm_norm]; exact le_rfl)
  convert ht.trans hr using 1
  funext z
  norm_num [FormalMultilinearSeries.partialSum, FormalMultilinearSeries.ofScalars_apply_eq,
    Finset.sum_range_succ, iteratedDeriv_succ, iteratedDeriv_zero]
  ring

def collisionUProfile (q D : ℝ → ℝ) (S z : ℝ) : ℝ := q (S - D z)
def collisionXProfile (a q D : ℝ → ℝ) (S z : ℝ) : ℝ := collisionGap a q (S - D z)

theorem collisionUProfile_analytic {q D : ℝ → ℝ} {S : ℝ}
    (hq : AnalyticAt ℝ q S) (hD : AnalyticAt ℝ D 0) (h0 : D 0 = 0) :
    AnalyticAt ℝ (collisionUProfile q D S) 0 := by
  have hg : AnalyticAt ℝ (fun z : ℝ => S - D z) 0 := analyticAt_const.sub hD
  exact AnalyticAt.comp (f := fun z : ℝ => S - D z) (x := 0)
    (show AnalyticAt ℝ q (S - D 0) by simpa [h0] using hq) hg

theorem collisionXProfile_analytic {a q D : ℝ → ℝ} {S : ℝ}
    (ha : AnalyticAt ℝ a S) (hq : AnalyticAt ℝ q S)
    (hD : AnalyticAt ℝ D 0) (h0 : D 0 = 0) :
    AnalyticAt ℝ (collisionXProfile a q D S) 0 := by
  exact (collisionUProfile_analytic hq hD h0).pow 2 |>.sub
    ((collisionUProfile_analytic ha hD h0).pow 2)

theorem collisionUProfile_first {q D : ℝ → ℝ} {S d : ℝ}
    (hq : HasDerivAt q 0 S) (hD : HasDerivAt D d 0) (h0 : D 0 = 0) :
    HasDerivAt (collisionUProfile q D S) 0 0 := by
  have hg := (hasDerivAt_const 0 S).sub hD
  have hq' : HasDerivAt q 0 (S - D 0) := by simpa [h0] using hq
  simpa [collisionUProfile] using hq'.comp 0 hg

theorem collisionUProfile_second {q D : ℝ → ℝ} {S d η : ℝ}
    (hq : AnalyticAt ℝ q S) (hD : AnalyticAt ℝ D 0) (h0 : D 0 = 0)
    (hd : HasDerivAt D d 0) (hq0 : HasDerivAt q 0 S)
    (hq2 : HasDerivAt (deriv q) (-2 * η) S) :
    HasDerivAt (deriv (collisionUProfile q D S)) (-2 * η * d ^ 2) 0 := by
  have hg := (hasDerivAt_const 0 S).sub hd
  have hq2' : HasDerivAt (deriv q) (-2 * η) (S - D 0) := by simpa [h0] using hq2
  have ht := (hq2'.comp 0 hg).mul hD.deriv.differentiableAt.hasDerivAt.neg
  have he : (fun z => deriv q (S - D z) * -deriv D z) =ᶠ[𝓝 (0 : ℝ)]
      deriv (collisionUProfile q D S) := by
    have hg0 : Tendsto (fun z => S - D z) (𝓝 (0 : ℝ)) (𝓝 S) := by
      simpa [h0] using (continuousAt_const.sub hD.continuousAt).tendsto
    filter_upwards [hD.eventually_analyticAt, hg0.eventually hq.eventually_analyticAt]
      with z hz hqz
    simpa only [zero_sub] using ((hqz.differentiableAt.hasDerivAt).comp z
      ((hasDerivAt_const z S).sub hz.differentiableAt.hasDerivAt)).deriv.symm
  apply (ht.congr_of_eventuallyEq he.symm).congr_deriv
  dsimp
  rw [h0, sub_zero, hq0.deriv, hd.deriv]
  ring

theorem collisionXProfile_first {I : Set ℝ} (hI : IsOpen I) {a V q p D : ℝ → ℝ} {S d : ℝ}
    (h : LocalTransverseSolutionOn I S a V q p) (hd : HasDerivAt D d 0) (h0 : D 0 = 0) :
    HasDerivAt (collisionXProfile a q D S) (2 * a S * deriv a S * d) 0 := by
  have hx : HasDerivAt (collisionGap a q) (-2 * a S * deriv a S) (S - D 0) := by
    simpa [h0] using collisionGap_hasDerivAt hI h
  convert hx.comp 0 ((hasDerivAt_const 0 S).sub hd) using 1
  dsimp
  ring

end AffineQuadric
