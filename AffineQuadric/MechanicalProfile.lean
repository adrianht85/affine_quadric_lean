import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Tactic

/-! The temporal profile in PE V8 eq:tau. Here t=3s; this is not Newtonian time. -/
noncomputable section
namespace AffineQuadric

def shapeNumerator (t : ℝ) : ℝ := t * Real.cosh t - Real.sinh t
def timeNumerator (t : ℝ) : ℝ := Real.sinh t * Real.cosh t - t
def mechanicalTime (t : ℝ) : ℝ := timeNumerator t / 2
def hyperbolicShape (t : ℝ) : ℝ := t * Real.cosh t / Real.sinh t - 1
def hyperbolicShapeSlope (t : ℝ) : ℝ := timeNumerator t / Real.sinh t ^ 2
def shapeSquareTauRate (t : ℝ) : ℝ :=
  2 * hyperbolicShape t * hyperbolicShapeSlope t / Real.sinh t ^ 2

theorem shapeNumerator_hasDerivAt (t : ℝ) :
    HasDerivAt shapeNumerator (t * Real.sinh t) t := by
  convert ((hasDerivAt_id t).mul (Real.hasDerivAt_cosh t)).sub (Real.hasDerivAt_sinh t) using 1
  dsimp
  ring

theorem timeNumerator_hasDerivAt (t : ℝ) :
    HasDerivAt timeNumerator (2 * Real.sinh t ^ 2) t := by
  convert ((Real.hasDerivAt_sinh t).mul (Real.hasDerivAt_cosh t)).sub (hasDerivAt_id t) using 1
  nlinarith [Real.cosh_sq_sub_sinh_sq t]

theorem shapeNumerator_pos {t : ℝ} (ht : 0 < t) : 0 < shapeNumerator t := by
  have hm : StrictMonoOn shapeNumerator (Set.Ici 0) := by
    apply strictMonoOn_of_deriv_pos (convex_Ici 0)
    · exact fun x _ => (shapeNumerator_hasDerivAt x).continuousAt.continuousWithinAt
    · intro x hx
      rw [interior_Ici] at hx
      rw [(shapeNumerator_hasDerivAt x).deriv]
      exact mul_pos hx (Real.sinh_pos_iff.2 hx)
  have hh := hm (by simp : (0 : ℝ) ∈ Set.Ici 0) (le_of_lt ht) ht
  simpa [shapeNumerator] using hh

theorem timeNumerator_pos {t : ℝ} (ht : 0 < t) : 0 < timeNumerator t := by
  have hm : StrictMonoOn timeNumerator (Set.Ici 0) := by
    apply strictMonoOn_of_deriv_pos (convex_Ici 0)
    · exact fun x _ => (timeNumerator_hasDerivAt x).continuousAt.continuousWithinAt
    · intro x hx
      rw [interior_Ici] at hx
      rw [(timeNumerator_hasDerivAt x).deriv]
      exact mul_pos (by norm_num) (sq_pos_of_pos (Real.sinh_pos_iff.2 hx))
  have hh := hm (by simp : (0 : ℝ) ∈ Set.Ici 0) (le_of_lt ht) ht
  simpa [timeNumerator] using hh

theorem mechanicalTime_hasDerivAt (t : ℝ) :
    HasDerivAt mechanicalTime (Real.sinh t ^ 2) t := by
  convert (timeNumerator_hasDerivAt t).div_const 2 using 1
  ring

theorem mechanicalTime_pos {t : ℝ} (ht : 0 < t) : 0 < mechanicalTime t := by
  exact div_pos (timeNumerator_pos ht) (by norm_num)

theorem mechanicalTime_deriv_pos {t : ℝ} (ht : 0 < t) : 0 < deriv mechanicalTime t := by
  rw [(mechanicalTime_hasDerivAt t).deriv]
  exact sq_pos_of_pos (Real.sinh_pos_iff.2 ht)

theorem hyperbolicShape_hasDerivAt {t : ℝ} (ht : 0 < t) :
    HasDerivAt hyperbolicShape (hyperbolicShapeSlope t) t := by
  have hn : Real.sinh t ≠ 0 := ne_of_gt (Real.sinh_pos_iff.2 ht)
  convert (((hasDerivAt_id t).mul (Real.hasDerivAt_cosh t)).div
    (Real.hasDerivAt_sinh t) hn).sub_const 1 using 1
  dsimp [hyperbolicShapeSlope, timeNumerator]
  field_simp
  linear_combination t * (Real.cosh_sq_sub_sinh_sq t)

theorem hyperbolicShape_pos {t : ℝ} (ht : 0 < t) : 0 < hyperbolicShape t := by
  have hn : Real.sinh t ≠ 0 := ne_of_gt (Real.sinh_pos_iff.2 ht)
  have heq : hyperbolicShape t = shapeNumerator t / Real.sinh t := by
    dsimp [hyperbolicShape, shapeNumerator]
    field_simp
  rw [heq]
  exact div_pos (shapeNumerator_pos ht) (Real.sinh_pos_iff.2 ht)

theorem hyperbolicShapeSlope_pos {t : ℝ} (ht : 0 < t) : 0 < hyperbolicShapeSlope t := by
  exact div_pos (timeNumerator_pos ht) (sq_pos_of_pos (Real.sinh_pos_iff.2 ht))

theorem shapeSquareTauRate_pos {t : ℝ} (ht : 0 < t) : 0 < shapeSquareTauRate t := by
  exact div_pos (mul_pos (mul_pos (by norm_num) (hyperbolicShape_pos ht))
    (hyperbolicShapeSlope_pos ht)) (sq_pos_of_pos (Real.sinh_pos_iff.2 ht))

end AffineQuadric
