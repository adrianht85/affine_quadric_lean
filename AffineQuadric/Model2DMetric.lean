import AffineQuadric.CollisionRadialCurvature
import Mathlib.Data.Fin.VecNotation

/-! A coordinate calculation for the two-dimensional metric w(s)(ds²+dθ²).
This is a surface model, with no asserted immersion into the metric of V8.
Coordinate partials below are actual real derivatives along coordinate lines. -/
noncomputable section
open Set Filter
open scoped Topology ContDiff BigOperators
namespace AffineQuadric

def model2DBasis (i : Fin 2) : Fin 2 → ℝ := Pi.single i 1

def model2DPartial (f : (Fin 2 → ℝ) → ℝ) (i : Fin 2) (x : Fin 2 → ℝ) : ℝ :=
  deriv (fun t : ℝ => f (x + t • model2DBasis i)) 0

def model2DMetric (w : ℝ → ℝ) (x u v : Fin 2 → ℝ) : ℝ :=
  w (x 0) * (u 0 * v 0 + u 1 * v 1)

def model2DMetricCoeff (w : ℝ → ℝ) (x : Fin 2 → ℝ) (i j : Fin 2) : ℝ :=
  if i = j then w (x 0) else 0

def model2DInverseCoeff (w : ℝ → ℝ) (x : Fin 2 → ℝ) (i j : Fin 2) : ℝ :=
  if i = j then (w (x 0))⁻¹ else 0

theorem model2DMetric_bilinear (w : ℝ → ℝ) (x u v z : Fin 2 → ℝ) (c : ℝ) :
    model2DMetric w x u v = model2DMetric w x v u ∧
    model2DMetric w x (u + v) z = model2DMetric w x u z + model2DMetric w x v z ∧
    model2DMetric w x (c • u) v = c * model2DMetric w x u v := by
  simp only [model2DMetric, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  constructor
  · ring
  constructor <;> ring

theorem model2DMetric_positive {w : ℝ → ℝ} {x : Fin 2 → ℝ}
    (hw : 0 < w (x 0)) {u : Fin 2 → ℝ} (hu : u ≠ 0) :
    0 < model2DMetric w x u u := by
  have hn : u 0 ≠ 0 ∨ u 1 ≠ 0 := by
    by_contra h
    push_neg at h
    apply hu
    funext i
    fin_cases i <;> simp [h.1, h.2]
  have hp : 0 < u 0 * u 0 + u 1 * u 1 := by
    rcases hn with h | h
    · nlinarith [sq_pos_of_ne_zero h, sq_nonneg (u 1)]
    · nlinarith [sq_pos_of_ne_zero h, sq_nonneg (u 0)]
  exact mul_pos hw hp

theorem model2DMetric_basis (w : ℝ → ℝ) (x : Fin 2 → ℝ) (i j : Fin 2) :
    model2DMetric w x (model2DBasis i) (model2DBasis j) = model2DMetricCoeff w x i j := by
  fin_cases i <;> fin_cases j <;> simp [model2DMetric, model2DMetricCoeff, model2DBasis]

theorem model2DMetric_inverse {w : ℝ → ℝ} {x : Fin 2 → ℝ} (hw : w (x 0) ≠ 0)
    (i j : Fin 2) :
    (∑ k : Fin 2, model2DInverseCoeff w x i k * model2DMetricCoeff w x k j) =
      if i = j then 1 else 0 := by
  fin_cases i <;> fin_cases j <;>
    simp [model2DInverseCoeff, model2DMetricCoeff, hw]

theorem model2DPartial_radial {f : ℝ → ℝ} {x : Fin 2 → ℝ}
    (hf : DifferentiableAt ℝ f (x 0)) (i : Fin 2) :
    model2DPartial (fun y => f (y 0)) i x = if i = 0 then deriv f (x 0) else 0 := by
  fin_cases i
  · have hd : HasDerivAt f (deriv f (x 0)) (x 0 + (0 : ℝ)) := by
      simpa using hf.hasDerivAt
    have h := hd.comp 0 ((hasDerivAt_id (0 : ℝ)).const_add (x 0))
    simpa [model2DPartial, model2DBasis] using h.deriv
  · simp [model2DPartial, model2DBasis]

theorem model2DMetricCoeff_partial {w : ℝ → ℝ} {x : Fin 2 → ℝ}
    (hw : DifferentiableAt ℝ w (x 0)) (i j k : Fin 2) :
    model2DPartial (fun y => model2DMetricCoeff w y j k) i x =
      if j = k then (if i = 0 then deriv w (x 0) else 0) else 0 := by
  by_cases h : j = k
  · simp only [model2DMetricCoeff, h, if_true]
    exact model2DPartial_radial hw i
  · simp [model2DMetricCoeff, h, model2DPartial]

def model2DB (w : ℝ → ℝ) (s : ℝ) : ℝ := deriv w s / (2 * w s)

/-- Levi-Civita coefficients from the metric and its actual partial derivatives.
The upper index is k, the direction index i, and the differentiated basis index j. -/
def model2DChristoffel (w : ℝ → ℝ) (x : Fin 2 → ℝ) (k i j : Fin 2) : ℝ :=
  (1 / 2 : ℝ) * ∑ l : Fin 2, model2DInverseCoeff w x k l *
    (model2DPartial (fun y => model2DMetricCoeff w y j l) i x +
     model2DPartial (fun y => model2DMetricCoeff w y i l) j x -
     model2DPartial (fun y => model2DMetricCoeff w y i j) l x)

def model2DChristoffelPattern (b : ℝ) (k i j : Fin 2) : ℝ :=
  if k = 0 then (if i = j then (if i = 0 then b else -b) else 0)
  else (if i = j then 0 else b)

theorem model2DChristoffel_eq {w : ℝ → ℝ} {x : Fin 2 → ℝ}
    (hw : DifferentiableAt ℝ w (x 0)) (k i j : Fin 2) :
    model2DChristoffel w x k i j = model2DChristoffelPattern (model2DB w (x 0)) k i j := by
  simp only [model2DChristoffel, model2DMetricCoeff_partial hw]
  fin_cases k <;> fin_cases i <;> fin_cases j <;>
    simp [model2DInverseCoeff, model2DChristoffelPattern, model2DB] <;> ring

/-- The coordinate basis commutes, so symmetry in i,j is zero torsion. -/
theorem model2DChristoffel_torsion_free (w : ℝ → ℝ) (x : Fin 2 → ℝ) (k i j : Fin 2) :
    model2DChristoffel w x k i j = model2DChristoffel w x k j i := by
  unfold model2DChristoffel
  congr 1
  apply Finset.sum_congr rfl
  intro l _
  congr 1
  have he : (fun y => model2DMetricCoeff w y i j) = (fun y => model2DMetricCoeff w y j i) := by
    funext y
    simp only [model2DMetricCoeff, eq_comm]
  rw [he]
  ring

/-- Coordinate metric compatibility: ∂i g(j,k)=g(∇i∂j,∂k)+g(∂j,∇i∂k). -/
theorem model2DChristoffel_metric_compatible {w : ℝ → ℝ} {x : Fin 2 → ℝ}
    (hd : DifferentiableAt ℝ w (x 0)) (hp : w (x 0) ≠ 0) (i j k : Fin 2) :
    model2DPartial (fun y => model2DMetricCoeff w y j k) i x =
      ∑ l : Fin 2, (model2DChristoffel w x l i j * model2DMetricCoeff w x l k +
        model2DChristoffel w x l i k * model2DMetricCoeff w x j l) := by
  simp only [model2DMetricCoeff_partial hd, model2DChristoffel_eq hd]
  fin_cases i <;> fin_cases j <;> fin_cases k <;>
    simp [Fin.sum_univ_two, model2DChristoffelPattern, model2DMetricCoeff, model2DB] <;>
    field_simp <;> ring

end AffineQuadric
