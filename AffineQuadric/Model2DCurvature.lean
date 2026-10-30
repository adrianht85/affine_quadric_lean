import AffineQuadric.Model2DMetric

/-! Curvature of the two-dimensional conformal model, calculated from the
metric connection. Sign: R(X,Y)Z=∇X∇Y Z−∇Y∇X Z−∇[X,Y]Z.
All coordinate derivatives are real derivatives, including those of Christoffel. -/
noncomputable section
open Set Filter
open scoped Topology ContDiff BigOperators
namespace AffineQuadric

theorem model2DPartial_congr {f g : (Fin 2 → ℝ) → ℝ} {x : Fin 2 → ℝ}
    (he : f =ᶠ[𝓝 x] g) (i : Fin 2) : model2DPartial f i x = model2DPartial g i x := by
  have hc : Continuous (fun t : ℝ => x + t • model2DBasis i) := by fun_prop
  have ht : Tendsto (fun t : ℝ => x + t • model2DBasis i) (𝓝 0) (𝓝 x) := by
    simpa using hc.continuousAt.tendsto (x := (0 : ℝ))
  have he' : (fun t : ℝ => f (x + t • model2DBasis i)) =ᶠ[𝓝 (0 : ℝ)]
      (fun t => g (x + t • model2DBasis i)) := ht.eventually he
  exact he'.deriv_eq

theorem model2DPartial_neg (f : (Fin 2 → ℝ) → ℝ) (i : Fin 2) (x : Fin 2 → ℝ) :
    model2DPartial (fun y => -f y) i x = -model2DPartial f i x := by
  exact deriv.fun_neg

theorem model2DB_hasDerivAt {I : Set ℝ} (hI : IsOpen I) {w : ℝ → ℝ}
    (hw : ContDiffOn ℝ ∞ w I) {s : ℝ} (hs : s ∈ I) (hp : w s ≠ 0) :
    HasDerivAt (model2DB w)
      ((deriv (deriv w) s * (2 * w s) - deriv w s * (2 * deriv w s)) / (2 * w s) ^ 2) s := by
  exact (smooth_hasDerivAt_on_open hI (smooth_deriv_on_open hI hw) hs).div
    ((smooth_hasDerivAt_on_open hI hw hs).const_mul 2) (mul_ne_zero (by norm_num) hp)

theorem model2DChristoffel_partial {I : Set ℝ} (hI : IsOpen I) {w : ℝ → ℝ}
    (hw : ContDiffOn ℝ ∞ w I) {x : Fin 2 → ℝ} (hx : x 0 ∈ I) (hp : w (x 0) ≠ 0)
    (k i j d : Fin 2) :
    model2DPartial (fun y => model2DChristoffel w y k i j) d x =
      model2DChristoffelPattern (if d = 0 then deriv (model2DB w) (x 0) else 0) k i j := by
  have he : (fun y => model2DChristoffel w y k i j) =ᶠ[𝓝 x]
      (fun y => model2DChristoffelPattern (model2DB w (y 0)) k i j) := by
    have hc : Continuous (fun y : Fin 2 → ℝ => y 0) := continuous_apply 0
    filter_upwards [hc.continuousAt.eventually (hI.mem_nhds hx)] with y hy
    exact model2DChristoffel_eq (smooth_hasDerivAt_on_open hI hw hy).differentiableAt k i j
  rw [model2DPartial_congr he]
  have hb := (model2DB_hasDerivAt hI hw hx hp).differentiableAt
  have hz : model2DPartial (fun _ => 0) d x = 0 := by simp [model2DPartial]
  fin_cases k <;> fin_cases i <;> fin_cases j <;>
    simp [model2DChristoffelPattern, model2DPartial_neg, model2DPartial_radial hb, hz]

/-- Coordinate tensor R^l_{ijk}: output l of R(∂i,∂j)∂k.
The derivative terms and both connection products are retained. -/
def model2DRiemann (w : ℝ → ℝ) (x : Fin 2 → ℝ) (l i j k : Fin 2) : ℝ :=
  model2DPartial (fun y => model2DChristoffel w y l j k) i x -
  model2DPartial (fun y => model2DChristoffel w y l i k) j x +
  ∑ m : Fin 2, (model2DChristoffel w x m j k * model2DChristoffel w x l i m -
    model2DChristoffel w x m i k * model2DChristoffel w x l j m)

theorem model2DRiemann_radial_vertical {I : Set ℝ} (hI : IsOpen I) {w : ℝ → ℝ}
    (hw : ContDiffOn ℝ ∞ w I) {x : Fin 2 → ℝ} (hx : x 0 ∈ I) (hp : w (x 0) ≠ 0)
    (l : Fin 2) :
    model2DRiemann w x l 0 1 1 = if l = 0 then -deriv (model2DB w) (x 0) else 0 := by
  have hd := (smooth_hasDerivAt_on_open hI hw hx).differentiableAt
  simp only [model2DRiemann, model2DChristoffel_partial hI hw hx hp, model2DChristoffel_eq hd]
  fin_cases l <;> simp [model2DChristoffelPattern, Fin.sum_univ_two]

def model2DGram (w : ℝ → ℝ) (x : Fin 2 → ℝ) : ℝ :=
  model2DMetric w x (model2DBasis 0) (model2DBasis 0) *
    model2DMetric w x (model2DBasis 1) (model2DBasis 1) -
    model2DMetric w x (model2DBasis 0) (model2DBasis 1) ^ 2

theorem model2DGram_eq (w : ℝ → ℝ) (x : Fin 2 → ℝ) : model2DGram w x = w (x 0) ^ 2 := by
  simp [model2DGram, model2DMetric_basis, model2DMetricCoeff, pow_two]

theorem model2DGram_positive {w : ℝ → ℝ} {x : Fin 2 → ℝ} (hp : 0 < w (x 0)) :
    0 < model2DGram w x := by
  rw [model2DGram_eq]
  exact sq_pos_of_pos hp

/-- The sectional curvature of the coordinate plane of this 2D model:
g(R(∂s,∂θ)∂θ,∂s) divided by the Gram determinant. -/
def model2DSectional (w : ℝ → ℝ) (x : Fin 2 → ℝ) : ℝ :=
  model2DMetric w x (fun l => model2DRiemann w x l 0 1 1) (model2DBasis 0) / model2DGram w x

theorem model2DSectional_eq_neg_deriv {I : Set ℝ} (hI : IsOpen I) {w : ℝ → ℝ}
    (hw : ContDiffOn ℝ ∞ w I) {x : Fin 2 → ℝ} (hx : x 0 ∈ I) (hp : w (x 0) ≠ 0) :
    model2DSectional w x = -deriv (model2DB w) (x 0) / w (x 0) := by
  simp only [model2DSectional, model2DMetric, model2DRiemann_radial_vertical hI hw hx hp,
    model2DGram_eq]
  simp [model2DBasis]
  field_simp

theorem model2DSectional_eq_quotient {I : Set ℝ} (hI : IsOpen I) {w : ℝ → ℝ}
    (hw : ContDiffOn ℝ ∞ w I) {x : Fin 2 → ℝ} (hx : x 0 ∈ I) (hp : 0 < w (x 0)) :
    model2DSectional w x = radialCurvatureQuotient w (x 0) := by
  rw [model2DSectional_eq_neg_deriv hI hw hx hp.ne', (model2DB_hasDerivAt hI hw hx hp.ne').deriv]
  dsimp [radialCurvatureQuotient]
  field_simp
  ring

theorem model2DSectional_eq_radialScalarCurvature {I : Set ℝ} (hI : IsOpen I) {w : ℝ → ℝ}
    (hw : ContDiffOn ℝ ∞ w I) {x : Fin 2 → ℝ} (hx : x 0 ∈ I) (hp : 0 < w (x 0)) :
    model2DSectional w x = radialScalarCurvature w (x 0) := by
  rw [model2DSectional_eq_quotient hI hw hx hp, radialScalarCurvature_eq hI hw hx hp]

end AffineQuadric
