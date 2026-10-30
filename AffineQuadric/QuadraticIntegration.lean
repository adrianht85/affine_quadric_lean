import AffineQuadric.QuadraticDetermining
import AffineQuadric.QuadraticTemporal

/-! Spatial integration of the determining equations. The integration functions
are constructed by evaluation at Z=1; no polynomial ansatz in time is imposed. -/
noncomputable section
open Set Filter
open scoped Topology ContDiff
namespace AffineQuadric

theorem smooth_time_slice {I : Set ℝ} {A : ℝ → ℝ → ℝ}
    (hA : ContDiffOn ℝ ∞ (Function.uncurry A) (I ×ˢ Ioi 0))
    {z : ℝ} (hz : 0 < z) : ContDiffOn ℝ ∞ (fun τ => A τ z) I := by
  exact hA.comp ((contDiff_id.prodMk contDiff_const).contDiffOn) (fun _ hτ => ⟨hτ, hz⟩)

theorem smooth_deriv_on_open {I : Set ℝ} (hI : IsOpen I) {f : ℝ → ℝ}
    (hf : ContDiffOn ℝ ∞ f I) : ContDiffOn ℝ ∞ (deriv f) I :=
  hf.deriv_of_isOpen hI (by simp)

theorem smooth_hasDerivAt_on_open {I : Set ℝ} (hI : IsOpen I) {f : ℝ → ℝ}
    (hf : ContDiffOn ℝ ∞ f I) {τ : ℝ} (hτ : τ ∈ I) : HasDerivAt f (deriv f τ) τ :=
  ((hf.contDiffAt (hI.mem_nhds hτ)).differentiableAt (by simp)).hasDerivAt

theorem hasDerivAt_congr_on_open {I : Set ℝ} (hI : IsOpen I) {f g : ℝ → ℝ}
    (he : ∀ x ∈ I, f x = g x) {τ d : ℝ} (hτ : τ ∈ I) (hg : HasDerivAt g d τ) :
    HasDerivAt f d τ :=
  hg.congr_of_eventuallyEq (Filter.eventually_of_mem (hI.mem_nhds hτ) (fun x hx => he x hx))

theorem quadratic_leading_independent {I : Set ℝ} (hI : IsOpen I)
    {K : ℝ → ℝ} {A₂ A₁ A₀ : ℝ → ℝ → ℝ} (hA : SmoothQuadraticOn I A₂ A₁ A₀)
    (he : ∀ τ ∈ I, ∀ z, 0 < z → QuadraticDeterminingAt K A₂ A₁ A₀ τ z)
    {τ z : ℝ} (hτ : τ ∈ I) (hz : 0 < z) : A₂ τ z = A₂ τ 1 := by
  apply interval_constant_of_hasDerivAt_zero isOpen_Ioi (convex_Ioi (0 : ℝ)).isPreconnected _ hz (by norm_num)
  intro x hx
  have hd := (smooth_coefficient_slices hI hA.smooth₂ hτ hx).2.hasDerivAt
  exact hd.congr_deriv (he τ hτ x hx).cubic

theorem quadratic_leading_time_derivative {I : Set ℝ} (hI : IsOpen I)
    {K : ℝ → ℝ} {A₂ A₁ A₀ : ℝ → ℝ → ℝ} (hA : SmoothQuadraticOn I A₂ A₁ A₀)
    (he : ∀ τ ∈ I, ∀ z, 0 < z → QuadraticDeterminingAt K A₂ A₁ A₀ τ z)
    {τ z : ℝ} (hτ : τ ∈ I) (hz : 0 < z) :
    coefficientTimeDeriv A₂ τ z = deriv (fun x => A₂ x 1) τ := by
  exact (hasDerivAt_congr_on_open hI
    (fun x hx => quadratic_leading_independent hI hA he hx hz) hτ
    (smooth_hasDerivAt_on_open hI (smooth_time_slice hA.smooth₂ (by norm_num)) hτ)).deriv

theorem quadratic_linear_integrated {I : Set ℝ} (hI : IsOpen I)
    {K : ℝ → ℝ} {A₂ A₁ A₀ : ℝ → ℝ → ℝ} (hA : SmoothQuadraticOn I A₂ A₁ A₀)
    (he : ∀ τ ∈ I, ∀ z, 0 < z → QuadraticDeterminingAt K A₂ A₁ A₀ τ z)
    {τ z : ℝ} (hτ : τ ∈ I) (hz : 0 < z) :
    A₁ τ z = -deriv (fun x => A₂ x 1) τ * z +
      (A₁ τ 1 + deriv (fun x => A₂ x 1) τ) := by
  let a₁ := deriv (fun x => A₂ x 1) τ
  have hd : ∀ x ∈ Ioi (0 : ℝ), HasDerivAt (fun y => A₁ τ y + a₁ * y) 0 x := by
    intro x hx
    have hs := (he τ hτ x hx).square
    rw [quadratic_leading_time_derivative hI hA he hτ hx] at hs
    apply ((smooth_coefficient_slices hI hA.smooth₁ hτ hx).2.hasDerivAt.add
      ((hasDerivAt_id x).const_mul a₁)).congr_deriv
    change coefficientPositionDeriv A₁ τ x + a₁ * 1 = 0
    dsimp [a₁]
    linarith
  have hh := interval_constant_of_hasDerivAt_zero isOpen_Ioi
    (convex_Ioi (0 : ℝ)).isPreconnected hd hz (by norm_num : (1 : ℝ) ∈ Ioi 0)
  dsimp [a₁] at hh
  linarith

structure IntegratedQuadraticOn (I : Set ℝ) (K : ℝ → ℝ) (A₂ A₁ A₀ : ℝ → ℝ → ℝ) where
  a : ℝ → ℝ
  b : ℝ → ℝ
  d : ℝ → ℝ
  a_smooth : ContDiffOn ℝ ∞ a I
  b_smooth : ContDiffOn ℝ ∞ b I
  d_diff : ∀ τ ∈ I, DifferentiableAt ℝ d τ
  leading : ∀ τ ∈ I, ∀ z, 0 < z → A₂ τ z = a τ
  linear : ∀ τ ∈ I, ∀ z, 0 < z → A₁ τ z = -deriv a τ * z + b τ
  constant : ∀ τ ∈ I, ∀ z, 0 < z → A₀ τ z =
    -9 * a τ * K τ * z ^ (-2 / 3 : ℝ) + deriv (deriv a) τ * z ^ 2 / 2 - deriv b τ * z + d τ

theorem quadratic_linear_time_derivative {I : Set ℝ} (hI : IsOpen I)
    {A₁ : ℝ → ℝ → ℝ} {a b : ℝ → ℝ}
    (ha : ContDiffOn ℝ ∞ a I) (hb : ContDiffOn ℝ ∞ b I)
    (hlin : ∀ τ ∈ I, ∀ z, 0 < z → A₁ τ z = -deriv a τ * z + b τ)
    {τ z : ℝ} (hτ : τ ∈ I) (hz : 0 < z) :
    coefficientTimeDeriv A₁ τ z = -deriv (deriv a) τ * z + deriv b τ := by
  exact (hasDerivAt_congr_on_open hI (fun x hx => hlin x hx z hz) hτ
    (((smooth_hasDerivAt_on_open hI (smooth_deriv_on_open hI ha) hτ).neg.mul_const z).add
      (smooth_hasDerivAt_on_open hI hb hτ))).deriv

theorem quadratic_constant_integrated {I : Set ℝ} (hI : IsOpen I)
    {K a b : ℝ → ℝ} {A₂ A₁ A₀ : ℝ → ℝ → ℝ}
    (hA : SmoothQuadraticOn I A₂ A₁ A₀)
    (he : ∀ τ ∈ I, ∀ z, 0 < z → QuadraticDeterminingAt K A₂ A₁ A₀ τ z)
    (ha : ContDiffOn ℝ ∞ a I) (hb : ContDiffOn ℝ ∞ b I)
    (hlead : ∀ τ ∈ I, ∀ z, 0 < z → A₂ τ z = a τ)
    (hlin : ∀ τ ∈ I, ∀ z, 0 < z → A₁ τ z = -deriv a τ * z + b τ)
    {τ z : ℝ} (hτ : τ ∈ I) (hz : 0 < z) :
    A₀ τ z = -9 * a τ * K τ * z ^ (-2 / 3 : ℝ) + deriv (deriv a) τ * z ^ 2 / 2 -
      deriv b τ * z + (A₀ τ 1 + 9 * a τ * K τ - deriv (deriv a) τ / 2 + deriv b τ) := by
  let g := fun x => A₀ τ x + 9 * a τ * K τ * x ^ (-2 / 3 : ℝ) -
    deriv (deriv a) τ * x ^ 2 / 2 + deriv b τ * x
  have hd : ∀ x ∈ Ioi (0 : ℝ), HasDerivAt g 0 x := by
    intro x hx
    have hh := (he τ hτ x hx).linear
    rw [quadratic_linear_time_derivative hI ha hb hlin hτ hx, hlead τ hτ x hx] at hh
    have hp := (hasDerivAt_id x).rpow_const (p := (-2 / 3 : ℝ)) (Or.inl (ne_of_gt hx))
    apply ((((smooth_coefficient_slices hI hA.smooth₀ hτ hx).2.hasDerivAt.add
      (hp.const_mul (9 * a τ * K τ))).sub
      ((((hasDerivAt_id x).pow 2).const_mul (deriv (deriv a) τ)).div_const 2)).add
      ((hasDerivAt_id x).const_mul (deriv b τ))).congr_deriv
    dsimp [newtonianForce, coefficientPositionDeriv] at hh ⊢
    rw [show (-2 / 3 : ℝ) - 1 = (-5 / 3 : ℝ) by norm_num]
    linear_combination hh
  have hh := interval_constant_of_hasDerivAt_zero isOpen_Ioi
    (convex_Ioi (0 : ℝ)).isPreconnected hd hz (by norm_num : (1 : ℝ) ∈ Ioi 0)
  dsimp [g] at hh
  norm_num only [Real.one_rpow, one_pow, mul_one] at hh
  linarith

theorem quadratic_integrated_from_determining {I : Set ℝ} (hI : IsOpen I)
    {K : ℝ → ℝ} {A₂ A₁ A₀ : ℝ → ℝ → ℝ} (hA : SmoothQuadraticOn I A₂ A₁ A₀)
    (hK : ∀ τ ∈ I, DifferentiableAt ℝ K τ)
    (he : ∀ τ ∈ I, ∀ z, 0 < z → QuadraticDeterminingAt K A₂ A₁ A₀ τ z) :
    Nonempty (IntegratedQuadraticOn I K A₂ A₁ A₀) := by
  let a := fun τ => A₂ τ 1
  let b := fun τ => A₁ τ 1 + deriv a τ
  let d := fun τ => A₀ τ 1 + 9 * a τ * K τ - deriv (deriv a) τ / 2 + deriv b τ
  have ha : ContDiffOn ℝ ∞ a I := smooth_time_slice hA.smooth₂ (by norm_num)
  have hb : ContDiffOn ℝ ∞ b I :=
    (smooth_time_slice hA.smooth₁ (by norm_num)).add (smooth_deriv_on_open hI ha)
  have hlead : ∀ τ ∈ I, ∀ z, 0 < z → A₂ τ z = a τ := by
    intro τ hτ z hz
    exact quadratic_leading_independent hI hA he hτ hz
  have hlin : ∀ τ ∈ I, ∀ z, 0 < z → A₁ τ z = -deriv a τ * z + b τ := by
    intro τ hτ z hz
    exact quadratic_linear_integrated hI hA he hτ hz
  refine ⟨⟨a, b, d, ha, hb, ?_, hlead, hlin, ?_⟩⟩
  · intro τ hτ
    have ha0 := (smooth_hasDerivAt_on_open hI ha hτ).differentiableAt
    have ha2 := (smooth_hasDerivAt_on_open hI
      (smooth_deriv_on_open hI (smooth_deriv_on_open hI ha)) hτ).differentiableAt
    have hb1 := (smooth_hasDerivAt_on_open hI (smooth_deriv_on_open hI hb) hτ).differentiableAt
    exact (((smooth_coefficient_slices hI hA.smooth₀ hτ (by norm_num : (0 : ℝ) < 1)).1.add
      ((ha0.const_mul 9).mul (hK τ hτ))).sub (ha2.div_const 2)).add hb1
  · intro τ hτ z hz
    exact quadratic_constant_integrated hI hA he ha hb hlead hlin hτ hz

theorem quadratic_integrated_residual {I : Set ℝ} (hI : IsOpen I)
    {K : ℝ → ℝ} {A₂ A₁ A₀ : ℝ → ℝ → ℝ}
    (h : IntegratedQuadraticOn I K A₂ A₁ A₀)
    (hK : ∀ τ ∈ I, DifferentiableAt ℝ K τ)
    (he : ∀ τ ∈ I, ∀ z, 0 < z → QuadraticDeterminingAt K A₂ A₁ A₀ τ z)
    {τ z : ℝ} (hτ : τ ∈ I) (hz : 0 < z) :
    deriv (deriv (deriv h.a)) τ * z ^ 2 / 2 - deriv (deriv h.b) τ * z + deriv h.d τ -
      (6 * deriv h.a τ * K τ + 9 * h.a τ * deriv K τ) * z ^ (-2 / 3 : ℝ) -
      3 * h.b τ * K τ * z ^ (-5 / 3 : ℝ) = 0 := by
  have hd := ((((((smooth_hasDerivAt_on_open hI h.a_smooth hτ).const_mul (-9)).mul
    (hK τ hτ).hasDerivAt).mul_const (z ^ (-2 / 3 : ℝ))).add
    (((smooth_hasDerivAt_on_open hI
      (smooth_deriv_on_open hI (smooth_deriv_on_open hI h.a_smooth)) hτ).mul_const (z ^ 2)).div_const 2)).sub
    ((smooth_hasDerivAt_on_open hI (smooth_deriv_on_open hI h.b_smooth) hτ).mul_const z)).add
    (h.d_diff τ hτ).hasDerivAt
  have ht := (hasDerivAt_congr_on_open hI (fun x hx => h.constant x hx z hz) hτ hd).deriv
  have hh := (he τ hτ z hz).constant
  rw [show coefficientTimeDeriv A₀ τ z = _ from ht, h.linear τ hτ z hz] at hh
  dsimp [newtonianForce] at hh
  have hp : z ^ (-2 / 3 : ℝ) = z * z ^ (-5 / 3 : ℝ) := by
    calc
      z ^ (-2 / 3 : ℝ) = z ^ ((1 : ℝ) + (-5 / 3 : ℝ)) := by congr 1; norm_num
      _ = z ^ (1 : ℝ) * z ^ (-5 / 3 : ℝ) := Real.rpow_add hz _ _
      _ = z * z ^ (-5 / 3 : ℝ) := by rw [Real.rpow_one]
  rw [hp] at hh ⊢
  linear_combination hh

end AffineQuadric
