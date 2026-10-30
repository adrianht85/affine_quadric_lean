import AffineQuadric.MechanicalClock
import AffineQuadric.RadiusBounds
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Tactic

/-! Stage B: the temporal obstruction. The hypotheses of the intermediate
lemmas are scalar differential equations, not hypotheses of Theorem 4.1. -/
noncomputable section
open Set Filter
open scoped Topology
namespace AffineQuadric

theorem interval_constant_of_hasDerivAt_zero {I : Set ℝ} (hI : IsOpen I)
    (hc : IsPreconnected I) {f : ℝ → ℝ} (hd : ∀ x ∈ I, HasDerivAt f 0 x)
    {x y : ℝ} (hx : x ∈ I) (hy : y ∈ I) : f x = f y := by
  exact hI.is_const_of_deriv_eq_zero hc
    (fun z hz => (hd z hz).differentiableAt.differentiableWithinAt)
    (fun z hz => (hd z hz).deriv) hx hy

theorem third_derivative_zero_quadratic {I : Set ℝ} (hI : IsOpen I)
    (hc : IsPreconnected I) (hne : I.Nonempty) {a a₁ a₂ : ℝ → ℝ}
    (ha : ∀ τ ∈ I, HasDerivAt a (a₁ τ) τ)
    (ha₁ : ∀ τ ∈ I, HasDerivAt a₁ (a₂ τ) τ)
    (ha₂ : ∀ τ ∈ I, HasDerivAt a₂ 0 τ) :
    ∃ c₂ c₁ c₀ : ℝ, ∀ τ ∈ I, a τ = c₂ * τ ^ 2 + c₁ * τ + c₀ := by
  obtain ⟨s, hs⟩ := hne
  have h2 : ∀ τ ∈ I, a₂ τ = a₂ s := fun τ hτ =>
    interval_constant_of_hasDerivAt_zero hI hc ha₂ hτ hs
  have hg1 : ∀ τ ∈ I, HasDerivAt (fun x => a₁ x - a₂ s * x) 0 τ := by
    intro τ hτ
    convert (ha₁ τ hτ).sub ((hasDerivAt_id τ).const_mul (a₂ s)) using 1
    simp [h2 τ hτ]
  have h1 : ∀ τ ∈ I, a₁ τ = a₂ s * τ + (a₁ s - a₂ s * s) := by
    intro τ hτ
    have hh := interval_constant_of_hasDerivAt_zero hI hc hg1 hτ hs
    linarith
  let c₂ := a₂ s / 2
  let c₁ := a₁ s - a₂ s * s
  have hg0 : ∀ τ ∈ I, HasDerivAt (fun x => a x - c₂ * x ^ 2 - c₁ * x) 0 τ := by
    intro τ hτ
    convert ((ha τ hτ).sub (((hasDerivAt_id τ).pow 2).const_mul c₂)).sub
      ((hasDerivAt_id τ).const_mul c₁) using 1
    dsimp [c₂, c₁]
    nlinarith [h1 τ hτ]
  refine ⟨c₂, c₁, a s - c₂ * s ^ 2 - c₁ * s, ?_⟩
  intro τ hτ
  have hh := interval_constant_of_hasDerivAt_zero hI hc hg0 hτ hs
  linarith

def shapeUpperAux (x : ℝ) : ℝ := (x + 1) * Real.sinh x - x * Real.cosh x

theorem shapeUpperAux_hasDerivAt (x : ℝ) :
    HasDerivAt shapeUpperAux (Real.sinh x + x * (Real.cosh x - Real.sinh x)) x := by
  convert (((hasDerivAt_id x).add_const 1).mul (Real.hasDerivAt_sinh x)).sub
    ((hasDerivAt_id x).mul (Real.hasDerivAt_cosh x)) using 1
  dsimp
  ring

theorem hyperbolicShape_lt_parameter {x : ℝ} (hx : 0 < x) : hyperbolicShape x < x := by
  have hm : 0 < shapeUpperAux x := by
    apply positive_from_zero_derivative (by simp [shapeUpperAux]) shapeUpperAux_hasDerivAt _ hx
    intro y hy
    have he : 0 < Real.cosh y - Real.sinh y := by
      rw [Real.cosh_eq, Real.sinh_eq]
      nlinarith [Real.exp_pos (-y)]
    exact add_pos (Real.sinh_pos_iff.mpr hy) (mul_pos hy he)
  dsimp [hyperbolicShape]
  have hs := Real.sinh_pos_iff.mpr hx
  have hh : x * Real.cosh x < (x + 1) * Real.sinh x := by
    dsimp [shapeUpperAux] at hm
    linarith
  have hh' := (div_lt_iff₀ hs).mpr hh
  linarith

theorem hyperbolicShape_tendsto_zero_right :
    Tendsto hyperbolicShape (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  apply squeeze_zero' _ _ (tendsto_id.mono_left inf_le_left)
  · exact eventually_mem_nhdsWithin.mono (fun x hx => (hyperbolicShape_pos hx).le)
  · exact eventually_mem_nhdsWithin.mono (fun x hx => (hyperbolicShape_lt_parameter hx).le)

theorem mechanicalTime_strictMonoOn : StrictMonoOn mechanicalTime (Ioi 0) := by
  apply strictMonoOn_of_deriv_pos (convex_Ioi 0)
  · exact fun x _ => (mechanicalTime_hasDerivAt x).continuousAt.continuousWithinAt
  · intro x hx
    rw [interior_Ioi] at hx
    exact mechanicalTime_deriv_pos hx

theorem mechanicalClock_right_inverse {I : Set ℝ} {t : ℝ → ℝ}
    (clock : RegularMechanicalClockOn I t) {x : ℝ} (hx : 0 < x)
    (hTx : mechanicalTime x ∈ I) : t (mechanicalTime x) = x := by
  apply mechanicalTime_strictMonoOn.injOn (clock.positive _ hTx) hx
  exact clock.inverse _ hTx

def temporalPolynomialProfile (c₂ c₁ c₀ : ℝ) (x : ℝ) : ℝ :=
  (c₂ * mechanicalTime x ^ 2 + c₁ * mechanicalTime x + c₀) * hyperbolicShape x ^ 3

theorem mechanicalTime_analyticAt (x : ℝ) : AnalyticAt ℝ mechanicalTime x := by
  exact (((Real.analyticAt_sinh.mul Real.analyticAt_cosh).sub analyticAt_id).div
    analyticAt_const (by norm_num : (2 : ℝ) ≠ 0))

theorem hyperbolicShape_analyticAt {x : ℝ} (hx : 0 < x) :
    AnalyticAt ℝ hyperbolicShape x := by
  exact ((analyticAt_id.mul Real.analyticAt_cosh).div Real.analyticAt_sinh
    (ne_of_gt (Real.sinh_pos_iff.mpr hx))).sub analyticAt_const

theorem temporalPolynomialProfile_analytic (c₂ c₁ c₀ : ℝ) :
    AnalyticOnNhd ℝ (temporalPolynomialProfile c₂ c₁ c₀) (Ioi 0) := by
  intro x hx
  exact (((analyticAt_const.mul ((mechanicalTime_analyticAt x).pow 2)).add
    (analyticAt_const.mul (mechanicalTime_analyticAt x))).add analyticAt_const).mul
    ((hyperbolicShape_analyticAt hx).pow 3)

theorem temporalPolynomialProfile_tendsto_zero (c₂ c₁ c₀ : ℝ) :
    Tendsto (temporalPolynomialProfile c₂ c₁ c₀) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  have hT : Tendsto mechanicalTime (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have ht := (mechanicalTime_hasDerivAt 0).continuousAt.tendsto.mono_left
      (inf_le_left : 𝓝[>] (0 : ℝ) ≤ 𝓝 0)
    simpa [mechanicalTime, timeNumerator] using ht
  have hh := ((((tendsto_const_nhds (x := c₂)).mul (hT.pow 2)).add
    ((tendsto_const_nhds (x := c₁)).mul hT)).add (tendsto_const_nhds (x := c₀))).mul
    (hyperbolicShape_tendsto_zero_right.pow 3)
  simpa [temporalPolynomialProfile] using hh

/-- Analytic continuation is applied only to the explicit direct-parameter
profile after polynomiality has been proved; the coefficients need not be analytic. -/
theorem temporalPolynomialProfile_constant_zero {I : Set ℝ} (hI : IsOpen I)
    (hne : I.Nonempty) {t : ℝ → ℝ} (clock : RegularMechanicalClockOn I t)
    (c₂ c₁ c₀ C : ℝ)
    (hC : ∀ τ ∈ I, (c₂ * τ ^ 2 + c₁ * τ + c₀) * hyperbolicShape (t τ) ^ 3 = C) : C = 0 := by
  obtain ⟨s, hs⟩ := hne
  let x₀ := t s
  have hx₀ : x₀ ∈ Ioi (0 : ℝ) := clock.positive s hs
  have ho : IsOpen (Ioi (0 : ℝ) ∩ mechanicalTime ⁻¹' I) :=
    isOpen_Ioi.inter (hI.preimage (continuous_iff_continuousAt.mpr
      (fun x => (mechanicalTime_hasDerivAt x).continuousAt)))
  have hm : x₀ ∈ Ioi (0 : ℝ) ∩ mechanicalTime ⁻¹' I :=
    ⟨hx₀, by simpa [x₀, clock.inverse s hs] using hs⟩
  have he : temporalPolynomialProfile c₂ c₁ c₀ =ᶠ[𝓝 x₀] (fun _ => C) := by
    apply Filter.eventually_of_mem (ho.mem_nhds hm)
    intro x hx
    have hh := hC (mechanicalTime x) hx.2
    rw [mechanicalClock_right_inverse clock hx.1 hx.2] at hh
    exact hh
  have hall := (temporalPolynomialProfile_analytic c₂ c₁ c₀).eqOn_of_preconnected_of_eventuallyEq
    (fun _ _ => analyticAt_const) (convex_Ioi (0 : ℝ)).isPreconnected hx₀ he
  have he' : temporalPolynomialProfile c₂ c₁ c₀ =ᶠ[𝓝[>] (0 : ℝ)] (fun _ => C) :=
    eventually_mem_nhdsWithin.mono (fun x hx => hall hx)
  have hlim : Tendsto (temporalPolynomialProfile c₂ c₁ c₀) (𝓝[>] (0 : ℝ)) (𝓝 C) :=
    tendsto_const_nhds.congr' he'.symm
  exact tendsto_nhds_unique hlim (temporalPolynomialProfile_tendsto_zero c₂ c₁ c₀)

theorem clockShape_hasDerivAt {I : Set ℝ} (hI : IsOpen I) {t : ℝ → ℝ}
    (clock : RegularMechanicalClockOn I t) {τ : ℝ} (hτ : τ ∈ I) :
    HasDerivAt (fun x => hyperbolicShape (t x))
      (hyperbolicShapeSlope (t τ) / Real.sinh (t τ) ^ 2) τ := by
  convert (hyperbolicShape_hasDerivAt (clock.positive τ hτ)).comp τ
    (mechanicalClock_hasDerivAt hI clock hτ) using 1
  ring

theorem obstruction_product_hasDerivAt_zero {I : Set ℝ} (hI : IsOpen I)
    {t a : ℝ → ℝ} (clock : RegularMechanicalClockOn I t) {τ a₁ : ℝ} (hτ : τ ∈ I)
    (ha : HasDerivAt a a₁ τ)
    (hobs : (4 / 3 : ℝ) * a₁ * hyperbolicTimeCoefficient t τ +
      2 * a τ * shapeSquareTauRate (t τ) = 0) :
    HasDerivAt (fun x => a x * hyperbolicShape (t x) ^ 3) 0 τ := by
  apply (ha.mul ((clockShape_hasDerivAt hI clock hτ).pow 3)).congr_deriv
  dsimp [hyperbolicTimeCoefficient, shapeSquareTauRate] at hobs ⊢
  linear_combination (3 / 4 : ℝ) * hyperbolicShape (t τ) * hobs

/-- Complete scalar temporal obstruction on any nonempty open connected interval.
This is an intermediate theorem: its scalar differential hypotheses must still
be deduced from the determining system to obtain Theorem 4.1. -/
theorem quadratic_temporal_obstruction {I : Set ℝ} (hI : IsOpen I)
    (hc : IsPreconnected I) (hne : I.Nonempty) {t a a₁ a₂ : ℝ → ℝ}
    (clock : RegularMechanicalClockOn I t)
    (ha : ∀ τ ∈ I, HasDerivAt a (a₁ τ) τ)
    (ha₁ : ∀ τ ∈ I, HasDerivAt a₁ (a₂ τ) τ)
    (ha₂ : ∀ τ ∈ I, HasDerivAt a₂ 0 τ)
    (hobs : ∀ τ ∈ I, (4 / 3 : ℝ) * a₁ τ * hyperbolicTimeCoefficient t τ +
      2 * a τ * shapeSquareTauRate (t τ) = 0) :
    ∀ τ ∈ I, a τ = 0 ∧ a₁ τ = 0 ∧ a₂ τ = 0 := by
  obtain ⟨c₂, c₁, c₀, hpoly⟩ := third_derivative_zero_quadratic hI hc hne ha ha₁ ha₂
  obtain ⟨s, hs⟩ := hne
  let C := a s * hyperbolicShape (t s) ^ 3
  have hprod : ∀ τ ∈ I, a τ * hyperbolicShape (t τ) ^ 3 = C := by
    intro τ hτ
    exact interval_constant_of_hasDerivAt_zero hI hc
      (fun x hx => obstruction_product_hasDerivAt_zero hI clock hx (ha x hx) (hobs x hx)) hτ hs
  have hC : C = 0 := temporalPolynomialProfile_constant_zero hI ⟨s, hs⟩ clock c₂ c₁ c₀ C
    (fun τ hτ => by rw [← hpoly τ hτ]; exact hprod τ hτ)
  have ha0 : ∀ τ ∈ I, a τ = 0 := by
    intro τ hτ
    have hh := hprod τ hτ
    rw [hC] at hh
    exact (mul_eq_zero.mp hh).resolve_right
      (pow_ne_zero _ (ne_of_gt (hyperbolicShape_pos (clock.positive τ hτ))))
  have ha10 : ∀ τ ∈ I, a₁ τ = 0 := by
    intro τ hτ
    have he : a =ᶠ[𝓝 τ] (fun _ : ℝ => (0 : ℝ)) :=
      Filter.eventually_of_mem (hI.mem_nhds hτ) (fun x hx => ha0 x hx)
    exact ((hasDerivAt_const τ (0 : ℝ)).congr_of_eventuallyEq he).unique (ha τ hτ) |>.symm
  intro τ hτ
  refine ⟨ha0 τ hτ, ha10 τ hτ, ?_⟩
  have he : a₁ =ᶠ[𝓝 τ] (fun _ : ℝ => (0 : ℝ)) :=
    Filter.eventually_of_mem (hI.mem_nhds hτ) (fun x hx => ha10 x hx)
  exact ((hasDerivAt_const τ (0 : ℝ)).congr_of_eventuallyEq he).unique (ha₁ τ hτ) |>.symm

end AffineQuadric
