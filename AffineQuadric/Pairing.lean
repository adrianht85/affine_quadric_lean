import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Tactic

/-! Direct Abel proof of PE V8, Proposition 4.3, in the original (u,v) variables.
The background and the radial and variational solutions are given, not constructed.
-/
noncomputable section
namespace AffineQuadric

/-- Scalar acceleration, with the declared background derivatives as arguments. -/
def radialF (a a₁ V V₁ x y : ℝ) : ℝ :=
  (2 * V₁ / V) * y - (2 * x * y ^ 2 + 2 * a * a₁ * y) / (x ^ 2 - a ^ 2)

def radialFx (a a₁ x y : ℝ) : ℝ :=
  (2 * (x ^ 2 + a ^ 2) * y ^ 2 + 4 * x * a * a₁ * y) / (x ^ 2 - a ^ 2) ^ 2

def radialFy (a a₁ V V₁ x y : ℝ) : ℝ :=
  2 * V₁ / V - (4 * x * y + 2 * a * a₁) / (x ^ 2 - a ^ 2)

theorem radialF_partial_x (a a₁ V V₁ x y : ℝ) (hX : x ^ 2 - a ^ 2 ≠ 0) :
    HasDerivAt (fun z => radialF a a₁ V V₁ z y) (radialFx a a₁ x y) x := by
  convert (hasDerivAt_const x ((2 * V₁ / V) * y)).sub
    ((((hasDerivAt_id x).const_mul (2 * y ^ 2)).add_const (2 * a * a₁ * y)).div
      (((hasDerivAt_id x).pow 2).sub_const (a ^ 2)) hX) using 1
  · funext z
    dsimp [radialF]
    ring
  · dsimp [radialFx]
    field_simp
    ring

theorem radialF_partial_y (a a₁ V V₁ x y : ℝ) (hX : x ^ 2 - a ^ 2 ≠ 0) :
    HasDerivAt (fun z => radialF a a₁ V V₁ x z) (radialFy a a₁ V V₁ x y) y := by
  convert ((hasDerivAt_id y).const_mul (2 * V₁ / V)).sub
    (((((hasDerivAt_id y).pow 2).const_mul (2 * x)).add
      ((hasDerivAt_id y).const_mul (2 * a * a₁))).div_const (x ^ 2 - a ^ 2)) using 1
  dsimp [radialFy]
  field_simp
  ring

/-- The positive branch of the momentum in eq:balance. -/
def radialMomentum (a V u v : ℝ → ℝ) (s : ℝ) : ℝ :=
  Real.sqrt (2 * V s ^ 2 * (u s ^ 2 - a s ^ 2) / v s)

def variationDet (ξ₁ ζ₁ ξ₂ ζ₂ : ℝ → ℝ) (s : ℝ) : ℝ :=
  ξ₁ s * ζ₂ s - ξ₂ s * ζ₁ s

def radialWeight (a V u v : ℝ → ℝ) (s : ℝ) : ℝ :=
  -radialMomentum a V u v s / (2 * v s)

def radialPairing (a V u v ξ₁ ζ₁ ξ₂ ζ₂ : ℝ → ℝ) (s : ℝ) : ℝ :=
  radialWeight a V u v s * variationDet ξ₁ ζ₁ ξ₂ ζ₂ s

/-- Only pointwise admissibility, actual derivatives and the scalar ODE are inputs. -/
structure RadialSolutionOn (I : Set ℝ) (a a₁ V V₁ u v : ℝ → ℝ) : Prop where
  V_pos : ∀ s ∈ I, 0 < V s
  X_pos : ∀ s ∈ I, 0 < u s ^ 2 - a s ^ 2
  v_pos : ∀ s ∈ I, 0 < v s
  da : ∀ s ∈ I, HasDerivAt a (a₁ s) s
  dV : ∀ s ∈ I, HasDerivAt V (V₁ s) s
  du : ∀ s ∈ I, HasDerivAt u (v s) s
  dv : ∀ s ∈ I, HasDerivAt v (radialF (a s) (a₁ s) (V s) (V₁ s) (u s) (v s)) s

/-- These coefficients are certified as state partial derivatives by the two lemmas above. -/
structure RadialVariationOn (I : Set ℝ) (a a₁ V V₁ u v ξ ζ : ℝ → ℝ) : Prop where
  dξ : ∀ s ∈ I, HasDerivAt ξ (ζ s) s
  dζ : ∀ s ∈ I, HasDerivAt ζ
    (radialFx (a s) (a₁ s) (u s) (v s) * ξ s +
      radialFy (a s) (a₁ s) (V s) (V₁ s) (u s) (v s) * ζ s) s

theorem variationDet_hasDerivAt {ξ₁ ζ₁ ξ₂ ζ₂ : ℝ → ℝ} {s A B : ℝ}
    (hξ₁ : HasDerivAt ξ₁ (ζ₁ s) s) (hξ₂ : HasDerivAt ξ₂ (ζ₂ s) s)
    (hζ₁ : HasDerivAt ζ₁ (A * ξ₁ s + B * ζ₁ s) s)
    (hζ₂ : HasDerivAt ζ₂ (A * ξ₂ s + B * ζ₂ s) s) :
    HasDerivAt (variationDet ξ₁ ζ₁ ξ₂ ζ₂) (B * variationDet ξ₁ ζ₁ ξ₂ ζ₂ s) s := by
  convert (hξ₁.mul hζ₂).sub (hξ₂.mul hζ₁) using 1
  dsimp [variationDet]
  ring

theorem radialMomentum_pos {a V u v : ℝ → ℝ} {s : ℝ}
    (hV : 0 < V s) (hX : 0 < u s ^ 2 - a s ^ 2) (hv : 0 < v s) :
    0 < radialMomentum a V u v s := by
  exact Real.sqrt_pos.2 (div_pos (mul_pos (mul_pos (by norm_num) (sq_pos_of_pos hV)) hX) hv)

theorem radialMomentum_sq {a V u v : ℝ → ℝ} {s : ℝ}
    (hV : 0 < V s) (hX : 0 < u s ^ 2 - a s ^ 2) (hv : 0 < v s) :
    radialMomentum a V u v s ^ 2 = 2 * V s ^ 2 * (u s ^ 2 - a s ^ 2) / v s := by
  exact Real.sq_sqrt (le_of_lt (div_pos
    (mul_pos (mul_pos (by norm_num) (sq_pos_of_pos hV)) hX) hv))

/-- Logarithmic differentiation of the radicand, using the scalar ODE, not a balance input. -/
theorem momentumRadicand_hasDerivAt {a a₁ V V₁ u v : ℝ → ℝ} {s : ℝ}
    (hV : V s ≠ 0) (hX : u s ^ 2 - a s ^ 2 ≠ 0) (hv : v s ≠ 0)
    (ha : HasDerivAt a (a₁ s) s) (hVd : HasDerivAt V (V₁ s) s)
    (hu : HasDerivAt u (v s) s)
    (hvd : HasDerivAt v (radialF (a s) (a₁ s) (V s) (V₁ s) (u s) (v s)) s) :
    HasDerivAt (fun t => 2 * V t ^ 2 * (u t ^ 2 - a t ^ 2) / v t)
      (8 * u s * V s ^ 2) s := by
  convert (((hVd.pow 2).const_mul 2).mul ((hu.pow 2).sub (ha.pow 2))).div hvd hv using 1
  dsimp [radialF]
  field_simp
  ring

theorem momentum_sqrt_rate (V X v p u : ℝ) (hX : X ≠ 0) (hv : v ≠ 0) (hp : p ≠ 0)
    (hsq : p ^ 2 = 2 * V ^ 2 * X / v) :
    (8 * u * V ^ 2) / (2 * p) = p * (2 * u * v / X) := by
  calc
    (8 * u * V ^ 2) / (2 * p) = (2 * u / X) * ((2 * V ^ 2 * X / v) / p) * v := by
      field_simp
      ring
    _ = (2 * u / X) * (p ^ 2 / p) * v := by rw [← hsq]
    _ = p * (2 * u * v / X) := by field_simp

/-- The derivative of the positive square root is derived from its definition. -/
theorem radialMomentum_hasDerivAt {I : Set ℝ} {a a₁ V V₁ u v : ℝ → ℝ}
    (h : RadialSolutionOn I a a₁ V V₁ u v) {s : ℝ} (hs : s ∈ I) :
    HasDerivAt (radialMomentum a V u v)
      (radialMomentum a V u v s * (2 * u s * v s / (u s ^ 2 - a s ^ 2))) s := by
  have hrad := momentumRadicand_hasDerivAt (ne_of_gt (h.V_pos s hs))
    (ne_of_gt (h.X_pos s hs)) (ne_of_gt (h.v_pos s hs))
    (h.da s hs) (h.dV s hs) (h.du s hs) (h.dv s hs)
  have harg : 0 < 2 * V s ^ 2 * (u s ^ 2 - a s ^ 2) / v s :=
    div_pos (mul_pos (mul_pos (by norm_num) (sq_pos_of_pos (h.V_pos s hs)))
      (h.X_pos s hs)) (h.v_pos s hs)
  convert hrad.sqrt (ne_of_gt harg) using 1
  exact (momentum_sqrt_rate (V s) (u s ^ 2 - a s ^ 2) (v s)
    (radialMomentum a V u v s) (u s) (ne_of_gt (h.X_pos s hs))
    (ne_of_gt (h.v_pos s hs)) (ne_of_gt (radialMomentum_pos
      (h.V_pos s hs) (h.X_pos s hs) (h.v_pos s hs)))
    (radialMomentum_sq (h.V_pos s hs) (h.X_pos s hs) (h.v_pos s hs))).symm

theorem radialMomentum_log_balance {I : Set ℝ} {a a₁ V V₁ u v : ℝ → ℝ}
    (h : RadialSolutionOn I a a₁ V V₁ u v) {s : ℝ} (hs : s ∈ I) :
    deriv (radialMomentum a V u v) s / radialMomentum a V u v s =
      2 * u s * v s / (u s ^ 2 - a s ^ 2) := by
  rw [(radialMomentum_hasDerivAt h hs).deriv]
  exact mul_div_cancel_left₀ _ (ne_of_gt (radialMomentum_pos
    (h.V_pos s hs) (h.X_pos s hs) (h.v_pos s hs)))

theorem radialWeight_hasDerivAt {I : Set ℝ} {a a₁ V V₁ u v : ℝ → ℝ}
    (h : RadialSolutionOn I a a₁ V V₁ u v) {s : ℝ} (hs : s ∈ I) :
    HasDerivAt (radialWeight a V u v)
      (-radialFy (a s) (a₁ s) (V s) (V₁ s) (u s) (v s) * radialWeight a V u v s) s := by
  convert (radialMomentum_hasDerivAt h hs).neg.div ((h.dv s hs).const_mul 2)
    (mul_ne_zero (by norm_num) (ne_of_gt (h.v_pos s hs))) using 1
  dsimp [radialF, radialFy, radialWeight]
  have hX := ne_of_gt (h.X_pos s hs)
  have hv := ne_of_gt (h.v_pos s hs)
  have hV := ne_of_gt (h.V_pos s hs)
  field_simp
  ring

theorem radialPairing_hasDerivAt_zero {I : Set ℝ} {a a₁ V V₁ u v ξ₁ ζ₁ ξ₂ ζ₂ : ℝ → ℝ}
    (h : RadialSolutionOn I a a₁ V V₁ u v)
    (h₁ : RadialVariationOn I a a₁ V V₁ u v ξ₁ ζ₁)
    (h₂ : RadialVariationOn I a a₁ V V₁ u v ξ₂ ζ₂) {s : ℝ} (hs : s ∈ I) :
    HasDerivAt (radialPairing a V u v ξ₁ ζ₁ ξ₂ ζ₂) 0 s := by
  convert (radialWeight_hasDerivAt h hs).mul
    (variationDet_hasDerivAt (h₁.dξ s hs) (h₂.dξ s hs) (h₁.dζ s hs) (h₂.dζ s hs)) using 1
  ring

/-- Constancy on an arbitrary open connected interval, not just a pointwise identity. -/
theorem radialPairing_constant {I : Set ℝ} (hI : IsOpen I) (hc : IsPreconnected I)
    {a a₁ V V₁ u v ξ₁ ζ₁ ξ₂ ζ₂ : ℝ → ℝ}
    (h : RadialSolutionOn I a a₁ V V₁ u v)
    (h₁ : RadialVariationOn I a a₁ V V₁ u v ξ₁ ζ₁)
    (h₂ : RadialVariationOn I a a₁ V V₁ u v ξ₂ ζ₂)
    {s t : ℝ} (hs : s ∈ I) (ht : t ∈ I) :
    radialPairing a V u v ξ₁ ζ₁ ξ₂ ζ₂ s = radialPairing a V u v ξ₁ ζ₁ ξ₂ ζ₂ t := by
  apply hI.is_const_of_deriv_eq_zero hc
    (fun x hx => (radialPairing_hasDerivAt_zero h h₁ h₂ hx).differentiableAt.differentiableWithinAt)
    (fun x hx => (radialPairing_hasDerivAt_zero h h₁ h₂ hx).deriv) hs ht

end AffineQuadric
