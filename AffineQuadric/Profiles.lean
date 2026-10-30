import AffineQuadric.Pairing

/-! The actual hyperbolic coefficients of PE V8, eq:background and eq:scalar.
Here beta = (3/2) |alpha'| in the paper. No existence result is used or asserted.
-/
noncomputable section
namespace AffineQuadric

def v8Volume (κ s : ℝ) : ℝ := κ * Real.sinh (3 * s)
def v8VolumeDerivative (κ s : ℝ) : ℝ := 3 * κ * Real.cosh (3 * s)
def v8Barrier (β s : ℝ) : ℝ := β * (3 * s * (Real.cosh (3 * s) / Real.sinh (3 * s)) - 1)
def v8BarrierDerivative (β s : ℝ) : ℝ :=
  β * (3 * Real.cosh (3 * s) / Real.sinh (3 * s) - 9 * s / Real.sinh (3 * s) ^ 2)

theorem v8Volume_hasDerivAt (κ s : ℝ) :
    HasDerivAt (v8Volume κ) (v8VolumeDerivative κ s) s := by
  convert ((Real.hasDerivAt_sinh (3 * s)).comp s
    ((hasDerivAt_id s).const_mul 3)).const_mul κ using 1
  dsimp [v8VolumeDerivative]
  ring

theorem v8Volume_pos {κ s : ℝ} (hκ : 0 < κ) (hs : 0 < s) : 0 < v8Volume κ s := by
  exact mul_pos hκ (Real.sinh_pos_iff.2 (by linarith))

theorem v8Barrier_hasDerivAt (β s : ℝ) (hs : 0 < s) :
    HasDerivAt (v8Barrier β) (v8BarrierDerivative β s) s := by
  have hn : Real.sinh (3 * s) ≠ 0 := ne_of_gt (Real.sinh_pos_iff.2 (by linarith))
  have hc := (Real.hasDerivAt_cosh (3 * s)).comp s ((hasDerivAt_id s).const_mul 3)
  have hh := (Real.hasDerivAt_sinh (3 * s)).comp s ((hasDerivAt_id s).const_mul 3)
  have hratio : HasDerivAt (fun t => Real.cosh (3 * t) / Real.sinh (3 * t))
      (-3 / Real.sinh (3 * s) ^ 2) s := by
    convert hc.div hh hn using 1
    dsimp
    field_simp
    nlinarith [Real.cosh_sq_sub_sinh_sq (3 * s)]
  convert ((((hasDerivAt_id s).const_mul 3).mul hratio).sub_const 1).const_mul β using 1
  dsimp [v8BarrierDerivative]
  ring

theorem v8_background_rate (κ s : ℝ) (hκ : κ ≠ 0) (hs : 0 < s) :
    2 * v8VolumeDerivative κ s / v8Volume κ s =
      6 * (Real.cosh (3 * s) / Real.sinh (3 * s)) := by
  have hn : Real.sinh (3 * s) ≠ 0 := ne_of_gt (Real.sinh_pos_iff.2 (by linarith))
  dsimp [v8VolumeDerivative, v8Volume]
  field_simp
  ring

def v8ScalarF (β s x y : ℝ) : ℝ :=
  6 * (Real.cosh (3 * s) / Real.sinh (3 * s)) * y -
    (2 * x * y ^ 2 + 2 * v8Barrier β s * v8BarrierDerivative β s * y) /
      (x ^ 2 - v8Barrier β s ^ 2)

theorem v8ScalarF_eq (β κ s x y : ℝ) (hκ : κ ≠ 0) (hs : 0 < s) :
    v8ScalarF β s x y = radialF (v8Barrier β s) (v8BarrierDerivative β s)
      (v8Volume κ s) (v8VolumeDerivative κ s) x y := by
  unfold v8ScalarF radialF
  rw [v8_background_rate κ s hκ hs]

/-- The logarithmic form eq:scalar and the first order acceleration are equivalent on v>0. -/
theorem v8_scalar_equation_iff (β s x y z : ℝ) (hy : y ≠ 0) :
    z / y = 6 * (Real.cosh (3 * s) / Real.sinh (3 * s)) -
        (2 * x * y + 2 * v8Barrier β s * v8BarrierDerivative β s) /
          (x ^ 2 - v8Barrier β s ^ 2) ↔ z = v8ScalarF β s x y := by
  rw [div_eq_iff hy]
  have heq : v8ScalarF β s x y =
      (6 * (Real.cosh (3 * s) / Real.sinh (3 * s)) -
        (2 * x * y + 2 * v8Barrier β s * v8BarrierDerivative β s) /
          (x ^ 2 - v8Barrier β s ^ 2)) * y := by
    unfold v8ScalarF
    ring
  rw [heq]

/-- Jacobian entries for the exact scalar equation appearing in the article. -/
theorem v8ScalarF_partial_x (β κ s x y : ℝ) (hκ : κ ≠ 0) (hs : 0 < s)
    (hX : x ^ 2 - v8Barrier β s ^ 2 ≠ 0) :
    HasDerivAt (fun z => v8ScalarF β s z y)
      (radialFx (v8Barrier β s) (v8BarrierDerivative β s) x y) x := by
  have heq : (fun z => v8ScalarF β s z y) =
      (fun z => radialF (v8Barrier β s) (v8BarrierDerivative β s)
        (v8Volume κ s) (v8VolumeDerivative κ s) z y) := by
    funext z
    exact v8ScalarF_eq β κ s z y hκ hs
  rw [heq]
  exact radialF_partial_x _ _ _ _ _ _ hX

theorem v8ScalarF_partial_y (β κ s x y : ℝ) (hκ : κ ≠ 0) (hs : 0 < s)
    (hX : x ^ 2 - v8Barrier β s ^ 2 ≠ 0) :
    HasDerivAt (fun z => v8ScalarF β s x z)
      (radialFy (v8Barrier β s) (v8BarrierDerivative β s)
        (v8Volume κ s) (v8VolumeDerivative κ s) x y) y := by
  have heq : (fun z => v8ScalarF β s x z) =
      (fun z => radialF (v8Barrier β s) (v8BarrierDerivative β s)
        (v8Volume κ s) (v8VolumeDerivative κ s) x z) := by
    funext z
    exact v8ScalarF_eq β κ s x z hκ hs
  rw [heq]
  exact radialF_partial_y _ _ _ _ _ _ hX

/-- Derive the general solution hypotheses from the actual hyperbolic scalar ODE. -/
theorem v8_radial_solution {I : Set ℝ} {β κ : ℝ} {u v : ℝ → ℝ}
    (hκ : 0 < κ) (hI : I ⊆ Set.Ioi 0)
    (hX : ∀ s ∈ I, 0 < u s ^ 2 - v8Barrier β s ^ 2)
    (hv : ∀ s ∈ I, 0 < v s)
    (hu : ∀ s ∈ I, HasDerivAt u (v s) s)
    (hvd : ∀ s ∈ I, HasDerivAt v (v8ScalarF β s (u s) (v s)) s) :
    RadialSolutionOn I (v8Barrier β) (v8BarrierDerivative β)
      (v8Volume κ) (v8VolumeDerivative κ) u v := by
  refine ⟨fun s hs => v8Volume_pos hκ (hI hs), hX, hv,
    fun s hs => v8Barrier_hasDerivAt β s (hI hs),
    fun s _ => v8Volume_hasDerivAt κ s, hu, ?_⟩
  intro s hs
  rw [← v8ScalarF_eq β κ s (u s) (v s) (ne_of_gt hκ) (hI hs)]
  exact hvd s hs

/-- The variational equation expressed using actual state derivatives of v8ScalarF. -/
structure V8VariationOn (I : Set ℝ) (β : ℝ) (u v ξ ζ : ℝ → ℝ) : Prop where
  dξ : ∀ s ∈ I, HasDerivAt ξ (ζ s) s
  dζ : ∀ s ∈ I, HasDerivAt ζ
    (deriv (fun x => v8ScalarF β s x (v s)) (u s) * ξ s +
      deriv (fun y => v8ScalarF β s (u s) y) (v s) * ζ s) s

theorem v8_variation_transport {I : Set ℝ} {β κ : ℝ} {u v ξ ζ : ℝ → ℝ}
    (hκ : 0 < κ) (hI : I ⊆ Set.Ioi 0)
    (hX : ∀ s ∈ I, 0 < u s ^ 2 - v8Barrier β s ^ 2)
    (h : V8VariationOn I β u v ξ ζ) :
    RadialVariationOn I (v8Barrier β) (v8BarrierDerivative β)
      (v8Volume κ) (v8VolumeDerivative κ) u v ξ ζ := by
  refine ⟨h.dξ, ?_⟩
  intro s hs
  have hx := (v8ScalarF_partial_x β κ s (u s) (v s) (ne_of_gt hκ)
    (hI hs) (ne_of_gt (hX s hs))).deriv
  have hy := (v8ScalarF_partial_y β κ s (u s) (v s) (ne_of_gt hκ)
    (hI hs) (ne_of_gt (hX s hs))).deriv
  simpa only [hx, hy] using h.dζ s hs

/-- PE V8 Proposition 4.3 for given admissible scalar solutions and their true variations. -/
theorem v8_pairing_constant {I : Set ℝ} (hIo : IsOpen I) (hc : IsPreconnected I)
    (hI : I ⊆ Set.Ioi 0) {β κ : ℝ} (hκ : 0 < κ)
    {u v ξ₁ ζ₁ ξ₂ ζ₂ : ℝ → ℝ}
    (hX : ∀ s ∈ I, 0 < u s ^ 2 - v8Barrier β s ^ 2)
    (hv : ∀ s ∈ I, 0 < v s)
    (hu : ∀ s ∈ I, HasDerivAt u (v s) s)
    (hvd : ∀ s ∈ I, HasDerivAt v (v8ScalarF β s (u s) (v s)) s)
    (h₁ : V8VariationOn I β u v ξ₁ ζ₁)
    (h₂ : V8VariationOn I β u v ξ₂ ζ₂)
    {s t : ℝ} (hs : s ∈ I) (ht : t ∈ I) :
    radialPairing (v8Barrier β) (v8Volume κ) u v ξ₁ ζ₁ ξ₂ ζ₂ s =
      radialPairing (v8Barrier β) (v8Volume κ) u v ξ₁ ζ₁ ξ₂ ζ₂ t := by
  exact radialPairing_constant hIo hc (v8_radial_solution hκ hI hX hv hu hvd)
    (v8_variation_transport hκ hI hX h₁) (v8_variation_transport hκ hI hX h₂) hs ht

/-- The physical branch u>a with a nonnegative implies the X>0 domain used above. -/
theorem physical_domain_X_pos (a u : ℝ) (ha : 0 ≤ a) (hu : a < u) :
    0 < u ^ 2 - a ^ 2 := by
  nlinarith

end AffineQuadric
