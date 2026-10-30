import AffineQuadric.MechanicalClock

/-! The link from PE V8 eq:hatODE to the Newtonian system is proved here.
No relation from the geometric p,s variables and no existence theorem is assumed proved.
-/
noncomputable section
namespace AffineQuadric

def scalarNewtonPosition (f : ℝ → ℝ) (τ : ℝ) : ℝ := f τ ^ (3 / 4 : ℝ)
def scalarNewtonVelocity (f u : ℝ → ℝ) (τ : ℝ) : ℝ := 3 * u τ * f τ ^ (-1 / 4 : ℝ)

structure ScalarMechanicalSolutionOn (I : Set ℝ) (β : ℝ) (K f u : ℝ → ℝ) : Prop where
  f_pos : ∀ τ ∈ I, 0 < f τ
  df : ∀ τ ∈ I, HasDerivAt f (4 * u τ) τ
  du : ∀ τ ∈ I, HasDerivAt u ((u τ ^ 2 - β ^ 2 * K τ) / f τ) τ

theorem scalar_position_force_power {x : ℝ} (hx : 0 < x) :
    (x ^ (3 / 4 : ℝ)) ^ (-5 / 3 : ℝ) = x ^ (-5 / 4 : ℝ) := by
  rw [← Real.rpow_mul (le_of_lt hx)]
  norm_num

theorem scalar_quarter_power {x : ℝ} (hx : 0 < x) :
    x ^ (-1 / 4 : ℝ) = x ^ (-5 / 4 : ℝ) * x := by
  convert Real.rpow_add_one (ne_of_gt hx) (-5 / 4 : ℝ) using 1
  norm_num

theorem scalarNewtonPosition_hasDerivAt {I : Set ℝ} {β : ℝ} {K f u : ℝ → ℝ}
    (h : ScalarMechanicalSolutionOn I β K f u) {τ : ℝ} (hτ : τ ∈ I) :
    HasDerivAt (scalarNewtonPosition f) (scalarNewtonVelocity f u τ) τ := by
  have hp := (h.df τ hτ).rpow_const (p := (3 / 4 : ℝ)) (Or.inl (ne_of_gt (h.f_pos τ hτ)))
  convert hp using 1
  rw [show (3 / 4 : ℝ) - 1 = (-1 / 4 : ℝ) by norm_num]
  dsimp [scalarNewtonVelocity]
  ring

theorem scalarNewtonVelocity_hasDerivAt {I : Set ℝ} {β : ℝ} {K f u : ℝ → ℝ}
    (h : ScalarMechanicalSolutionOn I β K f u) {τ : ℝ} (hτ : τ ∈ I) :
    HasDerivAt (scalarNewtonVelocity f u)
      (newtonianForce β (K τ) (scalarNewtonPosition f τ)) τ := by
  have hp := (h.df τ hτ).rpow_const (p := (-1 / 4 : ℝ)) (Or.inl (ne_of_gt (h.f_pos τ hτ)))
  convert ((h.du τ hτ).const_mul 3).mul hp using 1
  dsimp [newtonianForce, scalarNewtonPosition]
  rw [show (-1 / 4 : ℝ) - 1 = (-5 / 4 : ℝ) by norm_num,
    scalar_position_force_power (h.f_pos τ hτ), scalar_quarter_power (h.f_pos τ hτ)]
  have hn := ne_of_gt (h.f_pos τ hτ)
  field_simp
  ring

/-- Both Newtonian equations are consequences of eq:hatODE in f,u. -/
theorem scalar_to_newtonian {I : Set ℝ} {β : ℝ} {K f u : ℝ → ℝ}
    (h : ScalarMechanicalSolutionOn I β K f u) :
    NewtonianSolutionOn I β K (scalarNewtonPosition f) (scalarNewtonVelocity f u) := by
  refine ⟨?_, fun τ hτ => scalarNewtonPosition_hasDerivAt h hτ,
    fun τ hτ => scalarNewtonVelocity_hasDerivAt h hτ⟩
  exact fun τ hτ => Real.rpow_pos_of_pos (h.f_pos τ hτ) _

/-- The energy law is now linked to the scalar equations, not a postulated force. -/
theorem scalarMechanicalEnergy_hasDerivAt {I : Set ℝ} {β : ℝ} {K f u : ℝ → ℝ}
    (h : ScalarMechanicalSolutionOn I β K f u) {τ Kτ : ℝ} (hτ : τ ∈ I)
    (hK : HasDerivAt K Kτ τ) :
    HasDerivAt (newtonianEnergy β K (scalarNewtonPosition f) (scalarNewtonVelocity f u))
      (-((9 / 2 : ℝ) * β ^ 2) * (Kτ * (scalarNewtonPosition f τ) ^ (-2 / 3 : ℝ))) τ := by
  exact newtonianEnergy_hasDerivAt (scalar_to_newtonian h) hτ hK

/-- The actual hyperbolic energy formula follows from the f,u equations and the clock. -/
theorem hyperbolicScalarEnergy_hasDerivAt {I : Set ℝ} (hI : IsOpen I) {t : ℝ → ℝ}
    (clock : RegularMechanicalClockOn I t) {β : ℝ} {f u : ℝ → ℝ}
    (h : ScalarMechanicalSolutionOn I β (hyperbolicTimeCoefficient t) f u)
    {τ : ℝ} (hτ : τ ∈ I) :
    HasDerivAt (newtonianEnergy β (hyperbolicTimeCoefficient t)
      (scalarNewtonPosition f) (scalarNewtonVelocity f u))
      (-((9 / 2 : ℝ) * β ^ 2) * (shapeSquareTauRate (t τ) *
        (scalarNewtonPosition f τ) ^ (-2 / 3 : ℝ))) τ := by
  exact hyperbolicEnergy_hasDerivAt hI clock (scalar_to_newtonian h) hτ

theorem hyperbolicScalarEnergy_strictAntiOn {I : Set ℝ} (hI : IsOpen I) (hc : IsPreconnected I)
    {t : ℝ → ℝ} (clock : RegularMechanicalClockOn I t) {β : ℝ} (hβ : 0 < β)
    {f u : ℝ → ℝ} (h : ScalarMechanicalSolutionOn I β (hyperbolicTimeCoefficient t) f u) :
    StrictAntiOn (newtonianEnergy β (hyperbolicTimeCoefficient t)
      (scalarNewtonPosition f) (scalarNewtonVelocity f u)) I := by
  exact hyperbolicEnergy_strictAntiOn hI hc clock hβ (scalar_to_newtonian h)

theorem zero_flux_scalar_energy_constant {I : Set ℝ} (hI : IsOpen I) (hc : IsPreconnected I)
    {K f u : ℝ → ℝ} (h : ScalarMechanicalSolutionOn I 0 K f u)
    {σ τ : ℝ} (hσ : σ ∈ I) (hτ : τ ∈ I) :
    newtonianEnergy 0 K (scalarNewtonPosition f) (scalarNewtonVelocity f u) σ =
      newtonianEnergy 0 K (scalarNewtonPosition f) (scalarNewtonVelocity f u) τ := by
  exact zero_flux_energy_constant hI hc (scalar_to_newtonian h) hσ hτ

end AffineQuadric
