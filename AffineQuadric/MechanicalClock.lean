import AffineQuadric.MechanicalEnergy

/-! PE V8 eq:hatenergy in Newtonian time. The regular inverse clock is an explicit input. -/
noncomputable section
open Filter
open scoped Topology
namespace AffineQuadric

structure RegularMechanicalClockOn (I : Set ℝ) (t : ℝ → ℝ) : Prop where
  positive : ∀ τ ∈ I, 0 < t τ
  differentiable : ∀ τ ∈ I, DifferentiableAt ℝ t τ
  inverse : ∀ τ ∈ I, mechanicalTime (t τ) = τ

/-- The inverse derivative is deduced from T(t(tau))=tau, not assumed. -/
theorem mechanicalClock_hasDerivAt {I : Set ℝ} (hI : IsOpen I) {t : ℝ → ℝ}
    (h : RegularMechanicalClockOn I t) {τ : ℝ} (hτ : τ ∈ I) :
    HasDerivAt t (1 / Real.sinh (t τ) ^ 2) τ := by
  have hcomp := (mechanicalTime_hasDerivAt (t τ)).comp τ (h.differentiable τ hτ).hasDerivAt
  have heq : (fun x => mechanicalTime (t x)) =ᶠ[𝓝 τ] id :=
    Filter.eventually_of_mem (hI.mem_nhds hτ) (fun x hx => h.inverse x hx)
  have hid : HasDerivAt id (Real.sinh (t τ) ^ 2 * deriv t τ) τ :=
    hcomp.congr_of_eventuallyEq heq.symm
  have hprod := hid.unique (hasDerivAt_id τ)
  have hn : Real.sinh (t τ) ^ 2 ≠ 0 :=
    ne_of_gt (sq_pos_of_pos (Real.sinh_pos_iff.2 (h.positive τ hτ)))
  apply (h.differentiable τ hτ).hasDerivAt.congr_deriv
  apply (eq_div_iff hn).2
  simpa only [mul_comm] using hprod


theorem mechanicalClock_time_pos {I : Set ℝ} {t : ℝ → ℝ}
    (h : RegularMechanicalClockOn I t) {τ : ℝ} (hτ : τ ∈ I) : 0 < τ := by
  rw [← h.inverse τ hτ]
  exact mechanicalTime_pos (h.positive τ hτ)

theorem mechanicalClock_deriv_pos {I : Set ℝ} (hI : IsOpen I) {t : ℝ → ℝ}
    (h : RegularMechanicalClockOn I t) {τ : ℝ} (hτ : τ ∈ I) : 0 < deriv t τ := by
  rw [(mechanicalClock_hasDerivAt hI h hτ).deriv]
  exact div_pos (by norm_num) (sq_pos_of_pos (Real.sinh_pos_iff.2 (h.positive τ hτ)))
def hyperbolicTimeCoefficient (t : ℝ → ℝ) (τ : ℝ) : ℝ := hyperbolicShape (t τ) ^ 2

theorem hyperbolicTimeCoefficient_hasDerivAt {I : Set ℝ} (hI : IsOpen I) {t : ℝ → ℝ}
    (h : RegularMechanicalClockOn I t) {τ : ℝ} (hτ : τ ∈ I) :
    HasDerivAt (hyperbolicTimeCoefficient t) (shapeSquareTauRate (t τ)) τ := by
  convert ((hyperbolicShape_hasDerivAt (h.positive τ hτ)).comp τ
    (mechanicalClock_hasDerivAt hI h hτ)).pow 2 using 1
  dsimp [shapeSquareTauRate]
  ring

theorem hyperbolicTimeCoefficient_deriv_pos {I : Set ℝ} (hI : IsOpen I) {t : ℝ → ℝ}
    (h : RegularMechanicalClockOn I t) {τ : ℝ} (hτ : τ ∈ I) :
    0 < deriv (hyperbolicTimeCoefficient t) τ := by
  rw [(hyperbolicTimeCoefficient_hasDerivAt hI h hτ).deriv]
  exact shapeSquareTauRate_pos (h.positive τ hτ)

/-- The exact eq:hatenergy coefficient includes the positive inverse time factor. -/
theorem hyperbolicEnergy_hasDerivAt {I : Set ℝ} (hI : IsOpen I) {t : ℝ → ℝ}
    (clock : RegularMechanicalClockOn I t) {β : ℝ} {Z U : ℝ → ℝ}
    (h : NewtonianSolutionOn I β (hyperbolicTimeCoefficient t) Z U)
    {τ : ℝ} (hτ : τ ∈ I) :
    HasDerivAt (newtonianEnergy β (hyperbolicTimeCoefficient t) Z U)
      (-((9 / 2 : ℝ) * β ^ 2) * (shapeSquareTauRate (t τ) * Z τ ^ (-2 / 3 : ℝ))) τ := by
  exact newtonianEnergy_hasDerivAt h hτ (hyperbolicTimeCoefficient_hasDerivAt hI clock hτ)

theorem hyperbolicEnergy_deriv_neg {I : Set ℝ} (hI : IsOpen I) {t : ℝ → ℝ}
    (clock : RegularMechanicalClockOn I t) {β : ℝ} (hβ : 0 < β) {Z U : ℝ → ℝ}
    (h : NewtonianSolutionOn I β (hyperbolicTimeCoefficient t) Z U)
    {τ : ℝ} (hτ : τ ∈ I) :
    deriv (newtonianEnergy β (hyperbolicTimeCoefficient t) Z U) τ < 0 := by
  rw [(hyperbolicEnergy_hasDerivAt hI clock h hτ).deriv]
  apply mul_neg_of_neg_of_pos
  · exact neg_neg_of_pos (mul_pos (by norm_num) (sq_pos_of_pos hβ))
  · exact mul_pos (shapeSquareTauRate_pos (clock.positive τ hτ))
      (Real.rpow_pos_of_pos (h.Z_pos τ hτ) _)

/-- Strict decrease between all ordered times in the connected interval. -/
theorem hyperbolicEnergy_strictAntiOn {I : Set ℝ} (hI : IsOpen I) (hc : IsPreconnected I)
    {t : ℝ → ℝ} (clock : RegularMechanicalClockOn I t) {β : ℝ} (hβ : 0 < β)
    {Z U : ℝ → ℝ} (h : NewtonianSolutionOn I β (hyperbolicTimeCoefficient t) Z U) :
    StrictAntiOn (newtonianEnergy β (hyperbolicTimeCoefficient t) Z U) I := by
  apply strictAntiOn_of_deriv_neg hc.ordConnected.convex
  · exact fun x hx => (hyperbolicEnergy_hasDerivAt hI clock h hx).continuousAt.continuousWithinAt
  · exact fun x hx => hyperbolicEnergy_deriv_neg hI clock hβ h (interior_subset hx)

theorem hyperbolicEnergy_lt {I : Set ℝ} (hI : IsOpen I) (hc : IsPreconnected I)
    {t : ℝ → ℝ} (clock : RegularMechanicalClockOn I t) {β : ℝ} (hβ : 0 < β)
    {Z U : ℝ → ℝ} (h : NewtonianSolutionOn I β (hyperbolicTimeCoefficient t) Z U)
    {σ τ : ℝ} (hσ : σ ∈ I) (hτ : τ ∈ I) (hlt : σ < τ) :
    newtonianEnergy β (hyperbolicTimeCoefficient t) Z U τ <
      newtonianEnergy β (hyperbolicTimeCoefficient t) Z U σ := by
  exact hyperbolicEnergy_strictAntiOn hI hc clock hβ h hσ hτ hlt

end AffineQuadric
