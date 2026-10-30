import AffineQuadric.MechanicalProfile
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.Calculus.MeanValue

/-! Newtonian velocity U=dZ/dtau is distinct from the geometric v=u' of Pairing.lean. -/
noncomputable section
namespace AffineQuadric

def newtonianForce (β K Z : ℝ) : ℝ := -3 * β ^ 2 * K * Z ^ (-5 / 3 : ℝ)

def newtonianEnergy (β : ℝ) (K Z U : ℝ → ℝ) (τ : ℝ) : ℝ :=
  U τ ^ 2 / 2 - ((9 / 2 : ℝ) * β ^ 2) * (K τ * Z τ ^ (-2 / 3 : ℝ))

structure NewtonianSolutionOn (I : Set ℝ) (β : ℝ) (K Z U : ℝ → ℝ) : Prop where
  Z_pos : ∀ τ ∈ I, 0 < Z τ
  dZ : ∀ τ ∈ I, HasDerivAt Z (U τ) τ
  dU : ∀ τ ∈ I, HasDerivAt U (newtonianForce β (K τ) (Z τ)) τ

/-- The energy law follows from the EDOs and the derivative of a real power on Z>0. -/
theorem newtonianEnergy_hasDerivAt {I : Set ℝ} {β : ℝ} {K Z U : ℝ → ℝ}
    (h : NewtonianSolutionOn I β K Z U) {τ Kτ : ℝ} (hτ : τ ∈ I)
    (hK : HasDerivAt K Kτ τ) :
    HasDerivAt (newtonianEnergy β K Z U)
      (-((9 / 2 : ℝ) * β ^ 2) * (Kτ * Z τ ^ (-2 / 3 : ℝ))) τ := by
  have hp := (h.dZ τ hτ).rpow_const (p := (-2 / 3 : ℝ)) (Or.inl (ne_of_gt (h.Z_pos τ hτ)))
  have hraw := (((h.dU τ hτ).pow 2).div_const 2).sub
    ((hK.mul hp).const_mul ((9 / 2 : ℝ) * β ^ 2))
  apply hraw.congr_deriv
  dsimp [newtonianForce]
  rw [show (-2 / 3 : ℝ) - 1 = (-5 / 3 : ℝ) by norm_num]
  ring

theorem zero_flux_velocity_hasDerivAt {I : Set ℝ} {K Z U : ℝ → ℝ}
    (h : NewtonianSolutionOn I 0 K Z U) {τ : ℝ} (hτ : τ ∈ I) : HasDerivAt U 0 τ := by
  simpa [newtonianForce] using h.dU τ hτ

theorem zero_flux_energy_hasDerivAt {I : Set ℝ} {K Z U : ℝ → ℝ}
    (h : NewtonianSolutionOn I 0 K Z U) {τ : ℝ} (hτ : τ ∈ I) :
    HasDerivAt (newtonianEnergy 0 K Z U) 0 τ := by
  have heq : newtonianEnergy 0 K Z U = (fun x => U x ^ 2 / 2) := by
    funext x
    simp [newtonianEnergy]
  rw [heq]
  simpa using ((zero_flux_velocity_hasDerivAt h hτ).pow 2).div_const 2

theorem zero_flux_energy_constant {I : Set ℝ} (hI : IsOpen I) (hc : IsPreconnected I)
    {K Z U : ℝ → ℝ} (h : NewtonianSolutionOn I 0 K Z U)
    {σ τ : ℝ} (hσ : σ ∈ I) (hτ : τ ∈ I) :
    newtonianEnergy 0 K Z U σ = newtonianEnergy 0 K Z U τ := by
  exact hI.is_const_of_deriv_eq_zero hc
    (fun x hx => (zero_flux_energy_hasDerivAt h hx).differentiableAt.differentiableWithinAt)
    (fun x hx => (zero_flux_energy_hasDerivAt h hx).deriv) hσ hτ

theorem zero_flux_velocity_constant {I : Set ℝ} (hI : IsOpen I) (hc : IsPreconnected I)
    {K Z U : ℝ → ℝ} (h : NewtonianSolutionOn I 0 K Z U)
    {σ τ : ℝ} (hσ : σ ∈ I) (hτ : τ ∈ I) : U σ = U τ := by
  exact hI.is_const_of_deriv_eq_zero hc
    (fun x hx => (zero_flux_velocity_hasDerivAt h hx).differentiableAt.differentiableWithinAt)
    (fun x hx => (zero_flux_velocity_hasDerivAt h hx).deriv) hσ hτ

/-- A mechanical zero-flux example, not a reconstructed metric. -/
theorem zero_flux_affine_solution {I : Set ℝ} (K : ℝ → ℝ) (A B : ℝ)
    (hpos : ∀ τ ∈ I, 0 < A + B * τ) :
    NewtonianSolutionOn I 0 K (fun τ => A + B * τ) (fun _ => B) := by
  refine ⟨hpos, ?_, ?_⟩
  · intro τ _
    simpa using ((hasDerivAt_id τ).const_mul B).const_add A
  · intro τ _
    simpa [newtonianForce] using hasDerivAt_const τ B

theorem zero_flux_affine_energy (K : ℝ → ℝ) (A B τ : ℝ) :
    newtonianEnergy 0 K (fun x => A + B * x) (fun _ => B) τ = B ^ 2 / 2 := by
  simp [newtonianEnergy]

end AffineQuadric
