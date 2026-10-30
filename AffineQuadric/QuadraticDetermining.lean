import AffineQuadric.MechanicalClock
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Tactic

/-! Stage A1: deriving the determining equations from an arbitrary smooth candidate
and its transport identity ONLY on the admissible velocity half-line. -/
noncomputable section
open Set
open scoped ContDiff
namespace AffineQuadric

def coefficientTimeDeriv (A : ℝ → ℝ → ℝ) (τ z : ℝ) : ℝ := deriv (fun x => A x z) τ
def coefficientPositionDeriv (A : ℝ → ℝ → ℝ) (τ z : ℝ) : ℝ := deriv (A τ) z

def quadraticCandidate (A₂ A₁ A₀ : ℝ → ℝ → ℝ) (τ z v : ℝ) : ℝ :=
  A₂ τ z * v ^ 2 + A₁ τ z * v + A₀ τ z

def quadraticThreshold (K : ℝ → ℝ) (τ z : ℝ) : ℝ :=
  3 * Real.sqrt (K τ) * z ^ (-1 / 3 : ℝ)

def quadraticTransport (K : ℝ → ℝ) (A₂ A₁ A₀ : ℝ → ℝ → ℝ) (τ z v : ℝ) : ℝ :=
  deriv (fun x => quadraticCandidate A₂ A₁ A₀ x z v) τ +
    v * deriv (fun x => quadraticCandidate A₂ A₁ A₀ τ x v) z +
    newtonianForce 1 (K τ) z * deriv (quadraticCandidate A₂ A₁ A₀ τ z) v

structure SmoothQuadraticOn (I : Set ℝ) (A₂ A₁ A₀ : ℝ → ℝ → ℝ) : Prop where
  smooth₂ : ContDiffOn ℝ ∞ (Function.uncurry A₂) (I ×ˢ Ioi 0)
  smooth₁ : ContDiffOn ℝ ∞ (Function.uncurry A₁) (I ×ˢ Ioi 0)
  smooth₀ : ContDiffOn ℝ ∞ (Function.uncurry A₀) (I ×ˢ Ioi 0)

structure QuadraticDeterminingAt (K : ℝ → ℝ) (A₂ A₁ A₀ : ℝ → ℝ → ℝ) (τ z : ℝ) : Prop where
  cubic : coefficientPositionDeriv A₂ τ z = 0
  square : coefficientTimeDeriv A₂ τ z + coefficientPositionDeriv A₁ τ z = 0
  linear : coefficientTimeDeriv A₁ τ z + coefficientPositionDeriv A₀ τ z +
    2 * newtonianForce 1 (K τ) z * A₂ τ z = 0
  constant : coefficientTimeDeriv A₀ τ z + newtonianForce 1 (K τ) z * A₁ τ z = 0

theorem cubic_zero_on_halfline (c₃ c₂ c₁ c₀ M : ℝ)
    (h : ∀ v : ℝ, M < v → c₃ * v ^ 3 + c₂ * v ^ 2 + c₁ * v + c₀ = 0) :
    c₃ = 0 ∧ c₂ = 0 ∧ c₁ = 0 ∧ c₀ = 0 := by
  have h1 := h (M + 1) (by linarith)
  have h2 := h (M + 2) (by linarith)
  have h3 := h (M + 3) (by linarith)
  have h4 := h (M + 4) (by linarith)
  have hc3 : c₃ = 0 := by linear_combination (-1 / 6 : ℝ) * h1 + (1 / 2 : ℝ) * h2 - (1 / 2 : ℝ) * h3 + (1 / 6 : ℝ) * h4
  rw [hc3] at h1 h2 h3 h4
  have hc2 : c₂ = 0 := by linear_combination (1 / 2 : ℝ) * h1 - h2 + (1 / 2 : ℝ) * h3
  rw [hc2] at h1 h2
  have hc1 : c₁ = 0 := by linear_combination h2 - h1
  rw [hc1] at h1
  exact ⟨hc3, hc2, hc1, by simpa using h1⟩

theorem smooth_coefficient_slices {I : Set ℝ} (hI : IsOpen I) {A : ℝ → ℝ → ℝ}
    (hA : ContDiffOn ℝ ∞ (Function.uncurry A) (I ×ˢ Ioi 0))
    {τ z : ℝ} (hτ : τ ∈ I) (hz : 0 < z) :
    DifferentiableAt ℝ (fun x => A x z) τ ∧ DifferentiableAt ℝ (A τ) z := by
  have hp : ContDiffAt ℝ ∞ (Function.uncurry A) (τ, z) :=
    hA.contDiffAt ((hI.prod isOpen_Ioi).mem_nhds ⟨hτ, hz⟩)
  exact ⟨(hp.comp τ (contDiffAt_id.prodMk contDiffAt_const)).differentiableAt (by simp),
    (hp.comp z (contDiffAt_const.prodMk contDiffAt_id)).differentiableAt (by simp)⟩

theorem quadraticCandidate_time_hasDerivAt {A₂ A₁ A₀ : ℝ → ℝ → ℝ} {τ z : ℝ} (v : ℝ)
    (h₂ : DifferentiableAt ℝ (fun x => A₂ x z) τ)
    (h₁ : DifferentiableAt ℝ (fun x => A₁ x z) τ)
    (h₀ : DifferentiableAt ℝ (fun x => A₀ x z) τ) :
    HasDerivAt (fun x => quadraticCandidate A₂ A₁ A₀ x z v)
      (coefficientTimeDeriv A₂ τ z * v ^ 2 + coefficientTimeDeriv A₁ τ z * v + coefficientTimeDeriv A₀ τ z) τ := by
  exact ((h₂.hasDerivAt.mul_const (v ^ 2)).add (h₁.hasDerivAt.mul_const v)).add h₀.hasDerivAt

theorem quadraticCandidate_position_hasDerivAt {A₂ A₁ A₀ : ℝ → ℝ → ℝ} {τ z : ℝ} (v : ℝ)
    (h₂ : DifferentiableAt ℝ (A₂ τ) z) (h₁ : DifferentiableAt ℝ (A₁ τ) z)
    (h₀ : DifferentiableAt ℝ (A₀ τ) z) :
    HasDerivAt (fun x => quadraticCandidate A₂ A₁ A₀ τ x v)
      (coefficientPositionDeriv A₂ τ z * v ^ 2 + coefficientPositionDeriv A₁ τ z * v + coefficientPositionDeriv A₀ τ z) z := by
  exact ((h₂.hasDerivAt.mul_const (v ^ 2)).add (h₁.hasDerivAt.mul_const v)).add h₀.hasDerivAt

theorem quadraticCandidate_velocity_hasDerivAt (A₂ A₁ A₀ : ℝ → ℝ → ℝ) (τ z v : ℝ) :
    HasDerivAt (quadraticCandidate A₂ A₁ A₀ τ z) (2 * A₂ τ z * v + A₁ τ z) v := by
  convert ((((hasDerivAt_id v).pow 2).const_mul (A₂ τ z)).add
    ((hasDerivAt_id v).const_mul (A₁ τ z))).add_const (A₀ τ z) using 1
  dsimp
  ring

theorem quadraticTransport_expansion {I : Set ℝ} (hI : IsOpen I) {K : ℝ → ℝ}
    {A₂ A₁ A₀ : ℝ → ℝ → ℝ} (hA : SmoothQuadraticOn I A₂ A₁ A₀)
    {τ z : ℝ} (hτ : τ ∈ I) (hz : 0 < z) (v : ℝ) :
    quadraticTransport K A₂ A₁ A₀ τ z v =
      coefficientPositionDeriv A₂ τ z * v ^ 3 +
      (coefficientTimeDeriv A₂ τ z + coefficientPositionDeriv A₁ τ z) * v ^ 2 +
      (coefficientTimeDeriv A₁ τ z + coefficientPositionDeriv A₀ τ z +
        2 * newtonianForce 1 (K τ) z * A₂ τ z) * v +
      (coefficientTimeDeriv A₀ τ z + newtonianForce 1 (K τ) z * A₁ τ z) := by
  have h₂ := smooth_coefficient_slices hI hA.smooth₂ hτ hz
  have h₁ := smooth_coefficient_slices hI hA.smooth₁ hτ hz
  have h₀ := smooth_coefficient_slices hI hA.smooth₀ hτ hz
  unfold quadraticTransport
  rw [(quadraticCandidate_time_hasDerivAt v h₂.1 h₁.1 h₀.1).deriv,
    (quadraticCandidate_position_hasDerivAt v h₂.2 h₁.2 h₀.2).deriv,
    (quadraticCandidate_velocity_hasDerivAt A₂ A₁ A₀ τ z v).deriv]
  ring

/-- The initial candidate is arbitrary and smooth only on Omega. Its determining
system is a conclusion deduced from the velocity half-line transport condition. -/
theorem quadratic_determining_from_transport {I : Set ℝ} (hI : IsOpen I) {K : ℝ → ℝ}
    {A₂ A₁ A₀ : ℝ → ℝ → ℝ} (hA : SmoothQuadraticOn I A₂ A₁ A₀)
    (htransport : ∀ τ ∈ I, ∀ z, 0 < z → ∀ v, quadraticThreshold K τ z < v →
      quadraticTransport K A₂ A₁ A₀ τ z v = 0) :
    ∀ τ ∈ I, ∀ z, 0 < z → QuadraticDeterminingAt K A₂ A₁ A₀ τ z := by
  intro τ hτ z hz
  have hh := cubic_zero_on_halfline (coefficientPositionDeriv A₂ τ z)
    (coefficientTimeDeriv A₂ τ z + coefficientPositionDeriv A₁ τ z)
    (coefficientTimeDeriv A₁ τ z + coefficientPositionDeriv A₀ τ z + 2 * newtonianForce 1 (K τ) z * A₂ τ z)
    (coefficientTimeDeriv A₀ τ z + newtonianForce 1 (K τ) z * A₁ τ z)
    (quadraticThreshold K τ z) (fun v hv => by
      rw [← quadraticTransport_expansion hI hA hτ hz v]
      exact htransport τ hτ z hz v hv)
  exact ⟨hh.1, hh.2.1, hh.2.2.1, hh.2.2.2⟩

end AffineQuadric
