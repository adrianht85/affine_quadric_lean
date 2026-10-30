import AffineQuadric.QuadraticIntegration
import AffineQuadric.QuadraticPowers

/-! PE V8 Theorem 4.1, in Newtonian variables with the given regular inverse
clock. The initial candidate is arbitrary and C-infinity only on Omega.
Neither the determining equations nor the temporal obstruction is assumed. -/
noncomputable section
open Set Filter
open scoped Topology ContDiff
namespace AffineQuadric

theorem quadratic_scalar_obstruction_from_determining {I : Set ℝ} (hI : IsOpen I)
    {K : ℝ → ℝ} {A₂ A₁ A₀ : ℝ → ℝ → ℝ}
    (h : IntegratedQuadraticOn I K A₂ A₁ A₀)
    (hK : ∀ τ ∈ I, DifferentiableAt ℝ K τ)
    (hKpos : ∀ τ ∈ I, 0 < K τ)
    (he : ∀ τ ∈ I, ∀ z, 0 < z → QuadraticDeterminingAt K A₂ A₁ A₀ τ z)
    {τ : ℝ} (hτ : τ ∈ I) :
    deriv (deriv (deriv h.a)) τ = 0 ∧ h.b τ = 0 ∧ deriv h.d τ = 0 ∧
      (4 / 3 : ℝ) * deriv h.a τ * K τ + 2 * h.a τ * deriv K τ = 0 := by
  have hs := quadratic_residual_separation (deriv (deriv (deriv h.a)) τ)
    (deriv (deriv h.b) τ) (deriv h.d τ)
    (6 * deriv h.a τ * K τ + 9 * h.a τ * deriv K τ) (3 * h.b τ * K τ)
    (fun z hz => quadratic_integrated_residual hI h hK he hτ hz)
  refine ⟨hs.1, ?_, hs.2.2.1, ?_⟩
  · have hh := (mul_eq_zero.mp hs.2.2.2.2).resolve_right (ne_of_gt (hKpos τ hτ))
    linarith
  · linear_combination (2 / 9 : ℝ) * hs.2.2.2.1

/-- The coefficient form of V8 Theorem 4.1. Positivity of the times in I follows
already from the regular inverse clock (mechanicalClock_time_pos). -/
theorem quadratic_first_integral_coefficients {I : Set ℝ} (hI : IsOpen I)
    (hc : IsPreconnected I) (hne : I.Nonempty) {t : ℝ → ℝ}
    (clock : RegularMechanicalClockOn I t) {A₂ A₁ A₀ : ℝ → ℝ → ℝ}
    (hA : SmoothQuadraticOn I A₂ A₁ A₀)
    (htransport : ∀ τ ∈ I, ∀ z, 0 < z → ∀ v,
      quadraticThreshold (hyperbolicTimeCoefficient t) τ z < v →
      quadraticTransport (hyperbolicTimeCoefficient t) A₂ A₁ A₀ τ z v = 0) :
    ∃ D : ℝ, ∀ τ ∈ I, ∀ z, 0 < z → A₂ τ z = 0 ∧ A₁ τ z = 0 ∧ A₀ τ z = D := by
  have hK : ∀ τ ∈ I, DifferentiableAt ℝ (hyperbolicTimeCoefficient t) τ :=
    fun τ hτ => (hyperbolicTimeCoefficient_hasDerivAt hI clock hτ).differentiableAt
  have hKpos : ∀ τ ∈ I, 0 < hyperbolicTimeCoefficient t τ := by
    intro τ hτ
    exact pow_pos (hyperbolicShape_pos (clock.positive τ hτ)) 2
  have he := quadratic_determining_from_transport hI hA htransport
  obtain ⟨h⟩ := quadratic_integrated_from_determining hI hA hK he
  have hs := fun (τ : ℝ) (hτ : τ ∈ I) =>
    quadratic_scalar_obstruction_from_determining hI h hK hKpos he hτ
  have ha := fun (τ : ℝ) (hτ : τ ∈ I) => smooth_hasDerivAt_on_open hI h.a_smooth hτ
  have ha1 := fun (τ : ℝ) (hτ : τ ∈ I) =>
    smooth_hasDerivAt_on_open hI (smooth_deriv_on_open hI h.a_smooth) hτ
  have ha2 : ∀ τ ∈ I, HasDerivAt (deriv (deriv h.a)) 0 τ := by
    intro τ hτ
    have hh := smooth_hasDerivAt_on_open hI
      (smooth_deriv_on_open hI (smooth_deriv_on_open hI h.a_smooth)) hτ
    simpa only [(hs τ hτ).1] using hh
  have hobs : ∀ τ ∈ I, (4 / 3 : ℝ) * deriv h.a τ * hyperbolicTimeCoefficient t τ +
      2 * h.a τ * shapeSquareTauRate (t τ) = 0 := by
    intro τ hτ
    simpa only [(hyperbolicTimeCoefficient_hasDerivAt hI clock hτ).deriv] using (hs τ hτ).2.2.2
  have haz := quadratic_temporal_obstruction hI hc hne clock
    ha ha1 ha2 hobs
  have hb1z : ∀ τ ∈ I, deriv h.b τ = 0 := by
    intro τ hτ
    have hb0 : h.b =ᶠ[𝓝 τ] (fun _ => (0 : ℝ)) :=
      Filter.eventually_of_mem (hI.mem_nhds hτ) (fun x hx => (hs x hx).2.1)
    exact ((hasDerivAt_const τ (0 : ℝ)).congr_of_eventuallyEq hb0).deriv
  obtain ⟨s, hsI⟩ := hne
  refine ⟨h.d s, ?_⟩
  intro τ hτ z hz
  have hdconst : h.d τ = h.d s := interval_constant_of_hasDerivAt_zero hI hc
    (fun x hx => (h.d_diff x hx).hasDerivAt.congr_deriv (hs x hx).2.2.1) hτ hsI
  refine ⟨?_, ?_, ?_⟩
  · rw [h.leading τ hτ z hz, (haz τ hτ).1]
  · rw [h.linear τ hτ z hz, (haz τ hτ).2.1, (hs τ hτ).2.1]
    ring
  · rw [h.constant τ hτ z hz, (haz τ hτ).1, (haz τ hτ).2.2, hb1z τ hτ, hdconst]
    ring

/-- Full normalized quadratic-integral exclusion, deduced from transport only
on the admissible open velocity half-line. The conclusion in fact holds for
all velocities, because the coefficients have been identified. -/
theorem quadratic_first_integral_constant {I : Set ℝ} (hI : IsOpen I)
    (hc : IsPreconnected I) (hne : I.Nonempty) {t : ℝ → ℝ}
    (clock : RegularMechanicalClockOn I t) {A₂ A₁ A₀ : ℝ → ℝ → ℝ}
    (hA : SmoothQuadraticOn I A₂ A₁ A₀)
    (htransport : ∀ τ ∈ I, ∀ z, 0 < z → ∀ v,
      quadraticThreshold (hyperbolicTimeCoefficient t) τ z < v →
      quadraticTransport (hyperbolicTimeCoefficient t) A₂ A₁ A₀ τ z v = 0) :
    ∃ D : ℝ, ∀ τ ∈ I, ∀ z, 0 < z → ∀ v, quadraticCandidate A₂ A₁ A₀ τ z v = D := by
  obtain ⟨D, hD⟩ := quadratic_first_integral_coefficients hI hc hne clock hA htransport
  refine ⟨D, ?_⟩
  intro τ hτ z hz v
  rcases hD τ hτ z hz with ⟨h2, h1, h0⟩
  simp [quadraticCandidate, h2, h1, h0]

end AffineQuadric
