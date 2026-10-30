import AffineQuadric.QuadraticIntegral

/-! Positive-beta exclusion by scaling K, without changing coordinates.
The transport uses actual partial derivatives. The regular clock remains an input. -/
noncomputable section
open Set Filter
open scoped Topology ContDiff
namespace AffineQuadric

def betaTimeCoefficient (β : ℝ) (t : ℝ → ℝ) (τ : ℝ) : ℝ :=
  β ^ 2 * hyperbolicTimeCoefficient t τ

def betaQuadraticTransport (β : ℝ) (K : ℝ → ℝ)
    (A₂ A₁ A₀ : ℝ → ℝ → ℝ) (τ z v : ℝ) : ℝ :=
  deriv (fun x => quadraticCandidate A₂ A₁ A₀ x z v) τ +
    v * deriv (fun x => quadraticCandidate A₂ A₁ A₀ τ x v) z +
    newtonianForce β (K τ) z * deriv (quadraticCandidate A₂ A₁ A₀ τ z) v

theorem betaTimeCoefficient_one (t : ℝ → ℝ) :
    betaTimeCoefficient 1 t = hyperbolicTimeCoefficient t := by
  funext τ
  simp [betaTimeCoefficient]

theorem betaTimeCoefficient_hasDerivAt {I : Set ℝ} (hI : IsOpen I) {t : ℝ → ℝ}
    (clock : RegularMechanicalClockOn I t) (β : ℝ) {τ : ℝ} (hτ : τ ∈ I) :
    HasDerivAt (betaTimeCoefficient β t) (β ^ 2 * shapeSquareTauRate (t τ)) τ :=
  (hyperbolicTimeCoefficient_hasDerivAt hI clock hτ).const_mul (β ^ 2)

theorem betaTimeCoefficient_pos {I : Set ℝ} {t : ℝ → ℝ}
    (clock : RegularMechanicalClockOn I t) {β : ℝ} (hβ : 0 < β)
    {τ : ℝ} (hτ : τ ∈ I) : 0 < betaTimeCoefficient β t τ :=
  mul_pos (sq_pos_of_pos hβ) (pow_pos (hyperbolicShape_pos (clock.positive τ hτ)) 2)

theorem quadratic_scaled_force (β K z : ℝ) :
    newtonianForce 1 (β ^ 2 * K) z = newtonianForce β K z := by
  dsimp [newtonianForce]
  ring

/-- The threshold identity holds for every z; the final transport domain is z>0. -/
theorem quadratic_scaled_threshold {β : ℝ} (hβ : 0 < β) {K : ℝ → ℝ}
    {τ : ℝ} (hK : 0 < K τ) (z : ℝ) :
    quadraticThreshold (fun x => β ^ 2 * K x) τ z =
      3 * β * Real.sqrt (K τ) * z ^ (-1 / 3 : ℝ) := by
  have hs : Real.sqrt (β ^ 2 * K τ) = β * Real.sqrt (K τ) := by
    rw [Real.sqrt_mul' (β ^ 2) hK.le, Real.sqrt_sq hβ.le]
  simp only [quadraticThreshold, hs]
  ring

theorem betaQuadraticTransport_eq (β : ℝ) (t : ℝ → ℝ)
    (A₂ A₁ A₀ : ℝ → ℝ → ℝ) (τ z v : ℝ) :
    quadraticTransport (betaTimeCoefficient β t) A₂ A₁ A₀ τ z v =
      betaQuadraticTransport β (hyperbolicTimeCoefficient t) A₂ A₁ A₀ τ z v := by
  unfold quadraticTransport betaQuadraticTransport betaTimeCoefficient
  rw [quadratic_scaled_force]

theorem beta_quadratic_determining_from_transport {I : Set ℝ} (hI : IsOpen I)
    {t : ℝ → ℝ} (clock : RegularMechanicalClockOn I t) {β : ℝ} (hβ : 0 < β)
    {A₂ A₁ A₀ : ℝ → ℝ → ℝ} (hA : SmoothQuadraticOn I A₂ A₁ A₀)
    (htransport : ∀ τ ∈ I, ∀ z, 0 < z → ∀ v,
      3 * β * Real.sqrt (hyperbolicTimeCoefficient t τ) * z ^ (-1 / 3 : ℝ) < v →
      betaQuadraticTransport β (hyperbolicTimeCoefficient t) A₂ A₁ A₀ τ z v = 0) :
    ∀ τ ∈ I, ∀ z, 0 < z → QuadraticDeterminingAt (betaTimeCoefficient β t) A₂ A₁ A₀ τ z := by
  apply quadratic_determining_from_transport hI hA
  intro τ hτ z hz v hv
  have hK : 0 < hyperbolicTimeCoefficient t τ :=
    pow_pos (hyperbolicShape_pos (clock.positive τ hτ)) 2
  rw [show quadraticThreshold (betaTimeCoefficient β t) τ z =
      3 * β * Real.sqrt (hyperbolicTimeCoefficient t τ) * z ^ (-1 / 3 : ℝ) from
      quadratic_scaled_threshold hβ hK z] at hv
  rw [betaQuadraticTransport_eq]
  exact htransport τ hτ z hz v hv

theorem beta_quadratic_obstruction_cancel {β a a₁ K K₁ : ℝ} (hβ : 0 < β)
    (h : (4 / 3 : ℝ) * a₁ * (β ^ 2 * K) + 2 * a * (β ^ 2 * K₁) = 0) :
    (4 / 3 : ℝ) * a₁ * K + 2 * a * K₁ = 0 := by
  have he : β ^ 2 * ((4 / 3 : ℝ) * a₁ * K + 2 * a * K₁) = 0 := by
    linear_combination h
  exact (mul_eq_zero.mp he).resolve_left (pow_ne_zero 2 hβ.ne')

/-- The determining system, its integrated functions, and the temporal
obstruction are all derived internally from physical half-line transport. -/
theorem beta_quadratic_first_integral_coefficients {I : Set ℝ} (hI : IsOpen I)
    (hc : IsPreconnected I) (hne : I.Nonempty) {t : ℝ → ℝ}
    (clock : RegularMechanicalClockOn I t) {β : ℝ} (hβ : 0 < β)
    {A₂ A₁ A₀ : ℝ → ℝ → ℝ} (hA : SmoothQuadraticOn I A₂ A₁ A₀)
    (htransport : ∀ τ ∈ I, ∀ z, 0 < z → ∀ v,
      3 * β * Real.sqrt (hyperbolicTimeCoefficient t τ) * z ^ (-1 / 3 : ℝ) < v →
      betaQuadraticTransport β (hyperbolicTimeCoefficient t) A₂ A₁ A₀ τ z v = 0) :
    ∃ D : ℝ, ∀ τ ∈ I, ∀ z, 0 < z → A₂ τ z = 0 ∧ A₁ τ z = 0 ∧ A₀ τ z = D := by
  have hK : ∀ τ ∈ I, DifferentiableAt ℝ (betaTimeCoefficient β t) τ :=
    fun τ hτ => (betaTimeCoefficient_hasDerivAt hI clock β hτ).differentiableAt
  have hKpos := fun τ hτ => betaTimeCoefficient_pos clock hβ (τ := τ) hτ
  have he := beta_quadratic_determining_from_transport hI clock hβ hA htransport
  obtain ⟨h⟩ := quadratic_integrated_from_determining hI hA hK he
  have hs := fun (τ : ℝ) (hτ : τ ∈ I) =>
    quadratic_scalar_obstruction_from_determining hI h hK hKpos he hτ
  have ha := fun (τ : ℝ) (hτ : τ ∈ I) => smooth_hasDerivAt_on_open hI h.a_smooth hτ
  have ha1 := fun (τ : ℝ) (hτ : τ ∈ I) =>
    smooth_hasDerivAt_on_open hI (smooth_deriv_on_open hI h.a_smooth) (τ := τ) hτ
  have ha2 : ∀ τ ∈ I, HasDerivAt (deriv (deriv h.a)) 0 τ := by
    intro τ hτ
    simpa only [(hs τ hτ).1] using smooth_hasDerivAt_on_open hI
      (smooth_deriv_on_open hI (smooth_deriv_on_open hI h.a_smooth)) hτ
  have hobs : ∀ τ ∈ I, (4 / 3 : ℝ) * deriv h.a τ * hyperbolicTimeCoefficient t τ +
      2 * h.a τ * shapeSquareTauRate (t τ) = 0 := by
    intro τ hτ
    apply beta_quadratic_obstruction_cancel hβ
    simpa only [(betaTimeCoefficient_hasDerivAt hI clock β hτ).deriv,
      betaTimeCoefficient] using (hs τ hτ).2.2.2
  have haz := quadratic_temporal_obstruction hI hc hne clock ha ha1 ha2 hobs
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

theorem beta_quadratic_first_integral_constant {I : Set ℝ} (hI : IsOpen I)
    (hc : IsPreconnected I) (hne : I.Nonempty) {t : ℝ → ℝ}
    (clock : RegularMechanicalClockOn I t) {β : ℝ} (hβ : 0 < β)
    {A₂ A₁ A₀ : ℝ → ℝ → ℝ} (hA : SmoothQuadraticOn I A₂ A₁ A₀)
    (htransport : ∀ τ ∈ I, ∀ z, 0 < z → ∀ v,
      3 * β * Real.sqrt (hyperbolicTimeCoefficient t τ) * z ^ (-1 / 3 : ℝ) < v →
      betaQuadraticTransport β (hyperbolicTimeCoefficient t) A₂ A₁ A₀ τ z v = 0) :
    ∃ D : ℝ, ∀ τ ∈ I, ∀ z, 0 < z → ∀ v, quadraticCandidate A₂ A₁ A₀ τ z v = D := by
  obtain ⟨D, hD⟩ := beta_quadratic_first_integral_coefficients hI hc hne clock hβ hA htransport
  refine ⟨D, ?_⟩
  intro τ hτ z hz v
  rcases hD τ hτ z hz with ⟨h2, h1, h0⟩
  simp [quadraticCandidate, h2, h1, h0]

end AffineQuadric
