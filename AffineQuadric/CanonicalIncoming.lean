import AffineQuadric.CanonicalLocalExistence
import AffineQuadric.ODETerminalMatching

/-! The terminal solution is matched to the original incoming trajectory.
No endpoint differentiability or equality with the continuation is assumed. -/
noncomputable section
open Set Filter
open scoped Topology ContDiff
namespace AffineQuadric

def liftedCanonicalCurve (q p : ℝ → ℝ) (t : ℝ) : ℝ × ℝ × ℝ := (t, q t, p t)

structure IncomingCanonicalTrajectory (S pS ε0 : ℝ) (a V q p : ℝ → ℝ) : Prop where
  epsilon_pos : 0 < ε0
  dq : ∀ t ∈ Ioo (S - ε0) S, HasDerivAt q (qdot (V t) (a t) (q t) (p t)) t
  dp : ∀ t ∈ Ioo (S - ε0) S, HasDerivAt p (pdot (V t) (q t) (p t)) t
  q_limit : Tendsto q (𝓝[<] S) (𝓝 (a S))
  p_limit : Tendsto p (𝓝[<] S) (𝓝 pS)

theorem liftedCanonicalCurve_ode {a V q p : ℝ → ℝ} {t : ℝ}
    (hq : HasDerivAt q (qdot (V t) (a t) (q t) (p t)) t)
    (hp : HasDerivAt p (pdot (V t) (q t) (p t)) t) :
    HasDerivAt (liftedCanonicalCurve q p)
      (canonicalLiftedField a V (liftedCanonicalCurve q p t)) t :=
  (hasDerivAt_id t).prodMk (hq.prodMk hp)

theorem canonical_extension_lifted_ode {J : Set ℝ} {S pS : ℝ} {a V : ℝ → ℝ}
    (E : CanonicalSmoothExtension J S pS a V) :
    ∀ᶠ t in 𝓝 S, HasDerivAt (liftedCanonicalCurve E.q E.p)
      (canonicalLiftedField a V (liftedCanonicalCurve E.q E.p t)) t := by
  filter_upwards [E.open_I.mem_nhds E.S_mem] with t ht
  exact liftedCanonicalCurve_ode (E.canonical.dq t ht) (E.canonical.dp t ht)

theorem canonical_extension_initial {J : Set ℝ} {S pS : ℝ} {a V : ℝ → ℝ}
    (E : CanonicalSmoothExtension J S pS a V) :
    liftedCanonicalCurve E.q E.p S = (S, a S, pS) := by
  simp only [liftedCanonicalCurve, E.canonical.contact, E.p_terminal]

theorem canonical_smooth_extension_unique {J : Set ℝ} {S pS : ℝ} {a V : ℝ → ℝ}
    (h : CanonicalTerminalData J S pS a V)
    (E₁ E₂ : CanonicalSmoothExtension J S pS a V) :
    E₁.q =ᶠ[𝓝 S] E₂.q ∧ E₁.p =ᶠ[𝓝 S] E₂.p := by
  have he := autonomous_local_unique (canonicalLiftedField_terminal h)
    (canonical_extension_lifted_ode E₁) (canonical_extension_lifted_ode E₂)
    (canonical_extension_initial E₁) (canonical_extension_initial E₂)
  exact ⟨he.mono (fun _ ht => congrArg (fun x : ℝ × ℝ × ℝ => x.2.1) ht),
    he.mono (fun _ ht => congrArg (fun x : ℝ × ℝ × ℝ => x.2.2) ht)⟩

theorem canonical_incoming_match {J : Set ℝ} {S pS ε0 : ℝ} {a V q p : ℝ → ℝ}
    (h : CanonicalTerminalData J S pS a V)
    (hin : IncomingCanonicalTrajectory S pS ε0 a V q p)
    (E : CanonicalSmoothExtension J S pS a V) :
    ∃ ε : ℝ, 0 < ε ∧ ε ≤ ε0 ∧ ∀ t ∈ Ioo (S - ε) S,
      t ∈ E.I ∧ q t = E.q t ∧ p t = E.p t := by
  have ht : Tendsto (fun t : ℝ => t) (𝓝[<] S) (𝓝 S) := tendsto_id.mono_left inf_le_left
  have hlim : Tendsto (liftedCanonicalCurve q p) (𝓝[<] S) (𝓝 (S, a S, pS)) :=
    ht.prodMk_nhds (hin.q_limit.prodMk_nhds hin.p_limit)
  have hf : ∀ᶠ t in 𝓝[<] S, HasDerivAt (liftedCanonicalCurve q p)
      (canonicalLiftedField a V (liftedCanonicalCurve q p t)) t := by
    filter_upwards [Ioo_mem_nhdsLT (show S - ε0 < S by linarith [hin.epsilon_pos])] with t ht
    exact liftedCanonicalCurve_ode (hin.dq t ht) (hin.dp t ht)
  have he := autonomous_terminal_match (canonicalLiftedField_terminal h) hlim hf
    (canonical_extension_lifted_ode E) (canonical_extension_initial E)
  have hnear : ∀ᶠ t in 𝓝[<] S, t ∈ E.I ∧ q t = E.q t ∧ p t = E.p t := by
    filter_upwards [he, ht.eventually (E.open_I.mem_nhds E.S_mem)] with t he hm
    exact ⟨hm, congrArg (fun x : ℝ × ℝ × ℝ => x.2.1) he,
      congrArg (fun x : ℝ × ℝ × ℝ => x.2.2) he⟩
  obtain ⟨b, hb, hOn⟩ := mem_nhdsLT_iff_exists_Ioo_subset.mp hnear
  refine ⟨min (S - b) ε0, lt_min (sub_pos.mpr hb) hin.epsilon_pos, min_le_right _ _, ?_⟩
  intro t ht
  apply hOn
  constructor
  · linarith [min_le_left (S - b) ε0, ht.1]
  · exact ht.2

structure CanonicalContinuation (J : Set ℝ) (S pS ε0 : ℝ) (a V q p : ℝ → ℝ) where
  extension : CanonicalSmoothExtension J S pS a V
  epsilon : ℝ
  epsilon_pos : 0 < epsilon
  epsilon_le : epsilon ≤ ε0
  left_domain : ∀ t ∈ Ioo (S - epsilon) S, t ∈ extension.I
  agrees_q : ∀ t ∈ Ioo (S - epsilon) S, q t = extension.q t
  agrees_p : ∀ t ∈ Ioo (S - epsilon) S, p t = extension.p t

theorem canonical_continuation_exists {J : Set ℝ} {S pS ε0 : ℝ} {a V q p : ℝ → ℝ}
    (h : CanonicalTerminalData J S pS a V)
    (hin : IncomingCanonicalTrajectory S pS ε0 a V q p) :
    Nonempty (CanonicalContinuation J S pS ε0 a V q p) := by
  obtain ⟨E⟩ := canonical_smooth_extension_exists h
  obtain ⟨ε, hε, hε0, he⟩ := canonical_incoming_match h hin E
  exact ⟨⟨E, ε, hε, hε0, (fun t ht => (he t ht).1),
    (fun t ht => (he t ht).2.1), (fun t ht => (he t ht).2.2)⟩⟩

end AffineQuadric
