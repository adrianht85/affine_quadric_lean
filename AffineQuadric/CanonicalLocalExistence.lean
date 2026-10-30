import AffineQuadric.CanonicalLocalField

/-! Construction at the terminal point: Picard-Lindelof, the clock coordinate,
smooth bootstrap, and the unchanged canonical solution interface. -/
noncomputable section
open Set Filter
open scoped Topology ContDiff
namespace AffineQuadric

structure CanonicalSmoothExtension (J : Set ℝ) (S pS : ℝ) (a V : ℝ → ℝ) where
  I : Set ℝ
  q : ℝ → ℝ
  p : ℝ → ℝ
  open_I : IsOpen I
  S_mem : S ∈ I
  subset_J : I ⊆ J
  canonical : LocalTransverseSolutionOn I S a V q p
  p_terminal : p S = pS
  p_positive : ∀ t ∈ I, 0 < p t

theorem lifted_coordinate_derivatives {γ : ℝ → ℝ × ℝ × ℝ} {v : ℝ × ℝ × ℝ} {t : ℝ}
    (hγ : HasDerivAt γ v t) :
    HasDerivAt (fun s => (γ s).1) v.1 t ∧
    HasDerivAt (fun s => (γ s).2.1) v.2.1 t ∧
    HasDerivAt (fun s => (γ s).2.2) v.2.2 t := by
  refine ⟨(ContinuousLinearMap.fst ℝ ℝ (ℝ × ℝ)).hasFDerivAt.comp_hasDerivAt t hγ, ?_, ?_⟩
  · exact ((ContinuousLinearMap.fst ℝ ℝ ℝ).comp
      (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ))).hasFDerivAt.comp_hasDerivAt t hγ
  · exact ((ContinuousLinearMap.snd ℝ ℝ ℝ).comp
      (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ))).hasFDerivAt.comp_hasDerivAt t hγ

theorem lifted_solution_clock {l u S : ℝ} {a V : ℝ → ℝ} {γ : ℝ → ℝ × ℝ × ℝ}
    (hS : S ∈ Ioo l u) (h0 : (γ S).1 = S)
    (hγ : ∀ t ∈ Ioo l u, HasDerivAt γ (canonicalLiftedField a V (γ t)) t) :
    EqOn (fun t => (γ t).1) id (Ioo l u) := by
  apply isOpen_Ioo.eqOn_of_deriv_eq (convex_Ioo l u).isPreconnected
    (fun t ht => (lifted_coordinate_derivatives (hγ t ht)).1.differentiableAt.differentiableWithinAt)
    differentiableOn_id _ hS h0
  intro t ht
  rw [(lifted_coordinate_derivatives (hγ t ht)).1.deriv]
  simp [canonicalLiftedField]

theorem canonical_smooth_extension_exists {J : Set ℝ} {S pS : ℝ} {a V : ℝ → ℝ}
    (h : CanonicalTerminalData J S pS a V) :
    Nonempty (CanonicalSmoothExtension J S pS a V) := by
  obtain ⟨γ, hγ0, ε, hε, hγ⟩ := (canonicalLiftedField_terminal h).exists_forall_mem_closedBall_exists_eq_forall_mem_Ioo_hasDerivAt₀ S
  have hS0 : S ∈ Ioo (S - ε) (S + ε) := by constructor <;> linarith
  have ht := lifted_solution_clock hS0 (by rw [hγ0]) hγ
  have hpS : 0 < (γ S).2.2 := by rw [hγ0]; exact h.p_pos
  have hnear : ∀ᶠ t in 𝓝 S, t ∈ Ioo (S - ε) (S + ε) ∧ t ∈ J ∧ 0 < (γ t).2.2 := by
    filter_upwards [isOpen_Ioo.mem_nhds hS0, h.open_J.mem_nhds h.S_mem,
      (lifted_coordinate_derivatives (hγ S hS0)).2.2.continuousAt.eventually (Ioi_mem_nhds hpS)] with t h1 h2 h3
    exact ⟨h1, h2, h3⟩
  obtain ⟨l, u, hSI, hsub⟩ := mem_nhds_iff_exists_Ioo_subset.mp hnear
  let I := Ioo l u
  have hIJ : I ⊆ J := fun t ht => (hsub ht).2.1
  have hγI : ∀ t ∈ I, HasDerivAt γ (canonicalLiftedField a V (γ t)) t :=
    fun t ht => hγ t (hsub ht).1
  have hsmooth : ContDiffOn ℝ ∞ γ I := by
    apply autonomous_solution_smooth isOpen_Ioo
      (canonicalLiftedField_smooth h.open_J h.smooth_a h.smooth_V) hγI
    intro t htI
    constructor
    · have hclock : (γ t).1 = t := ht (hsub htI).1
      rw [hclock]
      exact hIJ htI
    · exact (hsub htI).2.2.ne'
  refine ⟨⟨I, (fun t => (γ t).2.1), (fun t => (γ t).2.2), isOpen_Ioo, hSI, hIJ,
    ?_, ?_, (fun t ht => (hsub ht).2.2)⟩⟩
  · refine ⟨hSI, h.S_pos, h.smooth_a.mono hIJ, h.smooth_V.mono hIJ,
      hsmooth.snd.fst, hsmooth.snd.snd, ?_, h.a_pos, h.V_pos, hpS, h.a_rate_pos, ?_, ?_⟩
    · rw [hγ0]
    · intro t htI
      simpa only [canonicalLiftedField, ht (hsub htI).1] using (lifted_coordinate_derivatives (hγI t htI)).2.1
    · intro t htI
      simpa only [canonicalLiftedField, ht (hsub htI).1] using (lifted_coordinate_derivatives (hγI t htI)).2.2
  · change (γ S).2.2 = pS
    rw [hγ0]

end AffineQuadric
