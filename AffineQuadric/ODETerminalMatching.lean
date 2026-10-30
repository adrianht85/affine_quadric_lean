import AffineQuadric.CanonicalLocalField
import Mathlib.Analysis.Calculus.FDeriv.Extend
import Mathlib.Analysis.ODE.Gronwall

/-! Endpoint uniqueness for a local autonomous field. The incoming curve is
extended by its limit; its left derivative is proved before using uniqueness. -/
noncomputable section
open Set Filter
open scoped Topology ContDiff
namespace AffineQuadric

def terminalUpdate {E : Type*} (f : ℝ → E) (S : ℝ) (xS : E) : ℝ → E :=
  Function.update f S xS

theorem terminalUpdate_left_limit {E : Type*} [TopologicalSpace E]
    {f : ℝ → E} {S : ℝ} {xS : E} (hf : Tendsto f (𝓝[<] S) (𝓝 xS)) :
    Tendsto (terminalUpdate f S xS) (𝓝[<] S) (𝓝 xS) := by
  apply hf.congr'
  filter_upwards [eventually_mem_nhdsWithin] with t ht
  simp [terminalUpdate, ne_of_lt (show t < S from ht)]

theorem terminalUpdate_hasDerivAt {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : ℝ → E} {S t : ℝ} {xS f' : E} (ht : t ≠ S) (hf : HasDerivAt f f' t) :
    HasDerivAt (terminalUpdate f S xS) f' t := by
  apply hf.congr_of_eventuallyEq
  filter_upwards [eventually_ne_nhds ht] with s hs
  simp [terminalUpdate, hs]

theorem terminalUpdate_ode {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : ℝ → E} {G : E → E} {S : ℝ} {xS : E}
    (hf : ∀ᶠ t in 𝓝[<] S, HasDerivAt f (G (f t)) t) :
    ∀ᶠ t in 𝓝[<] S,
      HasDerivAt (terminalUpdate f S xS) (G (terminalUpdate f S xS t)) t := by
  filter_upwards [hf, eventually_mem_nhdsWithin] with t ht hlt
  have hn : t ≠ S := ne_of_lt hlt
  simpa only [terminalUpdate, Function.update_of_ne hn] using terminalUpdate_hasDerivAt hn ht

theorem autonomous_terminal_deriv {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : ℝ → E} {G : E → E} {S : ℝ} {xS : E} (hG : ContinuousAt G xS)
    (hlim : Tendsto f (𝓝[<] S) (𝓝 xS))
    (hf : ∀ᶠ t in 𝓝[<] S, HasDerivAt f (G (f t)) t) :
    HasDerivWithinAt (terminalUpdate f S xS) (G xS) (Iic S) S := by
  have he := terminalUpdate_ode (xS := xS) hf
  have hl := terminalUpdate_left_limit hlim
  obtain ⟨b, hb, hOn⟩ := mem_nhdsLT_iff_exists_Ioo_subset.mp he
  have hc : ContinuousWithinAt (terminalUpdate f S xS) (Ioo b S) S := by
    change Tendsto (terminalUpdate f S xS) (𝓝[Ioo b S] S) (𝓝 (terminalUpdate f S xS S))
    have h0 : terminalUpdate f S xS S = xS := by simp [terminalUpdate]
    rw [h0]
    exact hl.mono_left (nhdsWithin_mono S Ioo_subset_Iio_self)
  have hdlim : Tendsto (fun t => deriv (terminalUpdate f S xS) t) (𝓝[<] S) (𝓝 (G xS)) := by
    apply (hG.tendsto.comp hl).congr'
    filter_upwards [he] with t ht
    exact ht.deriv.symm
  exact hasDerivWithinAt_Iic_of_tendsto_deriv
    (fun t ht => (hOn ht).differentiableAt.differentiableWithinAt) hc (Ioo_mem_nhdsLT hb) hdlim

theorem autonomous_terminal_match {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f g : ℝ → E} {G : E → E} {S : ℝ} {xS : E} (hG : ContDiffAt ℝ 1 G xS)
    (hlim : Tendsto f (𝓝[<] S) (𝓝 xS))
    (hf : ∀ᶠ t in 𝓝[<] S, HasDerivAt f (G (f t)) t)
    (hg : ∀ᶠ t in 𝓝 S, HasDerivAt g (G (g t)) t) (hg0 : g S = xS) :
    f =ᶠ[𝓝[<] S] g := by
  obtain ⟨K, U, hU, hLip⟩ := hG.exists_lipschitzOnWith
  have he := terminalUpdate_ode (xS := xS) hf
  have he0 : terminalUpdate f S xS S = xS := by simp [terminalUpdate]
  have heS := autonomous_terminal_deriv hG.continuousAt hlim hf
  have hgS := hg.self_of_nhds
  have hgl : Tendsto g (𝓝 S) (𝓝 xS) := by simpa only [hg0] using hgS.continuousAt.tendsto
  have hnear : ∀ᶠ t in 𝓝[<] S,
      HasDerivAt (terminalUpdate f S xS) (G (terminalUpdate f S xS t)) t ∧
      terminalUpdate f S xS t ∈ U ∧ HasDerivAt g (G (g t)) t ∧ g t ∈ U := by
    filter_upwards [he, (terminalUpdate_left_limit hlim).eventually hU,
      hg.filter_mono inf_le_left, (hgl.eventually hU).filter_mono inf_le_left]
      with t h1 h2 h3 h4
    exact ⟨h1, h2, h3, h4⟩
  obtain ⟨b, hb, hOn⟩ := mem_nhdsLT_iff_exists_Ioo_subset.mp hnear
  filter_upwards [Ioo_mem_nhdsLT hb] with t ht
  have hcE : ContinuousOn (terminalUpdate f S xS) (Icc t S) := by
    intro r hr
    by_cases hrs : r = S
    · subst r
      exact heS.continuousWithinAt.mono (fun x hx => hx.2)
    · exact (hOn ⟨lt_of_lt_of_le ht.1 hr.1, lt_of_le_of_ne hr.2 hrs⟩).1.continuousAt.continuousWithinAt
  have hcG : ContinuousOn g (Icc t S) := by
    intro r hr
    by_cases hrs : r = S
    · subst r; exact hgS.continuousAt.continuousWithinAt
    · exact (hOn ⟨lt_of_lt_of_le ht.1 hr.1, lt_of_le_of_ne hr.2 hrs⟩).2.2.1.continuousAt.continuousWithinAt
  have hdE : ∀ r ∈ Ioc t S,
      HasDerivWithinAt (terminalUpdate f S xS) (G (terminalUpdate f S xS r)) (Iic r) r := by
    intro r hr
    by_cases hrs : r = S
    · subst r; simpa only [he0] using heS
    · exact (hOn ⟨ht.1.trans hr.1, lt_of_le_of_ne hr.2 hrs⟩).1.hasDerivWithinAt
  have hdG : ∀ r ∈ Ioc t S, HasDerivWithinAt g (G (g r)) (Iic r) r := by
    intro r hr
    by_cases hrs : r = S
    · subst r; exact hgS.hasDerivWithinAt
    · exact (hOn ⟨ht.1.trans hr.1, lt_of_le_of_ne hr.2 hrs⟩).2.2.1.hasDerivWithinAt
  have hmE : ∀ r ∈ Ioc t S, terminalUpdate f S xS r ∈ U := by
    intro r hr
    by_cases hrs : r = S
    · subst r; rw [he0]; exact mem_of_mem_nhds hU
    · exact (hOn ⟨ht.1.trans hr.1, lt_of_le_of_ne hr.2 hrs⟩).2.1
  have hmG : ∀ r ∈ Ioc t S, g r ∈ U := by
    intro r hr
    by_cases hrs : r = S
    · subst r; rw [hg0]; exact mem_of_mem_nhds hU
    · exact (hOn ⟨ht.1.trans hr.1, lt_of_le_of_ne hr.2 hrs⟩).2.2.2
  have heq := ODE_solution_unique_of_mem_Icc_left (v := fun _ => G) (s := fun _ => U)
    (fun _ _ => hLip) hcE hdE hmE hcG hdG hmG (he0.trans hg0.symm)
  have hh := heq (show t ∈ Icc t S from ⟨le_rfl, ht.2.le⟩)
  simpa [terminalUpdate, ht.2.ne] using hh

theorem autonomous_local_unique {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f g : ℝ → E} {G : E → E} {S : ℝ} {xS : E} (hG : ContDiffAt ℝ 1 G xS)
    (hf : ∀ᶠ t in 𝓝 S, HasDerivAt f (G (f t)) t)
    (hg : ∀ᶠ t in 𝓝 S, HasDerivAt g (G (g t)) t) (hf0 : f S = xS) (hg0 : g S = xS) :
    f =ᶠ[𝓝 S] g := by
  obtain ⟨K, U, hU, hLip⟩ := hG.exists_lipschitzOnWith
  have hfc : Tendsto f (𝓝 S) (𝓝 xS) := by simpa only [hf0] using hf.self_of_nhds.continuousAt.tendsto
  have hgc : Tendsto g (𝓝 S) (𝓝 xS) := by simpa only [hg0] using hg.self_of_nhds.continuousAt.tendsto
  exact ODE_solution_unique_of_eventually (v := fun _ => G) (s := fun _ => U)
    (Eventually.of_forall (fun _ => hLip)) (hf.and (hfc.eventually hU)) (hg.and (hgc.eventually hU))
    (hf0.trans hg0.symm)

end AffineQuadric
