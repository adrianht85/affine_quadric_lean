import AffineQuadric.TransverseRadialLaw
import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Analysis.Asymptotics.Lemmas

/-! Local Taylor bounds on the right endpoint parameter. No regularity outside
the given open set is used. The bounds are uniform filter big-O statements. -/
noncomputable section
open Set Filter Asymptotics
open scoped Topology ContDiff
namespace AffineQuadric

def scalarTaylorJet (f : ℝ → ℝ) (n : ℕ) (S x : ℝ) : ℝ :=
  ∑ k ∈ Finset.range (n + 1), (k.factorial : ℝ)⁻¹ * (x - S) ^ k * iteratedDeriv k f S

theorem terminal_taylor_jet_bigO {I : Set ℝ} (hI : IsOpen I) {f : ℝ → ℝ}
    (hf : ContDiffOn ℝ ∞ f I) {S : ℝ} (hS : S ∈ I) (n : ℕ) :
    (fun δ => f (S - δ) - scalarTaylorJet f n S (S - δ)) =O[𝓝[>] (0 : ℝ)] (fun δ => δ ^ n) := by
  obtain ⟨l, u, hSJ, hJI⟩ := mem_nhds_iff_exists_Ioo_subset.mp (hI.mem_nhds hS)
  have hfj : ContDiffOn ℝ n f (Ioo l u) := (hf.mono hJI).of_le
    (by exact_mod_cast (le_top : (n : ℕ∞) ≤ ⊤))
  have ht := taylor_isLittleO (convex_Ioo l u) hSJ hfj
  have hm : Tendsto (fun δ : ℝ => S - δ) (𝓝[>] 0) (𝓝[Ioo l u] S) := by
    apply tendsto_nhdsWithin_iff.mpr
    exact ⟨endpoint_parameter_tendsto S,
      (endpoint_parameter_tendsto S).eventually (isOpen_Ioo.mem_nhds hSJ)⟩
  have hp : ∀ x, taylorWithinEval f n (Ioo l u) S x = scalarTaylorJet f n S x := by
    intro x
    rw [taylor_within_apply]
    apply Finset.sum_congr rfl
    intro k hk
    rw [iteratedDerivWithin_of_isOpen isOpen_Ioo hSJ]
    rfl
  have hh := (ht.comp_tendsto hm).isBigO
  have hr : (fun δ : ℝ => (S - δ - S) ^ n) =O[𝓝[>] 0] (fun δ => δ ^ n) := by
    exact (isBigO_const_mul_self ((-1 : ℝ) ^ n) (fun δ : ℝ => δ ^ n) _).congr_left
      (fun δ => by ring)
  simpa only [hp] using hh.trans hr

theorem terminal_taylor_first_bigO {I : Set ℝ} (hI : IsOpen I) {f : ℝ → ℝ}
    (hf : ContDiffOn ℝ ∞ f I) {S : ℝ} (hS : S ∈ I) :
    (fun δ => f (S - δ) - (f S - deriv f S * δ)) =O[𝓝[>] (0 : ℝ)] (fun δ => δ ^ 2) := by
  have ht := terminal_taylor_jet_bigO hI hf hS 2
  have hc := isBigO_const_mul_self (deriv (deriv f) S / 2) (fun δ : ℝ => δ ^ 2) (𝓝[>] (0 : ℝ))
  apply (ht.add hc).congr_left
  intro δ
  norm_num [scalarTaylorJet, Finset.sum_range_succ, iteratedDeriv_succ, iteratedDeriv_zero]
  ring

theorem terminal_taylor_second_bigO {I : Set ℝ} (hI : IsOpen I) {f : ℝ → ℝ}
    (hf : ContDiffOn ℝ ∞ f I) {S : ℝ} (hS : S ∈ I) :
    (fun δ => f (S - δ) - (f S - deriv f S * δ + deriv (deriv f) S / 2 * δ ^ 2))
      =O[𝓝[>] (0 : ℝ)] (fun δ => δ ^ 3) := by
  have ht := terminal_taylor_jet_bigO hI hf hS 3
  have hc := isBigO_const_mul_self (-iteratedDeriv 3 f S / 6) (fun δ : ℝ => δ ^ 3) (𝓝[>] (0 : ℝ))
  apply (ht.add hc).congr_left
  intro δ
  norm_num [scalarTaylorJet, Finset.sum_range_succ, iteratedDeriv_succ, iteratedDeriv_zero]
  ring

theorem terminal_constant_bigO {I : Set ℝ} (hI : IsOpen I) {f : ℝ → ℝ}
    (hf : ContDiffOn ℝ ∞ f I) {S : ℝ} (hS : S ∈ I) :
    (fun δ => f (S - δ) - f S) =O[𝓝[>] (0 : ℝ)] (fun δ => δ) := by
  have hh := ((smooth_hasDerivAt_on_open hI hf hS).isBigO_sub).comp_tendsto (endpoint_parameter_tendsto S)
  have hr : (fun δ : ℝ => S - δ - S) =O[𝓝[>] 0] (fun δ => δ) := by
    exact (isBigO_const_mul_self (-1 : ℝ) (fun δ : ℝ => δ) _).congr_left (fun δ => by ring)
  exact hh.trans hr

end AffineQuadric
