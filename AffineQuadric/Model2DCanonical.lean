import AffineQuadric.Model2DCurvature
import AffineQuadric.CanonicalContinuationResults
import Mathlib.Data.Fin.VecNotation

/-! The model surface associated to the constructed canonical continuation.
Only its two-dimensional sectional curvature is asserted. No embedding into
the six-dimensional metric, horizontal geometry or extension obstruction is proved. -/
noncomputable section
open Set Filter Asymptotics
open scoped Topology
namespace AffineQuadric

variable {J : Set ℝ} {S pS ε0 : ℝ} {a V q p : ℝ → ℝ}

theorem canonicalContinuation_model2D_near (C : CanonicalContinuation J S pS ε0 a V q p) :
    ∀ᶠ δ in 𝓝[>] (0 : ℝ), S - δ ∈ C.extension.I ∧
      0 < collisionRadialW C.extension.q (S - δ) ∧
      ∀ θ : ℝ, model2DSectional (collisionRadialW C.extension.q) ![S - δ, θ] =
        radialScalarCurvature (collisionRadialW C.extension.q) (S - δ) := by
  have hz := transverse_simple_radial_zero C.extension.open_I C.extension.canonical
  have hpos := simple_zero_sign_crossing hz.rate hz.zero (neg_neg_of_pos hz.eta_pos)
  filter_upwards [hpos, (endpoint_parameter_tendsto S).eventually
    (C.extension.open_I.mem_nhds C.extension.S_mem)] with δ hp hmem
  refine ⟨hmem, hp.1, ?_⟩
  intro θ
  exact model2DSectional_eq_radialScalarCurvature C.extension.open_I hz.smooth_w hmem hp.1

theorem canonicalContinuation_model2D_radial_limit
    (C : CanonicalContinuation J S pS ε0 a V q p) (θ : ℝ → ℝ) :
    Tendsto (fun δ => terminalDistance (collisionRadialW C.extension.q) S (S - δ) ^ 2 *
      model2DSectional (collisionRadialW C.extension.q) ![S - δ, θ δ])
      (𝓝[>] (0 : ℝ)) (𝓝 (2 / 9 : ℝ)) := by
  apply (canonicalContinuation_radial_limit C).congr'
  filter_upwards [canonicalContinuation_model2D_near C] with δ hδ
  rw [hδ.2.2 (θ δ)]

theorem canonicalContinuation_model2D_curvature_remainder
    (C : CanonicalContinuation J S pS ε0 a V q p) (θ : ℝ → ℝ) :
    (fun δ => model2DSectional (collisionRadialW C.extension.q) ![S - δ, θ δ] -
      (2 / 9 : ℝ) * terminalDistance (collisionRadialW C.extension.q) S (S - δ) ^ (-2 : ℝ))
      =O[𝓝[>] (0 : ℝ)]
        (fun δ => terminalDistance (collisionRadialW C.extension.q) S (S - δ) ^ (-4 / 3 : ℝ)) := by
  apply (canonicalContinuation_curvature_remainder C).congr' _ (EventuallyEq.rfl)
  filter_upwards [canonicalContinuation_model2D_near C] with δ hδ
  rw [hδ.2.2 (θ δ)]

/-- Existence and matching are constructed, rather than an assumed 2D curvature law.
The model's remainder needs smooth terminal data, not analytic solution data. -/
theorem canonical_model2D_continuation_exists
    (h : CanonicalTerminalData J S pS a V)
    (hin : IncomingCanonicalTrajectory S pS ε0 a V q p) :
    ∃ C : CanonicalContinuation J S pS ε0 a V q p,
      ∀ θ : ℝ → ℝ,
      (fun δ => model2DSectional (collisionRadialW C.extension.q) ![S - δ, θ δ] -
        (2 / 9 : ℝ) * terminalDistance (collisionRadialW C.extension.q) S (S - δ) ^ (-2 : ℝ))
        =O[𝓝[>] (0 : ℝ)]
          (fun δ => terminalDistance (collisionRadialW C.extension.q) S (S - δ) ^ (-4 / 3 : ℝ)) := by
  obtain ⟨C⟩ := canonical_continuation_exists h hin
  exact ⟨C, canonicalContinuation_model2D_curvature_remainder C⟩

end AffineQuadric
