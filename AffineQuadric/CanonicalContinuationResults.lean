import AffineQuadric.CanonicalIncoming

/-! Corollaries of the accepted scalar results, now on the continuation
constructed from the field and the incoming trajectory. No profile is reproved. -/
noncomputable section
open Set Filter Asymptotics
open scoped Topology
namespace AffineQuadric

variable {J : Set ℝ} {S pS ε0 : ℝ} {a V q p : ℝ → ℝ}

theorem canonicalContinuation_eta (C : CanonicalContinuation J S pS ε0 a V q p) :
    collisionEta a V C.extension.p S = 2 * V S ^ 2 * a S * deriv a S / pS ^ 2 := by
  simp only [collisionEta, C.extension.p_terminal]

theorem canonicalContinuation_fold (C : CanonicalContinuation J S pS ε0 a V q p) :
    HasDerivAt (fun s => (C.extension.q s, C.extension.p s))
      (0, 4 * V S ^ 2 * a S / C.extension.p S) S ∧
    (0, 4 * V S ^ 2 * a S / C.extension.p S) ≠ (0, (0 : ℝ)) ∧
    deriv C.extension.q S = 0 ∧
    deriv (deriv C.extension.q) S = -2 * collisionEta a V C.extension.p S ∧
    deriv (deriv C.extension.q) S < 0 :=
  transverse_differential_fold C.extension.open_I C.extension.canonical

theorem canonicalContinuation_crossing (C : CanonicalContinuation J S pS ε0 a V q p) :
    ∀ᶠ δ in 𝓝[>] (0 : ℝ),
      0 < collisionGap a C.extension.q (S - δ) ∧ collisionGap a C.extension.q (S + δ) < 0 := by
  apply simple_zero_sign_crossing (collisionGap_hasDerivAt C.extension.open_I C.extension.canonical)
    (by simp [collisionGap, C.extension.canonical.contact])
  nlinarith [C.extension.canonical.a_pos, C.extension.canonical.a_rate_pos]

theorem canonicalContinuation_taylor (C : CanonicalContinuation J S pS ε0 a V q p) :
    (fun δ => C.extension.q (S - δ) - (a S - collisionEta a V C.extension.p S * δ ^ 2))
      =O[𝓝[>] (0 : ℝ)] (fun δ => δ ^ 3) :=
  transverse_q_taylor_bigO C.extension.open_I C.extension.canonical

theorem canonicalContinuation_radial_limit (C : CanonicalContinuation J S pS ε0 a V q p) :
    Tendsto (fun δ => terminalDistance (collisionRadialW C.extension.q) S (S - δ) ^ 2 *
      radialScalarCurvature (collisionRadialW C.extension.q) (S - δ))
      (𝓝[>] (0 : ℝ)) (𝓝 (2 / 9 : ℝ)) :=
  (transverse_scalar_radial_law C.extension.open_I C.extension.canonical).1

theorem canonicalContinuation_curvature_remainder (C : CanonicalContinuation J S pS ε0 a V q p) :
    (fun δ => radialScalarCurvature (collisionRadialW C.extension.q) (S - δ) -
      (2 / 9 : ℝ) * terminalDistance (collisionRadialW C.extension.q) S (S - δ) ^ (-2 : ℝ))
      =O[𝓝[>] (0 : ℝ)]
        (fun δ => terminalDistance (collisionRadialW C.extension.q) S (S - δ) ^ (-4 / 3 : ℝ)) :=
  (transverse_curvature_remainders C.extension.open_I C.extension.canonical).2

end AffineQuadric
