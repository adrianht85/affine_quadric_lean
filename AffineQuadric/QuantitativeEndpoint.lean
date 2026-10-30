import AffineQuadric.RadiusBounds
import AffineQuadric.TerminalBounds
import AffineQuadric.WeightedTransport
import AffineQuadric.RadialLength
import AffineQuadric.Profiles

/-! Conditional quantitative endpoint bounds, with comparison, average normalization,
and endpoint data explicit. No global comparison or physical endpoint existence is proved. -/
noncomputable section
open Set
namespace AffineQuadric

def physicalTransportWeight (A κ s : ℝ) : ℝ := A * s * v8Volume κ s ^ 2

theorem physical_weight_transport {S A κ : ℝ} {R : ℝ → ℝ}
    (hA : 0 < A) (hκ : 0 < κ) (hRc : ContinuousOn R (Icc 0 S))
    (hRd : StrictAntiOn R (Icc 0 S)) :
    WeightedTransportOn S R (physicalTransportWeight A κ) := by
  have hc : Continuous (v8Volume κ) :=
    continuous_iff_continuousAt.2 (fun s => (v8Volume_hasDerivAt κ s).continuousAt)
  refine ⟨hRc, ((continuous_const.mul continuous_id).mul (hc.pow 2)).continuousOn, hRd, ?_, ?_⟩
  · intro s hs
    exact mul_nonneg (mul_nonneg hA.le hs.1) (sq_nonneg _)
  · intro s hs
    exact mul_pos (mul_pos hA hs.1) (sq_pos_of_pos (v8Volume_pos hκ hs.1))

/-- All four numerical bounds are derived from the average, not taken as input. -/
theorem quantitative_endpoint_bounds {S C A V X a a₁ p : ℝ} {R w u v : ℝ → ℝ}
    (hS : 0 < S) (hC : 1 < C) (hA : 0 < A) (hV : 0 < V) (hX : 0 < X)
    (ha : 0 < a) (ha₁ : 0 < a₁) (hp : 0 < p)
    (h : WeightedTransportOn S R w) (h0 : R 0 = 1 / C)
    (hQid : transportAverage R w S = p ^ 2 / criticalMomentumSquare V X A)
    (hRid : R S = a / (A * S)) (hprofile : R S = radiusProfile (3 * S))
    (hlen : RadialLengthData S u v) (hend : u S = a) :
    (R S < transportAverage R w S ∧ transportAverage R w S < 1 / C) ∧
    S < min (1 / (C - 1)) (C / (3 * (C - 1))) ∧
    (0 < p ^ 2 ∧ p ^ 2 < 2 * V ^ 2 * X / (C * A)) ∧
    (0 < C * A * a * a₁ / X ∧ C * A * a * a₁ / X < terminalAcceleration V a a₁ p) ∧
    (radialLength v S ^ 2 ≤ S * a / 2 ∧ radialLength v S ≤ Real.sqrt (S * a / 2)) ∧
    radialLength v S < Real.sqrt (A / (2 * C)) * S := by
  have hb := transportAverage_bounds h hS le_rfl
  have hQ : transportAverage R w S < 1 / C := by simpa only [h0] using hb.2
  have hR : R S < 1 / C := lt_trans hb.1 hQ
  have hrad : radiusProfile (3 * S) < 1 / C := by rw [← hprofile]; exact hR
  have hmoment : p ^ 2 / criticalMomentumSquare V X A < 1 / C := by rw [← hQid]; exact hQ
  have hCp : 0 < C := by linarith
  have haa : a < A * S / C := by
    have hh : a / (A * S) < 1 / C := by rw [← hRid]; exact hR
    have hh' := (div_lt_iff₀ (mul_pos hA hS)).mp hh
    calc
      a < (1 / C) * (A * S) := hh'
      _ = A * S / C := by ring
  exact ⟨⟨hb.1, hQ⟩, endpoint_radius_bound hS hC hrad,
    terminal_momentum_bound hV hX hA hp hmoment,
    terminal_acceleration_bound hV hX hA ha ha₁ hp hCp hmoment,
    ⟨radialLength_sq_bound hS hlen hend, radialLength_bound hS hlen hend⟩,
    radialLength_strict_bound hS hA hCp hlen hend haa⟩

/-- Application with the actual V8 weight. R is extended continuously to zero;
the identity R=u/(As) is only required at positive times. -/
theorem physical_weight_endpoint_bounds {S C A κ V X a a₁ p : ℝ} {R u v : ℝ → ℝ}
    (hS : 0 < S) (hC : 1 < C) (hA : 0 < A) (hκ : 0 < κ) (hV : 0 < V) (hX : 0 < X)
    (ha : 0 < a) (ha₁ : 0 < a₁) (hp : 0 < p)
    (hRc : ContinuousOn R (Icc 0 S)) (hRd : StrictAntiOn R (Icc 0 S)) (h0 : R 0 = 1 / C)
    (hQid : transportAverage R (physicalTransportWeight A κ) S = p ^ 2 / criticalMomentumSquare V X A)
    (hRid : ∀ s ∈ Ioc 0 S, R s = u s / (A * s))
    (hprofile : a / (A * S) = radiusProfile (3 * S))
    (hlen : RadialLengthData S u v) (hend : u S = a) :
    S < min (1 / (C - 1)) (C / (3 * (C - 1))) ∧
    (0 < p ^ 2 ∧ p ^ 2 < 2 * V ^ 2 * X / (C * A)) ∧
    (0 < C * A * a * a₁ / X ∧ C * A * a * a₁ / X < terminalAcceleration V a a₁ p) ∧
    radialLength v S ≤ Real.sqrt (S * a / 2) ∧
    radialLength v S < Real.sqrt (A / (2 * C)) * S := by
  have hRterminal : R S = a / (A * S) := by rw [hRid S ⟨hS, le_rfl⟩, hend]
  have hh := quantitative_endpoint_bounds hS hC hA hV hX ha ha₁ hp
    (physical_weight_transport hA hκ hRc hRd) h0 hQid hRterminal
    (hRterminal.trans hprofile) hlen hend
  exact ⟨hh.2.1, hh.2.2.1, hh.2.2.2.1, hh.2.2.2.2.1.2, hh.2.2.2.2.2⟩

end AffineQuadric
