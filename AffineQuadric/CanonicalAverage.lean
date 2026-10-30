import AffineQuadric.CriticalMomentum

/-! The average normalization is derived from the canonical p equation and zero-origin data.
The same given trajectory can be continued past S with p>0, without physical X>0 there. -/
noncomputable section
open Set MeasureTheory Filter
open scoped Topology
namespace AffineQuadric

structure CanonicalMomentumOn (T κ : ℝ) (u p : ℝ → ℝ) : Prop where
  u_cont : ContinuousOn u (Icc 0 T)
  p_cont : ContinuousOn p (Icc 0 T)
  u_initial : u 0 = 0
  p_initial : p 0 = 0
  p_pos : ∀ s ∈ Ioc 0 T, 0 < p s
  dp : ∀ s ∈ Ioo 0 T, HasDerivAt p (pdot (v8Volume κ s) (u s) (p s)) s

theorem canonical_square_integral {T κ s : ℝ} {u p : ℝ → ℝ}
    (h : CanonicalMomentumOn T κ u p) (hs : 0 < s) (hsT : s ≤ T) :
    p s ^ 2 = 8 * ∫ x in 0..s, u x * v8Volume κ x ^ 2 := by
  have hV : Continuous (v8Volume κ) :=
    continuous_iff_continuousAt.2 (fun x => (v8Volume_hasDerivAt κ x).continuousAt)
  have hc := (h.u_cont.mono (Icc_subset_Icc (le_refl 0) hsT)).mul (hV.pow 2).continuousOn
  have hi : IntervalIntegrable (fun x => 8 * (u x * v8Volume κ x ^ 2)) volume 0 s :=
    (continuousOn_const.mul hc).intervalIntegrable_of_Icc hs.le
  have hd : ∀ x ∈ Ioo 0 s, HasDerivAt (fun y => p y ^ 2) (8 * (u x * v8Volume κ x ^ 2)) x := by
    intro x hx
    exact (momentum_square_balance (ne_of_gt (h.p_pos x ⟨hx.1, hx.2.le.trans hsT⟩))
      (h.dp x ⟨hx.1, lt_of_lt_of_le hx.2 hsT⟩)).congr_deriv (by ring)
  have hh := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hs.le
    ((h.p_cont.mono (Icc_subset_Icc (le_refl 0) hsT)).pow 2) hd hi
  rw [intervalIntegral.integral_const_mul, h.p_initial, zero_pow (by norm_num : (2 : ℕ) ≠ 0), sub_zero] at hh
  exact hh.symm

theorem canonical_numerator_eq {T κ A s : ℝ} {R u p : ℝ → ℝ}
    (h : CanonicalMomentumOn T κ u p) (hA : A ≠ 0)
    (hR : ∀ x ∈ Ioc 0 T, R x = u x / (A * x)) (hs : 0 < s) (hsT : s ≤ T) :
    transportNumerator R (physicalTransportWeight A κ) s = p s ^ 2 / 8 := by
  have heq : transportNumerator R (physicalTransportWeight A κ) s =
      ∫ x in 0..s, u x * v8Volume κ x ^ 2 := by
    apply intervalIntegral.integral_congr
    intro x hx
    have hxI : x ∈ Icc 0 s := by simpa only [uIcc_of_le hs.le] using hx
    change R x * physicalTransportWeight A κ x = u x * v8Volume κ x ^ 2
    by_cases hx0 : x = 0
    · subst x
      simp [physicalTransportWeight, h.u_initial]
    · have hxp : 0 < x := lt_of_le_of_ne hxI.1 (Ne.symm hx0)
      rw [hR x ⟨hxp, hxI.2.trans hsT⟩]
      dsimp [physicalTransportWeight]
      field_simp
  rw [heq, canonical_square_integral h hs hsT]
  ring

theorem canonical_average_eq {T β κ s : ℝ} {R u p : ℝ → ℝ}
    (hβ : 0 < β) (hκ : 0 < κ) (h : CanonicalMomentumOn T κ u p)
    (hR : ∀ x ∈ Ioc 0 T, R x = u x / ((3 * β) * x)) (hs : 0 < s) (hsT : s ≤ T) :
    transportAverage R (physicalTransportWeight (3 * β) κ) s = p s ^ 2 / criticalMomentum β κ s ^ 2 := by
  dsimp [transportAverage]
  rw [canonical_numerator_eq h (mul_ne_zero (by norm_num) (ne_of_gt hβ)) hR hs hsT,
    criticalMomentum_sq_mass hβ hκ hs]
  ring

theorem criticalMomentum_sq_algebraic {β κ s : ℝ} (hβ : 0 < β) (hκ : 0 < κ) (hs : 0 < s) :
    criticalMomentum β κ s ^ 2 = criticalMomentumSquare (v8Volume κ s) (criticalX β s) (3 * β) := by
  rw [criticalMomentum_sq hβ hκ hs]
  exact (critical_radicand_eq_regular β κ s hs).symm

/-- This proves exactly the terminal normalization previously supplied to Hito4. -/
theorem canonical_endpoint_average_normalization {T β κ S : ℝ} {R u p : ℝ → ℝ}
    (hβ : 0 < β) (hκ : 0 < κ) (h : CanonicalMomentumOn T κ u p)
    (hR : ∀ x ∈ Ioc 0 T, R x = u x / ((3 * β) * x)) (hS : 0 < S) (hST : S ≤ T) :
    transportAverage R (physicalTransportWeight (3 * β) κ) S =
      p S ^ 2 / criticalMomentumSquare (v8Volume κ S) (criticalX β S) (3 * β) := by
  rw [canonical_average_eq hβ hκ h hR hS hST, criticalMomentum_sq_algebraic hβ hκ hS]

theorem canonical_relative_continuousOn {T κ A : ℝ} {R u p : ℝ → ℝ}
    (h : CanonicalMomentumOn T κ u p) (hA : A ≠ 0)
    (hR : ∀ x ∈ Ioc 0 T, R x = u x / (A * x)) : ContinuousOn R (Ioo 0 T) := by
  have hc := (h.u_cont.mono Ioo_subset_Icc_self).div
    (continuous_const.mul continuous_id).continuousOn (fun x hx => mul_ne_zero hA (ne_of_gt hx.1))
  exact hc.congr (fun x hx => hR x ⟨hx.1, hx.2.le⟩)

/-- The equality persists in an actual neighborhood of S, not only at its single value. -/
theorem canonical_average_eventuallyEq {T β κ S : ℝ} {R u p : ℝ → ℝ}
    (hβ : 0 < β) (hκ : 0 < κ) (h : CanonicalMomentumOn T κ u p)
    (hR : ∀ x ∈ Ioc 0 T, R x = u x / ((3 * β) * x)) (hS : 0 < S) (hST : S < T) :
    (fun x => p x ^ 2 / criticalMomentum β κ x ^ 2) =ᶠ[𝓝 S]
      transportAverage R (physicalTransportWeight (3 * β) κ) := by
  exact Filter.eventually_of_mem (Ioo_mem_nhds hS hST)
    (fun x hx => (canonical_average_eq hβ hκ h hR hx.1 hx.2.le).symm)

/-- Total canonical relative-momentum derivative and its strict terminal sign.
Only the comparison before S is assumed. The given continuation needs no X>0 after S. -/
theorem canonical_relative_momentum_terminal {T β κ S : ℝ} {R u p : ℝ → ℝ}
    (hβ : 0 < β) (hκ : 0 < κ) (h : CanonicalMomentumOn T κ u p)
    (hR : ∀ x ∈ Ioc 0 T, R x = u x / ((3 * β) * x)) (hS : 0 < S) (hST : S < T)
    (hcomp : WeightedTransportOn S R (physicalTransportWeight (3 * β) κ)) :
    HasDerivAt (fun x => p x ^ 2 / criticalMomentum β κ x ^ 2)
      (2 * deriv (criticalMomentum β κ) S / criticalMomentum β κ S *
        (R S - p S ^ 2 / criticalMomentum β κ S ^ 2)) S ∧
    deriv (fun x => p x ^ 2 / criticalMomentum β κ x ^ 2) S < 0 := by
  have hRc := canonical_relative_continuousOn h (mul_ne_zero (by norm_num) (ne_of_gt hβ)) hR
  have hterm := critical_transport_terminal hβ hκ hS hST hcomp hRc
  have hEq := canonical_average_eventuallyEq hβ hκ h hR hS hST
  have hrel := hterm.1.congr_of_eventuallyEq hEq
  constructor
  · simpa only [canonical_average_eq hβ hκ h hR hS hST.le] using hrel
  · rw [hrel.deriv, ← hterm.1.deriv]
    exact hterm.2

end AffineQuadric
