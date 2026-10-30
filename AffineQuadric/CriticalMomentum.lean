import AffineQuadric.TerminalTransport

/-! The critical profile of V8 is linked to a globally regular product.
The raw v8Barrier is used only at positive arguments; its value at zero is not a physical limit. -/
noncomputable section
open Set MeasureTheory
namespace AffineQuadric

def criticalBracket (t : ℝ) : ℝ := t ^ 2 * Real.sinh t ^ 2 - shapeNumerator t ^ 2

def criticalRegularSquare (β κ s : ℝ) : ℝ :=
  (2 * κ ^ 2 * β ^ 2 / (3 * β)) * criticalBracket (3 * s)

def criticalX (β s : ℝ) : ℝ := ((3 * β) * s) ^ 2 - v8Barrier β s ^ 2

/-- A=3beta is fixed here, not an independent constant. -/
def criticalMomentum (β κ s : ℝ) : ℝ := Real.sqrt (criticalRegularSquare β κ s)

theorem criticalBracket_hasDerivAt (t : ℝ) :
    HasDerivAt criticalBracket (4 * t * Real.sinh t ^ 2) t := by
  convert (((hasDerivAt_id t).pow 2).mul ((Real.hasDerivAt_sinh t).pow 2)).sub
    ((shapeNumerator_hasDerivAt t).pow 2) using 1
  dsimp [shapeNumerator]
  ring

theorem criticalBracket_initial : criticalBracket 0 = 0 := by
  norm_num [criticalBracket, shapeNumerator]

theorem criticalBracket_pos {t : ℝ} (ht : 0 < t) : 0 < criticalBracket t := by
  exact positive_from_zero_derivative criticalBracket_initial criticalBracket_hasDerivAt
    (fun x hx => mul_pos (mul_pos (by norm_num) hx) (sq_pos_of_pos (Real.sinh_pos_iff.2 hx))) ht

theorem criticalRegularSquare_hasDerivAt {β : ℝ} (hβ : β ≠ 0) (κ s : ℝ) :
    HasDerivAt (criticalRegularSquare β κ) (8 * physicalTransportWeight (3 * β) κ s) s := by
  convert ((criticalBracket_hasDerivAt (3 * s)).comp s ((hasDerivAt_id s).const_mul 3)).const_mul
    (2 * κ ^ 2 * β ^ 2 / (3 * β)) using 1
  dsimp [physicalTransportWeight, v8Volume]
  field_simp
  ring

theorem criticalRegularSquare_initial (β κ : ℝ) : criticalRegularSquare β κ 0 = 0 := by
  simp [criticalRegularSquare, criticalBracket_initial]

theorem criticalRegularSquare_pos {β κ s : ℝ} (hβ : 0 < β) (hκ : 0 < κ) (hs : 0 < s) :
    0 < criticalRegularSquare β κ s := by
  exact mul_pos (div_pos
    (mul_pos (mul_pos (by norm_num) (sq_pos_of_pos hκ)) (sq_pos_of_pos hβ))
    (mul_pos (by norm_num) hβ)) (criticalBracket_pos (by linarith))

theorem criticalRegularSquare_eq_mass {β : ℝ} (hβ : β ≠ 0) (κ s : ℝ) :
    criticalRegularSquare β κ s = 8 * transportMass (physicalTransportWeight (3 * β) κ) s := by
  have hw : IntervalIntegrable (physicalTransportWeight (3 * β) κ) volume 0 s :=
    (physicalTransportWeight_continuous (3 * β) κ).intervalIntegrable 0 s
  have hh := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun x _ => criticalRegularSquare_hasDerivAt hβ κ x) (hw.const_mul 8)
  rw [intervalIntegral.integral_const_mul, criticalRegularSquare_initial, sub_zero] at hh
  exact hh.symm

theorem critical_product_identity (β s : ℝ) (hs : 0 < s) :
    Real.sinh (3 * s) ^ 2 * criticalX β s = β ^ 2 * criticalBracket (3 * s) := by
  have hn : Real.sinh (3 * s) ≠ 0 := ne_of_gt (Real.sinh_pos_iff.2 (by linarith))
  dsimp [criticalX, v8Barrier, criticalBracket, shapeNumerator]
  field_simp

theorem criticalX_pos {β s : ℝ} (hβ : 0 < β) (hs : 0 < s) : 0 < criticalX β s := by
  have hh : 0 < Real.sinh (3 * s) ^ 2 * criticalX β s := by
    rw [critical_product_identity β s hs]
    exact mul_pos (sq_pos_of_pos hβ) (criticalBracket_pos (by linarith))
  by_contra hnot
  have hn := mul_nonpos_of_nonneg_of_nonpos (sq_nonneg (Real.sinh (3 * s))) (le_of_not_gt hnot)
  linarith

theorem critical_radicand_eq_regular (β κ s : ℝ) (hs : 0 < s) :
    2 * v8Volume κ s ^ 2 * criticalX β s / (3 * β) = criticalRegularSquare β κ s := by
  calc
    _ = (2 * κ ^ 2 / (3 * β)) * (Real.sinh (3 * s) ^ 2 * criticalX β s) := by
      dsimp [v8Volume]
      ring
    _ = (2 * κ ^ 2 / (3 * β)) * (β ^ 2 * criticalBracket (3 * s)) := by
      rw [critical_product_identity β s hs]
    _ = criticalRegularSquare β κ s := by dsimp [criticalRegularSquare]; ring

theorem criticalMomentum_formula (β κ s : ℝ) (hs : 0 < s) :
    criticalMomentum β κ s = Real.sqrt (2 * v8Volume κ s ^ 2 *
      (((3 * β) * s) ^ 2 - v8Barrier β s ^ 2) / (3 * β)) := by
  change Real.sqrt (criticalRegularSquare β κ s) = Real.sqrt (2 * v8Volume κ s ^ 2 * criticalX β s / (3 * β))
  rw [critical_radicand_eq_regular β κ s hs]

theorem criticalMomentum_pos {β κ s : ℝ} (hβ : 0 < β) (hκ : 0 < κ) (hs : 0 < s) :
    0 < criticalMomentum β κ s := by
  exact Real.sqrt_pos.2 (criticalRegularSquare_pos hβ hκ hs)

theorem criticalMomentum_sq {β κ s : ℝ} (hβ : 0 < β) (hκ : 0 < κ) (hs : 0 < s) :
    criticalMomentum β κ s ^ 2 = criticalRegularSquare β κ s := by
  exact Real.sq_sqrt (criticalRegularSquare_pos hβ hκ hs).le

theorem criticalMomentum_sq_mass {β κ s : ℝ} (hβ : 0 < β) (hκ : 0 < κ) (hs : 0 < s) :
    criticalMomentum β κ s ^ 2 = 8 * transportMass (physicalTransportWeight (3 * β) κ) s := by
  rw [criticalMomentum_sq hβ hκ hs, criticalRegularSquare_eq_mass (ne_of_gt hβ)]

theorem criticalMass_pos {β κ s : ℝ} (hβ : 0 < β) (hκ : 0 < κ) (hs : 0 < s) :
    0 < transportMass (physicalTransportWeight (3 * β) κ) s := by
  have hh := criticalRegularSquare_pos hβ hκ hs
  rw [criticalRegularSquare_eq_mass (ne_of_gt hβ)] at hh
  linarith

theorem criticalMomentum_hasDerivAt {β κ s : ℝ} (hβ : 0 < β) (hκ : 0 < κ) (hs : 0 < s) :
    HasDerivAt (criticalMomentum β κ)
      (8 * physicalTransportWeight (3 * β) κ s / (2 * criticalMomentum β κ s)) s := by
  exact (criticalRegularSquare_hasDerivAt (ne_of_gt hβ) κ s).sqrt
    (ne_of_gt (criticalRegularSquare_pos hβ hκ hs))

theorem criticalMomentumSquare_hasDerivAt {β κ s : ℝ} (hβ : 0 < β) (hκ : 0 < κ) (hs : 0 < s) :
    HasDerivAt (fun x => criticalMomentum β κ x ^ 2) (8 * physicalTransportWeight (3 * β) κ s) s := by
  have hn := ne_of_gt (criticalMomentum_pos hβ hκ hs)
  convert (criticalMomentum_hasDerivAt hβ hκ hs).pow 2 using 1
  field_simp
  norm_num

theorem critical_transport_coefficient {β κ s : ℝ} (hβ : 0 < β) (hκ : 0 < κ) (hs : 0 < s) :
    physicalTransportWeight (3 * β) κ s / transportMass (physicalTransportWeight (3 * β) κ) s =
      2 * deriv (criticalMomentum β κ) s / criticalMomentum β κ s := by
  have hsq := criticalMomentum_sq_mass hβ hκ hs
  calc
    _ = 8 * physicalTransportWeight (3 * β) κ s /
        (8 * transportMass (physicalTransportWeight (3 * β) κ) s) := by ring
    _ = 8 * physicalTransportWeight (3 * β) κ s / criticalMomentum β κ s ^ 2 := by rw [hsq]
    _ = _ := by rw [(criticalMomentum_hasDerivAt hβ hκ hs).deriv]; ring

theorem critical_transport_interior {S β κ s : ℝ} {R : ℝ → ℝ}
    (hβ : 0 < β) (hκ : 0 < κ) (h : WeightedTransportOn S R (physicalTransportWeight (3 * β) κ))
    (hs : s ∈ Ioo 0 S) :
    HasDerivAt (transportAverage R (physicalTransportWeight (3 * β) κ))
      (2 * deriv (criticalMomentum β κ) s / criticalMomentum β κ s *
        (R s - transportAverage R (physicalTransportWeight (3 * β) κ) s)) s := by
  have hh := transportAverage_hasDerivAt h hs
  rw [critical_transport_coefficient hβ hκ hs.1] at hh
  exact hh

theorem critical_transport_terminal {S T β κ : ℝ} {R : ℝ → ℝ}
    (hβ : 0 < β) (hκ : 0 < κ) (hS : 0 < S) (hST : S < T)
    (h : WeightedTransportOn S R (physicalTransportWeight (3 * β) κ))
    (hRc : ContinuousOn R (Ioo 0 T)) :
    HasDerivAt (transportAverage R (physicalTransportWeight (3 * β) κ))
      (2 * deriv (criticalMomentum β κ) S / criticalMomentum β κ S *
        (R S - transportAverage R (physicalTransportWeight (3 * β) κ) S)) S ∧
    deriv (transportAverage R (physicalTransportWeight (3 * β) κ)) S < 0 := by
  have hh := physical_average_terminal_hasDerivAt h hS hST hRc
  rw [critical_transport_coefficient hβ hκ hS] at hh
  exact ⟨hh, transportAverage_terminal_deriv_neg h hS hST hRc
    (physicalTransportWeight_continuous (3 * β) κ).continuousOn⟩

end AffineQuadric
