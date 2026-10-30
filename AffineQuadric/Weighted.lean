import Mathlib.Tactic

/-! Rational scalar identities intended for PE V8 (draft label: Proposition 6.4).
The article has not been supplied or checked against these statements.
The original weighted expressions are used only where X ≠ 0. Their rational
representatives are evaluated at the collision. No analyticity, tensor extension,
Puiseux expansion or curvature asymptotic is claimed by these scalar lemmas.
-/
namespace AffineQuadric

noncomputable def weightedVertical (V p : ℝ) : ℝ := V ^ 2 / p
noncomputable def weightedHorizontal (u a p : ℝ) : ℝ := p / (u + a)

theorem weighted_vertical_identity (V u a p : ℝ)
    (hp : p ≠ 0) (hX : u ^ 2 - a ^ 2 ≠ 0) :
    (p / (u ^ 2 - a ^ 2)) * (V ^ 2 * (u ^ 2 - a ^ 2) / p ^ 2) =
      weightedVertical V p := by
  dsimp [weightedVertical]
  field_simp

theorem weighted_horizontal_identity (u a p : ℝ)
    (hminus : u - a ≠ 0) (hplus : u + a ≠ 0) :
    (p / ((u - a) * (u + a))) * (u - a) = weightedHorizontal u a p := by
  dsimp [weightedHorizontal]
  field_simp

theorem weighted_horizontal_product (u a p : ℝ) (hplus : u + a ≠ 0) :
    (u + a) * weightedHorizontal u a p = p := by
  dsimp [weightedHorizontal]
  field_simp

theorem weighted_product (V u a p : ℝ) (hp : p ≠ 0) :
    weightedVertical V p * weightedHorizontal u a p = V ^ 2 / (u + a) := by
  dsimp [weightedVertical, weightedHorizontal]
  field_simp

theorem weighted_vertical_pos (V p : ℝ) (hV : V ≠ 0) (hp : 0 < p) :
    0 < weightedVertical V p := by
  exact div_pos (sq_pos_of_ne_zero hV) hp

theorem weighted_horizontal_pos (u a p : ℝ) (hplus : 0 < u + a) (hp : 0 < p) :
    0 < weightedHorizontal u a p := by
  exact div_pos hp hplus

theorem collision_horizontal_value (a p : ℝ) :
    weightedHorizontal a a p = p / (2 * a) := by
  simp [weightedHorizontal, two_mul]

theorem collision_scalar_positivity (V a p : ℝ)
    (hV : V ≠ 0) (ha : 0 < a) (hp : 0 < p) :
    0 < weightedVertical V p ∧ 0 < weightedHorizontal a a p := by
  constructor
  · exact weighted_vertical_pos V p hV hp
  · exact weighted_horizontal_pos a a p (by linarith) hp

theorem length_exponent_identity (m : ℝ) (hm : m + 2 ≠ 0) :
    (m / (m + 2)) * (1 - m / (m + 2)) = 2 * m / (m + 2) ^ 2 := by
  field_simp
  ring

theorem transverse_scalar_coefficient :
    (1 / (3 : ℝ)) * (1 - 1 / 3) = 2 / 9 := by
  norm_num

theorem collision_scalar_example :
    0 < weightedVertical 1 1 ∧ 0 < weightedHorizontal 1 1 1 := by
  norm_num [weightedVertical, weightedHorizontal]

end AffineQuadric
