import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Tactic

/-! Scalar Hamiltonian identities intended for PE V8 (draft label: Proposition 3.1).
The article has not been supplied or checked against these statements.
Time is fixed in the partial derivatives. The momentum balance is conditional
on the explicitly stated canonical differential equation at a point.
This file does not assert existence of any solution or the coordinate dictionary.
-/
namespace AffineQuadric

noncomputable def hamiltonian (V a q p : ℝ) : ℝ := -2 * V ^ 2 * (q ^ 2 - a ^ 2) / p
noncomputable def qdot (V a q p : ℝ) : ℝ := 2 * V ^ 2 * (q ^ 2 - a ^ 2) / p ^ 2
noncomputable def pdot (V q p : ℝ) : ℝ := 4 * V ^ 2 * q / p

theorem hamiltonian_partial_p (V a q p : ℝ) (hp : p ≠ 0) :
    HasDerivAt (fun r => hamiltonian V a q r) (qdot V a q p) p := by
  convert ((hasDerivAt_id p).inv hp).const_mul
    (-2 * V ^ 2 * (q ^ 2 - a ^ 2)) using 1
  simp [qdot, div_eq_mul_inv]

theorem hamiltonian_partial_q (V a q p : ℝ) :
    HasDerivAt (fun r => hamiltonian V a r p) (-pdot V q p) q := by
  have hfun : (fun r => hamiltonian V a r p) =
      (fun r => (-2 * V ^ 2 / p) * (r ^ 2 - a ^ 2)) := by
    funext r
    dsimp [hamiltonian]
    ring
  rw [hfun]
  convert (((hasDerivAt_id q).pow 2).sub_const (a ^ 2)).const_mul
    (-2 * V ^ 2 / p) using 1
  dsimp [pdot]
  ring

theorem momentum_square_balance {P : ℝ → ℝ} {s V u : ℝ}
    (hp : P s ≠ 0) (hP : HasDerivAt P (pdot V u (P s)) s) :
    HasDerivAt (fun t => P t ^ 2) (8 * u * V ^ 2) s := by
  convert hP.pow 2 using 1
  dsimp [pdot]
  field_simp
  ring

end AffineQuadric
