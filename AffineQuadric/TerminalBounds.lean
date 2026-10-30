import AffineQuadric.Canonical

/-! Algebraic terminal consequences and the total radial Hamiltonian derivative.
The inequality on Q is an auxiliary input here; the combined result obtains it from the average.
-/
noncomputable section
namespace AffineQuadric

def criticalMomentumSquare (V X A : ℝ) : ℝ := 2 * V ^ 2 * X / A
def terminalAcceleration (V a a₁ p : ℝ) : ℝ := 2 * V ^ 2 * a * a₁ / p ^ 2

theorem criticalMomentumSquare_pos {V X A : ℝ} (hV : 0 < V) (hX : 0 < X) (hA : 0 < A) :
    0 < criticalMomentumSquare V X A := by
  exact div_pos (mul_pos (mul_pos (by norm_num) (sq_pos_of_pos hV)) hX) hA

theorem terminal_momentum_bound {V X A p C : ℝ}
    (hV : 0 < V) (hX : 0 < X) (hA : 0 < A) (hp : 0 < p)
    (hQ : p ^ 2 / criticalMomentumSquare V X A < 1 / C) :
    0 < p ^ 2 ∧ p ^ 2 < 2 * V ^ 2 * X / (C * A) := by
  have hcrit := criticalMomentumSquare_pos hV hX hA
  have hh := (div_lt_iff₀ hcrit).mp hQ
  constructor
  · exact sq_pos_of_pos hp
  · calc
      p ^ 2 < (1 / C) * criticalMomentumSquare V X A := hh
      _ = 2 * V ^ 2 * X / (C * A) := by dsimp [criticalMomentumSquare]; ring

theorem terminal_acceleration_bound {V X A a a₁ p C : ℝ}
    (hV : 0 < V) (hX : 0 < X) (hA : 0 < A) (ha : 0 < a) (ha₁ : 0 < a₁)
    (hp : 0 < p) (hC : 0 < C)
    (hQ : p ^ 2 / criticalMomentumSquare V X A < 1 / C) :
    0 < C * A * a * a₁ / X ∧ C * A * a * a₁ / X < terminalAcceleration V a a₁ p := by
  have hm := (terminal_momentum_bound hV hX hA hp hQ).2
  have hcross := (lt_div_iff₀ (mul_pos hC hA)).mp hm
  have hratio : C * A / X < 2 * V ^ 2 / p ^ 2 :=
    (div_lt_div_iff₀ hX (sq_pos_of_pos hp)).2 (by nlinarith)
  constructor
  · exact div_pos (mul_pos (mul_pos (mul_pos hC hA) ha) ha₁) hX
  · calc
      C * A * a * a₁ / X = (C * A / X) * (a * a₁) := by ring
      _ < (2 * V ^ 2 / p ^ 2) * (a * a₁) := mul_lt_mul_of_pos_right hratio (mul_pos ha ha₁)
      _ = terminalAcceleration V a a₁ p := by dsimp [terminalAcceleration]; ring

def trajectoryHamiltonian (V a u p : ℝ → ℝ) (s : ℝ) : ℝ := hamiltonian (V s) (a s) (u s) (p s)

theorem canonical_collision_velocity {V a u p : ℝ → ℝ} {S : ℝ}
    (hc : u S = a S)
    (hu : HasDerivAt u (qdot (V S) (a S) (u S) (p S)) S) : HasDerivAt u 0 S := by
  simpa [qdot, hc] using hu

theorem trajectoryHamiltonian_collision_value {V a u p : ℝ → ℝ} {S : ℝ}
    (hc : u S = a S) : trajectoryHamiltonian V a u p S = 0 := by
  simp [trajectoryHamiltonian, hamiltonian, hc]

theorem trajectoryHamiltonian_collision_hasDerivAt {V a u p : ℝ → ℝ} {S V₁ a₁ p₁ : ℝ}
    (hc : u S = a S) (hp : p S ≠ 0)
    (hV : HasDerivAt V V₁ S) (ha : HasDerivAt a a₁ S) (hpd : HasDerivAt p p₁ S)
    (hu : HasDerivAt u (qdot (V S) (a S) (u S) (p S)) S) :
    HasDerivAt (trajectoryHamiltonian V a u p) (4 * V S ^ 2 * a S * a₁ / p S) S := by
  have hu0 := canonical_collision_velocity hc hu
  convert (((hV.pow 2).const_mul (-2)).mul ((hu0.pow 2).sub (ha.pow 2))).div hpd hp using 1
  dsimp
  rw [hc]
  field_simp
  ring

theorem trajectoryHamiltonian_collision_deriv_pos {V a u p : ℝ → ℝ} {S V₁ a₁ p₁ : ℝ}
    (hc : u S = a S) (hp : 0 < p S) (hVs : 0 < V S) (has : 0 < a S) (ha₁ : 0 < a₁)
    (hV : HasDerivAt V V₁ S) (ha : HasDerivAt a a₁ S) (hpd : HasDerivAt p p₁ S)
    (hu : HasDerivAt u (qdot (V S) (a S) (u S) (p S)) S) :
    deriv (trajectoryHamiltonian V a u p) S > 0 := by
  rw [(trajectoryHamiltonian_collision_hasDerivAt hc (ne_of_gt hp) hV ha hpd hu).deriv]
  exact div_pos (mul_pos (mul_pos (mul_pos (by norm_num) (sq_pos_of_pos hVs)) has) ha₁) hp

end AffineQuadric
