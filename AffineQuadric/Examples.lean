import AffineQuadric.Pairing

/-! A nonzero conserved pairing for a given solution of the GENERAL background system.
This background V(s)=s, a(s)=0 is not the hyperbolic V8 background.
-/
noncomputable section
namespace AffineQuadric

theorem example_radial_solution :
    RadialSolutionOn (Set.Ioi 0) (fun _ => 0) (fun _ => 0) id (fun _ => 1) id (fun _ => 1) := by
  refine ⟨fun s hs => hs, ?_, fun _ _ => by norm_num,
    fun s _ => hasDerivAt_const s 0, fun s _ => hasDerivAt_id s,
    fun s _ => hasDerivAt_id s, ?_⟩
  · intro s hs
    simpa using sq_pos_of_pos hs
  · intro s hs
    convert hasDerivAt_const s (1 : ℝ) using 1
    dsimp [radialF]
    have hn : s ≠ 0 := ne_of_gt hs
    field_simp
    ring

theorem example_variation_one :
    RadialVariationOn (Set.Ioi 0) (fun _ => 0) (fun _ => 0) id (fun _ => 1) id (fun _ => 1)
      id (fun _ => 1) := by
  refine ⟨fun s _ => hasDerivAt_id s, ?_⟩
  intro s hs
  convert hasDerivAt_const s (1 : ℝ) using 1
  dsimp [radialFx, radialFy]
  have hn : s ≠ 0 := ne_of_gt hs
  field_simp
  ring

theorem example_variation_two :
    RadialVariationOn (Set.Ioi 0) (fun _ => 0) (fun _ => 0) id (fun _ => 1) id (fun _ => 1)
      (fun s => 1 / s ^ 2) (fun s => -2 / s ^ 3) := by
  constructor
  · intro s hs
    have hn : s ≠ 0 := ne_of_gt hs
    convert ((hasDerivAt_id s).pow 2).inv (pow_ne_zero 2 hn) using 1
    · funext t
      simp
    · dsimp
      field_simp
  · intro s hs
    have hn : s ≠ 0 := ne_of_gt hs
    convert (((hasDerivAt_id s).pow 3).inv (pow_ne_zero 3 hn)).const_mul (-2) using 1
    dsimp [radialFx, radialFy]
    field_simp
    ring

theorem example_pairing_value {s : ℝ} (hs : 0 < s) :
    radialPairing (fun _ => 0) id id (fun _ => 1) id (fun _ => 1)
      (fun t => 1 / t ^ 2) (fun t => -2 / t ^ 3) s = 3 * Real.sqrt 2 / 2 := by
  have hn : s ≠ 0 := ne_of_gt hs
  have hrad : Real.sqrt (2 * s ^ 2 * (s ^ 2 - 0 ^ 2) / 1) = Real.sqrt 2 * s ^ 2 := by
    rw [show 2 * s ^ 2 * (s ^ 2 - 0 ^ 2) / 1 = 2 * (s ^ 2) ^ 2 by ring]
    rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_sq (sq_nonneg s)]
  dsimp [radialPairing, radialWeight, variationDet, radialMomentum]
  rw [hrad]
  field_simp
  ring

end AffineQuadric
