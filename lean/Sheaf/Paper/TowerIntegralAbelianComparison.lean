/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group H5
-/
module

public import Sheaf.Paper.TowerClassCoefficients
public import Sheaf.Paper.SemilinearOrdinaryInverseSystem
public import Sheaf.Paper.TowerIntegralPullbackData

/-! # Abelian comparison for integral ordinary inverse systems

Source: blueprint classes proof (2), integral reduction.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
namespace AlgebraicGeometry.ProEtale.SpTowerClasses

/-- The underlying abelian tower comparison supplied by an ordinary inverse system.
Source: blueprint latest, classes proof (2), integral reduction, and Zheng Construction 4.1.
(blueprint: lem-sp-tower-integral-abelian-comparison).

Proof: at each coefficient level, the moduleUnderlying comparison of the algebraic
inverse image is composed with the component comparison of the ordinary system and
with the evaluation identifications supplied by the two Forget structures.  The
module graph equations make these maps additive.  Naturality in system morphisms
and the restriction_underlying and transition equations make the level maps
compatible with horizontal arrows, so the component maps assemble to the required
natural isomorphism of abelian towers.
-/
theorem integralInverseSystem_abelian_comparison (l : ℕ) [Fact l.Prime]
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (I : ∀ n : ℕ, SheafOfModules.AlgebraicInverseImage
      (Scheme.proEtaleSheafInverseImage f (Type (u + 1)))
      ((Rrings l Y).obj (Opposite.op n)) ((Rrings l X).obj (Opposite.op n)))
    (P : WeilConjectures.SemilinearSections.OrdinaryInverseSystem.{u + 1, u, u + 1}
      (Scheme.ProEt.topology Y) (fun n ↦ (Rrings l Y).obj (Opposite.op n))
      (fun n ↦ (Rrings l Y).map (homOfLE (Nat.le_succ n)).op)
      (Scheme.ProEt.topology X) (Scheme.proEtaleSheafInverseImage f (Type (u + 1)))
      (fun n ↦ (Rrings l X).obj (Opposite.op n))
      (fun n ↦ (Rrings l X).map (homOfLE (Nat.le_succ n)).op) I)
    (FY : Forget Y (Rrings l Y)) (FX : Forget X (Rrings l X)) :
    Nonempty (FY.F ⋙ abPull f ≅ P.pull ⋙ FX.F) := by
  sorry

end AlgebraicGeometry.ProEtale.SpTowerClasses
