/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.FiniteEtaleTateTwist
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.TensorColimits

/-!
# Signed finite Tate sheaves

The nonnegative twists are `finiteEtaleTateTwist`. Negative integers are handled by the
internal sheaf Hom.

## References

* Stacks Project, Tag 03PK; Modules on Sites, Tag 04TT.
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory
open scoped ChangeOfRings

namespace AlgebraicGeometry.Scheme

/-- Extend the nonnegative finite Tate twists to all integers by sheaf duality.
(Stacks, Tags 03PK and 04TT.) -/
noncomputable def finiteEtaleTateSheaf (A : Type (u + 1)) [CommRing A] (m : ℕ)
    (T : Scheme.{u}) (hA : (m : A) = 0) :
    ℤ → Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)
  | .ofNat n => finiteEtaleTateTwist T m A hA n
  | .negSucc n =>
      (ihom (finiteEtaleTateTwist T m A hA (n + 1))).obj
        (finiteEtaleTateTwist T m A hA 0)

/-- The local pure tensor in the coefficient root line. The module structure on roots of
unity has the same underlying group, so its section `z` requires no choice.
(Stacks, Tags 03PK and 03EK.) -/
noncomputable def finiteEtaleTateOneGenerator (A : Type (u + 1)) [CommRing A] (m : ℕ)
    (T : Scheme.{u}) (hA : (m : A) = 0) (W : T.Etaleᵒᵖ) (a : A)
    (z : (T.rootsOfUnitySheaf m).obj.obj W) :
    (finiteEtaleTateSheaf A m T hA 1).obj.obj W :=
  (toSheafify T.smallEtaleTopology
    (finiteEtaleMuModulePresheaf T m ⋙
      ModuleCat.extendScalars (finiteEtaleTwistScalar m A hA))).app W
        (a ⊗ₜ[ZMod m, finiteEtaleTwistScalar m A hA] z)

end AlgebraicGeometry.Scheme
