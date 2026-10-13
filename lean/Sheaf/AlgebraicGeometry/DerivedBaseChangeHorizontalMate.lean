/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.RelativeMVMaps

@[expose] public section
universe u w
open CategoryTheory CategoryTheory.Limits
set_option autoImplicit false
set_option synthInstance.maxSize 2048
namespace AlgebraicGeometry

variable [∀ Z : Scheme.{u},
  HasDerivedCategory.{w} (SheafOfModules (moduleRings Z.toRingedSpace))]

/-- The mate calculation before the final relative composition comparison.
Source: Stacks Project, Cohomology, Tags 08HY and 0D5S.
(blueprint: new-lem-pc-derived-base-change-horizontal-mate).
The proof expands each base-change map as the transpose of the corresponding
counit, uses naturality and the triangle identity, and then applies associativity
of the pinned pullback comparison. This is the intermediate mate identity used
by `schemeDerivedBaseChange_horizontal`; it is stated before postcomposition by
the canonical direct-image composition isomorphism. -/
theorem schemeDerivedBaseChange_horizontal_mate
    {A X S A' X' S' : Scheme.{u}}
    (j : A ⟶ X) (f : X ⟶ S) (j' : A' ⟶ X') (f' : X' ⟶ S')
    (g : S' ⟶ S) (g' : X' ⟶ X) (v : A' ⟶ A)
    (h : g' ≫ f = f' ≫ g) (hj : v ≫ j = j' ≫ g')
    (E : schemeDerivedCategory A) :
    schemeDerivedBaseChangeMap f f' g g' h ((schemeDerivedDirectImage j).obj E) ≫
        (schemeDerivedDirectImage f').map
          (schemeDerivedBaseChangeMap j j' g' v hj E) =
      (derivedPullback g).map ((relativeMVImageComp j f).hom.app E) ≫
        schemeDerivedBaseChangeMap (j ≫ f) (j' ≫ f') g v
          (by rw [← Category.assoc, hj, Category.assoc, h, ← Category.assoc]) E ≫
        (relativeMVImageComp j' f').inv.app ((derivedPullback v).obj E) := by sorry

end AlgebraicGeometry
