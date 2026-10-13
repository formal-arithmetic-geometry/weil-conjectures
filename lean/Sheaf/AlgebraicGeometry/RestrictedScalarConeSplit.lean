/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q1
-/
module

public import Sheaf.AlgebraicGeometry.DerivedGlobalScalar

/-! # A scalar cone splits after restriction

Source: Stacks Project, Tags 08EK, 05QR, 05QS, and 05QT
(blueprint: lem-sc-restricted-scalar-cone-split).
-/

@[expose] public section

universe u w

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
  TopologicalSpace Opposite

namespace AlgebraicGeometry.Scheme

attribute [local instance] Functor.additive_of_preserves_binary_products
  comp_preservesFiniteLimits comp_preservesFiniteColimits

/-- If a scalar kills F, a cone of that scalar on an object whose restriction is a
finite sum of shifts of F restricts to the sum of its input and its shifted input.
Source: Stacks Project, Tag 08EK, cone construction, and Tags 05QR, 05QS, 05QT
(blueprint: lem-sc-restricted-scalar-cone-split).

Proof: The restriction functor is exact and its derived functor is triangulated.
Sectionwise multiplication commutes with restriction and the over-site equivalence.
The equality of top sections identifies the restricted scalar with g'; compatibility
of each family then gives equality on every smaller open. Derived scalar
multiplication is natural, commutes with shifts, and acts componentwise on finite
biproducts. Transporting along the given decomposition therefore makes the scalar
on the restricted input zero. The restricted triangle is a cone triangle of zero.
Rotate the restricted triangle once. Its objects are input, cone, input[1],
and its last map is minus the shift of the zero scalar map, hence zero. Apply
Tag 05QT (Mathlib's `exists_iso_binaryBiproduct_of_distTriang`) and invert the
resulting isomorphism to identify the cone with input plus input[1]. This includes
an empty family, where the input and its cone are zero. -/
theorem restricted_scalar_cone_split (X : Scheme.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    (U : X.Opens)
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace))]
    (g : RingCat.sectionsSubring (X.sheaf.obj ⋙ forget₂ CommRingCat RingCat.{u}))
    (g' : RingCat.sectionsSubring
      (U.toScheme.sheaf.obj ⋙ forget₂ CommRingCat RingCat.{u}))
    (hg : g'.val (op ⊤) = U.ι.appTop.hom (g.val (op ⊤)))
    (E K : schemeDerivedCategory X) (b : E ⟶ K) (d : K ⟶ E⟦(1 : ℤ)⟧)
    (hcone : Triangle.mk (schemeDerivedScalar X g (𝟙 E)) b d ∈
      distTriang (schemeDerivedCategory X))
    (F : schemeDerivedCategory U.toScheme)
    (hzero : schemeDerivedScalar U.toScheme g' (𝟙 F) = 0)
    (J : Type) [Finite J] (a : J → ℤ)
    (hE : Nonempty (((SheafOfModules.overFunctor.{u} (moduleRings X.toRingedSpace) U) ⋙
          Equivalence.functor
            (C := SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))
            (D := SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace))
            (Modules.overEquiv U)).mapDerivedCategory.obj E ≅ biproduct (fun j : J ↦ F⟦a j⟧))) :
    Nonempty (((SheafOfModules.overFunctor.{u} (moduleRings X.toRingedSpace) U) ⋙
          Equivalence.functor
            (C := SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))
            (D := SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace))
            (Modules.overEquiv U)).mapDerivedCategory.obj K ≅
      ((SheafOfModules.overFunctor.{u} (moduleRings X.toRingedSpace) U) ⋙
          Equivalence.functor
            (C := SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))
            (D := SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace))
            (Modules.overEquiv U)).mapDerivedCategory.obj E ⊞
        (((SheafOfModules.overFunctor.{u} (moduleRings X.toRingedSpace) U) ⋙
          Equivalence.functor
            (C := SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))
            (D := SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace))
            (Modules.overEquiv U)).mapDerivedCategory.obj E)⟦(1 : ℤ)⟧) := by
  sorry

end AlgebraicGeometry.Scheme
