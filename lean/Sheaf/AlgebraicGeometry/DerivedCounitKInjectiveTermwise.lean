/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF contributors
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStar
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.KInjective

/-!
# Derived counit on a K-injective representative

Source: `literature/stacks-project/derived.tex`, Tags 0DVC and 09T5
(blueprint: lem-asd-derived-counit-k-injective-termwise).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

/--
Source: Stacks Project, `derived.tex`, Tags 0DVC and 09T5, with Tag 070K for the
K-injective computation and Tag 015F for the exact inverse image.

(blueprint: lem-asd-derived-counit-k-injective-termwise).

Let `R` be a commutative ring and `f : X ⟶ Y` a morphism of schemes.  The derived
adjunction between the exact inverse image and the right derived direct image has,
at a K-injective complex `I` on `X`, the ordinary termwise sheaf counit.  The
five displayed factors below are respectively the K-injective comparison, the
canonical quotient comparison for the exact inverse image, the exact-functor
factorization, the ordinary counit on homotopy categories, and the quotient
comparison back to the derived category.  Thus the displayed equality is exactly
the representative assertion in the node, including the canonical comparison
`u⁻¹ Q (u_* I) ≅ Q (u⁻¹ u_* I)`.

Apply Mathlib's `Adjunction.derivedε_fac_app` to the termwise homotopy
adjunction at the quotient of `I`.  This identifies the derived counit after
precomposition with the image of the right-derived-functor unit.  That unit is
invertible because `I` is K-injective.  Expand `rightDerivedFunctorObjQIso` and
the quotient comparisons, and cancel the image of the unit.  The resulting
identity is precisely the displayed five-factor formula.  This calculation uses
the existing exact-functor and K-injective constructions directly; no separate
Hom-bijection calculation or exchange theorem is required.
-/
theorem derivedCounitKInjectiveTermwise
    {X Y : Scheme.{u}} (R : Type (u + 1)) [CommRing R] (f : X ⟶ Y)
    (I : CochainComplex (Sheaf X.smallEtaleTopology (ModuleCat R)) ℤ)
    [I.IsKInjective] :
    (mapDerivedUpperStarLowerStarAdjunction (ModuleCat R) f).counit.app
        (DerivedCategory.Q.obj I) =
      (D((f)^*[ModuleCat R])).map
          ((f)_*[ModuleCat R].rightDerivedFunctorObjQIso I).hom ≫
        D((f)^*[ModuleCat R]).map
          ((DerivedCategory.quotientCompQhIso
              (Sheaf Y.smallEtaleTopology (ModuleCat R))).inv.app
            (((f)_*[ModuleCat R].mapHomologicalComplex (ComplexShape.up ℤ)).obj I)) ≫
        (f)^*[ModuleCat R].mapDerivedCategoryFactorsh.hom.app
          ((HomotopyCategory.quotient
              (Sheaf Y.smallEtaleTopology (ModuleCat R)) (ComplexShape.up ℤ)).obj
            (((f)_*[ModuleCat R].mapHomologicalComplex (ComplexShape.up ℤ)).obj I)) ≫
        DerivedCategory.Qh.map
          ((Adjunction.mapHomotopyCategory (ComplexShape.up ℤ)
              (upperStarLowerStarAdjunction (ModuleCat R) f)).counit.app
            ((HomotopyCategory.quotient
                (Sheaf X.smallEtaleTopology (ModuleCat R)) (ComplexShape.up ℤ)).obj I)) ≫
        (DerivedCategory.quotientCompQhIso
            (Sheaf X.smallEtaleTopology (ModuleCat R))).hom.app I := by
  let L := (f)^*[ModuleCat R]
  let P := (f)_*[ModuleCat R]
  let K := (HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj I
  have h := ((upperStarLowerStarAdjunction (ModuleCat R) f).mapHomotopyCategory
    (ComplexShape.up ℤ)).derivedε_fac_app
      (HomotopyCategory.quasiIso _ (ComplexShape.up ℤ))
      L.mapDerivedCategoryFactorsh.hom P.rightDerivedFunctorUnit K
  change L.mapDerivedCategory.map (P.rightDerivedFunctorUnit.app K) ≫
    (mapDerivedUpperStarLowerStarAdjunction (ModuleCat R) f).counit.app
      (DerivedCategory.Q.obj I) = _ at h
  have hX : ∀ J, (DerivedCategory.quotientCompQhIso
      (Sheaf X.smallEtaleTopology (ModuleCat R))).hom.app J = 𝟙 _ := fun _ ↦ rfl
  have hYh : ∀ J, (DerivedCategory.quotientCompQhIso
      (Sheaf Y.smallEtaleTopology (ModuleCat R))).hom.app J = 𝟙 _ := fun _ ↦ rfl
  dsimp only [Functor.rightDerivedFunctorObjQIso, Iso.trans_hom, Iso.symm_hom,
    Functor.mapIso_hom, asIso_inv, Iso.app]
  erw [hX, hYh, P.rightDerivedFunctor.map_id, Category.id_comp, Category.comp_id,
    L.mapDerivedCategory.map_id, Category.id_comp, Category.comp_id]
  apply (cancel_epi (L.mapDerivedCategory.map (P.rightDerivedFunctorUnit.app K))).1
  rw [← L.mapDerivedCategory.map_comp_assoc, IsIso.hom_inv_id,
    L.mapDerivedCategory.map_id, Category.id_comp]
  exact h

end AlgebraicGeometry.Etale
