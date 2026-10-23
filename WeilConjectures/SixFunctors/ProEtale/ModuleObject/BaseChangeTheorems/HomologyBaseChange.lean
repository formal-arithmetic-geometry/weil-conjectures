/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.HomologyExchange
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.PullbackSquareComparison

/-!
# The base-change morphism on homology for exact pushforwards

Let `g' ≫ f = f' ≫ g` be a commutative square of schemes such that the pushforwards `f_*` and
`f'_*` of module objects over `Λ` are exact (for instance `f` and `f'` finite), and such that the
base-change morphism `β_* : f_* ⋙ g^* ⟶ g'^* ⋙ f'_*` of module objects (the exchange morphism of
the composition isomorphisms of the pullbacks) is an isomorphism (for instance `g` and `g'`
isomorphisms). Then on the homology sheaves, the derived base-change morphism
`BC : Rf_* ⋙ Lg^* ⟶ Lg'^* ⋙ Rf'_*` is the base-change morphism of module objects: through the
commutations `Hⁿ(Rf_* K) ≅ f_* Hⁿ(K)` and `Hⁿ(Lg^* K) ≅ g^* Hⁿ(K)` of the exact functors with
homology, `Hⁿ(BC_K)` is `β_*` at `Hⁿ(K)`
(`ProEtale.CondensedRing.homologyFunctor_map_boundedConstructibleBaseChange`).

The proof transports the question along the identifications `Lg^* ≅ D(g^*)` and
`Rf_* ≅ D(f_*)` of the total derived functors of exact functors with the levelwise functors
(`CategoryTheory.Adjunction.homologyFunctor_map_exchangeRight_derivedAdjunction`); the
composition isomorphisms of the derived pullbacks are the levelwise ones
(`ProEtale.CondensedRing.leftDerivedUpperStarComp_hom_app_eq`).

-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]

section Scheme

variable {X Y Z : Scheme.{u}}

/-- The composition isomorphism `L(a ≫ b)^* ≅ Lb^* ⋙ La^*` of the derived pullbacks is, through
the identifications of the derived pullbacks with the levelwise pullbacks, the isomorphism
`D((a ≫ b)^*) ≅ D(b^*) ⋙ D(a^*)` induced by the composition isomorphism of the pullbacks. -/
lemma leftDerivedUpperStarComp_hom_app_eq (a : X ⟶ Y) (b : Y ⟶ Z)
    (K : DerivedCategory (Mod (Sheaf (ProEt.topology Z) Ab.{u + 1}) (condensedRingObj Λ Z))) :
    (leftDerivedUpperStarComp Λ a b).hom.app K =
      (leftDerivedUpperStarIsoMapDerivedCategory Λ (a ≫ b)).hom.app K ≫
        (Functor.mapDerivedCategoryTriangleIso (upperStarComp Λ a b)).hom.app K ≫
        (a)^*⟦Λ⟧.mapDerivedCategory.map
          ((leftDerivedUpperStarIsoMapDerivedCategory Λ b).inv.app K) ≫
        (leftDerivedUpperStarIsoMapDerivedCategory Λ a).inv.app
          ((b)^*⟦Λ⟧.leftDerivedFunctor.obj K) := by
  simp [leftDerivedUpperStarComp, Functor.leftDerivedFunctorNatIso,
    Functor.leftDerivedFunctorCompIso, leftDerivedUpperStarIsoMapDerivedCategory]

/-- Along an equality `a = b` of morphisms of schemes, the transport of the derived pullbacks is,
through the identifications with the levelwise pullbacks, the isomorphism induced by the
transport of the pullbacks. -/
lemma leftDerivedUpperStarIsoMapDerivedCategory_inv_app_comp_eqToHom {a b : X ⟶ Y} (h : a = b)
    (K : DerivedCategory (Mod (Sheaf (ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y))) :
    (leftDerivedUpperStarIsoMapDerivedCategory Λ a).inv.app K ≫
        eqToHom (by rw [h]) ≫ (leftDerivedUpperStarIsoMapDerivedCategory Λ b).hom.app K =
      (Functor.mapDerivedCategoryNatIso (eqToIso (congrArg (upperStar Λ) h))).hom.app K := by
  subst h
  simp [Functor.mapDerivedCategoryNatIso_refl]
variable {X' Y' : Scheme.{u}} {f : X ⟶ Y} {g : Y' ⟶ Y} {f' : X' ⟶ Y'} {g' : X' ⟶ X}

/-- The comparison `Lg^* ⋙ Lf'^* ≅ Lf^* ⋙ Lg'^*` of the derived pullbacks along a commutative
square `g' ≫ f = f' ≫ g`, built from the composition isomorphisms
`ProEtale.CondensedRing.leftDerivedUpperStarComp`, is the comparison of the pullbacks of module
objects through the identifications of the derived pullbacks with the levelwise pullbacks. -/
lemma leftDerivedUpperStarSquare_hom_app_eq (hw : g' ≫ f = f' ≫ g)
    (K : DerivedCategory (Mod (Sheaf (ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y))) :
    (f')^*⟦Λ⟧.mapDerivedCategory.map ((leftDerivedUpperStarIsoMapDerivedCategory Λ g).inv.app K) ≫
        (leftDerivedUpperStarIsoMapDerivedCategory Λ f').inv.app
          ((g)^*⟦Λ⟧.leftDerivedFunctor.obj K) ≫
        ((leftDerivedUpperStarComp Λ f' g).symm ≪≫ eqToIso (by rw [hw]) ≪≫
          leftDerivedUpperStarComp Λ g' f).hom.app K =
      (Functor.mapDerivedCategorySquareIso ((upperStarComp Λ f' g).symm ≪≫
          eqToIso (by rw [hw]) ≪≫ upperStarComp Λ g' f)).hom.app K ≫
        (g')^*⟦Λ⟧.mapDerivedCategory.map ((leftDerivedUpperStarIsoMapDerivedCategory Λ f).inv.app K) ≫
        (leftDerivedUpperStarIsoMapDerivedCategory Λ g').inv.app
          ((f)^*⟦Λ⟧.leftDerivedFunctor.obj K) := by
  have h₁ : (f')^*⟦Λ⟧.mapDerivedCategory.map ((leftDerivedUpperStarIsoMapDerivedCategory Λ g).inv.app K) ≫
      (leftDerivedUpperStarIsoMapDerivedCategory Λ f').inv.app
        ((g)^*⟦Λ⟧.leftDerivedFunctor.obj K) ≫ (leftDerivedUpperStarComp Λ f' g).inv.app K =
      (Functor.mapDerivedCategoryTriangleIso (upperStarComp Λ f' g)).inv.app K ≫
        (leftDerivedUpperStarIsoMapDerivedCategory Λ (f' ≫ g)).inv.app K := by
    rw [← cancel_mono ((leftDerivedUpperStarComp Λ f' g).hom.app K),
      leftDerivedUpperStarComp_hom_app_eq]
    simp
  have h₂ := leftDerivedUpperStarIsoMapDerivedCategory_inv_app_comp_eqToHom Λ hw.symm K
  rw [Iso.trans_hom, Iso.trans_hom, NatTrans.comp_app, NatTrans.comp_app, Iso.symm_hom,
    reassoc_of% h₁, eqToIso.hom, eqToHom_app, leftDerivedUpperStarComp_hom_app_eq,
    reassoc_of% h₂]
  simp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, Category.assoc,
    Functor.mapDerivedCategoryNatIso_trans, Functor.mapDerivedCategoryNatIso_symm]
  rfl

end Scheme

end AlgebraicGeometry.ProEtale.CondensedRing
