/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Pur.PurEtaleScalarMateProjection
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import WeilConjectures.Algebra.Homology.SixFunctors.OrdinaryDerivedChangeOfRings
public import WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact
public import WeilConjectures.SixFunctors.Etale.Derived.LowerStarProjection
public import Mathlib.CategoryTheory.Adjunction.Basic

/-!
# Adjunct normal form of iterated scalar mates

Source: Stacks Project, sites-cohomology.tex, Tag 0E46,
remark-compose-base-change, coefficient-change specialization of the omitted verification
(blueprint: lem-pur-scalar-iterated-mates-adjunct).

The exact constant-ring inverse image is represented by its canonical total left derived
functor, as in the existing scalar/pullback comparison and scalar mate. The canonical
`leftDerivedUpperStarIsoMapDerivedCategory` identifies it with termwise inverse image.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

/-- The composite-adjunction adjunct of an arbitrary arrow with the iterated scalar-mate
endpoints: apply both pullbacks, then the s-counit, then the r-counit.
Source: Stacks Project, Tag 0E46, remark-compose-base-change, and Categories Tag 0037;
the composite counit is `CategoryTheory.Adjunction.comp_counit_app`
(blueprint: lem-pur-scalar-iterated-mates-adjunct). -/
def scalarIteratedAdjunct
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) {X Y Z : Scheme.{u}} (r : X ⟶ Y) (s : Y ⟶ Z)
    (M : DerivedCategoryModule A X)
    (h : (scalarExtension φ Z).obj
        (R(lowerStar (ModuleCat.{u + 1} A) s).obj
          (R(lowerStar (ModuleCat.{u + 1} A) r).obj M)) ⟶
      R(lowerStar (ModuleCat.{u + 1} B) s).obj
        (R(lowerStar (ModuleCat.{u + 1} B) r).obj ((scalarExtension φ X).obj M))) :
    L(upperStar (ModuleCat.{u + 1} B) r).obj
        (L(upperStar (ModuleCat.{u + 1} B) s).obj
          ((scalarExtension φ Z).obj
            (R(lowerStar (ModuleCat.{u + 1} A) s).obj
              (R(lowerStar (ModuleCat.{u + 1} A) r).obj M)))) ⟶
      (scalarExtension φ X).obj M :=
  L(upperStar (ModuleCat.{u + 1} B) r).map
      (L(upperStar (ModuleCat.{u + 1} B) s).map h) ≫
    L(upperStar (ModuleCat.{u + 1} B) r).map
      ((derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} B) s).counit.app
        (R(lowerStar (ModuleCat.{u + 1} B) r).obj ((scalarExtension φ X).obj M))) ≫
    (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} B) r).counit.app
      ((scalarExtension φ X).obj M)

/-- The adjunct of the two successive specified scalar mates is the two normalized
scalar/pullback comparisons followed by scalar extension of the composite A-counit.
Source: Stacks Project, Tag 0E46, remark-compose-base-change, coefficient-change
specialization of the omitted verification
(blueprint: lem-pur-scalar-iterated-mates-adjunct).

Proof:
1. By def-pur-etale-scalar-mate and situation-conventions, the B-pullback
   of each scalar mate followed by the B-counit equals its scalar/pullback comparison
   followed by scalar extension of the A-counit. Use this for (r,M) and (s,Rr_* M).
2. Expand the iterated mate and scalarIteratedAdjunct. Functoriality and naturality
   of the s-B-counit at the r-mate move that mate to immediately before the r-B-counit.
   This counit is from the canonical adjunction of definition-projection-formula-map--1.
3. Substitute the two equations of step 1. Associativity and functoriality give
   the s-scalar/pullback comparison, the pullback of scalar extension of the s-A-counit,
   the r-scalar/pullback comparison at Rr_* M, and scalar extension of the r-A-counit.
4. Naturality of the r-comparison from def-pur-etale-scalar-pullback-iso at the
   s-A-counit moves it before that counit. The resulting four arrows are exactly
   the displayed right side. No mate is inverted and no boundedness, properness,
   or coefficient flatness is used. -/
theorem scalarMate_iterated_adjunct
    {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) {X Y Z : Scheme.{u}} (r : X ⟶ Y) (s : Y ⟶ Z)
    (M : DerivedCategoryModule A X) :
    scalarIteratedAdjunct φ r s M
        ((scalarMate φ s).app (R(lowerStar (ModuleCat.{u + 1} A) r).obj M) ≫
          R(lowerStar (ModuleCat.{u + 1} B) s).map ((scalarMate φ r).app M)) =
      L(upperStar (ModuleCat.{u + 1} B) r).map
          ((scalarPullbackIso φ s).hom.app
            (R(lowerStar (ModuleCat.{u + 1} A) s).obj
              (R(lowerStar (ModuleCat.{u + 1} A) r).obj M))) ≫
        (scalarPullbackIso φ r).hom.app
          (L(upperStar (ModuleCat.{u + 1} A) s).obj
            (R(lowerStar (ModuleCat.{u + 1} A) s).obj
              (R(lowerStar (ModuleCat.{u + 1} A) r).obj M))) ≫
        (scalarExtension φ X).map
          (L(upperStar (ModuleCat.{u + 1} A) r).map
            ((derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) s).counit.app
              (R(lowerStar (ModuleCat.{u + 1} A) r).obj M))) ≫
        (scalarExtension φ X).map
          ((derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) r).counit.app M) := by
  let Pr := L(upperStar (ModuleCat.{u + 1} B) r)
  let Ps := L(upperStar (ModuleCat.{u + 1} B) s)
  let ar := derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) r
  let br := derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} B) r
  let as' := derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) s
  let bs := derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} B) s
  let U := R(lowerStar (ModuleCat.{u + 1} A) r).obj M
  have hr : Pr.map ((scalarMate φ r).app M) ≫ br.counit.app _ =
      (scalarPullbackIso φ r).hom.app U ≫ (scalarExtension φ X).map
        (ar.counit.app M) :=
    mateEquiv_counit ar br (TwoSquare.mk _ _ _ _ (scalarPullbackIso φ r).hom) M
  have hs : Ps.map ((scalarMate φ s).app U) ≫ bs.counit.app _ =
      (scalarPullbackIso φ s).hom.app _ ≫ (scalarExtension φ Y).map
        (as'.counit.app U) :=
    mateEquiv_counit as' bs (TwoSquare.mk _ _ _ _ (scalarPullbackIso φ s).hom) U
  have hn := bs.counit.naturality ((scalarMate φ r).app M)
  have hscalar := (scalarPullbackIso φ r).hom.naturality (as'.counit.app U)
  dsimp only [Functor.comp_map, Functor.id_map, Functor.comp_obj, Functor.id_obj]
    at hn hscalar
  change Ps.map (R(lowerStar (ModuleCat.{u + 1} B) s).map
      ((scalarMate φ r).app M)) ≫ bs.counit.app _ =
    bs.counit.app _ ≫ (scalarMate φ r).app M at hn
  change Pr.map ((scalarExtension φ Y).map (as'.counit.app U)) ≫
      (scalarPullbackIso φ r).hom.app U =
    (scalarPullbackIso φ r).hom.app _ ≫ (scalarExtension φ X).map
      (L(upperStar (ModuleCat.{u + 1} A) r).map (as'.counit.app U)) at hscalar
  unfold scalarIteratedAdjunct
  change Pr.map (Ps.map _) ≫ Pr.map (bs.counit.app _) ≫ br.counit.app _ = _
  rw [← Pr.map_comp_assoc, Ps.map_comp, Category.assoc]
  erw [hn]
  rw [← Category.assoc, hs, Pr.map_comp, Category.assoc, Pr.map_comp,
    Category.assoc, hr]
  rw [← Category.assoc (Pr.map ((scalarExtension φ Y).map (as'.counit.app U)))]
  erw [hscalar]
  rw [Category.assoc]
  rfl

end AlgebraicGeometry.Etale
