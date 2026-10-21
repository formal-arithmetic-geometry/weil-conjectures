/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N5
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusAdjunction
public import Mathlib.CategoryTheory.Adjunction.Mates
public import Mathlib.CategoryTheory.Localization.Predicate

/-! # The bounded-below derived mate of an arbitrary exact square

Source: Stacks Project, sites-cohomology.tex, Tag 07A7, remark-base-change;
`CategoryTheory.Adjunction.derivedPlus_mateEquiv_app_fac` in
WeilConjectures/CategoryTheory/DerivedCategory/RightDerivedFunctor/PlusAdjunction.lean.
(blueprint: lem-trf-bounded-below-derived-mate-model)

The square is constructed by localization, without assuming its invertibility.
The mate identity retains the exact-functor comparison isomorphisms.
-/

@[expose] public section

set_option autoImplicit false

universe uA uB uA' uB' vA vB vA' vB' wA wB wA' wB'

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

variable {A : Type uA} {B : Type uB} {A' : Type uA'} {B' : Type uB'}
  [Category.{vA} A] [Category.{vB} B] [Category.{vA'} A'] [Category.{vB'} B']
  [Abelian A] [Abelian B] [Abelian A'] [Abelian B']
  [HasDerivedCategory.{wA} A] [HasDerivedCategory.{wB} B]
  [HasDerivedCategory.{wA'} A'] [HasDerivedCategory.{wB'} B']
  {L : B ⥤ A} {L' : B' ⥤ A'} {G : B ⥤ B'} {H : A ⥤ A'}
  [L.Additive] [L'.Additive] [G.Additive] [H.Additive]
  [PreservesFiniteLimits L] [PreservesFiniteColimits L]
  [PreservesFiniteLimits L'] [PreservesFiniteColimits L']
  [PreservesFiniteLimits G] [PreservesFiniteColimits G]
  [PreservesFiniteLimits H] [PreservesFiniteColimits H]

/-- The termwise-derived square of an arbitrary transformation of exact additive functors.
This is the preimage of the termwise square conjugated by the canonical localization
comparisons. Fully faithful precomposition with `Qh` determines this transformation uniquely.
No inverse of the given square is used.

Source: localization universal property and the exact-functor comparisons in
PlusAdjunction.lean, proof of `derivedPlus_mateEquiv_app_fac`.
(blueprint: lem-trf-bounded-below-derived-mate-model) -/
noncomputable def boundedBelowDerivedSquare (σ : TwoSquare G L L' H) :
    TwoSquare G.mapDerivedCategoryPlus L.mapDerivedCategoryPlus
      L'.mapDerivedCategoryPlus H.mapDerivedCategoryPlus :=
  TwoSquare.mk _ _ _ _ <|
    (Localization.fullyFaithfulWhiskeringLeft DerivedCategory.Plus.Qh
      (HomotopyCategory.Plus.quasiIso B) (DerivedCategory.Plus A')).preimage
      ((Functor.associator _ _ _).inv ≫
        Functor.whiskerRight G.mapDerivedCategoryPlusFactorsh.hom L'.mapDerivedCategoryPlus ≫
        (Functor.associator _ _ _).hom ≫
        Functor.whiskerLeft G.mapHomotopyCategoryPlus L'.mapDerivedCategoryPlusFactorsh.hom ≫
        (Functor.associator _ _ _).inv ≫
        Functor.whiskerRight
          ((Functor.mapHomotopyCategoryPlusCompIso (Iso.refl (G ⋙ L'))).hom ≫
            NatTrans.mapHomotopyCategoryPlus σ.natTrans ≫
            (Functor.mapHomotopyCategoryPlusCompIso (Iso.refl (L ⋙ H))).inv)
          DerivedCategory.Plus.Qh ≫
        (Functor.associator _ _ _).hom ≫
        Functor.whiskerLeft L.mapHomotopyCategoryPlus H.mapDerivedCategoryPlusFactorsh.inv ≫
        (Functor.associator _ _ _).inv ≫
        Functor.whiskerRight L.mapDerivedCategoryPlusFactorsh.inv H.mapDerivedCategoryPlus ≫
        (Functor.associator _ _ _).hom)

/-- The canonical bounded-below derived mate is computed by the ordinary mate and the
right-derived comparison units. The initial factor on the right and the final factor
on the right are precisely the canonical exact-functor localization identifications.
The statement applies to every bounded-below homotopy complex, hence to every
bounded-below complex through the homotopy quotient. Neither invertibility of `σ`
nor preservation of injectives by `H` is assumed.

Source: Stacks Project, Tag 07A7, remark-base-change; PlusAdjunction.lean,
`derivedPlus_mateEquiv_app_fac`.
(blueprint: lem-trf-bounded-below-derived-mate-model)

Proof:
1. Apply the additive functors termwise on bounded-below homotopy categories. Naturality
of σ with each differential makes its components a chain map. The exact-functor
factorizations give the fixed isomorphisms φ for L, L', G, and H.
2. Use the right-derived comparison units for R and R' and the canonical derived
adjunctions `derivedPlus`, including their unit and counit factorization formulas.
3. The definition `boundedBelowDerivedSquare` lifts the termwise square by fully faithful
precomposition with the localization. Its component at qN is A_N q(σ_N) B_N⁻¹, where
A_N and B_N are the composites of the two exact localization comparisons. The preimage
identity yields the factorization hθ in `derivedPlus_mateEquiv_app_fac`.
4. Expand the derived mate as the primed unit followed by the image of the square and
of the unprimed counit. Naturality moves D(G)(α_P) through the unit and the square.
5. The derived counit formula replaces ε^D D(L)(α_P) by q(ε_P) φ_L. Naturality of φ_H
and the square factorization from step 3 reduce its argument to q(H(ε_P) σ_RP) φ_L'.
6. The primed derived unit formula replaces the remaining unit and φ_L' by q(η') and
α'. Naturality of α' moves q(H(ε_P) σ_RP) past α'. This holds for every homotopy
complex and requires no injectivity of H(P).
7. The termwise adjunction has the termwise unit and counit, so the resulting chain
map is C(b), where b is the ordinary mate. Keep φ_G and the inverse φ_H at the two
ends to obtain the displayed equality. Only these canonical isomorphisms are inverted;
σ and the right-derived comparison units are never canceled.
-/
theorem Adjunction.boundedBelowDerivedMateModel
    [EnoughInjectives A] [EnoughInjectives A']
    {R : A ⥤ B} {R' : A' ⥤ B'} [R.Additive] [R'.Additive]
    (adj : L ⊣ R) (adj' : L' ⊣ R') (σ : TwoSquare G L L' H)
    (P : HomotopyCategory.Plus A) :
    G.mapDerivedCategoryPlus.map (R.rightDerivedFunctorPlusUnit.app P) ≫
        (mateEquiv adj.derivedPlus adj'.derivedPlus
          (boundedBelowDerivedSquare σ)).natTrans.app (DerivedCategory.Plus.Qh.obj P) =
      G.mapDerivedCategoryPlusFactorsh.hom.app (R.mapHomotopyCategoryPlus.obj P) ≫
        DerivedCategory.Plus.Qh.map
          ((NatTrans.mapHomotopyCategoryPlus (mateEquiv adj adj' σ).natTrans).app P) ≫
        R'.rightDerivedFunctorPlusUnit.app (H.mapHomotopyCategoryPlus.obj P) ≫
        R'.rightDerivedFunctorPlus.map (H.mapDerivedCategoryPlusFactorsh.inv.app P) := by
  sorry

end CategoryTheory
