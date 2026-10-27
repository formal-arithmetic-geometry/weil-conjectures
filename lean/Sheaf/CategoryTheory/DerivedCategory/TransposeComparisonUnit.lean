/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q49
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusAdjunction
public import Mathlib.CategoryTheory.Adjunction.Mates

/-! # The derived transpose of a termwise mate and its comparison unit

Source: WeilConjectures/CategoryTheory/DerivedCategory/RightDerivedFunctor/PlusAdjunction.lean,
`derivedPlus_mateEquiv_app_fac`, the unit and naturality calculation;
WeilConjectures/CategoryTheory/HomotopyCategory/Adjunction.lean,
`mapHomotopyCategoryPlus_mateEquiv_app`, the degreewise calculation.
(blueprint: lem-trf-derived-transpose-comparison-unit)

The comparison unit is used at an arbitrary bounded-below complex, without being inverted.
The three conjuncts give the homotopy identity, its derived counterpart, and the explicit
components of the underlying termwise chain maps.
-/

@[expose] public section

set_option autoImplicit false

universe uA uB uA' uB' vA vB vA' vB' wA wB wA' wB'

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.Adjunction

/-- The homotopy transpose of the termwise square followed by the unprimed counit is
exactly the ordinary mate applied termwise. Its derived transpose is the localization
of this mate followed by the primed right-derived comparison unit, even when the target
complex is not injective. The last conjunct gives the equality before taking homotopy
classes, degree by degree on the representative of `P`.

Source: PlusAdjunction.lean, `derivedPlus_mateEquiv_app_fac`, unit/naturality steps;
HomotopyCategory/Adjunction.lean, `mapHomotopyCategoryPlus_mateEquiv_app`.
(blueprint: lem-trf-derived-transpose-comparison-unit)

Proof:
1. By lem-weil-pbc-termwise-adjunction-homotopy, the homotopy unit and counit are the
classes of the termwise chain maps. In degree n the transpose is the primed unit,
then R' applied to the component of σ at R(Pⁿ), then R'H applied to the unprimed
counit. This is the ordinary mate by def-weil-pbc-adjunction-mate. The chain maps
therefore agree degreewise, hence their homotopy classes agree (first conjunct).
2. Apply lem-trf-bounded-below-derived-adjunction's primed unit formula at
M = K(G)K(R)P. Postcompose with U'(q(d)), where d is the termwise square at K(R)P
followed by K(H) of the unprimed homotopy counit.
3. By lem-weil-pbc-right-derived-plus-injective, the comparison α' is natural on
all bounded-below homotopy complexes. Its naturality at d replaces the composite
U'(q(d)) α' by α' q(K(R')(d)). Functoriality of q and step 1 give the second
conjunct. No injectivity hypothesis on K(H)P and no inverse of α' is used.
-/
theorem derivedTransposeComparisonUnit
    {A : Type uA} {B : Type uB} {A' : Type uA'} {B' : Type uB'}
    [Category.{vA} A] [Category.{vB} B] [Category.{vA'} A'] [Category.{vB'} B']
    [Abelian A] [Abelian B] [Abelian A'] [Abelian B']
    [HasDerivedCategory.{wA} A] [HasDerivedCategory.{wB} B]
    [HasDerivedCategory.{wA'} A'] [HasDerivedCategory.{wB'} B']
    [EnoughInjectives A] [EnoughInjectives A']
    {L : B ⥤ A} {L' : B' ⥤ A'} {G : B ⥤ B'} {H : A ⥤ A'}
    {R : A ⥤ B} {R' : A' ⥤ B'}
    [L.Additive] [L'.Additive] [G.Additive] [H.Additive] [R.Additive] [R'.Additive]
    [PreservesFiniteLimits L] [PreservesFiniteColimits L]
    [PreservesFiniteLimits L'] [PreservesFiniteColimits L']
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    [PreservesFiniteLimits H] [PreservesFiniteColimits H]
    (adj : L ⊣ R) (adj' : L' ⊣ R') (σ : TwoSquare G L L' H)
    (P : HomotopyCategory.Plus A) :
    (adj'.mapHomotopyCategoryPlus.unit.app
          (G.mapHomotopyCategoryPlus.obj (R.mapHomotopyCategoryPlus.obj P)) ≫
        R'.mapHomotopyCategoryPlus.map
          ((NatTrans.mapHomotopyCategoryPlus σ.natTrans).app
              (R.mapHomotopyCategoryPlus.obj P) ≫
            H.mapHomotopyCategoryPlus.map (adj.mapHomotopyCategoryPlus.counit.app P)) =
      (NatTrans.mapHomotopyCategoryPlus (mateEquiv adj adj' σ).natTrans).app P) ∧
    (adj'.derivedPlus.unit.app (DerivedCategory.Plus.Qh.obj
          (G.mapHomotopyCategoryPlus.obj (R.mapHomotopyCategoryPlus.obj P))) ≫
        R'.rightDerivedFunctorPlus.map (L'.mapDerivedCategoryPlusFactorsh.hom.app
          (G.mapHomotopyCategoryPlus.obj (R.mapHomotopyCategoryPlus.obj P))) ≫
        R'.rightDerivedFunctorPlus.map (DerivedCategory.Plus.Qh.map
          ((NatTrans.mapHomotopyCategoryPlus σ.natTrans).app
              (R.mapHomotopyCategoryPlus.obj P) ≫
            H.mapHomotopyCategoryPlus.map (adj.mapHomotopyCategoryPlus.counit.app P))) =
      DerivedCategory.Plus.Qh.map
          ((NatTrans.mapHomotopyCategoryPlus (mateEquiv adj adj' σ).natTrans).app P) ≫
        R'.rightDerivedFunctorPlusUnit.app (H.mapHomotopyCategoryPlus.obj P)) ∧
    (∀ n : ℤ,
      adj'.unit.app (G.obj (R.obj (P.obj.as.X n))) ≫
          R'.map (σ.natTrans.app (R.obj (P.obj.as.X n))) ≫
          R'.map (H.map (adj.counit.app (P.obj.as.X n))) =
        (mateEquiv adj adj' σ).natTrans.app (P.obj.as.X n)) := by
  have hK :
      adj'.mapHomotopyCategoryPlus.unit.app
          (G.mapHomotopyCategoryPlus.obj (R.mapHomotopyCategoryPlus.obj P)) ≫
        R'.mapHomotopyCategoryPlus.map
          ((NatTrans.mapHomotopyCategoryPlus σ.natTrans).app
              (R.mapHomotopyCategoryPlus.obj P) ≫
            H.mapHomotopyCategoryPlus.map (adj.mapHomotopyCategoryPlus.counit.app P)) =
      (NatTrans.mapHomotopyCategoryPlus (mateEquiv adj adj' σ).natTrans).app P := by
    simpa only [Functor.map_comp] using
      (NatTrans.mapHomotopyCategoryPlus_mateEquiv_app adj adj' σ P).symm
  refine ⟨hK, ?_, ?_⟩
  · have hnat := R'.rightDerivedFunctorPlusUnit.naturality
      ((NatTrans.mapHomotopyCategoryPlus σ.natTrans).app
          (R.mapHomotopyCategoryPlus.obj P) ≫
        H.mapHomotopyCategoryPlus.map (adj.mapHomotopyCategoryPlus.counit.app P))
    simp only [Functor.comp_obj, Functor.comp_map] at hnat
    rw [← Category.assoc, derivedPlus_unit_app_fac, Category.assoc]
    erw [← hnat, ← Category.assoc, ← Functor.map_comp, hK]
    simp only [Functor.id_obj]
  · intro n
    simp [mateEquiv_apply]

end CategoryTheory.Adjunction
