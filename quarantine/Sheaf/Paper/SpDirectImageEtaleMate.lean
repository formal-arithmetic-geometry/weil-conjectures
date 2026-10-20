/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q03
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusCompatibility
public import Sheaf.Paper.BoundaryExceptionalComparisonData
public import Sheaf.AlgebraicGeometry.FixedComparisonDirectImageMate
public import Sheaf.AlgebraicGeometry.ProEtaleFiniteModules
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses
public import Sheaf.AlgebraicGeometry.ProEtaleConstantRingOperations
public import WeilConjectures.SixFunctors.Etale.Derived.LowerStarProjection
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ComparisonMonoidal
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.UpperStarMonoidal
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.FlatModuleCat
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.FlatModuleCat
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LowerStarProjComparison
import Sheaf.AlgebraicGeometry.ProEtaleSiteComparison

/-!
# The normalized pro-etale transpose of the etale projection

Source: blueprint main-20261015, sec-smooth-purity/sk-lem-sp-reduction,
`sk-lem-sp-reduction-direct-image.proof.md`, Step 1; Stacks Tags 0E48 and 07A4
(blueprint: lem-sp-direct-image-etale-mate-isomorphism).

All categories are ordinary uncompleted constant-ring module categories, in their
fixed-ring sheaf presentation. The coefficient on X is written as the canonical
pullback of B_Y, and its pro-etale realization as the pullback of nu_Y^* B_Y.
Thus every constant-coefficient identification in the statement is built into the
endpoints, without an arbitrary choice of comparison or any flatness assumption.

## Main definitions and statement

* `spDirectImageComparisonIso`: the recorded normalized comparison, included from D+.
* `spEtaleMate`: the transported etale projection, including both tensor comparisons.
* `spEtaleMate_transpose`: its normalized counit transpose and conditional invertibility.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 2048


universe u

open CategoryTheory CategoryTheory.Limits

open CategoryTheory.Functor

private def tensorTransport
    {C D : Type*} [Category C] [Category D]
    (T : C ⥤ C ⥤ C) (U : D ⥤ D ⥤ D)
    {F G : C ⥤ D} (e : F ≅ G)
    (m : (postcompose₂.obj F).obj T ≅ (((whiskeringLeft₂ D).obj F).obj F).obj U) :
    (postcompose₂.obj G).obj T ≅ (((whiskeringLeft₂ D).obj G).obj G).obj U :=
  (postcompose₂.mapIso e.symm).app T ≪≫ m ≪≫
    ((((whiskeringLeft₂ D).obj F).mapIso e).app U) ≪≫
    (((whiskeringLeft₂ D).mapIso e).app G).app U

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem comparisonCompatible_transport
    {C D C' D' : Type*} [Category C] [Category D] [Category C'] [Category D']
    {F : D ⥤ C} {F' : D' ⥤ C'}
    {N : D ⥤ D'} {M : C ⥤ C'} {N' : D ⥤ D'} {M' : C ⥤ C'}
    {T : D ⥤ D ⥤ D} {U : C ⥤ C ⥤ C}
    {T' : D' ⥤ D' ⥤ D'} {U' : C' ⥤ C' ⥤ C'}
    (a : N ⋙ F' ≅ F ⋙ M) (e : N ≅ N') (d : M ≅ M')
    (t : (postcompose₂.obj F).obj T ⟶ (((whiskeringLeft₂ C).obj F).obj F).obj U)
    (t' : (postcompose₂.obj F').obj T' ⟶ (((whiskeringLeft₂ C').obj F').obj F').obj U')
    (m : (postcompose₂.obj M).obj U ≅ (((whiskeringLeft₂ C').obj M).obj M).obj U')
    (n : (postcompose₂.obj N).obj T ≅ (((whiskeringLeft₂ D').obj N).obj N).obj T')
    (h : Adjunction.ComparisonCompatible a t t' m n) :
    Adjunction.ComparisonCompatible
      (Functor.isoWhiskerRight e.symm F' ≪≫ a ≪≫ Functor.isoWhiskerLeft F d)
      t t' (tensorTransport U U' d m) (tensorTransport T T' e n) := by
  intro X Y
  have hh := h X Y
  dsimp [tensorTransport]
  rw [d.inv.naturality_assoc, reassoc_of% hh]
  simp only [Functor.map_comp, NatTrans.comp_app, Category.assoc]
  rw [← F'.map_comp_assoc, Iso.hom_inv_id_app, CategoryTheory.Functor.map_id, Category.id_comp]
  have ht₁ := NatTrans.congr_app (t'.naturality (e.hom.app X)) (N'.obj Y)
  have ht₂ := (t'.app (N.obj X)).naturality (e.hom.app Y)
  dsimp at ht₁ ht₂
  rw [reassoc_of% ht₁, reassoc_of% ht₂]
  simp only [← NatTrans.comp_app_assoc, ← Functor.map_comp_assoc,
    Iso.hom_inv_id_app, CategoryTheory.Functor.map_id, Category.id_comp]
  rw [NatTrans.naturality_assoc]
  erw [(U'.map (d.hom.app (F.obj X))).naturality
    (a.hom.app Y ≫ d.hom.app (F.obj Y))]
  simp only [NatTrans.comp_app, Category.assoc, ← Functor.map_comp_assoc, Iso.hom_inv_id_app,
    Iso.hom_inv_id_app, CategoryTheory.Functor.map_id, Category.id_comp,
    NatTrans.comp_app, Category.assoc]
  simp only [Functor.map_comp]
  rfl

namespace AlgebraicGeometry.ProEtale

open Scheme

/-- B_Y in degree zero, with its A-action given by the specified ring homomorphism.
Source: blueprint direct-image proof, Step 1; Stacks 0E48
(blueprint: lem-sp-direct-image-etale-mate-isomorphism). -/
def spEtaleCoefficient {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (a : A →+* B) (Y : Scheme.{u}) :
    DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} A)) :=
  (DerivedCategory.singleFunctor _ 0).obj
    ((constantSheaf Y.smallEtaleTopology (ModuleCat.{u + 1} A)).obj
      ((ModuleCat.restrictScalars a).obj (ModuleCat.of B B)))

/-- H = K tensor B_X, writing B_X as the canonical pullback of B_Y.
Source: blueprint direct-image proof, Step 1; Stacks 07A4
(blueprint: lem-sp-direct-image-etale-mate-isomorphism). -/
def spEtaleTensorObject {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (a : A →+* B) {X Y : Scheme.{u}} (f : X ⟶ Y)
    (K : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A))) :=
  ((Etale.derivedTensor (ModuleCat.{u + 1} A) X).obj K).obj
    ((Etale.upperStar (ModuleCat.{u + 1} A) f).leftDerivedFunctor.obj
      (spEtaleCoefficient a Y))

/-- The specified etale projection pi_K, with coefficient B_Y.
Source: blueprint direct-image proof, Step 1; Stacks 0E48
(blueprint: lem-sp-direct-image-etale-mate-isomorphism). -/
abbrev spEtaleProjection {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (a : A →+* B) {X Y : Scheme.{u}} (f : X ⟶ Y)
    (K : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A))) :=
  ((Etale.rightDerivedLowerStarProjectionMap (ModuleCat.{u + 1} A) f).app K).app
    (spEtaleCoefficient a Y)

/-- Include the recorded normalized D+ comparison into the unbounded categories.
The four endpoint isomorphisms are the standard exact-functor and right-derived
compatibilities with the fully faithful D+ inclusion. In particular the middle
arrow is exactly fixedComparisonDirectImageMatePlus, not a chosen endpoint isomorphism.
Source: blueprint direct-image proof, Step 1; Stacks 099R and 0B65
(blueprint: lem-sp-direct-image-etale-mate-isomorphism). -/
def spDirectImageComparisonIso (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} (f : X ⟶ Y) [QuasiCompact f] [QuasiSeparated f]
    (K : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)))
    (hK : ∃ n : ℤ, K.IsGE n) :
    (comparisonUpperStar (ModuleCat.{u + 1} A) Y).mapDerivedCategory.obj
        ((Etale.lowerStar (ModuleCat.{u + 1} A) f).rightDerivedFunctor.obj K) ≅
      (lowerStar (ModuleCat.{u + 1} A) f).rightDerivedFunctor.obj
        ((comparisonUpperStar (ModuleCat.{u + 1} A) X).mapDerivedCategory.obj K) := by
  let J : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)) :=
    ⟨K, hK⟩
  letI := isIso_fixedComparisonDirectImageMatePlus A f
  exact
    (comparisonUpperStar (ModuleCat.{u + 1} A) Y).mapDerivedCategory.mapIso
        ((Etale.lowerStar (ModuleCat.{u + 1} A) f).rightDerivedFunctorPlusCompatibility.app
          J).symm ≪≫
      ((comparisonUpperStar (ModuleCat.{u + 1} A) Y).mapDerivedCategoryPlusCompatibility.app
        ((Etale.rightDerivedLowerStarPlus (ModuleCat.{u + 1} A) f).obj J)).symm ≪≫
      DerivedCategory.Plus.ι.mapIso
        ((asIso (fixedComparisonDirectImageMatePlus A f)).app J) ≪≫
      (lowerStar (ModuleCat.{u + 1} A) f).rightDerivedFunctorPlusCompatibility.app
        ((comparisonUpperStar (ModuleCat.{u + 1} A) X).mapDerivedCategoryPlus.obj J) ≪≫
      (lowerStar (ModuleCat.{u + 1} A) f).rightDerivedFunctor.mapIso
        ((comparisonUpperStar (ModuleCat.{u + 1} A) X).mapDerivedCategoryPlusCompatibility.app J)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem sp_included_counit
    (C : Type*) [Category.{u + 1} C] [Abelian C]
    [IsGrothendieckAbelian.{u + 1} C]
    [MonoidalCategory C] [MonoidalPreadditive C] [SymmetricCategory C]
    [MonoidalClosed C] [Abelian.HasFunctorialFlatResolution C]
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (J : DerivedCategory.Plus (Sheaf (Scheme.ProEt.topology X) C)) :
    (upperStar C f).mapDerivedCategory.map
        ((lowerStar C f).rightDerivedFunctorPlusCompatibility.hom.app J) ≫
      ((upperStarLowerStarAdjunction C f).derivedAdjunction.ofNatIsoLeft
        (upperStar C f).leftDerivedFunctorIsoMapDerivedCategory).counit.app J.obj =
    DerivedCategory.Plus.ι.map
      ((derivedUpperStarLowerStarAdjunctionPlus C f).counit.app J) := by
  simp only [derivedUpperStarLowerStarAdjunctionPlus, Adjunction.derivedAdjunctionPlus,
    Adjunction.map_restrictFullyFaithful_counit_app,
    Functor.mapDerivedCategoryPlusCompatibility, Iso.symm_inv, Iso.refl_hom,
    NatTrans.id_app, Category.id_comp]
  rfl

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem sp_included_etale_counit
    (C : Type*) [Category.{u + 1} C] [Abelian C]
    [IsGrothendieckAbelian.{u + 1} C]
    [MonoidalCategory C] [MonoidalPreadditive C] [SymmetricCategory C]
    [MonoidalClosed C] [Abelian.HasFunctorialFlatResolution C]
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (J : DerivedCategory.Plus (Sheaf X.smallEtaleTopology C)) :
    (Etale.upperStar C f).mapDerivedCategory.map
        ((Etale.lowerStar C f).rightDerivedFunctorPlusCompatibility.hom.app J) ≫
      ((Etale.upperStarLowerStarAdjunction C f).derivedAdjunction.ofNatIsoLeft
        (Etale.upperStar C f).leftDerivedFunctorIsoMapDerivedCategory).counit.app J.obj =
    DerivedCategory.Plus.ι.map
      ((Etale.derivedUpperStarLowerStarAdjunctionPlus C f).counit.app J) := by
  simp only [Etale.derivedUpperStarLowerStarAdjunctionPlus, Adjunction.derivedAdjunctionPlus,
    Adjunction.map_restrictFullyFaithful_counit_app,
    Functor.mapDerivedCategoryPlusCompatibility, Iso.symm_inv, Iso.refl_hom,
    NatTrans.id_app, Category.id_comp]
  rfl

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem sp_pullback_square
    (C : Type*) [Category.{u + 1} C] [Abelian C]
    [IsGrothendieckAbelian.{u + 1} C]
    [MonoidalCategory C] [MonoidalPreadditive C] [SymmetricCategory C]
    [MonoidalClosed C] [Abelian.HasFunctorialFlatResolution C]
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    BoundaryComparison.pullbackSquare C f =
      Functor.isoWhiskerRight
          (comparisonUpperStar C Y).leftDerivedFunctorIsoMapDerivedCategory.symm
          (upperStar C f).leftDerivedFunctor ≪≫
        leftDerivedComparisonUpperStarCompUpperStarIso C f ≪≫
        Functor.isoWhiskerLeft (Etale.upperStar C f).leftDerivedFunctor
          (comparisonUpperStar C X).leftDerivedFunctorIsoMapDerivedCategory := by
  ext J
  simp [BoundaryComparison.pullbackSquare,
    leftDerivedComparisonUpperStarCompUpperStarIso, Functor.leftDerivedFunctorCompNatIso,
    Functor.leftDerivedFunctorCompIso, Functor.leftDerivedFunctorNatIso]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem sp_comparison_hom
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} (f : X ⟶ Y) [QuasiCompact f] [QuasiSeparated f]
    (K : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)))
    (hK : ∃ n : ℤ, K.IsGE n) :
    (spDirectImageComparisonIso A f K hK).hom =
      (BoundaryComparison.directImageMate (ModuleCat.{u + 1} A) f).app K := by
  let J : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)) :=
    ⟨K, hK⟩
  let C := ModuleCat.{u + 1} A
  let E := Etale.upperStar C f
  let P := upperStar C f
  let DX := (comparisonUpperStar C X).mapDerivedCategory
  let DY := (comparisonUpperStar C Y).mapDerivedCategory
  let eps := ((upperStarLowerStarAdjunction C f).derivedAdjunction.ofNatIsoLeft
    P.leftDerivedFunctorIsoMapDerivedCategory).counit
  let epse := ((Etale.upperStarLowerStarAdjunction C f).derivedAdjunction.ofNatIsoLeft
    E.leftDerivedFunctorIsoMapDerivedCategory).counit
  have hn := congrArg DerivedCategory.Plus.ι.map
    (fixedComparisonDirectImageMatePlus_counit A f J)
  have hpull : DerivedCategory.Plus.ι.map
      ((fixedComparisonPullbackPlus A f).hom.app
        ((Etale.rightDerivedLowerStarPlus C f).obj J)) =
      ((Functor.mapDerivedCategoryCompIso E (comparisonUpperStar C X)).inv ≫
        (Functor.mapDerivedCategoryNatIso
          (comparisonUpperStarCompUpperStarIso C f).symm).hom ≫
        (Functor.mapDerivedCategoryCompIso (comparisonUpperStar C Y) P).hom).app
          (((Etale.lowerStar C f).rightDerivedFunctorPlus.obj J).obj) := by
    simp only [fixedComparisonPullbackPlus, Iso.trans_hom, Iso.symm_hom,
      NatTrans.comp_app, Functor.map_comp]
    have he : DerivedCategory.Plus.ι.mapIso
        ((Functor.mapDerivedCategoryPlusCompIso E (comparisonUpperStar C X)).app
          ((Etale.rightDerivedLowerStarPlus C f).obj J)) =
        (Functor.mapDerivedCategoryCompIso E (comparisonUpperStar C X)).app
          (((Etale.rightDerivedLowerStarPlus C f).obj J).obj) :=
      Iso.ext (Functor.ι_map_mapDerivedCategoryPlusCompIso_hom_app _ _ _)
    have hi := congrArg Iso.inv he
    change DerivedCategory.Plus.ι.map
      ((Functor.mapDerivedCategoryPlusCompIso E (comparisonUpperStar C X)).inv.app
        ((Etale.rightDerivedLowerStarPlus C f).obj J)) = _ at hi
    erw [hi, Functor.ι_map_mapDerivedCategoryPlusNatIso_hom_app,
      Functor.ι_map_mapDerivedCategoryPlusCompIso_hom_app]
    rfl
  simp only [Functor.map_comp] at hn
  rw [hpull, ← sp_included_counit C f] at hn
  change _ = DX.map (DerivedCategory.Plus.ι.map
    ((Etale.derivedUpperStarLowerStarAdjunctionPlus C f).counit.app J)) at hn
  rw [← sp_included_etale_counit C f] at hn
  change _ = DX.map (E.mapDerivedCategory.map
    ((Etale.lowerStar C f).rightDerivedFunctorPlusCompatibility.hom.app J) ≫ epse.app K) at hn
  apply ((derivedUpperStarLowerStarAdjunction C f).ofNatIsoLeft
    P.leftDerivedFunctorIsoMapDerivedCategory).homEquiv _ _ |>.symm.injective
  rw [Adjunction.homEquiv_counit]
  rw [Adjunction.homEquiv_ofNatIsoLeft_symm_apply,
    BoundaryComparison.directImageMate, Adjunction.homEquiv_counit, mateEquiv_counit]
  dsimp only [spDirectImageComparisonIso, Iso.trans_hom, Functor.mapIso_hom,
    Iso.symm_hom, Iso.symm_inv, Iso.app_hom, Iso.app_inv, asIso_hom,
    Functor.mapDerivedCategoryPlusCompatibility, Iso.refl_hom, Iso.refl_inv,
    NatTrans.id_app]
  let q := (Functor.mapDerivedCategoryCompIso E (comparisonUpperStar C X)).symm ≪≫
    Functor.mapDerivedCategoryNatIso (comparisonUpperStarCompUpperStarIso C f).symm ≪≫
    Functor.mapDerivedCategoryCompIso (comparisonUpperStar C Y) P
  let r := (Etale.lowerStar C f).rightDerivedFunctorPlusCompatibility.app J
  let b := DerivedCategory.Plus.ι.map ((fixedComparisonDirectImageMatePlus A f).app J)
  let c := (lowerStar C f).rightDerivedFunctorPlusCompatibility.hom.app
    ((comparisonUpperStar C X).mapDerivedCategoryPlus.obj J)
  erw [CategoryTheory.Functor.map_id, Category.comp_id, Category.id_comp]
  change P.mapDerivedCategory.map (DY.map r.inv ≫ b ≫ c) ≫ eps.app (DX.obj K) = _
  have hnorm : P.mapDerivedCategory.map b ≫ P.mapDerivedCategory.map c ≫
      eps.app (DX.obj K) = q.inv.app ((Etale.rightDerivedLowerStarPlus C f).obj J).obj ≫
        DX.map (E.mapDerivedCategory.map r.hom ≫ epse.app K) := by
    change q.hom.app _ ≫ P.mapDerivedCategory.map b ≫ P.mapDerivedCategory.map c ≫
      eps.app (DX.obj K) = _ at hn
    apply (cancel_epi (q.hom.app _)).1
    erw [Iso.hom_inv_id_app_assoc]
    exact hn
  simp only [Functor.map_comp, Category.assoc]
  rw [hnorm]
  erw [q.inv.naturality_assoc]
  simp only [Functor.comp_map, Functor.map_comp]
  change q.inv.app _ ≫ DX.map (E.mapDerivedCategory.map r.inv) ≫
    DX.map (E.mapDerivedCategory.map r.hom) ≫ DX.map (epse.app K) = _
  rw [← DX.map_comp_assoc, ← E.mapDerivedCategory.map_comp, r.inv_hom_id,
    CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id, Category.id_comp]
  simp only [q, epse, BoundaryComparison.pullbackSquare, Adjunction.ofNatIsoLeft_counit,
    Iso.trans_inv, Iso.trans_hom, Iso.symm_inv, Iso.symm_hom, NatTrans.comp_app,
    Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom,
    Functor.whiskerLeft_app, Functor.whiskerRight_app, Functor.map_comp, Category.assoc,
    ]
  erw [Iso.inv_hom_id_app_assoc]
  rfl

private theorem tensorTransport_app
    (C : Type*) [Category.{u + 1} C] [Abelian C]
    [IsGrothendieckAbelian.{u + 1} C]
    [MonoidalCategory C] [MonoidalPreadditive C] [SymmetricCategory C]
    [MonoidalClosed C] [Abelian.HasFunctorialFlatResolution C]
    (X : Scheme.{u}) [(comparisonUpperStar C X).PreservesFlat]
    (K Q : DerivedCategory (Sheaf X.smallEtaleTopology C)) :
    ((tensorTransport (Etale.derivedTensor C X) (derivedTensor C X)
      (comparisonUpperStar C X).leftDerivedFunctorIsoMapDerivedCategory
      (asIso (comparisonUpperStar C X).leftDerivedTensorComparison)).hom.app K).app Q =
      ((derivedTensorObjCompMapDerivedCategoryComparisonUpperStarIso C K).app Q).hom := by
  dsimp [tensorTransport, derivedTensorObjCompMapDerivedCategoryComparisonUpperStarIso]
  rfl

/-- The target identification C_X H = N tensor p^* C_Y B_Y, using the canonical
tensor comparison and the inverse of the canonical pullback square.
Source: blueprint direct-image proof, Step 1; Stacks 07A4 and 0E48
(blueprint: lem-sp-direct-image-etale-mate-isomorphism). -/
def spEtaleMateTargetIso {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A]
    (a : A →+* B) {X Y : Scheme.{u}} (f : X ⟶ Y)
    (K : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A))) :=
  (derivedTensorObjCompMapDerivedCategoryComparisonUpperStarIso
      (ModuleCat.{u + 1} A) K).app
      ((Etale.upperStar (ModuleCat.{u + 1} A) f).leftDerivedFunctor.obj
        (spEtaleCoefficient a Y)) ≪≫
    ((derivedTensor (ModuleCat.{u + 1} A) X).obj
      ((comparisonUpperStar (ModuleCat.{u + 1} A) X).mapDerivedCategory.obj K)).mapIso
        ((BoundaryComparison.pullbackSquare (ModuleCat.{u + 1} A) f).symm.app
          (spEtaleCoefficient a Y))

/-- The source RN tensor B_Y, with B_Y presented as C_Y of the etale coefficient.
Source: blueprint direct-image proof, Step 1; Stacks 0E48
(blueprint: lem-sp-direct-image-etale-mate-isomorphism). -/
abbrev spEtaleMateSource {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (a : A →+* B) {X Y : Scheme.{u}} (f : X ⟶ Y)
    (K : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A))) :=
  ((derivedTensor (ModuleCat.{u + 1} A) Y).obj
    ((lowerStar (ModuleCat.{u + 1} A) f).rightDerivedFunctor.obj
      ((comparisonUpperStar (ModuleCat.{u + 1} A) X).mapDerivedCategory.obj K))).obj
        ((comparisonUpperStar (ModuleCat.{u + 1} A) Y).mapDerivedCategory.obj
          (spEtaleCoefficient a Y))

/-- The tensor target N tensor B_X, in the same constant-section identifications.
Source: blueprint direct-image proof, Step 1; Stacks 0E48
(blueprint: lem-sp-direct-image-etale-mate-isomorphism). -/
abbrev spEtaleMateTarget {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (a : A →+* B) {X Y : Scheme.{u}} (f : X ⟶ Y)
    (K : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A))) :=
  ((derivedTensor (ModuleCat.{u + 1} A) X).obj
    ((comparisonUpperStar (ModuleCat.{u + 1} A) X).mapDerivedCategory.obj K)).obj
      ((upperStar (ModuleCat.{u + 1} A) f).leftDerivedFunctor.obj
        ((comparisonUpperStar (ModuleCat.{u + 1} A) Y).mapDerivedCategory.obj
          (spEtaleCoefficient a Y)))

/-- The map t: tensor beta_K inverse, undo the source tensor comparison, apply
C_Y(pi_K), then beta_H and the target tensor/pullback identification.
Only K and H are required to lie in D+; the source tensor on Y is unrestricted.
Source: blueprint direct-image proof, Step 1; Stacks 0E48
(blueprint: lem-sp-direct-image-etale-mate-isomorphism). -/
def spEtaleMate {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A]
    (a : A →+* B) {X Y : Scheme.{u}} (f : X ⟶ Y) [QuasiCompact f] [QuasiSeparated f]
    (K : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)))
    (hK : ∃ n : ℤ, K.IsGE n)
    (hH : ∃ n : ℤ, (spEtaleTensorObject a f K).IsGE n) :
    spEtaleMateSource a f K ⟶
      (lowerStar (ModuleCat.{u + 1} A) f).rightDerivedFunctor.obj
        (spEtaleMateTarget a f K) :=
  ((derivedTensor (ModuleCat.{u + 1} A) Y).map
      (spDirectImageComparisonIso A f K hK).inv).app
        ((comparisonUpperStar (ModuleCat.{u + 1} A) Y).mapDerivedCategory.obj
          (spEtaleCoefficient a Y)) ≫
    ((derivedTensorObjCompMapDerivedCategoryComparisonUpperStarIso
      (ModuleCat.{u + 1} A)
      ((Etale.lowerStar (ModuleCat.{u + 1} A) f).rightDerivedFunctor.obj K)).app
        (spEtaleCoefficient a Y)).inv ≫
    (comparisonUpperStar (ModuleCat.{u + 1} A) Y).mapDerivedCategory.map
      (spEtaleProjection a f K) ≫
    (spDirectImageComparisonIso A f (spEtaleTensorObject a f K) hH).hom ≫
    (lowerStar (ModuleCat.{u + 1} A) f).rightDerivedFunctor.map
      (spEtaleMateTargetIso a f K).hom

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem sp_projection_transpose
    (C : Type*) [Category.{u + 1} C] [Abelian C]
    [IsGrothendieckAbelian.{u + 1} C]
    [MonoidalCategory C] [MonoidalPreadditive C] [SymmetricCategory C]
    [MonoidalClosed C] [Abelian.HasFunctorialFlatResolution C]
    [UpperStarPreservesFlat C]
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (N : DerivedCategory (Sheaf (Scheme.ProEt.topology X) C))
    (Q : DerivedCategory (Sheaf (Scheme.ProEt.topology Y) C)) :
    (leftDerivedUpperStarTensorIso C f
      ((lowerStar C f).rightDerivedFunctor.obj N) Q).inv ≫
      ((derivedUpperStarLowerStarAdjunction C f).homEquiv
        (((derivedTensor C Y).obj ((lowerStar C f).rightDerivedFunctor.obj N)).obj Q)
        (((derivedTensor C X).obj N).obj ((upperStar C f).leftDerivedFunctor.obj Q))).symm
          (((rightDerivedLowerStarProjectionMap C f).app N).app Q) =
      ((derivedTensor C X).map
        ((derivedUpperStarLowerStarAdjunction C f).counit.app N)).app
        ((upperStar C f).leftDerivedFunctor.obj Q) := by
  erw [homEquiv_symm_rightDerivedLowerStarProjectionMap C f N Q]
  exact Iso.inv_hom_id_assoc (leftDerivedUpperStarTensorIso C f
    ((lowerStar C f).rightDerivedFunctor.obj N) Q) _

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem sp_projection_square
    (C : Type*) [Category.{u + 1} C] [Abelian C]
    [IsGrothendieckAbelian.{u + 1} C]
    [MonoidalCategory C] [MonoidalPreadditive C] [SymmetricCategory C]
    [MonoidalClosed C] [Abelian.HasFunctorialFlatResolution C]
    [Etale.UpperStarPreservesFlat C] [UpperStarPreservesFlat C]
    [∀ T : Scheme.{u}, (comparisonUpperStar C T).PreservesFlat]
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (K : DerivedCategory (Sheaf X.smallEtaleTopology C))
    (Q : DerivedCategory (Sheaf Y.smallEtaleTopology C)) :
    (comparisonUpperStar C Y).mapDerivedCategory.map
        (((Etale.rightDerivedLowerStarProjectionMap C f).app K).app Q) ≫
      (BoundaryComparison.directImageMate C f).app
        (((Etale.derivedTensor C X).obj K).obj
          ((Etale.upperStar C f).leftDerivedFunctor.obj Q)) ≫
      (lowerStar C f).rightDerivedFunctor.map
        (((derivedTensorObjCompMapDerivedCategoryComparisonUpperStarIso C K).app
          ((Etale.upperStar C f).leftDerivedFunctor.obj Q)).hom ≫
          ((derivedTensor C X).obj
            ((comparisonUpperStar C X).mapDerivedCategory.obj K)).map
            ((BoundaryComparison.pullbackSquare C f).inv.app Q)) =
    ((derivedTensorObjCompMapDerivedCategoryComparisonUpperStarIso C
      ((Etale.lowerStar C f).rightDerivedFunctor.obj K)).app Q).hom ≫
      ((derivedTensor C Y).map ((BoundaryComparison.directImageMate C f).app K)).app
        ((comparisonUpperStar C Y).mapDerivedCategory.obj Q) ≫
      ((rightDerivedLowerStarProjectionMap C f).app
        ((comparisonUpperStar C X).mapDerivedCategory.obj K)).app
        ((comparisonUpperStar C Y).mapDerivedCategory.obj Q) := by
  let N := (comparisonUpperStar C X).mapDerivedCategory.obj K
  let Q' := (comparisonUpperStar C Y).mapDerivedCategory.obj Q
  have hc := comparisonCompatible_transport
    (T := Etale.derivedTensor C Y) (U := Etale.derivedTensor C X)
    (T' := derivedTensor C Y) (U' := derivedTensor C X)
    (leftDerivedComparisonUpperStarCompUpperStarIso C f)
    (comparisonUpperStar C Y).leftDerivedFunctorIsoMapDerivedCategory
    (comparisonUpperStar C X).leftDerivedFunctorIsoMapDerivedCategory
    (Etale.leftDerivedUpperStarTensorComparison C f)
    (leftDerivedUpperStarTensorComparison C f)
    (asIso (comparisonUpperStar C X).leftDerivedTensorComparison)
    (asIso (comparisonUpperStar C Y).leftDerivedTensorComparison)
    (comparisonCompatible_leftDerivedComparisonUpperStarCompUpperStarIso C f)
  rw [← sp_pullback_square C f] at hc
  have ht := Adjunction.map_rightAdjointProjectionMap_comp_mateEquiv
    (T_C := Etale.derivedTensor C X) (T_D := Etale.derivedTensor C Y)
    (T_C' := derivedTensor C X) (T_D' := derivedTensor C Y)
    (Etale.derivedUpperStarLowerStarAdjunction C f)
    (derivedUpperStarLowerStarAdjunction C f) hc K Q
  change _ ≫ (BoundaryComparison.directImageMate C f).app _ ≫ _ =
    _ ≫ ((derivedTensor C Y).map ((BoundaryComparison.directImageMate C f).app K)).app _ ≫
      ((rightDerivedLowerStarProjectionMap C f).app N).app Q' at ht
  simp only [tensorTransport_app] at ht
  dsimp only [Functor.whiskeringLeft₂, Functor.whiskeringLeft, Functor.whiskeringRight,
    Functor.flip, Functor.comp_obj, Functor.id_obj] at ht
  dsimp only [Etale.rightDerivedLowerStarProjectionMap]
  convert! ht using 1

-- Keep the transport calculation generic in the coefficient category and object.
-- This avoids unfolding concrete derived tensor resolutions during specialization.
private def sp_transportedTargetIso
    (C : Type*) [Category.{u + 1} C] [Abelian C]
    [IsGrothendieckAbelian.{u + 1} C]
    [MonoidalCategory C] [MonoidalPreadditive C] [SymmetricCategory C]
    [MonoidalClosed C] [Abelian.HasFunctorialFlatResolution C]
    [Etale.UpperStarPreservesFlat C] [UpperStarPreservesFlat C]
    [∀ T : Scheme.{u}, (comparisonUpperStar C T).PreservesFlat]
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (K : DerivedCategory (Sheaf X.smallEtaleTopology C))
    (Q : DerivedCategory (Sheaf Y.smallEtaleTopology C)) :=
  (derivedTensorObjCompMapDerivedCategoryComparisonUpperStarIso C K).app
      ((Etale.upperStar C f).leftDerivedFunctor.obj Q) ≪≫
    ((derivedTensor C X).obj
      ((comparisonUpperStar C X).mapDerivedCategory.obj K)).mapIso
      ((BoundaryComparison.pullbackSquare C f).symm.app Q)

private def sp_transportedProjection
    (C : Type*) [Category.{u + 1} C] [Abelian C]
    [IsGrothendieckAbelian.{u + 1} C]
    [MonoidalCategory C] [MonoidalPreadditive C] [SymmetricCategory C]
    [MonoidalClosed C] [Abelian.HasFunctorialFlatResolution C]
    [Etale.UpperStarPreservesFlat C] [UpperStarPreservesFlat C]
    [∀ T : Scheme.{u}, (comparisonUpperStar C T).PreservesFlat]
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (K : DerivedCategory (Sheaf X.smallEtaleTopology C))
    (Q : DerivedCategory (Sheaf Y.smallEtaleTopology C))
    (bK : (comparisonUpperStar C Y).mapDerivedCategory.obj
      ((Etale.lowerStar C f).rightDerivedFunctor.obj K) ≅
      (lowerStar C f).rightDerivedFunctor.obj
        ((comparisonUpperStar C X).mapDerivedCategory.obj K))
    (bH : (comparisonUpperStar C Y).mapDerivedCategory.obj
      ((Etale.lowerStar C f).rightDerivedFunctor.obj
        (((Etale.derivedTensor C X).obj K).obj
          ((Etale.upperStar C f).leftDerivedFunctor.obj Q))) ≅
      (lowerStar C f).rightDerivedFunctor.obj
        ((comparisonUpperStar C X).mapDerivedCategory.obj
          (((Etale.derivedTensor C X).obj K).obj
            ((Etale.upperStar C f).leftDerivedFunctor.obj Q)))) :=
  ((derivedTensor C Y).map bK.inv).app
      ((comparisonUpperStar C Y).mapDerivedCategory.obj Q) ≫
    ((derivedTensorObjCompMapDerivedCategoryComparisonUpperStarIso C
      ((Etale.lowerStar C f).rightDerivedFunctor.obj K)).app Q).inv ≫
    (comparisonUpperStar C Y).mapDerivedCategory.map
      (((Etale.rightDerivedLowerStarProjectionMap C f).app K).app Q) ≫
    bH.hom ≫ (lowerStar C f).rightDerivedFunctor.map
      (sp_transportedTargetIso C f K Q).hom

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem sp_projection_transport
    (C : Type*) [Category.{u + 1} C] [Abelian C]
    [IsGrothendieckAbelian.{u + 1} C]
    [MonoidalCategory C] [MonoidalPreadditive C] [SymmetricCategory C]
    [MonoidalClosed C] [Abelian.HasFunctorialFlatResolution C]
    [Etale.UpperStarPreservesFlat C] [UpperStarPreservesFlat C]
    [∀ T : Scheme.{u}, (comparisonUpperStar C T).PreservesFlat]
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (K : DerivedCategory (Sheaf X.smallEtaleTopology C))
    (Q : DerivedCategory (Sheaf Y.smallEtaleTopology C))
    (bK : (comparisonUpperStar C Y).mapDerivedCategory.obj
      ((Etale.lowerStar C f).rightDerivedFunctor.obj K) ≅
      (lowerStar C f).rightDerivedFunctor.obj
        ((comparisonUpperStar C X).mapDerivedCategory.obj K))
    (bH : (comparisonUpperStar C Y).mapDerivedCategory.obj
      ((Etale.lowerStar C f).rightDerivedFunctor.obj
        (((Etale.derivedTensor C X).obj K).obj
          ((Etale.upperStar C f).leftDerivedFunctor.obj Q))) ≅
      (lowerStar C f).rightDerivedFunctor.obj
        ((comparisonUpperStar C X).mapDerivedCategory.obj
          (((Etale.derivedTensor C X).obj K).obj
            ((Etale.upperStar C f).leftDerivedFunctor.obj Q))))
    (hbK : bK.hom = (BoundaryComparison.directImageMate C f).app K)
    (hbH : bH.hom = (BoundaryComparison.directImageMate C f).app
      (((Etale.derivedTensor C X).obj K).obj
        ((Etale.upperStar C f).leftDerivedFunctor.obj Q))) :
    (leftDerivedUpperStarTensorIso C f
      ((lowerStar C f).rightDerivedFunctor.obj
        ((comparisonUpperStar C X).mapDerivedCategory.obj K))
      ((comparisonUpperStar C Y).mapDerivedCategory.obj Q)).inv ≫
      ((derivedUpperStarLowerStarAdjunction C f).homEquiv
        (((derivedTensor C Y).obj ((lowerStar C f).rightDerivedFunctor.obj
          ((comparisonUpperStar C X).mapDerivedCategory.obj K))).obj
            ((comparisonUpperStar C Y).mapDerivedCategory.obj Q))
        (((derivedTensor C X).obj
          ((comparisonUpperStar C X).mapDerivedCategory.obj K)).obj
          ((upperStar C f).leftDerivedFunctor.obj
            ((comparisonUpperStar C Y).mapDerivedCategory.obj Q)))).symm
        (sp_transportedProjection C f K Q bK bH) =
      ((derivedTensor C X).map
        ((derivedUpperStarLowerStarAdjunction C f).counit.app
          ((comparisonUpperStar C X).mapDerivedCategory.obj K))).app
        ((upperStar C f).leftDerivedFunctor.obj
          ((comparisonUpperStar C Y).mapDerivedCategory.obj Q)) ∧
      (IsIso (((Etale.rightDerivedLowerStarProjectionMap C f).app K).app Q) →
        IsIso (sp_transportedProjection C f K Q bK bH)) := by
  let N := (comparisonUpperStar C X).mapDerivedCategory.obj K
  let Q' := (comparisonUpperStar C Y).mapDerivedCategory.obj Q
  have ht := sp_projection_square C f K Q
  conv at ht =>
    rhs
    rw [← hbK]
  conv at ht =>
    lhs
    arg 2
    arg 1
    rw [← hbH]
  let si := (derivedTensorObjCompMapDerivedCategoryComparisonUpperStarIso C
    ((Etale.lowerStar C f).rightDerivedFunctor.obj K)).app Q
  let bi := ((derivedTensor C Y).mapIso bK).app Q'
  change _ = si.hom ≫ bi.hom ≫ _ at ht
  rw [← Iso.inv_comp_eq, ← Iso.inv_comp_eq] at ht
  have heq : sp_transportedProjection C f K Q bK bH =
      ((rightDerivedLowerStarProjectionMap C f).app N).app Q' := by
    dsimp only [sp_transportedProjection, sp_transportedTargetIso, Iso.trans_hom,
      Functor.mapIso_hom, Iso.app_hom, Iso.app_inv, Iso.symm_hom,
      Etale.rightDerivedLowerStarProjectionMap]
    dsimp only [bi, si, Functor.mapIso_inv, Iso.app_inv, Iso.app_hom, N, Q'] at ht
    convert! ht using 1
  constructor
  · have he := congrArg
      (fun m ↦ (leftDerivedUpperStarTensorIso C f
          ((lowerStar C f).rightDerivedFunctor.obj N) Q').inv ≫
        ((derivedUpperStarLowerStarAdjunction C f).homEquiv
          (((derivedTensor C Y).obj ((lowerStar C f).rightDerivedFunctor.obj N)).obj Q')
          (((derivedTensor C X).obj N).obj
            ((upperStar C f).leftDerivedFunctor.obj Q'))).symm m) heq
    exact he.trans (sp_projection_transpose C f N Q')
  · intro hpi
    have := hpi
    dsimp only [sp_transportedProjection]
    infer_instance

attribute [local irreducible] MonoidalCategory.curriedTensor

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in

-- Specialize the projection square without unfolding K-flat resolutions.
/-- The normalized transpose of the transported etale projection is the pro-etale
counit tensored with the coefficient identity. Invertibility of pi_K implies that of t.
Source: blueprint main-20261015, direct-image proof, Step 1; Stacks 0E48 and 07A4
(blueprint: lem-sp-direct-image-etale-mate-isomorphism).

Proof (the four steps of the node):
1. Include the normalized bounded-below comparison and its counit equation into
   the unbounded categories. Adjoint transposition identifies its components
   with BoundaryComparison.directImageMate at K and H.
2. Transport the existing tensor compatibility for left-derived site comparisons
   along their exact-functor comparison isomorphisms. Apply the proved categorical
   projection/mate square (lem-sp-categorical-projection-mate-square). Its tensor
   components are the canonical fixed-coefficient comparison isomorphisms.
3. Cancel the tensor comparison and beta_K tensor identity in this square. This
   identifies spEtaleMate with the pro-etale projection map. Its transpose is the
   pullback tensor comparison followed by counit tensor identity; cancel the
   former comparison to obtain the stated normalized transpose.
4. If pi_K is invertible, every factor defining spEtaleMate is invertible.
   Functorial preservation of isomorphisms proves the second conclusion. -/
theorem spEtaleMate_transpose (ℓ p : ℕ) (_hℓ : ℓ.Prime)
    (k : Type u) [Field k] [CharP k p] (_hp : 0 < p) (_hne : p ≠ ℓ)
    {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (_hA : ∃ n : ℕ, (ℓ : A) ^ n = 0) (_hB : ∃ n : ℕ, (ℓ : B) ^ n = 0)
    (a : A →+* B) {X Y : Scheme.{u}}
    [X.Over (Spec (.of k))]
    [Y.Over (Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))]
    [IsSeparated (Y ↘ Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of k))] [IsProper f]
    (K : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)))
    (hK : ∃ n : ℤ, K.IsGE n)
    (hH : ∃ n : ℤ, (spEtaleTensorObject a f K).IsGE n) :
    (leftDerivedUpperStarTensorIso (ModuleCat.{u + 1} A) f
      ((lowerStar (ModuleCat.{u + 1} A) f).rightDerivedFunctor.obj
        ((comparisonUpperStar (ModuleCat.{u + 1} A) X).mapDerivedCategory.obj K))
      ((comparisonUpperStar (ModuleCat.{u + 1} A) Y).mapDerivedCategory.obj
        (spEtaleCoefficient a Y))).inv ≫
      ((derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) f).homEquiv
        (spEtaleMateSource a f K) (spEtaleMateTarget a f K)).symm
          (spEtaleMate a f K hK hH) =
      ((derivedTensor (ModuleCat.{u + 1} A) X).map
        ((derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) f).counit.app
          ((comparisonUpperStar (ModuleCat.{u + 1} A) X).mapDerivedCategory.obj K))).app
        ((upperStar (ModuleCat.{u + 1} A) f).leftDerivedFunctor.obj
          ((comparisonUpperStar (ModuleCat.{u + 1} A) Y).mapDerivedCategory.obj
            (spEtaleCoefficient a Y))) ∧
    (IsIso (spEtaleProjection a f K) → IsIso (spEtaleMate a f K hK hH)) := by
  have h := sp_projection_transport (ModuleCat.{u + 1} A) f K (spEtaleCoefficient a Y)
    (spDirectImageComparisonIso A f K hK)
    (spDirectImageComparisonIso A f (spEtaleTensorObject a f K) hH)
    (sp_comparison_hom A f K hK)
    (sp_comparison_hom A f (spEtaleTensorObject a f K) hH)
  dsimp only [sp_transportedProjection, sp_transportedTargetIso] at h
  dsimp only [spEtaleMate, spEtaleMateTargetIso, spEtaleMateSource, spEtaleMateTarget,
    spEtaleProjection]
  convert! h using 1

end AlgebraicGeometry.ProEtale
