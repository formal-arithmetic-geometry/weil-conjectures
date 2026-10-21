/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q70
-/
module

public import Sheaf.Paper.FiniteRingCompactSupportProjectionMap


import Sheaf.Paper.FiniteRingConstructibleDerivedOrigin
import WeilConjectures.SixFunctors.Etale.Derived.Kunneth.ProperProjectionFormula
import Sheaf.AlgebraicGeometry.UnboundedDirectImageComparison

import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LowerStarProjComparison
import WeilConjectures.SixFunctors.ProEtale.Comparison.Flat

/-!
# Compact-support projection with arbitrary finite primary coefficients

Source: Weil blueprint, main-20261015, sec-smooth-purity/sk-lem-sp-reduction,
`sk-lem-sp-reduction-compatibilities.proof.md`, Proof (3); Stacks Project, Tag 0F0G
(blueprint: lem-sp-finite-ring-compact-support-projection).

The canonical coefficient realization changes only the presentation of module sheaves.
The projection arrow below is the published counit-defined compactification projection
transported by that realization, on the ordinary unbounded intrinsic derived categories.
-/

@[expose] public section

set_option autoImplicit false
set_option backward.proofsInPublic true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

attribute [local instance 2000] CommRing.toRing
attribute [local instance 2000] isNoetherian_of_finite

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor

namespace AlgebraicGeometry.Scheme

attribute [local instance 10000] finiteProjection_groupW finiteProjection_groupSheafify
  finiteProjection_moduleSheafify finiteProjection_sheafGroth finiteProjection_functorLimits
  finiteProjection_functorColimits finiteProjection_inverseAdditive finiteProjection_inverseLimits
  finiteProjection_inverseColimits finiteProjection_moduleGroth finiteProjection_modulePreadditive
  finiteProjection_moduleFlat finiteProjection_upperFlat

private theorem etaleGroupW {X : Scheme.{u}} :
    X.smallEtaleTopology.WEqualsLocallyBijective AddCommGrpCat.{u + 1} := inferInstance

private theorem etaleGroupSheafify {X : Scheme.{u}} :
    HasSheafify X.smallEtaleTopology AddCommGrpCat.{u + 1} := inferInstance

private theorem etaleModuleSheafify (R : Type u) [CommRing R] {X : Scheme.{u}} :
    HasSheafify X.smallEtaleTopology
      (ModuleCat.{u + 1} (ULift.{u + 1, u} R)) := inferInstance

private theorem etaleSheafGroth (R : Type u) [CommRing R] {X : Scheme.{u}} :
    IsGrothendieckAbelian.{u + 1}
      (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1, u} R))) := inferInstance

private theorem etalePullbackFlat (R : Type u) [CommRing R] [Finite R] :
    Etale.UpperStarPreservesFlat
      (ModuleCat.{u + 1} (ULift.{u + 1, u} R)) := inferInstance

private theorem comparisonFlat (R : Type u) [CommRing R] [Finite R] (X : Scheme.{u}) :
    (ProEtale.comparisonUpperStar
      (ModuleCat.{u + 1} (ULift.{u + 1, u} R)) X).PreservesFlat := inferInstance

attribute [local instance 10000] etaleGroupW etaleGroupSheafify etaleModuleSheafify
  etaleSheafGroth etalePullbackFlat comparisonFlat

private theorem mate_change_left
    {C D C' D' : Type*} [Category C] [Category D] [Category C'] [Category D']
    {F H : D ⥤ C} {G : C ⥤ D} {F' H' : D' ⥤ C'} {G' : C' ⥤ D'}
    (adj : F ⊣ G) (adj' : F' ⊣ G') (ah : H ⊣ G) (ah' : H' ⊣ G')
    {N : D ⥤ D'} {P : C ⥤ C'} (e : F ≅ H) (e' : F' ≅ H')
    (a : N ⋙ F' ≅ F ⋙ P) (M : C)
    (h : IsIso ((mateEquiv ah ah'
      (isoWhiskerLeft N e'.symm ≪≫ a ≪≫ isoWhiskerRight e P).hom).app M)) :
    IsIso ((mateEquiv adj adj' a.hom).app M) := by
  have h1 := conjugateEquiv_mateEquiv_vcomp ah adj adj' e.hom a.hom
  have h2 := mateEquiv_conjugateEquiv_vcomp ah adj' ah'
    (TwoSquare.whiskerLeft a.hom e.hom) e'.inv
  have : IsIso (conjugateEquiv ah adj e.hom) := inferInstance
  have : IsIso (conjugateEquiv adj' ah' e'.inv) := inferInstance
  have hh := congrArg (fun z ↦ z.app M) h2
  rw [h1] at hh
  simp only [TwoSquare.whiskerTop_app, TwoSquare.whiskerBottom_app,
    Category.assoc] at hh
  change _ = N.map ((conjugateEquiv ah adj e.hom).app M) ≫
    (mateEquiv adj adj' a.hom).app M ≫
      (conjugateEquiv adj' ah' e'.inv).app (P.obj M) at hh
  have ht : IsIso (N.map ((conjugateEquiv ah adj e.hom).app M) ≫
      (mateEquiv adj adj' a.hom).app M ≫
        (conjugateEquiv adj' ah' e'.inv).app (P.obj M)) := by
    rw [← hh]
    exact h
  have hi := IsIso.of_isIso_comp_left
    (N.map ((conjugateEquiv ah adj e.hom).app M))
    ((mateEquiv adj adj' a.hom).app M ≫
      (conjugateEquiv adj' ah' e'.inv).app (P.obj M))
  exact IsIso.of_isIso_comp_right _
    ((conjugateEquiv adj' ah' e'.inv).app (P.obj M))

private theorem mate_change_horizontal
    {C D C' D' : Type*} [Category C] [Category D] [Category C'] [Category D']
    {F : D ⥤ C} {G : C ⥤ D} {F' : D' ⥤ C'} {G' : C' ⥤ D'}
    (adj : F ⊣ G) (adj' : F' ⊣ G')
    {N N' : D ⥤ D'} {P P' : C ⥤ C'} (e : N ≅ N') (d : P ≅ P')
    (a : N ⋙ F' ≅ F ⋙ P) (M : C)
    (h : IsIso ((mateEquiv adj adj'
      (isoWhiskerRight e.symm F' ≪≫ a ≪≫ isoWhiskerLeft F d).hom).app M)) :
    IsIso ((mateEquiv adj adj' a.hom).app M) := by
  have hh : (mateEquiv adj adj'
        (isoWhiskerRight e.symm F' ≪≫ a ≪≫ isoWhiskerLeft F d).hom).app M =
      e.inv.app (G.obj M) ≫ (mateEquiv adj adj' a.hom).app M ≫ G'.map (d.hom.app M) := by
    apply (adj'.homEquiv _ _).symm.injective
    simp only [Adjunction.homEquiv_counit, Functor.map_comp, Category.assoc]
    rw [adj'.counit_naturality]
    rw [mateEquiv_counit, reassoc_of% (mateEquiv_counit adj adj' a.hom)]
    simp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
      isoWhiskerRight_hom, isoWhiskerLeft_hom, Functor.whiskerRight_app,
      Functor.whiskerLeft_app]
    simp only [Category.assoc]
    rw [← d.hom.naturality]
    rfl
  have : IsIso (e.inv.app (G.obj M) ≫
      (mateEquiv adj adj' a.hom).app M ≫ G'.map (d.hom.app M)) := by
    rw [← hh]
    exact h
  have := IsIso.of_isIso_comp_left (e.inv.app (G.obj M))
    ((mateEquiv adj adj' a.hom).app M ≫ G'.map (d.hom.app M))
  exact IsIso.of_isIso_comp_right _ (G'.map (d.hom.app M))

private theorem mate_eq_homEquiv
    {C D C' D' : Type*} [Category C] [Category D] [Category C'] [Category D']
    {F : D ⥤ C} {G : C ⥤ D} {F' : D' ⥤ C'} {G' : C' ⥤ D'}
    (adj : F ⊣ G) (adj' : F' ⊣ G') {N : D ⥤ D'} {P : C ⥤ C'}
    (a : N ⋙ F' ⟶ F ⋙ P) (M : C) :
    (mateEquiv adj adj' a).app M =
      adj'.homEquiv _ _ (a.app (G.obj M) ≫ P.map (adj.counit.app M)) := by
  apply (adj'.homEquiv _ _).symm.injective
  simp only [Functor.comp_obj, Functor.id_obj, Equiv.symm_apply_apply,
    Adjunction.homEquiv_counit]
  exact mateEquiv_counit adj adj' a M

private theorem comparisonPullback_transport
    (C : Type*) [Category.{u + 1} C] [Abelian C] [IsGrothendieckAbelian.{u + 1} C]
    [MonoidalCategory C] [MonoidalPreadditive C] [SymmetricCategory C] [MonoidalClosed C]
    [Abelian.HasFunctorialFlatResolution C]
    {X Y : Scheme.{u}} (g : X ⟶ Y) :
    Functor.isoWhiskerLeft
        (ProEtale.comparisonUpperStar C Y).mapDerivedCategory
        (ProEtale.upperStar C g).leftDerivedFunctorIsoMapDerivedCategory.symm ≪≫
      (Functor.isoWhiskerRight
          (ProEtale.comparisonUpperStar C Y).leftDerivedFunctorIsoMapDerivedCategory.symm
          (ProEtale.upperStar C g).leftDerivedFunctor ≪≫
        ProEtale.leftDerivedComparisonUpperStarCompUpperStarIso C g ≪≫
        Functor.isoWhiskerLeft (Etale.upperStar C g).leftDerivedFunctor
          (ProEtale.comparisonUpperStar C X).leftDerivedFunctorIsoMapDerivedCategory) ≪≫
      Functor.isoWhiskerRight (Etale.upperStar C g).leftDerivedFunctorIsoMapDerivedCategory
        (ProEtale.comparisonUpperStar C X).mapDerivedCategory =
    (Functor.mapDerivedCategoryCompIso
        (ProEtale.comparisonUpperStar C Y) (ProEtale.upperStar C g)).symm ≪≫
      Functor.mapDerivedCategoryNatIso
        (ProEtale.comparisonUpperStarCompUpperStarIso C g) ≪≫
      Functor.mapDerivedCategoryCompIso
        (Etale.upperStar C g) (ProEtale.comparisonUpperStar C X) := by
  ext J
  simp [ProEtale.leftDerivedComparisonUpperStarCompUpperStarIso,
    Functor.leftDerivedFunctorCompNatIso, Functor.leftDerivedFunctorCompIso,
    Functor.leftDerivedFunctorNatIso]

private theorem isIso_comparisonMate_of_mapDerived
    (C : Type*) [Category.{u + 1} C] [Abelian C] [IsGrothendieckAbelian.{u + 1} C]
    [MonoidalCategory C] [MonoidalPreadditive C] [SymmetricCategory C] [MonoidalClosed C]
    [Abelian.HasFunctorialFlatResolution C]
    {X Y : Scheme.{u}} (g : X ⟶ Y)
    (E : DerivedCategory (Sheaf X.smallEtaleTopology C))
    (h : IsIso ((mateEquiv
      (Etale.upperStarLowerStarAdjunction C g).mapDerivedCategoryRightDerivedAdjunction
      (ProEtale.upperStarLowerStarAdjunction C g).mapDerivedCategoryRightDerivedAdjunction
      ((Functor.mapDerivedCategoryCompIso
          (ProEtale.comparisonUpperStar C Y) (ProEtale.upperStar C g)).symm ≪≫
        Functor.mapDerivedCategoryNatIso (ProEtale.comparisonUpperStarCompUpperStarIso C g) ≪≫
        Functor.mapDerivedCategoryCompIso
          (Etale.upperStar C g) (ProEtale.comparisonUpperStar C X)).hom).app E)) :
    IsIso ((mateEquiv (Etale.derivedUpperStarLowerStarAdjunction C g)
      (ProEtale.derivedUpperStarLowerStarAdjunction C g)
      (ProEtale.leftDerivedComparisonUpperStarCompUpperStarIso
        C g).hom).app E) := by
  let e := (ProEtale.comparisonUpperStar C Y).leftDerivedFunctorIsoMapDerivedCategory
  let d := (ProEtale.comparisonUpperStar C X).leftDerivedFunctorIsoMapDerivedCategory
  let a := ProEtale.leftDerivedComparisonUpperStarCompUpperStarIso C g
  let b := Functor.isoWhiskerRight e.symm (ProEtale.upperStar C g).leftDerivedFunctor ≪≫
    a ≪≫ Functor.isoWhiskerLeft (Etale.upperStar C g).leftDerivedFunctor d
  refine mate_change_horizontal
    (Etale.derivedUpperStarLowerStarAdjunction C g)
    (ProEtale.derivedUpperStarLowerStarAdjunction C g) e d a E ?_
  refine mate_change_left
    (Etale.derivedUpperStarLowerStarAdjunction C g)
    (ProEtale.derivedUpperStarLowerStarAdjunction C g)
    (Etale.upperStarLowerStarAdjunction C g).mapDerivedCategoryRightDerivedAdjunction
    (ProEtale.upperStarLowerStarAdjunction C g).mapDerivedCategoryRightDerivedAdjunction
    (Etale.upperStar C g).leftDerivedFunctorIsoMapDerivedCategory
    (ProEtale.upperStar C g).leftDerivedFunctorIsoMapDerivedCategory b E ?_
  dsimp only [b, a, e, d]
  rw [comparisonPullback_transport]
  exact h

private theorem isIso_comparisonMate_of_unbounded
    (R : Type u) [CommRing R] [Finite R]
    {X Y : Scheme.{u}} (g : X ⟶ Y)
    (E : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1, u} R))))
    (h : IsIso (ProEtale.unboundedDirectImageComparisonMap (ULift.{u + 1, u} R) g E)) :
    IsIso ((mateEquiv (Etale.derivedUpperStarLowerStarAdjunction
      (ModuleCat.{u + 1} (ULift.{u + 1, u} R)) g)
      (ProEtale.derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} (ULift.{u + 1, u} R)) g)
      (ProEtale.leftDerivedComparisonUpperStarCompUpperStarIso
        (ModuleCat.{u + 1} (ULift.{u + 1, u} R)) g).hom).app E) := by
  apply isIso_comparisonMate_of_mapDerived (ModuleCat.{u + 1} (ULift.{u + 1, u} R)) g E
  rw [mate_eq_homEquiv]
  exact h

private theorem isIso_projection_of_comparisonMates
    (A : Type*) [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
    [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
    [Abelian.HasFunctorialFlatResolution A]
    [Etale.UpperStarPreservesFlat A] [ProEtale.UpperStarPreservesFlat A]
    [∀ T : Scheme.{u}, (ProEtale.comparisonUpperStar A T).PreservesFlat]
    {X Y : Scheme.{u}} (g : X ⟶ Y)
    (E : DerivedCategory (Sheaf X.smallEtaleTopology A))
    (K : DerivedCategory (Sheaf Y.smallEtaleTopology A))
    (hE : IsIso ((mateEquiv (Etale.derivedUpperStarLowerStarAdjunction A g)
      (ProEtale.derivedUpperStarLowerStarAdjunction A g)
      (ProEtale.leftDerivedComparisonUpperStarCompUpperStarIso A g).hom).app E))
    (hH : IsIso ((mateEquiv (Etale.derivedUpperStarLowerStarAdjunction A g)
      (ProEtale.derivedUpperStarLowerStarAdjunction A g)
      (ProEtale.leftDerivedComparisonUpperStarCompUpperStarIso A g).hom).app
        (((Etale.derivedTensor A X).obj E).obj
          ((Etale.upperStar A g).leftDerivedFunctor.obj K))))
    (hp : IsIso (((Etale.rightDerivedLowerStarProjectionMap A g).app E).app K)) :
    IsIso (((ProEtale.rightDerivedLowerStarProjectionMap A g).app
      ((ProEtale.comparisonUpperStar A X).leftDerivedFunctor.obj E)).app
        ((ProEtale.comparisonUpperStar A Y).leftDerivedFunctor.obj K)) := by
  have := hE
  have := hH
  have : IsIso ((((Etale.derivedUpperStarLowerStarAdjunction A g).rightAdjointProjectionMap
      (Etale.leftDerivedUpperStarTensorComparison A g)).app E).app K) := hp
  exact Adjunction.isIso_rightAdjointProjectionMap_of_mateEquiv
    (Etale.derivedUpperStarLowerStarAdjunction A g)
    (ProEtale.derivedUpperStarLowerStarAdjunction A g)
    (ProEtale.comparisonCompatible_leftDerivedComparisonUpperStarCompUpperStarIso A g) E K

private theorem isIso_projection_of_allComparisonMates
    (A : Type*) [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
    [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
    [Abelian.HasFunctorialFlatResolution A]
    [Etale.UpperStarPreservesFlat A] [ProEtale.UpperStarPreservesFlat A]
    [∀ T : Scheme.{u}, (ProEtale.comparisonUpperStar A T).PreservesFlat]
    {X Y : Scheme.{u}} (g : X ⟶ Y)
    (E : DerivedCategory (Sheaf X.smallEtaleTopology A))
    (K : DerivedCategory (Sheaf Y.smallEtaleTopology A))
    (hcomp : ∀ J : DerivedCategory (Sheaf X.smallEtaleTopology A),
      IsIso ((mateEquiv (Etale.derivedUpperStarLowerStarAdjunction A g)
        (ProEtale.derivedUpperStarLowerStarAdjunction A g)
        (ProEtale.leftDerivedComparisonUpperStarCompUpperStarIso A g).hom).app J))
    (hp : IsIso (((Etale.rightDerivedLowerStarProjectionMap A g).app E).app K)) :
    IsIso (((ProEtale.rightDerivedLowerStarProjectionMap A g).app
      ((ProEtale.comparisonUpperStar A X).leftDerivedFunctor.obj E)).app
        ((ProEtale.comparisonUpperStar A Y).leftDerivedFunctor.obj K)) := by
  exact isIso_projection_of_comparisonMates A g E K (hcomp E) (hcomp _) hp

private theorem isIso_projection_of_allComparisonMates_fixed
    (R : Type u) [CommRing R] [Finite R]
    {X Y : Scheme.{u}} (g : X ⟶ Y)
    (E : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1, u} R))))
    (K : DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1, u} R))))
    (hcomp : ∀ J : DerivedCategory
      (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1, u} R))),
      IsIso ((mateEquiv (Etale.derivedUpperStarLowerStarAdjunction
        (ModuleCat.{u + 1} (ULift.{u + 1, u} R)) g)
        (ProEtale.derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} (ULift.{u + 1, u} R)) g)
        (ProEtale.leftDerivedComparisonUpperStarCompUpperStarIso
          (ModuleCat.{u + 1} (ULift.{u + 1, u} R)) g).hom).app J))
    (hp : IsIso (((Etale.rightDerivedLowerStarProjectionMap
      (ModuleCat.{u + 1} (ULift.{u + 1, u} R)) g).app E).app K)) :
    IsIso (((ProEtale.rightDerivedLowerStarProjectionMap
      (ModuleCat.{u + 1} (ULift.{u + 1, u} R)) g).app
      ((ProEtale.comparisonUpperStar
        (ModuleCat.{u + 1} (ULift.{u + 1, u} R)) X).leftDerivedFunctor.obj E)).app
        ((ProEtale.comparisonUpperStar
          (ModuleCat.{u + 1} (ULift.{u + 1, u} R)) Y).leftDerivedFunctor.obj K)) := by
  exact isIso_projection_of_allComparisonMates
    (ModuleCat.{u + 1} (ULift.{u + 1, u} R)) g E K hcomp hp

attribute [local irreducible] Etale.rightDerivedLowerStarProjectionMap
  ProEtale.rightDerivedLowerStarProjectionMap ProEtale.unboundedDirectImageComparisonMap
  Etale.derivedTensor ProEtale.derivedTensor

private theorem isIso_properProjection_of_unboundedComparison
    (k : Type u) [Field k] [IsAlgClosed k]
    (l : ℕ) [Fact l.Prime] (hl : IsUnit (algebraMap ℤ k (l : ℤ)))
    (R : Type u) [CommRing R] [Finite R]
    (hR : ∃ n : ℕ, (l : ULift.{u + 1, u} R) ^ n = 0)
    {X Y : Scheme.{u}}
    [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
    (g : X ⟶ Y) [IsProper g]
    (E : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1, u} R))))
    (K : DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1, u} R)))) :
    IsIso (((ProEtale.rightDerivedLowerStarProjectionMap
      (ModuleCat.{u + 1} (ULift.{u + 1, u} R)) g).app
      ((ProEtale.comparisonUpperStar
        (ModuleCat.{u + 1} (ULift.{u + 1, u} R)) X).mapDerivedCategory.obj E)).app
      ((ProEtale.comparisonUpperStar
        (ModuleCat.{u + 1} (ULift.{u + 1, u} R)) Y).mapDerivedCategory.obj K)) := by
  have hp : IsIso (((ProEtale.rightDerivedLowerStarProjectionMap
      (ModuleCat.{u + 1} (ULift.{u + 1, u} R)) g).app
      ((ProEtale.comparisonUpperStar
        (ModuleCat.{u + 1} (ULift.{u + 1, u} R)) X).leftDerivedFunctor.obj E)).app
      ((ProEtale.comparisonUpperStar
        (ModuleCat.{u + 1} (ULift.{u + 1, u} R)) Y).leftDerivedFunctor.obj K)) := by
    apply isIso_projection_of_allComparisonMates_fixed R g E K
    · intro J
      apply isIso_comparisonMate_of_unbounded R g
      exact ProEtale.unboundedDirectImageComparison k (Or.inr inferInstance) hl
        (ULift.{u + 1, u} R) hR g J
    · have := Etale.isIso_rightDerivedLowerStarProjectionMap_of_isProper
        (ULift.{u + 1, u} R) isAddTorsion_of_finite g
      infer_instance
  exact NatTrans.isIso_app_app_of_iso
    (ProEtale.rightDerivedLowerStarProjectionMap
      (ModuleCat.{u + 1} (ULift.{u + 1, u} R)) g)
    ((ProEtale.comparisonUpperStar
      (ModuleCat.{u + 1} (ULift.{u + 1, u} R)) X).leftDerivedFunctorIsoMapDerivedCategory.app E)
    ((ProEtale.comparisonUpperStar
      (ModuleCat.{u + 1} (ULift.{u + 1, u} R)) Y).leftDerivedFunctorIsoMapDerivedCategory.app K)

private noncomputable def inverse_realization_origin
    {A B C : Type*} [Category A] [Category B] [Category C]
    [Abelian A] [Abelian B] [Abelian C]
    [HasDerivedCategory A] [HasDerivedCategory B] [HasDerivedCategory C]
    (e : B ≌ C) [e.functor.Additive] [e.inverse.Additive]
    (F : A ⥤ B) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (E : DerivedCategory A) (M : DerivedCategory C)
    (h : (F ⋙ e.functor).mapDerivedCategory.obj E ≅ M) :
    F.mapDerivedCategory.obj E ≅ e.inverse.mapDerivedCategory.obj M :=
  e.mapDerivedCategory.unitIso.app (F.mapDerivedCategory.obj E) ≪≫
    e.inverse.mapDerivedCategory.mapIso
      ((Functor.mapDerivedCategoryCompIso F e.functor).symm.app E ≪≫ h)

private noncomputable def realization_origin_iso
    (X : Scheme.{u}) (R : Type u) [CommRing R] [Finite R]
    (E : DerivedCategory (Sheaf X.smallEtaleTopology
      (ModuleCat.{u + 1} (ULift.{u + 1, u} R))))
    (M : proEtaleDerivedCategory X R)
    (h : (ProEtale.finiteCoefficientIntrinsicDerivedComparison X R).obj E ≅ M) :
    (ProEtale.comparisonUpperStar
      (ModuleCat.{u + 1} (ULift.{u + 1, u} R)) X).mapDerivedCategory.obj E ≅
      (sfIntrinsicModuleEquivalence X R).inverse.mapDerivedCategory.obj M := by
  apply inverse_realization_origin (sfIntrinsicModuleEquivalence X R)
    (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} R)) X) E M
  simpa only [sfIntrinsicModuleEquivalence,
    ProEtale.finiteCoefficientIntrinsicDerivedComparison,
    ProEtale.finiteCoefficientIntrinsicComparison, Functor.asEquivalence_functor] using h

private theorem exists_fixed_origin
    (X : Scheme.{u}) (R : Type u) [CommRing R] [Finite R]
    (M : proEtaleDerivedCategory X R)
    (h : (ObjectProperty.ι (Etale.DerivedCategory.isBoundedConstructible
        (ULift.{u + 1, u} R) X) ⋙
      ProEtale.finiteCoefficientIntrinsicDerivedComparison X R).essImage M) :
    ∃ E : DerivedCategory (Sheaf X.smallEtaleTopology
      (ModuleCat.{u + 1} (ULift.{u + 1, u} R))),
      Nonempty ((ProEtale.comparisonUpperStar
        (ModuleCat.{u + 1} (ULift.{u + 1, u} R)) X).mapDerivedCategory.obj E ≅
        (sfIntrinsicModuleEquivalence X R).inverse.mapDerivedCategory.obj M) := by
  obtain ⟨E, ⟨e⟩⟩ := h
  exact ⟨E.obj, ⟨realization_origin_iso X R E.obj M e⟩⟩

attribute [local irreducible] sfIntrinsicModuleEquivalence
  ProEtale.projectionMapOfCompactification

private theorem isIso_compactSupportProjection_of_proper
    (R : Type u) [CommRing R] [Finite R]
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (M : proEtaleDerivedCategory X R) (K : proEtaleDerivedCategory Y R)
    (hp : IsIso (((ProEtale.rightDerivedLowerStarProjectionMap
      (ModuleCat.{u + 1} (ULift.{u + 1, u} R)) c.g).app
      ((ProEtale.openImmersionLowerShriek
        (ModuleCat.{u + 1} (ULift.{u + 1, u} R)) c.i).mapDerivedCategory.obj
        ((sfIntrinsicModuleEquivalence X R).inverse.mapDerivedCategory.obj M))).app
      ((sfIntrinsicModuleEquivalence Y R).inverse.mapDerivedCategory.obj K))) :
    IsIso (((finiteRingCompactSupportProjection R c).app M).app K) := by
  have := hp
  have : IsIso (((ProEtale.projectionMapOfCompactification
      (ModuleCat.{u + 1} (ULift.{u + 1, u} R)) c).app
      ((sfIntrinsicModuleEquivalence X R).inverse.mapDerivedCategory.obj M)).app
      ((sfIntrinsicModuleEquivalence Y R).inverse.mapDerivedCategory.obj K)) := by
    rw [ProEtale.projectionMapOfCompactification_app_app]
    infer_instance
  dsimp only [finiteRingCompactSupportProjection, Functor.postcompose₂,
    Functor.whiskeringLeft₂, Functor.whiskeringRight, Functor.whiskeringLeft,
    Functor.comp_obj, Functor.comp_map, Functor.whiskerLeft, Functor.whiskerRight]
  infer_instance

private theorem finiteField_prime_isUnit
    (D : WeilConjectures.FiniteFieldDatum.{u}) (l : ℕ)
    (hl : l.Prime) (hlp : l ≠ D.p) :
    IsUnit (algebraMap ℤ D.k (l : ℤ)) := by
  let := Fintype.ofFinite D.k₀
  have : Fact D.p.Prime := ⟨D.prime⟩
  have : CharP D.k₀ D.p := charP_of_card_eq_prime_pow
    ((Nat.card_eq_fintype_card (α := D.k₀)).symm.trans
      (D.card_base.trans D.cardinality_eq))
  have : CharP D.k D.p :=
    charP_of_injective_algebraMap (algebraMap D.k₀ D.k).injective D.p
  have hi : IsUnit (l : D.k) :=
    (CharP.isUnit_natCast_iff (R := D.k) D.prime).2
      (fun h ↦ hlp ((Nat.prime_dvd_prime_iff_eq D.prime hl).1 h).symm)
  simpa using hi

attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits

private noncomputable def derived_open_comparison
    (A : Type*) [Category.{u + 1} A] [Abelian A]
    [IsGrothendieckAbelian.{u + 1} A]
    {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] :
    (ProEtale.comparisonUpperStar A U).mapDerivedCategory ⋙
        (ProEtale.openImmersionLowerShriek A j).mapDerivedCategory ≅
      (Etale.openImmersionLowerShriek A j).mapDerivedCategory ⋙
        (ProEtale.comparisonUpperStar A X).mapDerivedCategory :=
  (Functor.mapDerivedCategoryCompIso _ _).symm ≪≫
    Functor.mapDerivedCategoryNatIso
      (ProEtale.openImmersionLowerShriekComparisonUpperStarIso A j).symm ≪≫
    Functor.mapDerivedCategoryCompIso _ _


/-- The canonical compact-support projection is invertible for bounded intrinsically
constructible complexes over every finite primary commutative ring. A compactification
records exactly `j = c.i`, `p = c.g`, `Xbar = c.Z`, and `f = j ≫ p` by `c.comm`.
The coefficient realization is the canonical extension of fixed scalar actions to
locally constant scalar sections; it changes no objects or morphisms mathematically.
Naturality in `M,K` comes from `projectionMapOfCompactification`, a transformation of
bifunctors, and the functors used to transport it.
Source: Weil blueprint, main-20261015, sec-smooth-purity/sk-lem-sp-reduction,
`sk-lem-sp-reduction-compatibilities.proof.md`, Proof (3); Stacks Tag 0F0G
(blueprint: lem-sp-finite-ring-compact-support-projection).

Proof (the node's six steps):
1. By lem-weil-pbc-finite-ring-constructible-derived-origin, choose bounded
   constructible etale origins M0,K0 for M,K, using intrinsic constructibility over
   the given finite ring. No finite Tor amplitude or DVR presentation is required.
2. Put E = j! M0. The exact etale and pro-etale extensions by zero act degreewise
   (lem-weil-pbc-extension-by-zero-exact, lem-cbc-proetale-extension-zero).
   Apply lem-cbc-proetale-extension-zero-comparison in each degree; exactness
   descends it and its inverse to identify the pro-etale realization of E with j! M.
3. Form H = E tensor-derived p* K0 in the unbounded etale category.
   The proved fixed-coefficient derived pullback/tensor comparison identifies its
   realization with the pro-etale tensor and also identifies the source tensor.
   These comparisons apply even if H is unbounded below.
4. The ring is torsion by its primary annihilation hypothesis. Stacks 0F0G
   (lem-kun-0f0g) makes the specified etale proper projection an isomorphism.
   lem-sfb-unbounded-direct-image-comparison applies to E and H: the field is
   algebraically closed, the prime is invertible, and p is finite type between
   finite-type schemes. Its comparison is the canonical derived counit mate.
5. The proved fixed-coefficient mate/projection compatibility for the etale/pro-etale
   square identifies the two projection maps through those comparison isomorphisms.
   No cartesian-square hypothesis is needed. Hence the actual pro-etale proper
   projection is invertible. Naturality transports it to the given M,K.
6. lem-cbc-extension-zero-projection-formula makes the canonical open factor
   invertible on unbounded categories. Proper pushforward preserves its inverse.
   Compose with step 5 and the pullback-composition isomorphism. Every factor
   is natural in both inputs, so the specified composite is natural as well. -/
theorem isIso_finiteRingCompactSupportProjection
    (D : WeilConjectures.FiniteFieldDatum.{u})
    (l : ℕ) (_hl : l.Prime) (_hlp : l ≠ D.p)
    (R : Type u) [CommRing R] [Finite R]
    (n : ℕ) (_hn : 1 ≤ n) (_hR : ∀ r : R, (l ^ n) • r = 0)
    {X Y : Scheme.{u}}
    [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))]
    [IsSeparated (X ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))]
    [QuasiCompact (X ↘ Spec (.of D.k))]
    [IsSeparated (Y ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of D.k))]
    [QuasiCompact (Y ↘ Spec (.of D.k))]
    (f : X ⟶ Y) (c : Compactification f)
    [c.Z.Over (Spec (.of D.k))]
    [IsSeparated (c.Z ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (c.Z ↘ Spec (.of D.k))]
    [QuasiCompact (c.Z ↘ Spec (.of D.k))]
    [c.i.IsOver (Spec (.of D.k))] [c.g.IsOver (Spec (.of D.k))]
    (M : proEtaleDerivedCategory X R) (K : proEtaleDerivedCategory Y R)
    (_hMc : ∀ i : ℤ, IsConstructibleProEtaleModuleSheaf X R
      ((DerivedCategory.homologyFunctor
        (proEtaleRingModules X (proEtaleConstantRing X R)) i).obj M))
    (_hMb : ∃ a b : ℤ, a ≤ b ∧ ∀ i : ℤ, (i < a ∨ b < i) →
      IsZero ((DerivedCategory.homologyFunctor
        (proEtaleRingModules X (proEtaleConstantRing X R)) i).obj M))
    (_hKc : ∀ i : ℤ, IsConstructibleProEtaleModuleSheaf Y R
      ((DerivedCategory.homologyFunctor
        (proEtaleRingModules Y (proEtaleConstantRing Y R)) i).obj K))
    (_hKb : ∃ a b : ℤ, a ≤ b ∧ ∀ i : ℤ, (i < a ∨ b < i) →
      IsZero ((DerivedCategory.homologyFunctor
        (proEtaleRingModules Y (proEtaleConstantRing Y R)) i).obj K)) :
    IsIso (((finiteRingCompactSupportProjection R c).app M).app K) := by
  classical
  -- Keep coefficient types explicit: a local type alias makes kernel conversion expensive.
  obtain ⟨M₀, ⟨eM⟩⟩ := exists_fixed_origin X R M
    (((finiteRing_constructibleDerived_origin X R).2.2.1 M).2 ⟨_hMc, _hMb⟩)
  obtain ⟨K₀, ⟨eK⟩⟩ := exists_fixed_origin Y R K
    (((finiteRing_constructibleDerived_origin Y R).2.2.1 K).2 ⟨_hKc, _hKb⟩)
  let E :=
    (Etale.openImmersionLowerShriek
      (ModuleCat.{u + 1} (ULift.{u + 1, u} R)) c.i).mapDerivedCategory.obj M₀
  have eE : (ProEtale.openImmersionLowerShriek
      (ModuleCat.{u + 1} (ULift.{u + 1, u} R)) c.i).mapDerivedCategory.obj
        ((sfIntrinsicModuleEquivalence X R).inverse.mapDerivedCategory.obj M) ≅
      (ProEtale.comparisonUpperStar
        (ModuleCat.{u + 1} (ULift.{u + 1, u} R)) c.Z).mapDerivedCategory.obj E :=
    (ProEtale.openImmersionLowerShriek
      (ModuleCat.{u + 1} (ULift.{u + 1, u} R)) c.i).mapDerivedCategory.mapIso eM.symm ≪≫
      (derived_open_comparison (ModuleCat.{u + 1} (ULift.{u + 1, u} R)) c.i).app M₀
  have : IsAlgClosed D.k := IsAlgClosure.isAlgClosed D.k₀
  have : Fact l.Prime := ⟨_hl⟩
  have hunit := finiteField_prime_isUnit D l _hl _hlp
  have hA : ∃ n : ℕ, (l : ULift.{u + 1, u} R) ^ n = 0 := by
    refine ⟨n, ?_⟩
    apply ULift.ext
    change (l : R) ^ n = 0
    simpa only [nsmul_eq_mul, Nat.cast_pow, mul_one] using _hR 1
  have := isIso_properProjection_of_unboundedComparison D.k l hunit
    R hA c.g E K₀
  have hi : IsIso (((ProEtale.rightDerivedLowerStarProjectionMap
      (ModuleCat.{u + 1} (ULift.{u + 1, u} R)) c.g).app
      ((ProEtale.openImmersionLowerShriek
        (ModuleCat.{u + 1} (ULift.{u + 1, u} R)) c.i).mapDerivedCategory.obj
        ((sfIntrinsicModuleEquivalence X R).inverse.mapDerivedCategory.obj M))).app
      ((sfIntrinsicModuleEquivalence Y R).inverse.mapDerivedCategory.obj K)) :=
    NatTrans.isIso_app_app_of_iso
      (ProEtale.rightDerivedLowerStarProjectionMap
        (ModuleCat.{u + 1} (ULift.{u + 1, u} R)) c.g) eE.symm eK
  exact isIso_compactSupportProjection_of_proper R c M K hi

end AlgebraicGeometry.Scheme

end
