/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProEtaleAffineLineCounit
public import WeilConjectures.AlgebraicGeometry.OpenProjectionSiteTransport
public import WeilConjectures.AlgebraicGeometry.PurityFiniteSetting
public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FiniteType

import all WeilConjectures.SixFunctors.ComparisonOpenTensorCoherence
import all WeilConjectures.AlgebraicGeometry.GeoP1Cohomology
import all WeilConjectures.AlgebraicGeometry.PurityFiniteSetting
import WeilConjectures.AlgebraicGeometry.SupportedProjectiveChernComparison

/-! # Supported Kummer projective-line trace across sites

Source: Stacks Project, Tags 09AF and 0B65; main-20261015,
sec-six-functors-basics/sk-lem-geo-p1-cohomology/def-amb-p1-trace.md.
(blueprint: lem-pur-p1-kummer-trace-site-transport)
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.VectorIntegrationSite

attribute [local irreducible] Etale.projectiveLineTraceDatum Etale.projectiveLineTraceTransport
  BoundaryComparison.directImageMate ProjectiveSpace.twist Etale.ordinaryFiniteP1ChernSpec
  Etale.ordinaryFiniteShiftedLinePullback Etale.ordinaryFiniteP1Unit
  Etale.ordinaryFiniteP1ChernPushforward

/-- The actual etale derived open counit in left-derived restriction coordinates.
Source: Stacks 09AF; exact-derived-adjunction convention
(blueprint: lem-pur-p1-kummer-trace-site-transport). -/
@[irreducible]
def kummerTraceEtaleOpenCounit (A : Type (u + 1)) [CommRing A]
    {U T : Scheme.{u}} (j : U ⟶ T) [IsOpenImmersion j]
    (K : Etale.DerivedCategoryModule A T) :
    (Etale.openImmersionLowerShriek (ModuleCat.{u + 1} A) j).mapDerivedCategory.obj
      ((Etale.upperStar (ModuleCat.{u + 1} A) j).leftDerivedFunctor.obj K) ⟶ K :=
  ((Etale.derivedOpenImmersionLowerShriekUpperStarAdjunction
    (ModuleCat.{u + 1} A) j).ofNatIsoRight
      (Etale.leftDerivedUpperStarIsoMapDerivedCategory
        (ModuleCat.{u + 1} A) j).symm).counit.app K

/-- The specified source comparison: extension comparison followed by restriction
comparison, both descended termwise with the canonical composition identifications.
Source: Stacks 09AF, 099R
(blueprint: lem-pur-p1-kummer-trace-site-transport). -/
@[irreducible]
def kummerTraceOpenComparison (A : Type (u + 1)) [CommRing A] [Finite A]
    {U T : Scheme.{u}} (j : U ⟶ T) [IsOpenImmersion j]
    (K : Etale.DerivedCategoryModule A T) :
    (comparison A T).obj
      ((Etale.openImmersionLowerShriek (ModuleCat.{u + 1} A) j).mapDerivedCategory.obj
        ((Etale.upperStar (ModuleCat.{u + 1} A) j).leftDerivedFunctor.obj K)) ≅
    (openImmersionLowerShriek (ModuleCat.{u + 1} A) j).mapDerivedCategory.obj
      ((upperStar (ModuleCat.{u + 1} A) j).leftDerivedFunctor.obj
        ((comparison A T).obj K)) :=
  (openProjectionExtensionComparison A j).app _ ≪≫
    (openImmersionLowerShriek (ModuleCat.{u + 1} A) j).mapDerivedCategory.mapIso
      ((openProjectionRestrictionComparison A j).app K)

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra (Padic l) E]
  [FiniteDimensional (Padic l) E] (n : ℕ)

/-- The existing ordinary datum at the positive exponent, using the source-implied
invertibility of its power. This is only an application of the recorded construction.
Source: blueprint def-amb-p1-trace
(blueprint: lem-pur-p1-kummer-trace-site-transport). -/
@[irreducible]
def kummerTraceOrdinaryDatum (S : Scheme.{u}) [IsNoetherian S]
    (hS : IsUnit (l : Γ(S, ⊤))) (r : ℕ)
    (hA : ((l ^ (r + 1) : ℕ) : Scheme.finiteTateCoefficient l E n) = 0) :=
  Etale.projectiveLineTraceDatum (l ^ (r + 1))
    (pow_pos (Fact.out : l.Prime).pos _) (Scheme.finiteTateCoefficient l E n) hA S
    (by simpa only [Nat.cast_pow] using hS.pow (r + 1))

/-- The etale affine-chart counit followed by the prescribed projective trace.
Source: Stacks 09AF and 0B65; blueprint def-amb-p1-trace
(blueprint: lem-pur-p1-kummer-trace-site-transport). -/
@[irreducible]
def kummerTraceEtaleAffine (S : Scheme.{u}) [IsNoetherian S] (hS : IsUnit (l : Γ(S, ⊤))) (r : ℕ)
    (hA : ((l ^ (r + 1) : ℕ) : Scheme.finiteTateCoefficient l E n) = 0) :
    (Etale.ordinaryFinitePushforward (Scheme.finiteTateCoefficient l E n) (ProjectiveLine S ↘
        S)).obj ((Etale.openImmersionLowerShriek (ModuleCat.{u + 1} (Scheme.finiteTateCoefficient l
        E n))
      (ProjectiveLine.affineChart S)).mapDerivedCategory.obj
        ((Etale.upperStar (ModuleCat.{u + 1} (Scheme.finiteTateCoefficient l E n))
          (ProjectiveLine.affineChart S)).leftDerivedFunctor.obj ((Etale.ordinaryFiniteLine
        (Scheme.finiteTateCoefficient l E n) (l ^ (r + 1)) hA
      (ProjectiveLine S))⟦(2 : ℤ)⟧))) ⟶ Etale.ordinaryFiniteUnit (Scheme.finiteTateCoefficient l E
        n) S :=
  (Etale.ordinaryFinitePushforward (Scheme.finiteTateCoefficient l E n) (ProjectiveLine S ↘ S)).map
        (kummerTraceEtaleOpenCounit (Scheme.finiteTateCoefficient l E n) (ProjectiveLine.affineChart
        S) ((Etale.ordinaryFiniteLine (Scheme.finiteTateCoefficient l E n) (l ^ (r + 1)) hA
      (ProjectiveLine S))⟦(2 : ℤ)⟧)) ≫
    (kummerTraceOrdinaryDatum l E n S hS r hA).decomposition.inv ≫ biprod.snd

/-- The pro-etale affine-chart counit followed by the supported projective trace.
Source: Stacks 09AF and 0B65; blueprint def-amb-p1-trace
(blueprint: lem-pur-p1-kummer-trace-site-transport). -/
@[irreducible]
def kummerTraceProAffine (S : Scheme.{u}) [IsNoetherian S] (hS : IsUnit (l : Γ(S, ⊤))) (r : ℕ)
    (hA : ((l ^ (r + 1) : ℕ) : Scheme.finiteTateCoefficient l E n) = 0) :
    (lowerStar (ModuleCat.{u + 1} (Scheme.finiteTateCoefficient l E n))
      (ProjectiveLine S ↘ S)).rightDerivedFunctor.obj ((openImmersionLowerShriek (ModuleCat.{u + 1}
        (Scheme.finiteTateCoefficient l E n))
      (ProjectiveLine.affineChart S)).mapDerivedCategory.obj
        ((upperStar (ModuleCat.{u + 1} (Scheme.finiteTateCoefficient l E n))
          (ProjectiveLine.affineChart S)).leftDerivedFunctor.obj (line l E n r hA (ProjectiveLine
        S)))) ⟶ unit (Scheme.finiteTateCoefficient l E n) S :=
  (lowerStar (ModuleCat.{u + 1} (Scheme.finiteTateCoefficient l E n))
      (ProjectiveLine S ↘ S)).rightDerivedFunctor.map ((openAdjunction (Scheme.finiteTateCoefficient
        l E n) (ProjectiveLine.affineChart S)).counit.app
    (line l E n r hA (ProjectiveLine S))) ≫
      projectiveTrace l E n S hS (infinityCartier S) r hA

/-- The counit mate followed by direct image of the specified open source comparison.
Source: Stacks 09AF and 0B65; blueprint def-amb-p1-trace
(blueprint: lem-pur-p1-kummer-trace-site-transport). -/
@[irreducible]
def kummerTraceAffineComparison (S : Scheme.{u}) (r : ℕ)
    (hA : ((l ^ (r + 1) : ℕ) : Scheme.finiteTateCoefficient l E n) = 0) :
    (comparison (Scheme.finiteTateCoefficient l E n) S).obj ((Etale.ordinaryFinitePushforward
        (Scheme.finiteTateCoefficient l E n) (ProjectiveLine S ↘ S)).obj
        ((Etale.openImmersionLowerShriek (ModuleCat.{u + 1} (Scheme.finiteTateCoefficient l E n))
      (ProjectiveLine.affineChart S)).mapDerivedCategory.obj
        ((Etale.upperStar (ModuleCat.{u + 1} (Scheme.finiteTateCoefficient l E n))
          (ProjectiveLine.affineChart S)).leftDerivedFunctor.obj ((Etale.ordinaryFiniteLine
        (Scheme.finiteTateCoefficient l E n) (l ^ (r + 1)) hA
      (ProjectiveLine S))⟦(2 : ℤ)⟧)))) ⟶
      (lowerStar (ModuleCat.{u + 1} (Scheme.finiteTateCoefficient l E n))
      (ProjectiveLine S ↘ S)).rightDerivedFunctor.obj ((openImmersionLowerShriek (ModuleCat.{u + 1}
        (Scheme.finiteTateCoefficient l E n))
      (ProjectiveLine.affineChart S)).mapDerivedCategory.obj
        ((upperStar (ModuleCat.{u + 1} (Scheme.finiteTateCoefficient l E n))
          (ProjectiveLine.affineChart S)).leftDerivedFunctor.obj (line l E n r hA (ProjectiveLine
        S)))) :=
  geoP1PushComparison (Scheme.finiteTateCoefficient l E n) (ProjectiveLine S ↘ S)
        ((Etale.openImmersionLowerShriek (ModuleCat.{u + 1} (Scheme.finiteTateCoefficient l E n))
      (ProjectiveLine.affineChart S)).mapDerivedCategory.obj
        ((Etale.upperStar (ModuleCat.{u + 1} (Scheme.finiteTateCoefficient l E n))
          (ProjectiveLine.affineChart S)).leftDerivedFunctor.obj ((Etale.ordinaryFiniteLine
        (Scheme.finiteTateCoefficient l E n) (l ^ (r + 1)) hA
      (ProjectiveLine S))⟦(2 : ℤ)⟧))) ≫
    (lowerStar (ModuleCat.{u + 1} (Scheme.finiteTateCoefficient l E n))
      (ProjectiveLine S ↘ S)).rightDerivedFunctor.map (kummerTraceOpenComparison
        (Scheme.finiteTateCoefficient l E n) (ProjectiveLine.affineChart S)
        ((Etale.ordinaryFiniteLine (Scheme.finiteTateCoefficient l E n) (l ^ (r + 1)) hA
      (ProjectiveLine S))⟦(2 : ℤ)⟧)).hom

/-- The projective and affine-chart arrow equations in the specified finite site coordinates.
The canonical mate is evaluated on the bounded shifted line; its affine source is
bounded below by exactness of restriction and extension by zero.
Source: Stacks 09AF and 0B65; blueprint def-amb-p1-trace
(blueprint: lem-pur-p1-kummer-trace-site-transport). -/
def P1KummerTraceTransport (S : Scheme.{u}) [IsNoetherian S]
    (hS : IsUnit (l : Γ(S, ⊤))) (r : ℕ)
    (hA : ((l ^ (r + 1) : ℕ) : Scheme.finiteTateCoefficient l E n) = 0) : Prop :=
  ((comparison (Scheme.finiteTateCoefficient l E n) S).map
    (Etale.ordinaryFiniteP1ChernPushforward (Scheme.finiteTateCoefficient l E n) (l ^ (r + 1))
    hA S (kummerTraceOrdinaryDatum l E n S hS r hA).chern) ≫ (directImage
    (Scheme.finiteTateCoefficient l E n) (ProjectiveLine S ↘ S) (linePlus l E n r hA
    (ProjectiveLine S))).hom = projectiveH l E n S hS (infinityCartier S) r hA) ∧
  ((comparison (Scheme.finiteTateCoefficient l E n) S).map (kummerTraceOrdinaryDatum l E n S hS
    r hA).decomposition.hom ≫ (directImage (Scheme.finiteTateCoefficient l E n) (ProjectiveLine
    S ↘ S) (linePlus l E n r hA (ProjectiveLine S))).hom = projectiveSum l E n r hA S ≫
    projectiveB l E n S hS (infinityCartier S) r hA) ∧
  IsIso (projectiveB l E n S hS (infinityCartier S) r hA) ∧
  ((directImage (Scheme.finiteTateCoefficient l E n) (ProjectiveLine S ↘ S) (linePlus l E n r hA
    (ProjectiveLine S))).hom ≫ projectiveTrace l E n S hS (infinityCartier S) r hA = (comparison
    (Scheme.finiteTateCoefficient l E n) S).map ((kummerTraceOrdinaryDatum l E n S hS r
    hA).decomposition.inv ≫ biprod.snd)) ∧
  (projectiveH l E n S hS (infinityCartier S) r hA ≫ projectiveTrace l E n S hS (infinityCartier
    S) r hA = 𝟙 (unit (Scheme.finiteTateCoefficient l E n) S)) ∧
  (kummerTraceAffineComparison l E n S r hA ≫ kummerTraceProAffine l E n S hS r hA =
    (comparison (Scheme.finiteTateCoefficient l E n) S).map (kummerTraceEtaleAffine l E n S hS r
        hA))

section ProofHelpers

set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

open CategoryTheory.Abelian CategoryTheory.MonoidalCategory
attribute [local irreducible] CategoryTheory.Abelian.Ext
  Localization.SmallHom Localization.SmallShiftedHom
  constantSheaf presheafToSheaf CochainComplex.singleFunctors HomologicalComplex.single
attribute [local irreducible] DerivedCategory _root_.instCategoryDerivedCategory
  HasDerivedCategory.ofIsGrothendieckAbelian
  DerivedCategory.singleFunctors Ext.homEquiv Ext.comp Ext.mk₀ Ext.mapExactFunctor
attribute [local implicit_reducible] Etale.cartierAbelianPro Etale.cartierAbelianEtale
  Etale.cartierAbelianGroups
attribute [local implicit_reducible] Etale.ordinaryFiniteDegreeZero
  Scheme.finiteEtaleTateTwist
attribute [local irreducible] Scheme.finiteEtaleTateLine
attribute [local irreducible] AlgebraicGeometry.ProjectiveSpace AlgebraicGeometry.AffineSpace
attribute [local irreducible] Etale.ordinaryFiniteP1Exchange
  Etale.ordinaryFiniteP1DecompositionSourceMap
  Etale.p1DecompositionMap Etale.p1DecompositionChernAdjoint
  geoP1PushComparison geoP1PullComparison geoP1Trace

private lemma counit_of_unit
    {C D C' D' : Type*} [Category* C] [Category* D] [Category* C'] [Category* D']
    {F : C ⥤ D} {G : D ⥤ C} {F' : C' ⥤ D'} {G' : D' ⥤ C'}
    (a : F ⊣ G) (b : F' ⊣ G') {U : C ⥤ C'} {V : D ⥤ D'}
    (β : U ⋙ F' ⟶ F ⋙ V) (τ : G ⋙ U ⟶ V ⋙ G')
    (h : ∀ K, b.unit.app (U.obj K) ≫ G'.map (β.app K) =
      U.map (a.unit.app K) ≫ τ.app (F.obj K)) (K : D) :
    F'.map (τ.app K) ≫ b.counit.app (V.obj K) = β.app (G.obj K) ≫ V.map (a.counit.app K) := by
  apply (b.homEquiv _ _).injective
  dsimp only [Functor.comp_obj]
  simp only [Adjunction.homEquiv_unit, Functor.map_comp]
  have hn := b.unit.naturality (τ.app K)
  dsimp only [Functor.comp_map, Functor.id_map] at hn
  rw [← reassoc_of% hn, b.right_triangle_components, Category.comp_id]
  rw [reassoc_of% (h (G.obj K))]
  have ht := τ.naturality (a.counit.app K)
  dsimp only [Functor.comp_map, Functor.comp_obj, Functor.id_obj] at ht
  rw [← ht, ← Category.assoc, ← U.map_comp]
  rw [a.right_triangle_components, U.map_id, Category.id_comp]

set_option backward.isDefEq.respectTransparency false in
private theorem open_counit (A : Type (u + 1)) [CommRing A] [Finite A]
    {U T : Scheme.{u}} (j : U ⟶ T) [IsOpenImmersion j]
    (K : Etale.DerivedCategoryModule A T) :
    (comparison A T).map (kummerTraceEtaleOpenCounit A j K) =
      (kummerTraceOpenComparison A j K).hom ≫
        (openAdjunction A j).counit.app ((comparison A T).obj K) := by
  let B := ModuleCat.{u + 1} A
  let e := Etale.derivedOpenImmersionLowerShriekUpperStarAdjunction B j
  let p := derivedOpenImmersionLowerShriekUpperStarAdjunction B j
  let c := (openProjectionExtensionComparison A j).symm
  let a := Functor.mapDerivedCategorySquareIso
    (F₁ := Etale.upperStar B j) (F₂ := comparisonUpperStar B U)
    (G₁ := comparisonUpperStar B T) (G₂ := upperStar B j)
    (supportSiteComparisonCoefficientPullbackIso B j)
  have hunit (J : Etale.DerivedCategoryModule A U) :
      p.unit.app ((comparison A U).obj J) ≫ (upperStar B j).mapDerivedCategory.map
        (c.hom.app J) = (comparison A U).map (e.unit.app J) ≫
          a.hom.app ((Etale.openImmersionLowerShriek B j).mapDerivedCategory.obj J) := by
    exact comparison_derived_extension_mate A j J
  have hc := counit_of_unit e p c.hom a.hom hunit K
  have ha : supportSiteComparisonCoefficientPullbackIso B j =
      (comparisonUpperStarCompUpperStarIso B j).symm := supportComparison_eq A j
  have hc' : (comparison A T).map (e.counit.app K) =
      c.inv.app _ ≫ (openImmersionLowerShriek B j).mapDerivedCategory.map
        (a.hom.app K) ≫ p.counit.app ((comparison A T).obj K) := by
    rw [hc]
    simp only [Iso.inv_hom_id_app_assoc]
  unfold kummerTraceEtaleOpenCounit kummerTraceOpenComparison openAdjunction
  simp only [Adjunction.ofNatIsoRight_counit, NatTrans.comp_app,
    Functor.map_comp, Iso.trans_hom, Iso.app_hom, Functor.mapIso_hom,
    Category.assoc]
  rw [hc']
  dsimp only [c, Iso.symm_inv]
  simp only [a, ha, Functor.mapDerivedCategorySquareIso,
    openProjectionRestrictionComparison, Iso.trans_hom, Iso.trans_inv,
    Iso.symm_hom, Iso.symm_inv, Functor.isoWhiskerRight_hom,
    Functor.isoWhiskerLeft_hom, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    NatTrans.comp_app, Functor.mapDerivedCategoryNatIso_symm,
    Functor.map_comp, Category.assoc]
  simp only [← Functor.map_comp_assoc, Iso.inv_hom_id_app]
  rw [reassoc_of% (show (comparison A T).map
      ((Etale.openImmersionLowerShriek B j).mapDerivedCategory.map
        ((Etale.leftDerivedUpperStarIsoMapDerivedCategory B j).hom.app K)) ≫
      (openProjectionExtensionComparison A j).hom.app _ =
      (openProjectionExtensionComparison A j).hom.app _ ≫
        (openImmersionLowerShriek B j).mapDerivedCategory.map
          ((comparison A U).map
            ((Etale.leftDerivedUpperStarIsoMapDerivedCategory B j).hom.app K)) from
      (openProjectionExtensionComparison A j).hom.naturality _)]
  simp only [Functor.map_comp, Category.assoc]
  dsimp only [B] at *
  congr 1
  simp
  rfl

private theorem compare_chern (S : Scheme.{u}) [IsNoetherian S]
    (hS : IsUnit (l : Γ(S, ⊤))) (r : ℕ)
    (hA : ((l ^ (r + 1) : ℕ) : Scheme.finiteTateCoefficient l E n) = 0) :
    (comparison (Scheme.finiteTateCoefficient l E n) (ProjectiveLine S)).map
      (kummerTraceOrdinaryDatum l E n S hS r hA).chern =
        projectiveChern l E n S hS (infinityCartier S) r hA := by
  unfold kummerTraceOrdinaryDatum
  exact (supportedProjectiveChern_comparison l E n S hS (infinityCartier S) r hA).symm

attribute [local irreducible] Functor.mapDerivedCategory Functor.mapDerivedCategorySingleFunctor
  HasDerivedCategory.ofHasKInjectiveResolutions

private theorem directImage_hom (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} (f : X ⟶ Y) [QuasiCompact f] [QuasiSeparated f]
    (K : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A))) :
    (directImage A f K).hom = geoP1PushComparison A f K.obj := by
  unfold directImage
  simp only [Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom, Iso.app_hom]
  rw [← pushComparison_plus A f K]
  simp only [← Functor.map_comp_assoc, ← Iso.app_hom, Iso.inv_hom_id]
  change (comparison A Y).map (𝟙 _) ≫ _ = _
  exact (congrArg (fun z ↦ z ≫ geoP1PushComparison A f K.obj)
    ((comparison A Y).map_id _)).trans (Category.id_comp _)

private theorem compare_adjunct (A : Type (u + 1)) [CommRing A]
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (M : Etale.DerivedCategoryModule A Y) (K : Etale.DerivedCategoryModule A X)
    (c : (Etale.ordinaryFinitePullback A f).obj M ⟶ K) :
    (comparison A Y).map
        ((Etale.derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) f).homEquiv M K c) ≫
      geoP1PushComparison A f K =
    (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) f).homEquiv _ _
      ((geoP1PullComparison A f).hom.app M ≫ (comparison A X).map c) := by
  let e := Etale.derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) f
  let p := derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) f
  unfold geoP1PushComparison
  change (comparison A Y).map (e.homEquiv M K c) ≫ p.homEquiv _ _ _ = _
  rw [← p.homEquiv_naturality_left]
  congr 1
  rw [← Category.assoc]
  dsimp only [Etale.ordinaryFinitePushforward]
  rw [show (upperStar (ModuleCat.{u + 1} A) f).leftDerivedFunctor.map
      ((comparison A Y).map (e.homEquiv M K c)) ≫
        (geoP1PullComparison A f).hom.app _ =
      (geoP1PullComparison A f).hom.app M ≫
        (comparison A X).map ((Etale.ordinaryFinitePullback A f).map
          (e.homEquiv M K c)) from (geoP1PullComparison A f).hom.naturality _]
  rw [Category.assoc, ← Functor.map_comp]
  congr 2
  exact (e.homEquiv _ _).symm_apply_apply c

private theorem chern_push (S : Scheme.{u}) [IsNoetherian S]
    (hS : IsUnit (l : Γ(S, ⊤))) (r : ℕ)
    (hA : ((l ^ (r + 1) : ℕ) : Scheme.finiteTateCoefficient l E n) = 0)
    (hc : (comparison (Scheme.finiteTateCoefficient l E n) (ProjectiveLine S)).map
      (kummerTraceOrdinaryDatum l E n S hS r hA).chern =
        projectiveChern l E n S hS (infinityCartier S) r hA) :
    (comparison (Scheme.finiteTateCoefficient l E n) S).map
      (Etale.ordinaryFiniteP1ChernPushforward (Scheme.finiteTateCoefficient l E n)
        (l ^ (r + 1)) hA S (kummerTraceOrdinaryDatum l E n S hS r hA).chern) ≫
      (directImage (Scheme.finiteTateCoefficient l E n) (ProjectiveLine S ↘ S)
        (linePlus l E n r hA (ProjectiveLine S))).hom =
      projectiveH l E n S hS (infinityCartier S) r hA := by
  rw [directImage_hom]
  unfold Etale.ordinaryFiniteP1ChernPushforward
  rw [compare_adjunct]
  unfold projectiveH pullbackUnit geoP1UnitPullback
  simp only [Iso.trans_hom, Iso.app_hom, Functor.mapIso_hom, Functor.map_comp, Category.assoc]
  congr 1
  exact congrArg (fun z ↦
    (geoP1PullComparison (Scheme.finiteTateCoefficient l E n)
      (ProjectiveLine S ↘ S)).hom.app _ ≫
    (comparison (Scheme.finiteTateCoefficient l E n) (ProjectiveLine S)).map
      (Etale.ordinaryFiniteUnitPullback (Scheme.finiteTateCoefficient l E n)
        (ProjectiveLine S ↘ S)).hom ≫ z) hc
private theorem unit_push (S : Scheme.{u}) [IsNoetherian S]
    (hS : IsUnit (l : Γ(S, ⊤))) (r : ℕ)
    (hA : ((l ^ (r + 1) : ℕ) : Scheme.finiteTateCoefficient l E n) = 0) :
    (comparison (Scheme.finiteTateCoefficient l E n) S).map
      (Etale.ordinaryFiniteP1Unit (Scheme.finiteTateCoefficient l E n)
        (l ^ (r + 1)) hA
        (Etale.projectiveLineTraceTransport (l ^ (r + 1))
          (pow_pos (Fact.out : l.Prime).pos _) _ hA) S
        (by simpa only [Nat.cast_pow] using hS.pow (r + 1))) ≫
      (directImage (Scheme.finiteTateCoefficient l E n) (ProjectiveLine S ↘ S)
        (linePlus l E n r hA (ProjectiveLine S))).hom =
      projectiveU l E n S hS r hA := by
  rw [directImage_hom]
  unfold Etale.ordinaryFiniteP1Unit
  dsimp only [Etale.ordinaryFinitePushforward]
  rw [← Adjunction.homEquiv_unit]
  rw [compare_adjunct]
  unfold projectiveU pullback
  rfl

private theorem desc_comp {C : Type*} [Category C] [HasZeroMorphisms C] {X Y Z W : C}
    [HasBinaryBiproduct X Y] (f : X ⟶ Z) (g : Y ⟶ Z) (h : Z ⟶ W) :
    biprod.desc f g ≫ h = biprod.desc (f ≫ h) (g ≫ h) := by
  apply biprod.hom_ext' <;> simp

private theorem compared_desc {C D : Type*} [Category C] [Category D]
    [Preadditive C] [Preadditive D] [HasBinaryBiproducts C] [HasBinaryBiproducts D]
    (F : C ⥤ D) [F.Additive] [PreservesBinaryBiproducts F]
    {X Y Z : C} {W : D} (f : X ⟶ Z) (g : Y ⟶ Z) (e : F.obj Z ⟶ W)
    (u : F.obj X ⟶ W) (h : F.obj Y ⟶ W)
    (hu : F.map f ≫ e = u) (hh : F.map g ≫ e = h) :
    F.map (biprod.desc f g) ≫ e = (F.mapBiprod X Y).hom ≫ biprod.desc u h := by
  rw [← hu, ← hh, ← desc_comp, ← Category.assoc, biprod.mapBiprod_hom_desc]

private theorem decomposition (S : Scheme.{u}) [IsNoetherian S]
    (hS : IsUnit (l : Γ(S, ⊤))) (r : ℕ)
    (hA : ((l ^ (r + 1) : ℕ) : Scheme.finiteTateCoefficient l E n) = 0)
    (hc : (comparison (Scheme.finiteTateCoefficient l E n) (ProjectiveLine S)).map
      (kummerTraceOrdinaryDatum l E n S hS r hA).chern =
        projectiveChern l E n S hS (infinityCartier S) r hA) :
    (comparison (Scheme.finiteTateCoefficient l E n) S).map
      (kummerTraceOrdinaryDatum l E n S hS r hA).decomposition.hom ≫
      (directImage (Scheme.finiteTateCoefficient l E n) (ProjectiveLine S ↘ S)
        (linePlus l E n r hA (ProjectiveLine S))).hom =
      projectiveSum l E n r hA S ≫
        projectiveB l E n S hS (infinityCartier S) r hA := by
  rw [(kummerTraceOrdinaryDatum l E n S hS r hA).decomposition_hom]
  let := preservesBinaryBiproducts_of_preservesBinaryCoproducts
    (comparison (Scheme.finiteTateCoefficient l E n) S)
  unfold projectiveSum projectiveB
  rw [← Functor.mapBiprod_hom]
  exact compared_desc (comparison (Scheme.finiteTateCoefficient l E n) S) _ _ _ _ _
    (unit_push l E n S hS r hA) (chern_push l E n S hS r hA hc)

private theorem supported_decomposition_isIso (S : Scheme.{u}) [IsNoetherian S]
    (hS : IsUnit (l : Γ(S, ⊤))) (r : ℕ)
    (hA : ((l ^ (r + 1) : ℕ) : Scheme.finiteTateCoefficient l E n) = 0)
    (hc : (comparison (Scheme.finiteTateCoefficient l E n) (ProjectiveLine S)).map
      (kummerTraceOrdinaryDatum l E n S hS r hA).chern =
        projectiveChern l E n S hS (infinityCartier S) r hA) :
    IsIso (projectiveB l E n S hS (infinityCartier S) r hA) := by
  let A := Scheme.finiteTateCoefficient l E n
  let C := comparison A S
  let d := kummerTraceOrdinaryDatum l E n S hS r hA
  let e := directImage A (ProjectiveLine S ↘ S) (linePlus l E n r hA (ProjectiveLine S))
  let b := projectiveB l E n S hS (infinityCartier S) r hA
  let := preservesBinaryBiproducts_of_preservesBinaryCoproducts C
  have hb := decomposition l E n S hS r hA hc
  unfold projectiveSum at hb
  change C.map d.decomposition.hom ≫ e.hom = (C.mapBiprod _ _).hom ≫ b at hb
  have : IsIso ((C.mapBiprod _ _).hom ≫ b) := hb ▸ inferInstance
  exact IsIso.of_isIso_comp_left (C.mapBiprod _ _).hom b

private theorem trace_of_square {C D : Type*} [Category C] [Category D]
    [Preadditive C] [Preadditive D] [HasBinaryBiproducts C] [HasBinaryBiproducts D]
    (F : C ⥤ D) [F.Additive] [PreservesBinaryBiproducts F]
    {X Y Z : C} {W : D} (d : X ⊞ Y ≅ Z) (e : F.obj Z ≅ W)
    (b : F.obj X ⊞ F.obj Y ⟶ W) [IsIso b]
    (h : F.map d.hom ≫ e.hom = (F.mapBiprod X Y).hom ≫ b) :
    e.hom ≫ inv b ≫ biprod.snd = F.map (d.inv ≫ biprod.snd) := by
  apply (cancel_epi (F.map d.hom)).mp
  rw [← Category.assoc, ← Category.assoc, h]
  simp only [Category.assoc, IsIso.hom_inv_id_assoc]
  rw [← F.map_comp, ← Category.assoc, d.hom_inv_id, Category.id_comp]
  rw [Functor.mapBiprod_hom, biprod.lift_snd]

private theorem trace_comparison (S : Scheme.{u}) [IsNoetherian S]
    (hS : IsUnit (l : Γ(S, ⊤))) (r : ℕ)
    (hA : ((l ^ (r + 1) : ℕ) : Scheme.finiteTateCoefficient l E n) = 0)
    (hc : (comparison (Scheme.finiteTateCoefficient l E n) (ProjectiveLine S)).map
      (kummerTraceOrdinaryDatum l E n S hS r hA).chern =
        projectiveChern l E n S hS (infinityCartier S) r hA) :
    (directImage (Scheme.finiteTateCoefficient l E n) (ProjectiveLine S ↘ S)
      (linePlus l E n r hA (ProjectiveLine S))).hom ≫
      projectiveTrace l E n S hS (infinityCartier S) r hA =
      (comparison (Scheme.finiteTateCoefficient l E n) S).map
        ((kummerTraceOrdinaryDatum l E n S hS r hA).decomposition.inv ≫ biprod.snd) := by
  let A := Scheme.finiteTateCoefficient l E n
  let C := comparison A S
  let d := kummerTraceOrdinaryDatum l E n S hS r hA
  let e := directImage A (ProjectiveLine S ↘ S) (linePlus l E n r hA (ProjectiveLine S))
  let b := projectiveB l E n S hS (infinityCartier S) r hA
  let := preservesBinaryBiproducts_of_preservesBinaryCoproducts C
  have hb := decomposition l E n S hS r hA hc
  unfold projectiveSum at hb
  change C.map d.decomposition.hom ≫ e.hom = (C.mapBiprod _ _).hom ≫ b at hb
  have : IsIso b := by
    have : IsIso ((C.mapBiprod _ _).hom ≫ b) := hb ▸ inferInstance
    exact IsIso.of_isIso_comp_left (C.mapBiprod _ _).hom b
  have ht := trace_of_square C d.decomposition e b hb
  unfold projectiveTrace geoP1Trace
  exact ht

private theorem trace_chern (S : Scheme.{u}) [IsNoetherian S]
    (hS : IsUnit (l : Γ(S, ⊤))) (r : ℕ)
    (hA : ((l ^ (r + 1) : ℕ) : Scheme.finiteTateCoefficient l E n) = 0)
    [IsIso (projectiveB l E n S hS (infinityCartier S) r hA)] :
    projectiveH l E n S hS (infinityCartier S) r hA ≫
      projectiveTrace l E n S hS (infinityCartier S) r hA =
      𝟙 (unit (Scheme.finiteTateCoefficient l E n) S) := by
  unfold projectiveTrace geoP1Trace
  change _ ≫ inv (projectiveB l E n S hS (infinityCartier S) r hA) ≫ biprod.snd = _
  rw [show projectiveH l E n S hS (infinityCartier S) r hA =
    biprod.inr ≫ projectiveB l E n S hS (infinityCartier S) r hA by
      unfold projectiveB; simp only [biprod.inr_desc]]
  simp only [Category.assoc, IsIso.hom_inv_id_assoc, biprod.inr_snd]
private theorem affine_square
    {C D E H : Type*} [Category C] [Category D] [Category E] [Category H]
    (F : C ⥤ D) (R : E ⥤ C) (G : E ⥤ H) (Q : H ⥤ D)
    {J K : E} {L : H} {M : C} (v : J ⟶ K) (a : G.obj J ⟶ L)
    (w : L ⟶ G.obj K) (bJ : F.obj (R.obj J) ⟶ Q.obj (G.obj J))
    (bK : F.obj (R.obj K) ⟶ Q.obj (G.obj K))
    (t : Q.obj (G.obj K) ⟶ F.obj M) (te : R.obj K ⟶ M)
    (hn : F.map (R.map v) ≫ bK = bJ ≫ Q.map (G.map v))
    (ho : G.map v = a ≫ w) (ht : bK ≫ t = F.map te) :
    (bJ ≫ Q.map a) ≫ (Q.map w ≫ t) = F.map (R.map v ≫ te) := by
  calc
    _ = bJ ≫ Q.map (G.map v) ≫ t := by rw [ho, Q.map_comp]; simp only [Category.assoc]
    _ = F.map (R.map v) ≫ (bK ≫ t) := by rw [← Category.assoc, ← hn, Category.assoc]
    _ = _ := by rw [ht, ← F.map_comp]

-- Keep the abstract affine-square specialization compact.
set_option backward.isDefEq.respectTransparency false in
private theorem affine_comparison (S : Scheme.{u}) [IsNoetherian S]
    (hS : IsUnit (l : Γ(S, ⊤))) (r : ℕ)
    (hA : ((l ^ (r + 1) : ℕ) : Scheme.finiteTateCoefficient l E n) = 0)
    (hc : (comparison (Scheme.finiteTateCoefficient l E n) (ProjectiveLine S)).map
      (kummerTraceOrdinaryDatum l E n S hS r hA).chern =
        projectiveChern l E n S hS (infinityCartier S) r hA)
    (hopen : (comparison (Scheme.finiteTateCoefficient l E n) (ProjectiveLine S)).map
      (kummerTraceEtaleOpenCounit (Scheme.finiteTateCoefficient l E n)
        (ProjectiveLine.affineChart S)
        ((Etale.ordinaryFiniteLine (Scheme.finiteTateCoefficient l E n)
          (l ^ (r + 1)) hA (ProjectiveLine S))⟦(2 : ℤ)⟧)) =
      (kummerTraceOpenComparison (Scheme.finiteTateCoefficient l E n)
        (ProjectiveLine.affineChart S)
        ((Etale.ordinaryFiniteLine (Scheme.finiteTateCoefficient l E n)
          (l ^ (r + 1)) hA (ProjectiveLine S))⟦(2 : ℤ)⟧)).hom ≫
        (openAdjunction (Scheme.finiteTateCoefficient l E n)
          (ProjectiveLine.affineChart S)).counit.app (line l E n r hA (ProjectiveLine S))) :
    kummerTraceAffineComparison l E n S r hA ≫ kummerTraceProAffine l E n S hS r hA =
      (comparison (Scheme.finiteTateCoefficient l E n) S).map
        (kummerTraceEtaleAffine l E n S hS r hA) := by
  let A := Scheme.finiteTateCoefficient l E n
  let j := ProjectiveLine.affineChart S
  let K := (Etale.ordinaryFiniteLine A (l ^ (r + 1)) hA (ProjectiveLine S))⟦(2 : ℤ)⟧
  have hn := pushComparison_naturality A (ProjectiveLine S ↘ S)
    (kummerTraceEtaleOpenCounit A j K)
  have ht := trace_comparison l E n S hS r hA hc
  rw [directImage_hom] at ht
  unfold kummerTraceAffineComparison kummerTraceProAffine kummerTraceEtaleAffine
  have hs := affine_square (comparison A S) (Etale.ordinaryFinitePushforward A
    (ProjectiveLine S ↘ S)) (comparison A (ProjectiveLine S))
    (lowerStar (ModuleCat.{u + 1} A) (ProjectiveLine S ↘ S)).rightDerivedFunctor
    (kummerTraceEtaleOpenCounit A j K)
    (kummerTraceOpenComparison A j K).hom
    ((openAdjunction A j).counit.app ((comparison A (ProjectiveLine S)).obj K))
    (geoP1PushComparison A (ProjectiveLine S ↘ S) _)
    (geoP1PushComparison A (ProjectiveLine S ↘ S) K)
    (projectiveTrace l E n S hS (infinityCartier S) r hA)
    ((kummerTraceOrdinaryDatum l E n S hS r hA).decomposition.inv ≫ biprod.snd)
    hn hopen ht
  exact hs

end ProofHelpers

/-- Supported Kummer Chern and decomposition transport, invertibility, trace
normalization, unbounded open counit transport, and the affine-chart trace composite.
The natural indices `n,r` denote the positive indices `n+1,r+1` of the node;
all finite positive coefficient levels and all annihilating exponents occur.

Source: Stacks 09AF, lemma-jshriek-comparison; 0B65,
lemma-transformation-between-functors-and-adjoints; blueprint def-amb-p1-trace.
(blueprint: lem-pur-p1-kummer-trace-site-transport).

Proof:
1. Finite type over the fixed field makes S Noetherian, with no separatedness
assumption on S. The coefficient prime differs from the characteristic and is
therefore invertible on S. The projective projection is proper, hence qcqs.
2. On the infinity chart the infinity divisor is cut out by the polynomial
coordinate, a nonzerodivisor; on the other chart it is empty. Its divisor line
is O(1). The supported Cartier Kummer realization and root-projection finite
Tate descent identify its composite with comparison of the positive Kummer class.
3. Transpose comparison of the ordinary Chern adjunct under the pro-etale
adjunction. The direct-image mate counit identity and pullback naturality give
exactly the supported Chern composite, hence the first equation.
4. The mate-unit identity similarly compares the shifted twisted units, with
the canonical finite-line pullback. The two biproduct components give the
second equation. Invertibility of the ordinary decomposition and the qcqs
bounded-below comparison imply invertibility of the supported decomposition.
5. Invert that equation and take the second projection. This gives the trace
comparison; the second injection gives trace of the Chern adjunct equal to one.
6. For an arbitrary open immersion transpose the compared etale counit using
the adjoint-normalized sheaf extension comparison. Its unit normalization,
naturality, and the triangle identity identify both transposes with the same
restriction comparison. Thus the actual counits agree on sheaves.
7. Both open functors and comparison are exact. Apply the preceding identity
degreewise to arbitrary complexes and localize. Exact-derived adjunctions
have precisely these localized counits, without a boundedness restriction.
8. For the affine chart, apply direct-image mate naturality to its counit,
then the trace equation and step 7. The source is bounded below because the
shifted line is bounded below and open restriction and extension are exact.
Finite Tate descent supplies the specified target twist in every equation.
No flatness of A over the Kummer coefficient ring is used.
-/
theorem p1KummerTraceSiteTransport (P : WeilConjectures.PurityFiniteSetting.{u})
    (S : Scheme.{u}) (aS : S ⟶ Spec (CommRingCat.of P.field.k))
    [LocallyOfFiniteType aS] [QuasiCompact aS] :
    ∃ hS : IsUnit (P.coefficients.l : Γ(S, ⊤)),
      (∀ (r : ℕ)
        (hA : ((P.coefficients.l ^ (r + 1) : ℕ) :
          Scheme.finiteTateCoefficient P.coefficients.l P.extension (P.level - 1)) = 0),
        @P1KummerTraceTransport.{u} P.coefficients.l _ P.extension _ _ _ (P.level - 1) S
          (isNoetherian_of_locallyOfFiniteType aS) hS r hA) ∧
      (∀ (U T : Scheme.{u}) [U.Over (Spec (CommRingCat.of P.field.k))]
        [T.Over (Spec (CommRingCat.of P.field.k))]
        [LocallyOfFiniteType (U ↘ Spec (CommRingCat.of P.field.k))]
        [QuasiCompact (U ↘ Spec (CommRingCat.of P.field.k))]
        [LocallyOfFiniteType (T ↘ Spec (CommRingCat.of P.field.k))]
        [QuasiCompact (T ↘ Spec (CommRingCat.of P.field.k))]
        (j : U ⟶ T) [IsOpenImmersion j]
        (K : Etale.DerivedCategoryModule
          (Scheme.finiteTateCoefficient P.coefficients.l P.extension (P.level - 1)) T),
        (comparison
          (Scheme.finiteTateCoefficient P.coefficients.l P.extension (P.level - 1)) T).map
          (kummerTraceEtaleOpenCounit
            (Scheme.finiteTateCoefficient P.coefficients.l P.extension (P.level - 1)) j K) =
          (kummerTraceOpenComparison
            (Scheme.finiteTateCoefficient P.coefficients.l P.extension (P.level - 1)) j K).hom ≫
            (openAdjunction
              (Scheme.finiteTateCoefficient P.coefficients.l P.extension (P.level - 1))
              j).counit.app
                ((comparison
                  (Scheme.finiteTateCoefficient P.coefficients.l P.extension (P.level - 1))
                  T).obj K)) := by
  let : IsNoetherian S := isNoetherian_of_locallyOfFiniteType aS
  let hS := WeilConjectures.PurityFiniteSetting.coefficientPrime_isUnit_sections P S aS
  refine ⟨hS, ?_, ?_⟩
  · intro r hA
    let l := P.coefficients.l
    let E := P.extension
    let n := P.level - 1
    have hc := compare_chern l E n S hS r hA
    have hB := supported_decomposition_isIso l E n S hS r hA hc
    exact ⟨chern_push l E n S hS r hA hc,
      decomposition l E n S hS r hA hc, hB,
      trace_comparison l E n S hS r hA hc, trace_chern l E n S hS r hA,
      affine_comparison l E n S hS r hA hc (open_counit _ _ _)⟩
  · intro U T _ _ _ _ _ _ j _ K
    exact open_counit _ j K

end AlgebraicGeometry.ProEtale.VectorIntegrationSite
