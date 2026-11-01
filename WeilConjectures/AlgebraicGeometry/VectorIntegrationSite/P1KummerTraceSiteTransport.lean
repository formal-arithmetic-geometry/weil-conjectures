/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.VectorIntegrationSite.ProEtaleAffineLineCounit
public import WeilConjectures.AlgebraicGeometry.Open.OpenProjectionSiteTransport
public import WeilConjectures.SmoothPurity.PurityFiniteSetting.PurityFiniteSetting
public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FiniteType

import all WeilConjectures.AlgebraicGeometry.Comparison.ComparisonOpenTensorCoherence
import all WeilConjectures.AlgebraicGeometry.Geo.GeoP1Cohomology
import all WeilConjectures.SmoothPurity.PurityFiniteSetting.PurityFiniteSetting
import WeilConjectures.AlgebraicGeometry.VectorIntegrationSite.SupportedProjectiveChernComparison

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
set_option backward.isDefEq.respectTransparency false in
end ProofHelpers

end AlgebraicGeometry.ProEtale.VectorIntegrationSite
