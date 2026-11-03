/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.DncCoefficientTransport.DncCoefficientTransportData
import all WeilConjectures.AlgebraicGeometry.Unbounded.UnboundedEtaleCompactSupportComparisonsSupplement
import all WeilConjectures.AlgebraicGeometry.Etale.ProEtale.EtaleProEtaleScalarMate
import all WeilConjectures.AlgebraicGeometry.Etale.Proper.EtaleProperCoefficientTensorUnit
import all WeilConjectures.AlgebraicGeometry.Etale.Compact.EtaleCompactScalarBaseChange
import all WeilConjectures.AlgebraicGeometry.Etale.Compact.EtaleCompactScalarCoherence
import all WeilConjectures.AlgebraicGeometry.Proper.Open.ProperOpenCoefficientRefinement
import WeilConjectures.AlgebraicGeometry.Etale.Scalar.EtaleScalarPullbackUnitCoherence
import all WeilConjectures.AlgebraicGeometry.Etale.Scalar.EtaleScalarPullbackCompactification
import WeilConjectures.AlgebraicGeometry.Scalar.ScalarPullbackComposition
import WeilConjectures.CategoryTheory.Adjunction.ProperBaseChange.CoefficientExchange

/-! # Scalar compatibility of the canonical exceptional section base-change mate -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.Etale

-- Cache the standard instances and keep the derived functors folded during matching.
attribute [local instance 2000] scalarSheafMonoidal
attribute [local instance] cachedEtaleGroth cachedEtaleSheafify
  cachedEtaleMonoidalPreadditive cachedEtaleCoproducts cachedEtaleColimits
  cachedEtaleFlatResolution cachedEtaleInjectiveResolution cachedEtaleExactColimits
  cachedEtaleTensor4 cachedEtaleTensor12 cachedEtaleTensor23
  cachedEtaleTensorColimits cachedEtaleTensorFlipColimits
attribute [local irreducible] upperStar lowerStar openImmersionLowerShriek
  Functor.mapDerivedCategory Functor.leftDerivedFunctor Functor.rightDerivedFunctor

-- The general proper scalar mate avoids Noetherian and boundedness restrictions.
private theorem compact_scalar_isIso
    {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A]
    (φ : A →+* B) {X Y : Scheme.{u}} {f : X ⟶ Y}
    (c : Compactification f) (M : DerivedCategoryModule A X) :
    IsIso (ExceptionalCoefficients.compactSupportMap φ c M) := by
  have := proper_scalarMate_isIso φ c.g
    ((openImmersionLowerShriek (ModuleCat.{u + 1} A) c.i).mapDerivedCategory.obj M)
  unfold ExceptionalCoefficients.compactSupportMap
  infer_instance

-- Use the open-adjunction transpose to extend refinement coherence to all inputs.
private theorem refinement_scalar_open
    {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) {X Y : Scheme.{u}} {f : X ⟶ Y} {c d : Compactification f}
    (r : c.Refinement d) (hp : IsPullback c.i (𝟙 X) r.hom d.i)
    (M : DerivedCategoryModule A X) :
    (scalarExtension φ d.Z).map
        ((mapDerivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) r.hom).unit.app
          ((openImmersionLowerShriek (ModuleCat.{u + 1} A) d.i).mapDerivedCategory.obj M) ≫
        (rightDerivedLowerStar (ModuleCat.{u + 1} A) r.hom).map
          ((refinementLowerShriekBaseChangeDerivedIso (ModuleCat.{u + 1} A) r hp).inv.app M)) ≫
      (scalarMate φ r.hom).app
        ((openImmersionLowerShriek (ModuleCat.{u + 1} A) c.i).mapDerivedCategory.obj M) ≫
      (rightDerivedLowerStar (ModuleCat.{u + 1} B) r.hom).map
        ((ExceptionalCoefficients.openIso φ c.i).hom.app M) =
    (ExceptionalCoefficients.openIso φ d.i).hom.app M ≫
      (mapDerivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} B) r.hom).unit.app
        ((openImmersionLowerShriek (ModuleCat.{u + 1} B) d.i).mapDerivedCategory.obj
          ((scalarExtension φ X).obj M)) ≫
      (rightDerivedLowerStar (ModuleCat.{u + 1} B) r.hom).map
        ((refinementLowerShriekBaseChangeDerivedIso (ModuleCat.{u + 1} B) r hp).inv.app
          ((scalarExtension φ X).obj M)) := by
  let α (R : Type (u + 1)) [CommRing R] [Finite R] (K : DerivedCategoryModule R X) :=
    (mapDerivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} R) r.hom).unit.app
        ((openImmersionLowerShriek (ModuleCat.{u + 1} R) d.i).mapDerivedCategory.obj K) ≫
      (rightDerivedLowerStar (ModuleCat.{u + 1} R) r.hom).map
        ((refinementLowerShriekBaseChangeDerivedIso (ModuleCat.{u + 1} R) r hp).inv.app K)
  have hα (R : Type (u + 1)) [CommRing R] [Finite R] (K : DerivedCategoryModule R X) :
      (derivedOpenImmersionLowerShriekUpperStarAdjunction
        (ModuleCat.{u + 1} R) d.i).homEquiv _ _ (α R K) ≫
        (refinementRestriction R r.hom c.i d.i r.i_hom).app
          ((openImmersionLowerShriek (ModuleCat.{u + 1} R) c.i).mapDerivedCategory.obj K) =
      (derivedOpenImmersionLowerShriekUpperStarAdjunction
        (ModuleCat.{u + 1} R) c.i).unit.app K := by
    simpa only [α, refinementRestriction, upperStarCompIso_eq,
      Functor.mapDerivedCategoryTriangleIso, Functor.id_obj, rightDerivedLowerStar,
      mapDerivedUpperStarLowerStarAdjunction_eq] using
      refinement_transpose_normalization
        (openImmersionLowerShriek (ModuleCat.{u + 1} R) c.i).mapDerivedCategory
        (upperStar (ModuleCat.{u + 1} R) c.i).mapDerivedCategory
        (openImmersionLowerShriek (ModuleCat.{u + 1} R) d.i).mapDerivedCategory
        (upperStar (ModuleCat.{u + 1} R) d.i).mapDerivedCategory
        (upperStar (ModuleCat.{u + 1} R) r.hom).mapDerivedCategory
        (rightDerivedLowerStar (ModuleCat.{u + 1} R) r.hom)
        (derivedOpenImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} R) c.i)
        (derivedOpenImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} R) d.i)
        (mapDerivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} R) r.hom)
        (Functor.mapDerivedCategoryTriangleIso
          (upperStarCompIso (ModuleCat.{u + 1} R) c.i r.hom d.i r.i_hom))
        (refinementLowerShriekBaseChangeDerivedIso (ModuleCat.{u + 1} R) r hp)
        (unit_map_refinementLowerShriekBaseChangeDerivedIso (ModuleCat.{u + 1} R) r hp) K
  have : IsIso (α B ((scalarExtension φ X).obj M)) := by
    have := isIso_mapDerivedUpperStarLowerStarAdjunction_unit_app_openImmersionLowerShriek
      (Λ := B) r hp ((scalarExtension φ X).obj M)
    dsimp only [α]
    infer_instance
  have : IsIso ((derivedOpenImmersionLowerShriekUpperStarAdjunction
      (ModuleCat.{u + 1} B) d.i).homEquiv _ _ (α B ((scalarExtension φ X).obj M))) := by
    simp only [Adjunction.homEquiv_unit]
    infer_instance
  have : IsIso ((refinementRestriction B r.hom c.i d.i r.i_hom).app
      ((openImmersionLowerShriek (ModuleCat.{u + 1} B) c.i).mapDerivedCategory.obj
        ((scalarExtension φ X).obj M))) := by
    have : IsIso (((derivedOpenImmersionLowerShriekUpperStarAdjunction
        (ModuleCat.{u + 1} B) d.i).homEquiv _ _ (α B ((scalarExtension φ X).obj M))) ≫
        (refinementRestriction B r.hom c.i d.i r.i_hom).app
          ((openImmersionLowerShriek (ModuleCat.{u + 1} B) c.i).mapDerivedCategory.obj
            ((scalarExtension φ X).obj M))) := by
      rw [hα]
      infer_instance
    exact IsIso.of_isIso_comp_left
      ((derivedOpenImmersionLowerShriekUpperStarAdjunction
        (ModuleCat.{u + 1} B) d.i).homEquiv _ _ (α B ((scalarExtension φ X).obj M))) _
  have hχ (K : DerivedCategoryModule A c.Z) :
      (upperStar (ModuleCat.{u + 1} B) d.i).mapDerivedCategory.map
          ((scalarMate φ r.hom).app K) ≫
        (refinementRestriction B r.hom c.i d.i r.i_hom).app
          ((scalarExtension φ c.Z).obj K) ≫
        (properOpenCoefficientPullbackIso φ c.i).hom.app K =
      (properOpenCoefficientPullbackIso φ d.i).hom.app
          ((rightDerivedLowerStar (ModuleCat.{u + 1} A) r.hom).obj K) ≫
        (scalarExtension φ X).map
          ((refinementRestriction A r.hom c.i d.i r.i_hom).app K) := by
    simpa only [refinementRestriction, rightDerivedLowerStar,
      mapDerivedUpperStarLowerStarAdjunction_eq, Functor.map_comp, Category.assoc] using
      restriction_coefficient_mate
        (mapDerivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) r.hom)
        (mapDerivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} B) r.hom)
        (upperStar (ModuleCat.{u + 1} A) c.i).mapDerivedCategory
        (upperStar (ModuleCat.{u + 1} A) d.i).mapDerivedCategory
        (upperStar (ModuleCat.{u + 1} B) c.i).mapDerivedCategory
        (upperStar (ModuleCat.{u + 1} B) d.i).mapDerivedCategory
        (scalarExtension φ X) (scalarExtension φ c.Z) (scalarExtension φ d.Z)
        (Functor.mapDerivedCategoryNatIso
          (upperStarComp (ModuleCat.{u + 1} A) c.i r.hom d.i r.i_hom.symm) ≪≫
          Functor.mapDerivedCategoryCompIso _ _)
        (Functor.mapDerivedCategoryNatIso
          (upperStarComp (ModuleCat.{u + 1} B) c.i r.hom d.i r.i_hom.symm) ≪≫
          Functor.mapDerivedCategoryCompIso _ _)
        (properOpenCoefficientPullbackIso φ c.i)
        (properOpenCoefficientPullbackIso φ d.i)
        (properOpenCoefficientPullbackIso φ r.hom)
        (scalarMate φ r.hom) (fun K ↦ by
          simpa only [mapDerivedUpperStarLowerStarAdjunction_eq] using
            coefficientMate_counit φ r.hom K)
        (fun K ↦ by simpa only [properOpenCoefficientPullbackIso] using
          scalarPullback_composition φ r.hom c.i d.i r.i_hom K) K
  have h := coefficient_refinement_of_restriction
    (derivedOpenImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) c.i)
    (derivedOpenImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) d.i)
    (derivedOpenImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} B) c.i)
    (derivedOpenImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} B) d.i)
    (rightDerivedLowerStar (ModuleCat.{u + 1} A) r.hom)
    (rightDerivedLowerStar (ModuleCat.{u + 1} B) r.hom)
    (scalarExtension φ X) (scalarExtension φ c.Z) (scalarExtension φ d.Z)
    (refinementRestriction A r.hom c.i d.i r.i_hom)
    (refinementRestriction B r.hom c.i d.i r.i_hom)
    (properOpenCoefficientPullbackIso φ c.i) (properOpenCoefficientPullbackIso φ d.i)
    (scalarMate φ r.hom) hχ M (α A M) (α B ((scalarExtension φ X).obj M))
    ((ExceptionalCoefficients.openIso φ c.i).app M)
    ((ExceptionalCoefficients.openIso φ d.i).app M)
    (by simpa only [Iso.app_inv, compactScalarOpen_normalization,
      properOpenCoefficientOpenIso, Iso.symm_inv, asIso_hom] using
        coefficientOpen_unit φ c.i M)
    (by simpa only [Iso.app_inv, compactScalarOpen_normalization,
      properOpenCoefficientOpenIso, Iso.symm_inv, asIso_hom] using
        coefficientOpen_unit φ d.i M)
    (hα A M) (hα B ((scalarExtension φ X).obj M))
  exact h

variable {A B : Type (u + 1)} [CommRing A] [CommRing B]

private theorem sectionScalar_refinement
    [Finite A] [Finite B] (φ : A →+* B) {X Y : Scheme.{u}}
    {f : X ⟶ Y} {c d : Compactification f}
    (r : c.Refinement d) (hp : IsPullback c.i (𝟙 X) r.hom d.i)
    (M : DerivedCategoryModule A X) :
    (scalarExtension φ Y).map
        ((rightDerivedLowerShriekOfCompactificationComparison (ModuleCat.{u + 1} A)
          r hp).app M) ≫ (compactScalarMap φ c).app M =
      (compactScalarMap φ d).app M ≫
        (rightDerivedLowerShriekOfCompactificationComparison (ModuleCat.{u + 1} B)
          r hp).app ((scalarExtension φ X).obj M) := by
  let α (R : Type (u + 1)) [CommRing R] [Finite R] (K : DerivedCategoryModule R X) :=
    (mapDerivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} R) r.hom).unit.app
        ((openImmersionLowerShriek (ModuleCat.{u + 1} R) d.i).mapDerivedCategory.obj K) ≫
      (rightDerivedLowerStar (ModuleCat.{u + 1} R) r.hom).map
        ((refinementLowerShriekBaseChangeDerivedIso (ModuleCat.{u + 1} R) r hp).inv.app K)
  let αA := α A M
  let αB := α B ((scalarExtension φ X).obj M)
  let kA := Functor.rightDerivedFunctorCompIso' (lowerStar (ModuleCat.{u + 1} A) r.hom)
    (lowerStar (ModuleCat.{u + 1} A) d.g) (refinementLowerStarComp (ModuleCat.{u + 1} A) r)
  let kB := Functor.rightDerivedFunctorCompIso' (lowerStar (ModuleCat.{u + 1} B) r.hom)
    (lowerStar (ModuleCat.{u + 1} B) d.g) (refinementLowerStarComp (ModuleCat.{u + 1} B) r)
  have heA : (rightDerivedLowerShriekOfCompactificationComparison
      (ModuleCat.{u + 1} A) r hp).app M =
      (rightDerivedLowerStar (ModuleCat.{u + 1} A) d.g).map αA ≫
        kA.hom.app
          ((openImmersionLowerShriek (ModuleCat.{u + 1} A) c.i).mapDerivedCategory.obj M) := by
    simp only [rightDerivedLowerShriekOfCompactificationComparison, NatTrans.comp_app,
      Functor.whiskerRight_app, Functor.whiskerLeft_app, Functor.comp_map,
      ← Functor.map_comp_assoc]
    dsimp only [αA, αB, α, kA, kB]
    congr 2
  have heB : (rightDerivedLowerShriekOfCompactificationComparison
      (ModuleCat.{u + 1} B) r hp).app ((scalarExtension φ X).obj M) =
      (rightDerivedLowerStar (ModuleCat.{u + 1} B) d.g).map αB ≫
        kB.hom.app
          ((openImmersionLowerShriek (ModuleCat.{u + 1} B) c.i).mapDerivedCategory.obj
            ((scalarExtension φ X).obj M)) := by
    simp only [rightDerivedLowerShriekOfCompactificationComparison, NatTrans.comp_app,
      Functor.whiskerRight_app, Functor.whiskerLeft_app, Functor.comp_map,
      ← Functor.map_comp_assoc]
    dsimp only [αA, αB, α, kA, kB]
    congr 2
  have ho := refinement_scalar_open φ r hp M
  have hc (N : DerivedCategoryModule A c.Z) :
      (scalarExtension φ Y).map (kA.hom.app N) ≫ (scalarMate φ c.g).app N =
        (scalarMate φ d.g).app ((rightDerivedLowerStar (ModuleCat.{u + 1} A) r.hom).obj N) ≫
          (rightDerivedLowerStar (ModuleCat.{u + 1} B) d.g).map ((scalarMate φ r.hom).app N) ≫
          kB.hom.app ((scalarExtension φ c.Z).obj N) := by
    dsimp only [kA, kB]
    rw [refinementLowerStarComp_eq, refinementLowerStarComp_eq]
    exact scalarMate_directImage_composition_eq φ r.hom d.g c.g r.hom_g.symm N
  dsimp only [rightDerivedLowerStar] at *
  rw [heA, heB]
  dsimp only [compactScalarMap, ExceptionalCoefficients.compactSupportMap,
    rightDerivedLowerShriekOfCompactification, Functor.comp_obj]
  simp only [Functor.map_comp, Category.assoc]
  rw [reassoc_of% hc]
  have hn := (scalarMate φ d.g).naturality αA
  dsimp only [Functor.comp_map, rightDerivedLowerStar] at hn
  erw [reassoc_of% hn]
  have hk := kB.hom.naturality ((ExceptionalCoefficients.openIso φ c.i).hom.app M)
  dsimp only [Functor.comp_map, Functor.comp_obj] at hk
  erw [← hk]
  simp only [← Functor.map_comp_assoc]
  dsimp only [αA, αB, α]
  exact congrArg (fun z ↦ (scalarMate φ d.g).app _ ≫
    (rightDerivedLowerStar (ModuleCat.{u + 1} B) d.g).map z ≫
      kB.hom.app _) ho

private theorem sectionScalar_compactification
    [Finite A] [Finite B] (φ : A →+* B) {X Y : Scheme.{u}}
    {f : X ⟶ Y} [QuasiCompact f]
    (c d : Compactification f)
    (M : DerivedCategoryModule A X) :
    (scalarExtension φ Y).map
        ((rightDerivedLowerShriekOfCompactificationIso A c d).hom.app M) ≫
      (compactScalarMap φ d).app M =
      (compactScalarMap φ c).app M ≫
        (rightDerivedLowerShriekOfCompactificationIso B c d).hom.app
          ((scalarExtension φ X).obj M) := by
  have h₁ := sectionScalar_refinement φ (Compactification.infFst c d)
    (Compactification.isPullback_infFst c d) M
  have h₂ := sectionScalar_refinement φ (Compactification.infSnd c d)
    (Compactification.isPullback_infSnd c d) M
  simp only [rightDerivedLowerShriekOfCompactificationIso, Iso.trans_hom,
    Iso.symm_hom, NatTrans.comp_app, Functor.map_comp, asIso_hom]
  apply (cancel_mono ((rightDerivedLowerShriekOfCompactificationComparison
    (ModuleCat.{u + 1} B) (Compactification.infSnd c d)
      (Compactification.isPullback_infSnd c d)).app
        ((scalarExtension φ X).obj M))).1
  simp only [Category.assoc, asIso_inv, NatIso.isIso_inv_app, IsIso.inv_hom_id, Category.comp_id]
  rw [← h₂]
  simp only [← Functor.map_comp_assoc, IsIso.inv_hom_id,
    _root_.CategoryTheory.Functor.map_id, Category.id_comp]
  exact h₁

-- Exact inverse-image transport is formal and imposes no scheme finiteness condition.
private theorem sectionScalar_exchange_normalization
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X X' Y Y' : Scheme.{u}}
    {f : X ⟶ Y} {f' : X' ⟶ Y'} {v : Y' ⟶ Y} {v' : X' ⟶ X}
    (sq : IsPullback v' f' f v) (c : Compactification f) :
    unboundedEtaleCompactSupportExchange A sq c =
      (Functor.associator _ _ _).hom ≫
      Functor.whiskerLeft
        (openImmersionLowerShriek (ModuleCat.{u + 1} A) c.i).mapDerivedCategory
        (exactDerivedBaseChangeMap (ModuleCat.{u + 1} A)
          (IsPullback.of_hasPullback c.g v).toCommSq) ≫
      (Functor.associator _ _ _).inv ≫
      Functor.whiskerRight
        (mapDerivedCategoryOpenImmersionLowerShriekBaseChangeIso (ModuleCat.{u + 1} A)
          (c.isPullback_i_ofIsPullback sq)).inv
        (rightDerivedLowerStar (ModuleCat.{u + 1} A) (c.ofIsPullback sq).g) ≫
      (Functor.associator _ _ _).hom := by
  ext K
  have h := congrArg (fun η ↦ η.app
    ((openImmersionLowerShriek (ModuleCat.{u + 1} A) c.i).mapDerivedCategory.obj K))
    (exact_exchange_transport A (IsPullback.of_hasPullback c.g v).toCommSq)
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app] at h
  simp only [unboundedEtaleCompactSupportExchange,
    rightDerivedLowerShriekOfCompactificationBaseChangeMap,
    derivedOpenImmersionLowerShriekBaseChangeIso, Iso.trans_inv,
    Functor.isoWhiskerLeft_inv, Functor.isoWhiskerRight_inv, Iso.symm_inv,
    NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_hom_app, Functor.associator_inv_app, Functor.map_comp,
    Category.id_comp, Category.comp_id, Category.assoc]
  dsimp only [rightDerivedLowerShriekOfCompactification, rightDerivedLowerStar,
    Functor.comp_obj, Functor.comp_map] at h ⊢
  simp only [← Functor.map_comp, Iso.inv_hom_id_app]
  simp only [Functor.map_comp]
  rw [← h]
  simp only [Category.assoc]
  rw [((openImmersionLowerShriek (ModuleCat.{u + 1} A)
    (c.ofIsPullback sq).i).mapDerivedCategory).map_id]
  erw [CategoryTheory.Functor.map_id]
  rw [Category.comp_id]
  rfl

private theorem sectionScalar_exchange_raw
    {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) {X X' Y Y' : Scheme.{u}}
    {f : X ⟶ Y} {f' : X' ⟶ Y'} {g : Y' ⟶ Y} {h : X' ⟶ X}
    (sq : IsPullback h f' f g) (c : Compactification f)
    (M : DerivedCategoryModule A X) :
    (upperStar (ModuleCat.{u + 1} B) g).mapDerivedCategory.map
        ((compactScalarMap φ c).app M) ≫
      (unboundedEtaleCompactSupportExchange B sq c).app ((scalarExtension φ X).obj M) ≫
      (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} B)
        (c.ofIsPullback sq)).map ((properOpenCoefficientPullbackIso φ h).hom.app M) =
      (properOpenCoefficientPullbackIso φ g).hom.app
        ((rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c).obj M) ≫
      (scalarExtension φ Y').map ((unboundedEtaleCompactSupportExchange A sq c).app M) ≫
      (compactScalarMap φ (c.ofIsPullback sq)).app
        ((upperStar (ModuleCat.{u + 1} A) h).mapDerivedCategory.obj M) := by
  let psq : ChosenCartesianSquare (pullback.fst c.g g) (pullback.snd c.g g) c.g g :=
    { toCommSq := (IsPullback.of_hasPullback c.g g).toCommSq
      isoPullback := Iso.refl _
      hom_fst := Category.id_comp _
      hom_snd := Category.id_comp _ }
  have hp := exactDerivedBaseChangeMap_scalarExtension φ _ _ _ _ psq
    ((openImmersionLowerShriek (ModuleCat.{u + 1} A) c.i).mapDerivedCategory.obj M)
  have ho := open_scalar_exchange_forward φ (c.isPullback_i_ofIsPullback sq) M
  have hn := (exactDerivedBaseChangeMap (ModuleCat.{u + 1} B) psq.toCommSq).naturality
    ((ExceptionalCoefficients.openIso φ c.i).hom.app M)
  have hm := (scalarMate φ (c.ofIsPullback sq).g).naturality
    ((mapDerivedCategoryOpenImmersionLowerShriekBaseChangeIso
      (ModuleCat.{u + 1} A) (c.isPullback_i_ofIsPullback sq)).inv.app M)
  simp only [sectionScalar_exchange_normalization,
    NatTrans.comp_app, Functor.associator_hom_app, Functor.associator_inv_app,
    Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Category.id_comp, Category.comp_id, Category.assoc]
  dsimp only [compactScalarMap, ExceptionalCoefficients.compactSupportMap,
    rightDerivedLowerShriekOfCompactification, Functor.comp_map, Functor.comp_obj]
  simp only [Functor.map_comp, Category.assoc]
  dsimp only [Functor.comp_map, Functor.comp_obj] at hn hm
  dsimp only [Compactification.ofIsPullback, rightDerivedLowerStar] at ho hm hp hn ⊢
  erw [reassoc_of% hn]
  simp only [← Functor.map_comp_assoc, ← Functor.map_comp]
  erw [ho]
  simp only [Functor.map_comp, Category.assoc]
  erw [reassoc_of% hp, reassoc_of% hm]

private theorem chosen_exchange_app
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X X' Y Y' : Scheme.{u}} {f : X ⟶ Y} {f' : X' ⟶ Y'}
    {g : Y' ⟶ Y} {h : X' ⟶ X}
    [HasCompactification f] [HasCompactification f'] [QuasiCompact f']
    (sq : IsPullback h f' f g) (M : DerivedCategoryModule A X) :
    (unboundedEtaleCompactSupportBaseChange A sq).app M =
      (unboundedEtaleCompactSupportExchange A sq
        (HasCompactification.compactification f)).app M ≫
      (rightDerivedLowerShriekIso A
        ((HasCompactification.compactification f).ofIsPullback sq)).hom.app
        ((upperStar (ModuleCat.{u + 1} A) h).mapDerivedCategory.obj M) := by
  simp only [unboundedEtaleCompactSupportBaseChange,
    unboundedEtaleCompactSupportExchange, rightDerivedLowerShriekBaseChangeMap,
    NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app, Category.assoc]
  erw [← (rightDerivedLowerShriekIso A
    ((HasCompactification.compactification f).ofIsPullback sq)).hom.naturality
      ((leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) h).hom.app M)]
  rfl

private theorem sectionScalar_exchange_exact
    {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) {X X' Y Y' : Scheme.{u}}
    {f : X ⟶ Y} {f' : X' ⟶ Y'} {g : Y' ⟶ Y} {h : X' ⟶ X}
    [QuasiCompact f']
    [HasCompactification f] [HasCompactification f']
    (sq : IsPullback h f' f g)
    (M : DerivedCategoryModule A X) :
    (upperStar (ModuleCat.{u + 1} B) g).mapDerivedCategory.map
        ((compactScalarChosenMap φ f).app M) ≫
      (unboundedEtaleCompactSupportBaseChange B sq).app ((scalarExtension φ X).obj M) ≫
      (rightDerivedLowerShriek (ModuleCat.{u + 1} B) f').map
        ((properOpenCoefficientPullbackIso φ h).hom.app M) =
      (properOpenCoefficientPullbackIso φ g).hom.app
        ((rightDerivedLowerShriek (ModuleCat.{u + 1} A) f).obj M) ≫
      (scalarExtension φ Y').map ((unboundedEtaleCompactSupportBaseChange A sq).app M) ≫
      (compactScalarChosenMap φ f').app
        ((upperStar (ModuleCat.{u + 1} A) h).mapDerivedCategory.obj M) := by
  let c := HasCompactification.compactification f
  let d := c.ofIsPullback sq
  let e := HasCompactification.compactification f'
  have hc := sectionScalar_compactification φ d e
    ((upperStar (ModuleCat.{u + 1} A) h).mapDerivedCategory.obj M)
  have hn := (rightDerivedLowerShriekIso B d).hom.naturality
    ((properOpenCoefficientPullbackIso φ h).hom.app M)
  dsimp only [Functor.comp_map, Functor.comp_obj] at hn
  simp only [chosen_exchange_app, Category.assoc]
  erw [← hn]
  erw [reassoc_of% (sectionScalar_exchange_raw φ sq c M)]
  change _ = _
  erw [← hc]
  simp only [Functor.map_comp, Category.assoc]
  rfl

private theorem sectionScalar_exchange_left [Finite A] [Finite B]
    (φ : A →+* B)
    {X X' Y Y' : Scheme.{u}}
    {f : X ⟶ Y} {f' : X' ⟶ Y'} {g : Y' ⟶ Y} {h : X' ⟶ X}
    [QuasiCompact f']
    [HasCompactification f] [HasCompactification f']
    (sq : IsPullback h f' f g)
    (M : DerivedCategoryModule A X) :
    (upperStar (ModuleCat.{u + 1} B) g).leftDerivedFunctor.map
        ((compactScalarChosenMap φ f).app M) ≫
      (rightDerivedLowerShriekBaseChangeMap B sq).app ((scalarExtension φ X).obj M) ≫
      (rightDerivedLowerShriek (ModuleCat.{u + 1} B) f').map
        ((scalarPullbackIso φ h).hom.app M) =
      (scalarPullbackIso φ g).hom.app
        ((rightDerivedLowerShriek (ModuleCat.{u + 1} A) f).obj M) ≫
      (scalarExtension φ Y').map ((rightDerivedLowerShriekBaseChangeMap A sq).app M) ≫
      (compactScalarChosenMap φ f').app
        ((upperStar (ModuleCat.{u + 1} A) h).leftDerivedFunctor.obj M) := by
  have hh := sectionScalar_exchange_exact φ sq M
  simp only [properOpenCoefficientPullbackIso, unboundedEtaleCompactSupportBaseChange,
    Iso.trans_hom, Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom,
    Iso.symm_hom, NatTrans.comp_app, Functor.whiskerLeft_app,
    Functor.whiskerRight_app, Functor.map_comp, Category.assoc] at hh
  have hn := (leftDerivedUpperStarIsoMapDerivedCategory
    (ModuleCat.{u + 1} B) g).inv.naturality
    ((compactScalarChosenMap φ f).app M)
  dsimp only [Functor.comp_map, Functor.comp_obj] at hn
  dsimp only [rightDerivedLowerShriek, rightDerivedLowerShriekOfCompactification,
    Functor.comp_obj, Functor.comp_map] at hh hn ⊢
  erw [reassoc_of% hn] at hh
  simp only [← Functor.map_comp_assoc, Iso.hom_inv_id_app,
    CategoryTheory.Functor.map_id, Category.id_comp] at hh
  have hb := (compactScalarChosenMap φ f').naturality
    ((leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) h).hom.app M)
  dsimp only [Functor.comp_map, Functor.comp_obj] at hb
  dsimp only [rightDerivedLowerShriek, rightDerivedLowerShriekOfCompactification,
    Functor.comp_obj, Functor.comp_map] at hb
  simp only [Functor.map_comp, Category.assoc] at hh
  erw [hb] at hh
  simp only [← Functor.map_comp_assoc, Iso.hom_inv_id_app_assoc] at hh
  apply (cancel_epi ((leftDerivedUpperStarIsoMapDerivedCategory
    (ModuleCat.{u + 1} B) g).inv.app _)).1
  apply (cancel_mono ((rightDerivedLowerShriek (ModuleCat.{u + 1} B) f').map
    ((scalarExtension φ X').map
      ((leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) h).hom.app M)))).1
  simpa only [Category.assoc, rightDerivedLowerShriek,
    rightDerivedLowerShriekOfCompactification, Functor.comp_map] using hh

private noncomputable def sectionScalar_iso [Finite A] [Finite B]
    (φ : A →+* B) {X Y : Scheme.{u}} (f : X ⟶ Y) [HasCompactification f] :
    rightDerivedLowerShriek (ModuleCat.{u + 1} A) f ⋙ scalarExtension φ Y ≅
      scalarExtension φ X ⋙ rightDerivedLowerShriek (ModuleCat.{u + 1} B) f := by
  let c := HasCompactification.compactification f
  let (M : DerivedCategoryModule A X) :
      IsIso (ExceptionalCoefficients.compactSupportMap φ c M) := compact_scalar_isIso φ c M
  exact NatIso.ofComponents (fun M ↦ asIso (ExceptionalCoefficients.compactSupportMap φ c M))
    (fun h ↦ compactScalarMap_naturality φ c h)

private theorem sectionScalar_iso_hom [Finite A] [Finite B]
    (φ : A →+* B) {X Y : Scheme.{u}} (f : X ⟶ Y) [HasCompactification f] :
    (sectionScalar_iso φ f).hom = compactScalarChosenMap φ f := by
  rfl

private theorem sectionScalar_inverse [Finite A] [Finite B]
    (φ : A →+* B) {X Y : Scheme.{u}} (f : X ⟶ Y) [HasCompactification f]
    (M : DerivedCategoryModule A X) :
    ExceptionalCoefficients.comparisonInverse φ (HasCompactification.compactification f) M =
      (sectionScalar_iso φ f).inv.app M := by
  unfold ExceptionalCoefficients.comparisonInverse
  rw [dif_pos (compact_scalar_isIso φ (HasCompactification.compactification f) M)]
  rfl

private theorem sectionScalar_counit [Finite A] [Finite B]
    (φ : A →+* B) {X Y : Scheme.{u}} (f : X ⟶ Y) [HasCompactification f]
    (K : DerivedCategoryModule A Y) :
    (rightDerivedLowerShriek (ModuleCat.{u + 1} B) f).map
        (ExceptionalCoefficients.mateMap φ f K) ≫
      (rightDerivedUpperShriekAdjunction B f).counit.app
        ((scalarExtension φ Y).obj K) =
    (sectionScalar_iso φ f).inv.app
        ((rightDerivedUpperShriek A f).obj K) ≫
      (scalarExtension φ Y).map
        ((rightDerivedUpperShriekAdjunction A f).counit.app K) := by
  rw [← sectionScalar_inverse]
  exact (rightDerivedUpperShriekAdjunction B f).homEquiv
    _ ((scalarExtension φ Y).obj K) |>.symm_apply_apply _

attribute [local irreducible] sectionScalar_iso

-- Transpose the compact-support cube, retaining its specified canonical arrows.
private theorem sectionScalar_exceptional [Finite A] [Finite B]
    (φ : A →+* B) {X X' Y Y' : Scheme.{u}}
    {f : X ⟶ Y} {f' : X' ⟶ Y'} {g : Y' ⟶ Y} {h : X' ⟶ X}
    [HasCompactification f] [HasCompactification f'] [QuasiCompact f']
    (sq : IsPullback h f' f g) (K : DerivedCategoryModule A Y) :
    (scalarExtension φ X').map ((rightDerivedUpperShriekBaseChangeMap A sq).app K) ≫
      ExceptionalCoefficients.mateMap φ f'
        ((upperStar (ModuleCat.{u + 1} A) g).leftDerivedFunctor.obj K) ≫
      (rightDerivedUpperShriek B f').map
        ((scalarPullbackIso φ g).inv.app K) =
    (scalarPullbackIso φ h).inv.app
        ((rightDerivedUpperShriek A f).obj K) ≫
      (upperStar (ModuleCat.{u + 1} B) h).leftDerivedFunctor.map
        (ExceptionalCoefficients.mateMap φ f K) ≫
      (rightDerivedUpperShriekBaseChangeMap B sq).app ((scalarExtension φ Y).obj K) := by
  let := isIso_rightDerivedLowerShriekBaseChangeMap A sq
  let := isIso_rightDerivedLowerShriekBaseChangeMap B sq
  let eA := asIso (rightDerivedLowerShriekBaseChangeMap A sq)
  let eB := asIso (rightDerivedLowerShriekBaseChangeMap B sq)
  let a := rightDerivedUpperShriekAdjunction A f
  let b := rightDerivedUpperShriekAdjunction A f'
  let ae := rightDerivedUpperShriekAdjunction B f
  let be := rightDerivedUpperShriekAdjunction B f'
  let αU := sectionScalar_iso φ f
  let αV := sectionScalar_iso φ f'
  have hfwd := sectionScalar_exchange_left φ sq
    ((rightDerivedUpperShriek A f).obj K)
  rw [← sectionScalar_iso_hom φ f, ← sectionScalar_iso_hom φ f'] at hfwd
  have hcube : Adjunction.coefficientPullbackSquare eA.inv eB.inv αU αV
      (scalarPullbackIso φ h).inv (scalarPullbackIso φ g).inv
        ((rightDerivedUpperShriek A f).obj K) := by
    unfold Adjunction.coefficientPullbackSquare
    change (upperStar (ModuleCat.{u + 1} B) g).leftDerivedFunctor.map
        (αU.hom.app _) ≫ eB.hom.app _ ≫
          (rightDerivedLowerShriek (ModuleCat.{u + 1} B) f').map
            ((scalarPullbackIso φ h).hom.app _) =
      (scalarPullbackIso φ g).hom.app _ ≫
        (scalarExtension φ Y').map (eA.hom.app _) ≫ αV.hom.app _ at hfwd
    have hi := IsIso.inv_eq_inv.mpr hfwd
    have hh := congrArg (fun z ↦ αV.hom.app
      ((upperStar (ModuleCat.{u + 1} A) h).leftDerivedFunctor.obj
        ((rightDerivedUpperShriek A f).obj K)) ≫
      z ≫ (upperStar (ModuleCat.{u + 1} B) g).leftDerivedFunctor.map
        (αU.hom.app ((rightDerivedUpperShriek A f).obj K))) hi
    simpa only [IsIso.inv_comp, ← Functor.map_inv, NatIso.inv_hom_app,
      Functor.comp_obj, Category.assoc, ← Functor.map_comp_assoc, ← Functor.map_comp,
      Iso.inv_hom_id_app, Iso.hom_inv_id_app, Iso.inv_hom_id_app_assoc,
      Iso.hom_inv_id_app_assoc, CategoryTheory.Functor.map_id,
      Category.id_comp, Category.comp_id] using hh.symm
  have hβ (R : Type (u + 1)) [CommRing R] [Finite R]
      [IsIso (rightDerivedLowerShriekBaseChangeMap R sq)]
      (L : DerivedCategoryModule R Y) :
      (rightDerivedLowerShriek (ModuleCat.{u + 1} R) f').map
          ((rightDerivedUpperShriekBaseChangeMap R sq).app L) ≫
        (rightDerivedUpperShriekAdjunction R f').counit.app
          ((upperStar (ModuleCat.{u + 1} R) g).leftDerivedFunctor.obj L) =
        inv ((rightDerivedLowerShriekBaseChangeMap R sq).app
          ((rightDerivedUpperShriek R f).obj L)) ≫
        (upperStar (ModuleCat.{u + 1} R) g).leftDerivedFunctor.map
          ((rightDerivedUpperShriekAdjunction R f).counit.app L) := by
    simpa only [rightDerivedUpperShriekBaseChangeMap, NatIso.isIso_inv_app] using
      mateEquiv_counit
      (rightDerivedUpperShriekAdjunction R f)
      (rightDerivedUpperShriekAdjunction R f')
      (inv (rightDerivedLowerShriekBaseChangeMap R sq)) L
  have hh := Adjunction.coefficient_exchange_of_counit_at a b ae be eA.inv eB.inv K
    ((rightDerivedUpperShriekBaseChangeMap A sq).app K)
    ((rightDerivedUpperShriekBaseChangeMap B sq).app ((scalarExtension φ Y).obj K))
    (by simpa only [a, b, eA, asIso, NatIso.isIso_inv_app] using hβ A K)
    (by simpa only [ae, be, eB, asIso, NatIso.isIso_inv_app]
      using hβ B ((scalarExtension φ Y).obj K))
    αU αV (scalarPullbackIso φ h).inv (scalarPullbackIso φ g).inv
    (ExceptionalCoefficients.mateMap φ f K)
    (ExceptionalCoefficients.mateMap φ f'
      ((upperStar (ModuleCat.{u + 1} A) g).leftDerivedFunctor.obj K))
    (sectionScalar_counit φ f K) (sectionScalar_counit φ f' _) hcube
  exact hh.symm

private theorem sectionScalar_mate_eq [Finite A] [Finite B]
    (φ : A →+* B) {X Y : Scheme.{u}} (f : X ⟶ Y) [HasCompactification f]
    (K : DerivedCategoryModule A Y) :
    ExceptionalCoefficients.mateMap φ f K =
      (mateEquiv (rightDerivedUpperShriekAdjunction A f)
        (rightDerivedUpperShriekAdjunction B f)
        (TwoSquare.mk _ _ _ _ (sectionScalar_iso φ f).inv)).app K := by
  apply ((rightDerivedUpperShriekAdjunction
    B f).homEquiv _ _).symm.injective
  rw [ExceptionalCoefficients.mateMap, Equiv.symm_apply_apply,
    Adjunction.homEquiv_counit, mateEquiv_counit, sectionScalar_inverse]

private theorem sectionScalar_mate_naturality [Finite A] [Finite B]
    (φ : A →+* B) {X Y : Scheme.{u}} (f : X ⟶ Y) [HasCompactification f]
    {K L : DerivedCategoryModule A Y} (a : K ⟶ L) :
    (scalarExtension φ X).map ((rightDerivedUpperShriek A f).map a) ≫
        ExceptionalCoefficients.mateMap φ f L =
      ExceptionalCoefficients.mateMap φ f K ≫
        (rightDerivedUpperShriek B f).map
          ((scalarExtension φ Y).map a) := by
  simp only [sectionScalar_mate_eq]
  exact (mateEquiv (rightDerivedUpperShriekAdjunction A f)
    (rightDerivedUpperShriekAdjunction B f)
    (TwoSquare.mk _ _ _ _ (sectionScalar_iso φ f).inv)).naturality a

private theorem sectionScalar_dualizing [Finite A] [Finite B]
    (φ : A →+* B) {X X' Y Y' : Scheme.{u}}
    {f : X ⟶ Y} {f' : X' ⟶ Y'} {g : Y' ⟶ Y} {h : X' ⟶ X}
    [HasCompactification f] [HasCompactification f'] [QuasiCompact f']
    (sq : IsPullback h f' f g) :
    (scalarExtension φ X').map (dualizingComplexBaseChangeMap A sq) ≫
        WeilConjectures.DncCoefficientTransport.dualizingMap φ f' =
      (scalarPullbackIso φ h).inv.app (dualizingComplex A f) ≫
        (upperStar (ModuleCat.{u + 1} B) h).leftDerivedFunctor.map
          (WeilConjectures.DncCoefficientTransport.dualizingMap φ f) ≫
        dualizingComplexBaseChangeMap B sq := by
  have hc := sectionScalar_exceptional φ sq (𝟙_ (DerivedCategoryModule A Y))
  have hu := etaleScalarPullback_unit φ g
  have hu' := congrArg (fun z ↦
    (scalarPullbackIso φ g).inv.app (𝟙_ (DerivedCategoryModule A Y)) ≫ z) hu
  simp only [← Category.assoc, Iso.inv_hom_id_app, Category.id_comp] at hu'
  have hn := sectionScalar_mate_naturality φ f'
    (leftDerivedUpperStarUnitIso (ModuleCat.{u + 1} A) g).hom
  have hb := (rightDerivedUpperShriekBaseChangeMap B sq).naturality
    (ExceptionalCoefficients.unitIso φ Y).hom
  dsimp only [Functor.comp_obj, Functor.comp_map] at hb
  simp only [dualizingComplexBaseChangeMap,
    WeilConjectures.DncCoefficientTransport.dualizingMap,
    Functor.map_comp, Category.assoc]
  rw [reassoc_of% hn]
  simp only [← Functor.map_comp_assoc, ← Functor.map_comp]
  rw [hu']
  simp only [Functor.map_comp, Category.assoc]
  rw [reassoc_of% hc, reassoc_of% hb]
  rfl

-- Transport the exact scalar compositor through the exact/left-derived isomorphisms.
private theorem sectionScalar_composition
    (φ : A →+* B) {X Z Y : Scheme.{u}}
    (g : Z ⟶ Y) (j : X ⟶ Z) (f : X ⟶ Y) (h : f = j ≫ g)
    (K : DerivedCategoryModule A Y) :
    (leftDerivedUpperStarComp (ModuleCat.{u + 1} B) j g f h).hom.app
        ((scalarExtension φ Y).obj K) ≫
      (upperStar (ModuleCat.{u + 1} B) j).leftDerivedFunctor.map
        ((scalarPullbackIso φ g).hom.app K) ≫
      (scalarPullbackIso φ j).hom.app
        ((upperStar (ModuleCat.{u + 1} A) g).leftDerivedFunctor.obj K) =
    (scalarPullbackIso φ f).hom.app K ≫ (scalarExtension φ X).map
      ((leftDerivedUpperStarComp (ModuleCat.{u + 1} A) j g f h).hom.app K) := by
  let eA := fun {V W : Scheme.{u}} (p : V ⟶ W) ↦
    leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) p
  let eB := fun {V W : Scheme.{u}} (p : V ⟶ W) ↦
    leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} B) p
  let cA := Functor.mapDerivedCategoryNatIso
      (upperStarComp (ModuleCat.{u + 1} A) j g f h) ≪≫
    Functor.mapDerivedCategoryCompIso _ _
  let cB := Functor.mapDerivedCategoryNatIso
      (upperStarComp (ModuleCat.{u + 1} B) j g f h) ≪≫
    Functor.mapDerivedCategoryCompIso _ _
  have hcomp := scalarPullback_composition φ g j f h.symm K
  simp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom,
    Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Category.assoc] at hcomp
  have ht := transport_composition (scalarExtension φ Y) (scalarExtension φ Z)
    (scalarExtension φ X) (eA g) (eA j) (eA f)
    (eB g) (eB j) (eB f)
    (scalarPullbackIso φ g) (scalarPullbackIso φ j) (scalarPullbackIso φ f)
    cA cB K (by
      simpa only [eA, eB, cA, cB, Iso.trans_hom, NatTrans.comp_app,
        Functor.map_comp, Category.assoc] using hcomp)
  have hf : (leftDerivedUpperStarComp (ModuleCat.{u + 1} B) j g f h).hom.app
        ((scalarExtension φ Y).obj K) ≫
      (upperStar (ModuleCat.{u + 1} B) j).leftDerivedFunctor.map
        ((scalarPullbackIso φ g).hom.app K) ≫
      (scalarPullbackIso φ j).hom.app
        ((upperStar (ModuleCat.{u + 1} A) g).leftDerivedFunctor.obj K) =
    (scalarPullbackIso φ f).hom.app K ≫ (scalarExtension φ X).map
      ((leftDerivedUpperStarComp (ModuleCat.{u + 1} A) j g f h).hom.app K) := by
    simpa only [leftDerivedUpperStarComp, Functor.leftDerivedFunctorNatIso,
      Functor.leftDerivedFunctorCompIso, leftDerivedUpperStarIsoMapDerivedCategory,
      eA, eB, cA, cB, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
      Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom,
      Functor.whiskerLeft_app, Functor.whiskerRight_app, Category.assoc,
      Iso.inv_hom_id_app_assoc] using ht
  exact hf

private theorem sectionScalar_square
    (φ : A →+* B) {X X' Y Y' : Scheme.{u}}
    (b : Y' ⟶ Y) (v : X' ⟶ X) (s : Y ⟶ X) (s' : Y' ⟶ X')
    (hs : s' ≫ v = b ≫ s) (M : DerivedCategoryModule A X) :
    (scalarExtension φ Y').map
        ((leftDerivedUpperStarComp (ModuleCat.{u + 1} A) b s).inv.app M ≫
          (leftDerivedUpperStarComp (ModuleCat.{u + 1} A) s' v
            (b ≫ s) hs.symm).hom.app M) ≫
      (scalarPullbackIso φ s').inv.app
        ((upperStar (ModuleCat.{u + 1} A) v).leftDerivedFunctor.obj M) ≫
      (upperStar (ModuleCat.{u + 1} B) s').leftDerivedFunctor.map
        ((scalarPullbackIso φ v).inv.app M) =
    (scalarPullbackIso φ b).inv.app
        ((upperStar (ModuleCat.{u + 1} A) s).leftDerivedFunctor.obj M) ≫
      (upperStar (ModuleCat.{u + 1} B) b).leftDerivedFunctor.map
        ((scalarPullbackIso φ s).inv.app M) ≫
      (leftDerivedUpperStarComp (ModuleCat.{u + 1} B) b s).inv.app
        ((scalarExtension φ X).obj M) ≫
      (leftDerivedUpperStarComp (ModuleCat.{u + 1} B) s' v
        (b ≫ s) hs.symm).hom.app ((scalarExtension φ X).obj M) := by
  let k₁ (R : Type (u + 1)) [CommRing R] :=
    leftDerivedUpperStarComp (ModuleCat.{u + 1} R) b s
  let k₂ (R : Type (u + 1)) [CommRing R] :=
    leftDerivedUpperStarComp (ModuleCat.{u + 1} R) s' v (b ≫ s) hs.symm
  let c (R : Type (u + 1)) [CommRing R] := (k₁ R).symm ≪≫ k₂ R
  have h₁ := sectionScalar_composition φ s b (b ≫ s) rfl M
  have h₂ := sectionScalar_composition φ v s' (b ≫ s) hs.symm M
  have hh : (c B).hom.app ((scalarExtension φ X).obj M) ≫
        (upperStar (ModuleCat.{u + 1} B) s').leftDerivedFunctor.map
          ((scalarPullbackIso φ v).hom.app M) ≫
        (scalarPullbackIso φ s').hom.app
          ((upperStar (ModuleCat.{u + 1} A) v).leftDerivedFunctor.obj M) =
      (upperStar (ModuleCat.{u + 1} B) b).leftDerivedFunctor.map
          ((scalarPullbackIso φ s).hom.app M) ≫
        (scalarPullbackIso φ b).hom.app
          ((upperStar (ModuleCat.{u + 1} A) s).leftDerivedFunctor.obj M) ≫
        (scalarExtension φ Y').map ((c A).hom.app M) := by
    simp only [c, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
      Functor.map_comp, Category.assoc]
    rw [h₂]
    apply (cancel_epi ((k₁ B).hom.app ((scalarExtension φ X).obj M))).1
    simp only [Iso.hom_inv_id_app_assoc]
    rw [reassoc_of% h₁]
    dsimp only [k₁, k₂]
    simp only [← Functor.map_comp_assoc, Iso.hom_inv_id_app,
      CategoryTheory.Functor.map_id, Category.id_comp]
  have hh' := congrArg (fun z ↦
    (scalarPullbackIso φ b).inv.app
        ((upperStar (ModuleCat.{u + 1} A) s).leftDerivedFunctor.obj M) ≫
    (upperStar (ModuleCat.{u + 1} B) b).leftDerivedFunctor.map
      ((scalarPullbackIso φ s).inv.app M) ≫ z ≫
    (scalarPullbackIso φ s').inv.app
      ((upperStar (ModuleCat.{u + 1} A) v).leftDerivedFunctor.obj M) ≫
    (upperStar (ModuleCat.{u + 1} B) s').leftDerivedFunctor.map
      ((scalarPullbackIso φ v).inv.app M)) hh
  dsimp only [Functor.comp_obj] at hh'
  simp only [Category.assoc, ← Functor.map_comp_assoc, ← Functor.map_comp,
    Iso.hom_inv_id_app_assoc, Iso.inv_hom_id_app_assoc, Iso.hom_inv_id_app,
    Iso.inv_hom_id_app, Functor.comp_obj, CategoryTheory.Functor.map_id,
    Category.id_comp, Category.comp_id] at hh'
  simpa only [c, k₁, k₂, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    Functor.map_comp, Category.assoc] using hh'.symm

private theorem sectionScalar_sections [Finite A] [Finite B]
    (φ : A →+* B) {X X' Y Y' : Scheme.{u}}
    (f : X ⟶ Y) (f' : X' ⟶ Y')
    [HasCompactification f] [HasCompactification f'] [QuasiCompact f']
    (b : Y' ⟶ Y) (v : X' ⟶ X) (sq : IsPullback v f' f b)
    (s : Y ⟶ X) (s' : Y' ⟶ X') (hs : s' ≫ v = b ≫ s) :
    (scalarPullbackIso φ b).inv.app (sectionInvariant A f s) ≫
        (upperStar (ModuleCat.{u + 1} B) b).leftDerivedFunctor.map
          (WeilConjectures.DncCoefficientTransport.sectionMap φ f s) ≫
        NoetherianSectionSpecialization.sectionMap B f f' b v sq s s' hs =
      (scalarExtension φ Y').map
          (NoetherianSectionSpecialization.sectionMap A f f' b v sq s s' hs) ≫
        WeilConjectures.DncCoefficientTransport.sectionMap φ f' s' := by
  have hc := sectionScalar_dualizing φ sq
  have hsquare := sectionScalar_square φ b v s s' hs
    (dualizingComplex A f)
  have hn := (scalarPullbackIso φ s').inv.naturality (dualizingComplexBaseChangeMap A sq)
  have hp := ((leftDerivedUpperStarComp (ModuleCat.{u + 1} B) b s).symm ≪≫
    leftDerivedUpperStarComp (ModuleCat.{u + 1} B) s' v (b ≫ s) hs.symm).hom.naturality
      (WeilConjectures.DncCoefficientTransport.dualizingMap φ f)
  dsimp only [Functor.comp_obj, Functor.comp_map] at hn hp
  simp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, Category.assoc] at hp
  simp only [Functor.map_comp, Category.assoc] at hsquare
  simp only [sectionInvariant, NoetherianSectionSpecialization.sectionMap,
    WeilConjectures.DncCoefficientTransport.sectionMap,
    Iso.app_inv, Iso.app_hom, Functor.map_comp, Category.assoc]
  rw [reassoc_of% hp, ← reassoc_of% hsquare, reassoc_of% hn]
  simp only [← Functor.map_comp_assoc, ← Functor.map_comp]
  rw [hc]

private theorem sectionScalar_smooth
    (R : Type (u + 1)) [CommRing R] [Finite R]
    {X Y Y' : Scheme.{u}} (f : X ⟶ Y) [HasCompactification f] [QuasiCompact f]
    (g : Y' ⟶ Y) (K : DerivedCategoryModule R Y) :
    smoothExceptionalBaseChangeMap R f g K =
      (rightDerivedUpperShriekBaseChangeMap R (IsPullback.of_hasPullback f g)).app K := by
  let := isIso_rightDerivedLowerShriekBaseChangeMap R (IsPullback.of_hasPullback f g)
  apply ((rightDerivedUpperShriekAdjunction
    R (pullback.snd f g)).homEquiv _ _).symm.injective
  rw [smoothExceptionalBaseChangeMap, Equiv.symm_apply_apply, Adjunction.homEquiv_counit]
  symm
  simpa only [rightDerivedUpperShriekBaseChangeMap, NatIso.isIso_inv_app] using
    mateEquiv_counit (rightDerivedUpperShriekAdjunction R f)
      (rightDerivedUpperShriekAdjunction R (pullback.snd f g))
      (inv (rightDerivedLowerShriekBaseChangeMap R (IsPullback.of_hasPullback f g))) K

end AlgebraicGeometry.Etale

namespace WeilConjectures.DncCoefficientTransport

/-- Scalar extension commutes with the actual exceptional base-change square and
its pullback to any pair of compatible sections.
Source: blueprint/latest, sec-smooth-purity/sk-prop-sp-purity-bc/
sk-prop-sp-purity-bc-mixed.proof.md, exceptional mate cube, and
sk-thm-smooth-purity-general-ring.proof.md, Proof (2), fibre identifications
(blueprint: lem-pur-section-scalar-base-change).
Proof: transpose the two paths under the primed B compact-support adjunction.
The compact-support coefficient comparison is the composite of the ordinary open
comparison and proper scalar mate. Their base-change cube commutes on K-flat
representatives, with the same inverse-image balancing. The counit equations of
the exceptional coefficient map and base-change mate identify the transposes.
This proves the square at the unit, after its canonical scalar and pullback unit
identifications. Whisker by the primed section pullback; inverse-image composition
and scalar balancing identify s' followed by v with b followed by s, giving the
second equation. These are identities of the specified maps, not choices of
isomorphisms. For a merely locally Noetherian primed base, restrict to its affine
open cover and use canonical inverse-image coherence. This proves the section
identity without imposing quasi-compactness on an etale localization. -/
theorem section_scalar_base_change
    {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) (N : ℕ) (hN : 0 < N) (hA : (N : A) = 0) (hB : (N : B) = 0)
    {V S : Scheme.{u}} [IsNoetherian V] [IsNoetherian S]
    (hS : IsUnit (N : Γ(S, ⊤))) (g : V ⟶ S) [HasCompactification g]
    [IsSeparated g] [QuasiCompact g] (d : ℕ) [SmoothOfRelativeDimension d g] :
    (∀ {S' : Scheme.{u}} [IsNoetherian S'] (b : S' ⟶ S),
      Etale.ExceptionalCoefficients.BaseChangeCompatibility φ g b (𝟙_ _)) ∧
    ∀ {V' S' : Scheme.{u}} [IsLocallyNoetherian S'] (g' : V' ⟶ S')
      [HasCompactification g'] [QuasiCompact g']
      (b : S' ⟶ S) (v : V' ⟶ V) (sq : IsPullback v g' g b)
      (s : S ⟶ V) (s' : S' ⟶ V') (hs : s' ≫ v = b ≫ s),
      (Etale.scalarPullbackIso φ b).inv.app (Etale.sectionInvariant A g s) ≫
          (Etale.upperStar (ModuleCat.{u + 1} B) b).leftDerivedFunctor.map
            (sectionMap φ g s) ≫
          Etale.NoetherianSectionSpecialization.sectionMap B g g' b v sq s s' hs =
        (Etale.scalarExtension φ S').map
            (Etale.NoetherianSectionSpecialization.sectionMap A g g' b v sq s s' hs) ≫
          sectionMap φ g' s' := by
  -- The proof is global; equality of derived maps need not descend from an affine cover.
  have _ := hN
  have _ := hA
  have _ := hB
  have _ := hS
  constructor
  · intro S' _ b
    unfold Etale.ExceptionalCoefficients.BaseChangeCompatibility
    simp only [Etale.sectionScalar_smooth]
    exact Etale.sectionScalar_exceptional φ (IsPullback.of_hasPullback g b) _
  · intro V' S' _ g' _ _ b v sq s s' hs
    exact Etale.sectionScalar_sections φ g g' b v sq s s' hs

end WeilConjectures.DncCoefficientTransport
