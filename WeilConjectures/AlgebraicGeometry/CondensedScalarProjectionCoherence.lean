/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.InternalScalarPullbackNormalization
public import WeilConjectures.AlgebraicGeometry.ModuleObjectProjectionMap
public import WeilConjectures.SixFunctors.ScalarSixCompactSupport
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.MonoidalStructure
public import WeilConjectures.CategoryTheory.ModuleObjects.ExtendScalarsFlat
public import WeilConjectures.CategoryTheory.ModuleObjects.ExtendScalarsMonoidal
public import WeilConjectures.CategoryTheory.Monoidal.Instances.DerivedCategoryBraided
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OpenImmersionProjection
public import WeilConjectures.PoincareDuality.ProjectionFormula
public import WeilConjectures.PoincareDuality.Abstract
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LocalizingInputs
import WeilConjectures.CategoryTheory.DerivedCategory.FlatModel
import WeilConjectures.AlgebraicGeometry.QuotientTensorLeftFlatComputation
import WeilConjectures.AlgebraicGeometry.QuotientTensorRightFlatComputation
import WeilConjectures.AlgebraicGeometry.QuotientScalarTensorCanonical
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.PullIsoMonoidal
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.MonoidalBraided
import WeilConjectures.CategoryTheory.Adjunction.ProjectionMapMate

public import WeilConjectures.Topology.ProfiniteCondensedRing
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Hom
public import WeilConjectures.AlgebraicGeometry.CondensedModuleDerivedPushpull
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
public import Mathlib.RingTheory.Ideal.Quotient.Index
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic
import WeilConjectures.SixFunctors.ScalarSixDirectImage
import WeilConjectures.SixFunctors.ScalarSixPullback
import WeilConjectures.SixFunctors.ScalarSixDefinitions

import all WeilConjectures.AlgebraicGeometry.InternalScalarRestrictionMateNormalization
import all WeilConjectures.AlgebraicGeometry.ScalarPullbackSquareCoherence
import WeilConjectures.AlgebraicGeometry.InternalPullNormalizationExistence
import all WeilConjectures.SixFunctors.ScalarSixTensorComparison
import WeilConjectures.CategoryTheory.Adjunction.ProjectionMapCompat
import WeilConjectures.Mathlib.CategoryTheory.Functor.Derived.Adjunction

/-! # Normalized condensed scalar projection coherence

Source: literature/blueprint/latest/blueprint/sec-six-functors/sk-thm-sf-kunneth-verdier/
lem-fix-operation-reduction.proof.md, paragraphs 1 and 3
(blueprint: lem-fix-condensed-scalar-projection-coherence).

All functors are the specified internal-module functors, with ordinary unbounded,
uncompleted relative tensors. The helpers below specialize existing constructions.
-/

@[expose] public noncomputable section
set_option autoImplicit false
-- Keep the large derived-functor proofs from elaborating concurrently.
set_option Elab.async false
set_option synthInstance.maxSize 4096

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped CategoryTheory.Obj

attribute [local irreducible] CategoryTheory.Functor.leftDerivedFunctor
  CategoryTheory.Functor.rightDerivedFunctor CategoryTheory.Functor.mapDerivedCategory
  DerivedCategory.monoidalClosed CategoryTheory.Mod.monoidalClosed
  AlgebraicGeometry.ProEtale.upperStarFromPoint CategoryTheory.Sheaf.monoidalCategory
  DerivedCategory.monoidalCategoryOfMonoidalClosedBraidedCategory

private def uncurryTensorComparison
    {C D : Type*} [Category C] [Category D]
    (F : C ⥤ D) (T : C ⥤ C ⥤ C) (S : D ⥤ D ⥤ D)
    (t : (Functor.postcompose₂.obj F).obj T ⟶
      (((Functor.whiskeringLeft₂ _).obj F).obj F).obj S) :
    Functor.uncurry.obj T ⋙ F ⟶ (F.prod F) ⋙ Functor.uncurry.obj S where
  app Z := (t.app Z.1).app Z.2
  naturality X Y f := by
    have h := (Functor.uncurry.map t).naturality f
    change (F.map ((T.map f.1).app X.2) ≫
      F.map ((T.obj Y.1).map f.2)) ≫ (t.app Y.1).app Y.2 = _ at h
    change F.map ((T.map f.1).app X.2 ≫ (T.obj Y.1).map f.2) ≫ _ = _
    rw [F.map_comp]
    exact h

private theorem natTrans_ext_flat
    {C D : Type*} [Category.{u + 1} C] [Abelian C] [IsGrothendieckAbelian.{u + 1} C]
    [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalClosed C] [BraidedCategory C]
    [Abelian.HasFunctorialFlatResolution C] [HasDerivedCategory.{u + 1} C] [Category D]
    {F G : DerivedCategory C × DerivedCategory C ⥤ D} (α β : F ⟶ G)
    (h : ∀ P Q : CochainComplex C ℤ,
      (HomologicalComplex.quasiIso C (.up ℤ)).kFlat P →
      (HomologicalComplex.quasiIso C (.up ℤ)).kFlat Q →
      (∀ i : ℤ, ObjectProperty.flat (P.X i)) →
      (∀ i : ℤ, ObjectProperty.flat (Q.X i)) →
      α.app (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q) =
        β.app (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q)) : α = β := by
  ext ⟨U, V⟩
  obtain ⟨P, p, hp, hPflat, hP⟩ :=
    CochainComplex.exists_quasiIso_flat_kFlat (DerivedCategory.Q.objPreimage U)
  obtain ⟨Q, q, hq, hQflat, hQ⟩ :=
    CochainComplex.exists_quasiIso_flat_kFlat (DerivedCategory.Q.objPreimage V)
  have := hp
  have := hq
  let eP := asIso (DerivedCategory.Q.map p) ≪≫ DerivedCategory.Q.objObjPreimageIso U
  let eQ := asIso (DerivedCategory.Q.map q) ≪≫ DerivedCategory.Q.objObjPreimageIso V
  apply (cancel_epi (F.mapIso (eP.prod eQ)).hom).1
  change F.map (Prod.mkHom eP.hom eQ.hom) ≫ α.app (U, V) =
    F.map (Prod.mkHom eP.hom eQ.hom) ≫ β.app (U, V)
  rw [α.naturality, β.naturality, h P Q hP hQ hPflat hQflat]

namespace AlgebraicGeometry.ProEtale.QuotientChange


variable {Λ Λ' : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
  [MonObj Λ] [IsCommMonObj Λ] [MonObj Λ'] [IsCommMonObj Λ']

/-- The canonical K-flat monoidal structure on internal derived scalar extension.
This specializes the existing derived-functor construction to the ordinary balanced
extension-of-scalars tensorator, for arbitrary coefficient maps.
Source: Stacks 06YY, 07A4; blueprint tensor reassociation
(blueprint: lem-fix-condensed-scalar-projection-coherence). -/
instance scalarProjectionMonoidal (a : Λ ⟶ Λ') [IsMonHom a] (T : Scheme.{u}) :
    (D a T).Monoidal := by
  unfold D
  letI := Mod.extendScalarsMonoidal (coefficientMap a T)
  exact (extension a T).leftDerivedFunctorMonoidal

/-- The canonical pullback monoidal structure, specialized to the recorded L interface.
Source: Stacks 07A4; blueprint tensor reassociation
(blueprint: lem-fix-condensed-scalar-projection-coherence). -/
instance pullProjectionMonoidal {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (L Λ f).Monoidal := by
  unfold L CondensedRing.moduleObjectDerivedPullback
  exact CondensedRing.monoidal_leftDerivedUpperStar Λ f

/-- The forward K-flat scalar tensorator (functor of tensor to tensor of images).
Source: Stacks 06YY, 07A4; blueprint tensor reassociation
(blueprint: lem-fix-condensed-scalar-projection-coherence). -/
def scalarProjectionTensor (a : Λ ⟶ Λ') [IsMonHom a] (T : Scheme.{u})
    (P Q : DerivedCategory (Modules Λ T)) :
    (D a T).obj (P ⊗ Q) ⟶ (D a T).obj P ⊗ (D a T).obj Q :=
  Functor.OplaxMonoidal.δ (D a T) P Q

/-- The forward canonical pullback tensorator already used in moduleObjectProjectionMap.
Source: Stacks 07A4; blueprint tensor reassociation
(blueprint: lem-fix-condensed-scalar-projection-coherence). -/
def pullProjectionTensor {X Y : Scheme.{u}} (f : X ⟶ Y)
    (P Q : DerivedCategory (Modules Λ Y)) :
    (L Λ f).obj (P ⊗ Q) ⟶ (L Λ f).obj P ⊗ (L Λ f).obj Q :=
  by
    unfold L CondensedRing.moduleObjectDerivedPullback
    exact ((CondensedRing.leftDerivedUpperStarTensor Λ f).app P).app Q

/-- The specified pullback unit with the normalized scalar interface exposed.
Source: Stacks 07A4 (blueprint: lem-fix-condensed-scalar-projection-coherence). -/
def pullProjectionUnit {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (L Λ f).obj (𝟙_ _) ⟶ 𝟙_ _ := by
  unfold L CondensedRing.moduleObjectDerivedPullback
  exact (CondensedRing.leftDerivedUpperStarUnitIso Λ f).hom

/-- The specified counit-transpose projection with its endpoints exposed.
Source: Stacks 0E48 (blueprint: lem-fix-condensed-scalar-projection-coherence). -/
def actualProjection {X Y : Scheme.{u}} (f : X ⟶ Y)
    (K : DerivedCategory (Modules Λ X)) (N : DerivedCategory (Modules Λ Y)) :
    (F Λ f).obj K ⊗ N ⟶ (F Λ f).obj (K ⊗ (L Λ f).obj N) := by
  unfold F L CondensedRing.moduleObjectDerivedPushforward
    CondensedRing.moduleObjectDerivedPullback
  exact CondensedRing.moduleObjectProjectionMap Λ f K N

/-- The existing signed derived symmetry, with its chosen braiding explicit.
Source: K-flat signed total tensor (blueprint: lem-fix-condensed-scalar-projection-coherence).
-/
def scalarProjectionSymmetry (T : Scheme.{u}) (P Q : DerivedCategory (Modules Λ T)) :
    P ⊗ Q ≅ Q ⊗ P :=
  @BraidedCategory.braiding _ _ _ (DerivedCategory.braidedCategory' _) P Q

attribute [local semireducible] D L F

private theorem scalarMonoidal_eq (a : Λ ⟶ Λ') [IsMonHom a] (T : Scheme.{u}) :
    CondensedRing.internalScalarMonoidal a T = Mod.extendScalarsMonoidal (coefficientMap a T) := by
  apply (CondensedRing.internalScalarMonoidalNormalized_existsUnique a T).unique
  · exact (CondensedRing.internalScalarMonoidalNormalized_existsUnique a T).exists.choose_spec
  · intro M N
    exact Mod.tensorObjπ_extendUnitHom_δ_hom (coefficientMap a T) M N

set_option maxHeartbeats 1600000 in
-- Keep the canonical derived and module tensor structures folded during elaboration.
private theorem canonicalTensor_component (a : Λ ⟶ Λ') [IsMonHom a] (T : Scheme.{u})
    (P Q : DerivedCategory (Modules Λ T)) :
    (QuotientSectionTensor.canonicalTensor a T).hom.app (P, Q) =
      scalarProjectionTensor a T P Q := by
  unfold QuotientSectionTensor.canonicalTensor
  dsimp only [id_eq, QuotientSectionTensor.uncurryTensorIso,
    NatIso.ofComponents, Iso.app, asIso]
  rw [scalarMonoidal_eq]
  unfold scalarProjectionTensor D scalarProjectionMonoidal
  let := Mod.extendScalarsMonoidal (coefficientMap a T)
  exact ((extension a T).leftDerivedFunctorMonoidal_δ P Q).symm

set_option maxHeartbeats 1600000 in
-- Keep the canonical derived and module tensor structures folded during elaboration.
private theorem scalarPullTensor (a : Λ ⟶ Λ') [IsMonHom a]
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (b : D a Y ⋙ L Λ' f ≅ L Λ f ⋙ D a X) (hb : PullNormalized a f b)
    (U V : DerivedCategory (Modules Λ Y)) :
    b.hom.app (U ⊗ V) ≫ (D a X).map (pullProjectionTensor f U V) ≫
        scalarProjectionTensor a X ((L Λ f).obj U) ((L Λ f).obj V) =
      (L Λ' f).map (scalarProjectionTensor a Y U V) ≫
        pullProjectionTensor f ((D a Y).obj U) ((D a Y).obj V) ≫
        (b.hom.app U ⊗ₘ b.hom.app V) := by
  let : ∀ T : Scheme.{u}, IsGrothendieckAbelian.{u + 1}
      (ModuleRingedComparison.modules Λ T) :=
    fun T ↦ IsGrothendieckAbelian.of_equivalence (ModuleRingedComparison.equivalence Λ T)
  let : ∀ T : Scheme.{u}, IsGrothendieckAbelian.{u + 1}
      (ModuleRingedComparison.modules Λ' T) :=
    fun T ↦ IsGrothendieckAbelian.of_equivalence (ModuleRingedComparison.equivalence Λ' T)
  let : ∀ T : Scheme.{u}, HasDerivedCategory.{u + 1}
      (ModuleRingedComparison.modules Λ T) :=
    fun _ ↦ HasDerivedCategory.ofIsGrothendieckAbelian _
  let : ∀ T : Scheme.{u}, HasDerivedCategory.{u + 1}
      (ModuleRingedComparison.modules Λ' T) :=
    fun _ ↦ HasDerivedCategory.ofIsGrothendieckAbelian _
  let TY := Functor.uncurry.obj (CondensedRing.derivedTensor Λ Y)
  let TX := Functor.uncurry.obj (CondensedRing.derivedTensor Λ' X)
  let DY := D a Y
  let DX := D a X
  let LR := L Λ f
  let LS := L Λ' f
  let tR := uncurryTensorComparison LR
    (CondensedRing.derivedTensor Λ Y) (CondensedRing.derivedTensor Λ X)
    (by dsimp only [LR]
        unfold L CondensedRing.moduleObjectDerivedPullback
        exact CondensedRing.leftDerivedUpperStarTensor Λ f)
  let tS := uncurryTensorComparison LS
    (CondensedRing.derivedTensor Λ' Y) (CondensedRing.derivedTensor Λ' X)
    (by dsimp only [LS]
        unfold L CondensedRing.moduleObjectDerivedPullback
        exact CondensedRing.leftDerivedUpperStarTensor Λ' f)
  let lhs : TY ⋙ (DY ⋙ LS) ⟶ ((LR ⋙ DX).prod (LR ⋙ DX)) ⋙ TX :=
    Functor.whiskerLeft TY b.hom ≫ Functor.whiskerRight tR DX ≫
      Functor.whiskerLeft (LR.prod LR) (QuotientSectionTensor.canonicalTensor a X).hom
  let rhs : TY ⋙ (DY ⋙ LS) ⟶ ((LR ⋙ DX).prod (LR ⋙ DX)) ⋙ TX :=
    Functor.whiskerRight (QuotientSectionTensor.canonicalTensor a Y).hom LS ≫
      Functor.whiskerLeft (DY.prod DY) tS ≫
      Functor.whiskerRight (NatTrans.prod b.hom b.hom) TX
  have h : lhs = rhs := by
    apply natTrans_ext_flat (C := Modules Λ Y) lhs rhs
    intro P Q hP hQ hPflat hQflat
    dsimp only [lhs, rhs, TY, TX, DY, DX, LR, LS, tR, tS,
      uncurryTensorComparison, NatTrans.comp_app,
      Functor.whiskerLeft_app, Functor.whiskerRight_app]
    have := QuotientTensorFlatModel.targetCompute_isIso a f P Q hP hQ
    apply (cancel_mono (QuotientTensorFlatModel.targetCompute a f P Q)).1
    have := QuotientTensorFlatModel.targetLocalization_isIso a f
      (QuotientSectionTensor.canonicalTensor a X)
      (QuotientSectionTensor.canonicalTensor_normalized a X) P Q hP hQ hPflat hQflat
    have hleft := QuotientTensorFlatModel.left_flat_computation a f b hb
      (QuotientSectionTensor.canonicalTensor a X)
      (QuotientSectionTensor.canonicalTensor_normalized a X) P Q hP hQ hPflat hQflat
    have hright := QuotientTensorFlatModel.right_flat_computation a f b hb
      (QuotientSectionTensor.canonicalTensor a Y)
      (QuotientSectionTensor.canonicalTensor_normalized a Y) P Q hP hQ hPflat hQflat
    rw [QuotientTensorFlatModel.ordinary_square] at hleft
    simpa only [id_eq, Functor.comp_obj, Category.assoc, CondensedRing.derivedTensor,
      Functor.uncurry_obj_obj,
      Functor.uncurry_obj_map, curriedTensor_obj_obj, curriedTensor_map_app,
      curriedTensor_obj_map, ← MonoidalCategory.tensorHom_def, Functor.prod_obj,
      NatTrans.prod] using hleft.trans hright.symm
  simpa only [id_eq, lhs, rhs, TY, TX, DY, DX, LR, LS, tR, tS, uncurryTensorComparison,
    NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.uncurry_obj_obj, Functor.uncurry_obj_map, Functor.prod_obj,
    Functor.comp_obj, NatTrans.prod, CondensedRing.derivedTensor,
    curriedTensor_obj_obj, curriedTensor_map_app, curriedTensor_obj_map,
    ← MonoidalCategory.tensorHom_def, canonicalTensor_component, pullProjectionTensor]
    using NatTrans.congr_app h (U, V)


set_option maxHeartbeats 1600000 in
-- Keep the canonical derived and module tensor structures folded during elaboration.
private theorem scalarSymmetry (a : Λ ⟶ Λ') [IsMonHom a] (T : Scheme.{u})
    (P Q : DerivedCategory (Modules Λ T)) :
    (D a T).map (scalarProjectionSymmetry _ P Q).hom ≫ scalarProjectionTensor a T Q P =
      scalarProjectionTensor a T P Q ≫
        (scalarProjectionSymmetry _ ((D a T).obj P) ((D a T).obj Q)).hom := by
  unfold D scalarProjectionTensor scalarProjectionSymmetry scalarProjectionMonoidal
  let := Mod.extendScalarsMonoidal (coefficientMap a T)
  exact (extension a T).leftDerivedFunctor_map_braiding_hom_δ
    (Mod.extendScalars_map_braiding_hom_δ (coefficientMap a T)) P Q

set_option maxHeartbeats 1600000 in
-- Keep the canonical derived and module tensor structures folded during elaboration.
private theorem pullSymmetry {X Y : Scheme.{u}} (f : X ⟶ Y)
    (P Q : DerivedCategory (Modules Λ Y)) :
    (L Λ f).map (scalarProjectionSymmetry _ P Q).hom ≫ pullProjectionTensor f Q P =
      pullProjectionTensor f P Q ≫
        (scalarProjectionSymmetry _ ((L Λ f).obj P) ((L Λ f).obj Q)).hom := by
  unfold L CondensedRing.moduleObjectDerivedPullback pullProjectionTensor
    scalarProjectionSymmetry
  exact CondensedRing.leftDerivedUpperStarTensor_braiding Λ f P Q

private def pullTensor {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (Functor.postcompose₂.obj (L Λ f)).obj (CondensedRing.derivedTensor Λ Y) ⟶
      (((Functor.whiskeringLeft₂ _).obj (L Λ f)).obj (L Λ f)).obj
        (CondensedRing.derivedTensor Λ X) := by
  unfold L CondensedRing.moduleObjectDerivedPullback
  exact CondensedRing.leftDerivedUpperStarTensor Λ f

set_option maxHeartbeats 1600000 in
-- Keep the canonical derived and module tensor structures folded during elaboration.
private def scalarTensorIso (a : Λ ⟶ Λ') [IsMonHom a] (T : Scheme.{u}) :
    (Functor.postcompose₂.obj (D a T)).obj (CondensedRing.derivedTensor Λ T) ≅
      (((Functor.whiskeringLeft₂ _).obj (D a T)).obj (D a T)).obj
        (CondensedRing.derivedTensor Λ' T) := by
  letI := Mod.extendScalarsMonoidal (coefficientMap a T)
  unfold D CondensedRing.derivedTensor
  exact asIso (extension a T).leftDerivedTensorComparison

set_option maxHeartbeats 1600000 in
-- Keep the canonical derived and module tensor structures folded during elaboration.
private theorem scalarTensorIso_component (a : Λ ⟶ Λ') [IsMonHom a] (T : Scheme.{u})
    (P Q : DerivedCategory (Modules Λ T)) :
    ((scalarTensorIso a T).hom.app P).app Q = scalarProjectionTensor a T P Q := by
  unfold scalarTensorIso scalarProjectionTensor D scalarProjectionMonoidal
  let := Mod.extendScalarsMonoidal (coefficientMap a T)
  exact ((extension a T).leftDerivedFunctorMonoidal_δ P Q).symm

set_option maxHeartbeats 1600000 in
-- Keep the canonical derived and module tensor structures folded during elaboration.
private theorem projectionCompatibility (a : Λ ⟶ Λ') [IsMonHom a]
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (b : D a Y ⋙ L Λ' f ≅ L Λ f ⋙ D a X) (hb : PullNormalized a f b) :
    Adjunction.ComparisonCompatible b (pullTensor (Λ := Λ) f) (pullTensor (Λ := Λ') f)
      (scalarTensorIso a X) (scalarTensorIso a Y) := by
  intro P Q
  apply (cancel_epi (b.hom.app (P ⊗ Q))).1
  simpa only [id_eq, scalarTensorIso_component, Category.assoc, Iso.hom_inv_id_app_assoc,
    CondensedRing.derivedTensor, curriedTensor_obj_obj, curriedTensor_map_app,
    curriedTensor_obj_map, ← MonoidalCategory.tensorHom_def, pullTensor,
    pullProjectionTensor] using scalarPullTensor a f b hb P Q

set_option maxHeartbeats 1600000 in
-- Keep the canonical derived and module tensor structures folded during elaboration.
private theorem pullTensor_eq_δ {X Y : Scheme.{u}} (f : X ⟶ Y)
    (P Q : DerivedCategory (Modules Λ Y)) :
    pullProjectionTensor f P Q = Functor.OplaxMonoidal.δ (L Λ f) P Q := by
  rfl

set_option maxHeartbeats 1600000 in
-- Keep the canonical derived and module tensor structures folded during elaboration.
private theorem pullUnit_eq_η {X Y : Scheme.{u}} (f : X ⟶ Y) :
    pullProjectionUnit (Λ := Λ) f = Functor.OplaxMonoidal.η (L Λ f) := by
  rfl

set_option maxHeartbeats 1600000 in
-- The normalized square specializes several large derived functor structures.
/-- Monoidality of the computation-counit-normalized balancing and compatibility of its
actual unit/counit mate with the specified projection morphism.
Source: blueprint latest, lem-fix-operation-reduction.proof.md, paragraphs 1 and 3;
Stacks 07A4, 0D6D and 0E48 (blueprint: lem-fix-condensed-scalar-projection-coherence).

Proof:
1. Regard both tensor routes as natural transformations on the product of the derived
categories. Every object has a flat-term K-flat representative; naturality and
cancellation of its quasi-isomorphism therefore reduce equality to such pairs.
The left and right flat computations identify the routes with the same ordinary
balanced tensor square. The canonical scalar tensor comparison is exactly the
oplax tensorator, by uniqueness of its ordinary monoidal structure.
2. This tensor equation makes b a monoidal natural isomorphism. Its unit equation
follows by cancellation of the strong monoidal unit. The existing derived braided
structures give all four symmetry equations, including the signed total symmetry.
3. Apply the categorical projection-mate identity to the specified geometric
adjunctions, b, and the four canonical tensorators. Its compatibility assumption is
the tensor equation, and its mate is rho. Unfolding the recorded projection interface
identifies the result with the displayed final equation. No projection or scalar
mate is inverted, and no coefficient flatness or perfectness is used. -/
theorem condensedScalarProjectionCoherence (a : Λ ⟶ Λ') [IsMonHom a]
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (b : D a Y ⋙ L Λ' f ≅ L Λ f ⋙ D a X) (_hb : PullNormalized a f b) :
    (∀ P Q : DerivedCategory (Modules Λ Y),
      b.hom.app (P ⊗ Q) ≫ (D a X).map (pullProjectionTensor f P Q) ≫
          scalarProjectionTensor a X ((L Λ f).obj P) ((L Λ f).obj Q) =
        (L Λ' f).map (scalarProjectionTensor a Y P Q) ≫
          pullProjectionTensor f ((D a Y).obj P) ((D a Y).obj Q) ≫
          (b.hom.app P ⊗ₘ b.hom.app Q)) ∧
    (b.hom.app (𝟙_ _) ≫
        (D a X).map (pullProjectionUnit (Λ := Λ) f) ≫
        Functor.OplaxMonoidal.η (D a X) =
      (L Λ' f).map (Functor.OplaxMonoidal.η (D a Y)) ≫
        (pullProjectionUnit (Λ := Λ') f)) ∧
    (∀ P Q : DerivedCategory (Modules Λ X),
      (D a X).map (scalarProjectionSymmetry _ P Q).hom ≫
          scalarProjectionTensor a X Q P =
        scalarProjectionTensor a X P Q ≫
          (scalarProjectionSymmetry _ ((D a X).obj P) ((D a X).obj Q)).hom) ∧
    (∀ P Q : DerivedCategory (Modules Λ Y),
      (D a Y).map (scalarProjectionSymmetry _ P Q).hom ≫
          scalarProjectionTensor a Y Q P =
        scalarProjectionTensor a Y P Q ≫
          (scalarProjectionSymmetry _ ((D a Y).obj P) ((D a Y).obj Q)).hom) ∧
    (∀ P Q : DerivedCategory (Modules Λ Y),
      (L Λ f).map (scalarProjectionSymmetry _ P Q).hom ≫
          pullProjectionTensor f Q P =
        pullProjectionTensor f P Q ≫
          (scalarProjectionSymmetry _ ((L Λ f).obj P) ((L Λ f).obj Q)).hom) ∧
    (∀ P Q : DerivedCategory (Modules Λ' Y),
      (L Λ' f).map (scalarProjectionSymmetry _ P Q).hom ≫
          pullProjectionTensor f Q P =
        pullProjectionTensor f P Q ≫
          (scalarProjectionSymmetry _ ((L Λ' f).obj P) ((L Λ' f).obj Q)).hom) ∧
    (∀ (K : DerivedCategory (Modules Λ X)) (N : DerivedCategory (Modules Λ Y)),
      scalarProjectionTensor a Y ((F Λ f).obj K) N ≫
          ((rho a f b).app K ⊗ₘ 𝟙 ((D a Y).obj N)) ≫
          actualProjection f ((D a X).obj K) ((D a Y).obj N) =
        (D a Y).map (actualProjection f K N) ≫
          (rho a f b).app (K ⊗ (L Λ f).obj N) ≫
          (F Λ' f).map (scalarProjectionTensor a X K ((L Λ f).obj N)) ≫
          (F Λ' f).map (𝟙 ((D a X).obj K) ⊗ₘ b.inv.app N)) := by
  have hTensor := scalarPullTensor a f b _hb
  let : NatTrans.IsMonoidal b.hom := by
    apply NatTrans.IsMonoidal.of_isIso_of_δ
    intro P Q
    simpa only [Functor.OplaxMonoidal.comp_δ, Category.assoc,
      ← pullTensor_eq_δ, scalarProjectionTensor] using hTensor P Q
  refine ⟨hTensor, ?_, scalarSymmetry a X, scalarSymmetry a Y,
    pullSymmetry f, pullSymmetry f, ?_⟩
  · have hη : b.hom.app (𝟙_ _) ≫
        Functor.OplaxMonoidal.η (L Λ f ⋙ D a X) =
        Functor.OplaxMonoidal.η (D a Y ⋙ L Λ' f) := by
      apply (cancel_epi (Functor.LaxMonoidal.ε (D a Y ⋙ L Λ' f))).1
      rw [← Category.assoc, NatTrans.IsMonoidal.unit, Functor.Monoidal.ε_η,
        Functor.Monoidal.ε_η]
    simpa only [Functor.OplaxMonoidal.comp_η, Category.assoc, ← pullUnit_eq_η] using hη
  · intro K N
    have h := (Adjunction.map_rightAdjointProjectionMap_comp_mateEquiv
      (adj Λ f) (adj Λ' f) (projectionCompatibility a f b _hb) K N).symm
    simpa only [Functor.map_comp, scalarTensorIso_component, CondensedRing.derivedTensor,
      curriedTensor_obj_obj, curriedTensor_map_app, curriedTensor_obj_map,
      ← MonoidalCategory.tensorHom_def, Category.assoc, actualProjection, rho,
      pullTensor, adj, L, F, CondensedRing.moduleObjectDerivedPullback,
      CondensedRing.moduleObjectDerivedPushforward, CondensedRing.moduleObjectProjectionMap,
      CondensedRing.moduleObjectProjectionData, tensorHom_id, id_tensorHom, id_eq]
      using h

/-- The compactification-normalized forward projection: the proper counit transpose,
then proper image of the inverse open projection transpose, then the pullback compositor.
Only the open projection is inverted. This is the published exceptional projection
morphism `CondensedRing.exceptionalProjectionMorphismOfCompactification`, with the
recorded `L` interface exposed; no second construction of the same map is made.
Source: blueprint latest, lem-fix-operation-reduction.proof.md, paragraph 3;
Stacks 0E8I (blueprint: lem-fix-condensed-scalar-projection-coherence). -/
def compactScalarProjection {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (K : DerivedCategory (Modules Λ X)) (N : DerivedCategory (Modules Λ Y)) :
    (CondensedRing.rightDerivedLowerShriekOfCompactification Λ c).obj K ⊗ N ⟶
      (CondensedRing.rightDerivedLowerShriekOfCompactification Λ c).obj
        (K ⊗ (L Λ f).obj N) := by
  unfold L CondensedRing.moduleObjectDerivedPullback
  exact CondensedRing.exceptionalProjectionMorphismOfCompactification Λ c K N

/-- The specified scalar compact-support map with the normalized D endpoints exposed.
It is exactly the existing proper/open paste, without replacing either factor.
Source: blueprint scalar-six compact-support composite
(blueprint: lem-fix-condensed-scalar-projection-coherence). -/
def actualCompactScalarComparison {A B : CondensedRing.ScalarSixRing.{u}} (a : A ⟶ B)
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (K : DerivedCategory (Modules A.X X)) :
    (D (Λ := A.X) (Λ' := B.X) a.hom.hom Y).obj
        ((CondensedRing.rightDerivedLowerShriekOfCompactification A.X c).obj K) ⟶
      (CondensedRing.rightDerivedLowerShriekOfCompactification B.X c).obj
        ((D (Λ := A.X) (Λ' := B.X) a.hom.hom X).obj K) := by
  unfold D
  exact (CondensedRing.scalarCompactSupportMap a c.i c.g).app K

set_option backward.defeqAttrib.useBackward true

-- Elementary monoidal-mate and cancellation calculations used in the compact-support paste.
private theorem mixedTensor
    {C₁ C₂ C₃ C₄ : Type*} [Category* C₁] [Category* C₂]
    [Category* C₃] [Category* C₄]
    [MonoidalCategory C₁] [MonoidalCategory C₂]
    [MonoidalCategory C₃] [MonoidalCategory C₄]
    (LR : C₁ ⥤ C₂) (LS : C₃ ⥤ C₄) (DY : C₁ ⥤ C₃) (DX : C₂ ⥤ C₄)
    [LR.Monoidal] [LS.Monoidal] [DY.Monoidal] [DX.Monoidal]
    (b : DY ⋙ LS ≅ LR ⋙ DX) [NatTrans.IsMonoidal b.hom] (P Q : C₁) :
    DX.map (Functor.LaxMonoidal.μ LR P Q) ≫ b.inv.app (P ⊗ Q) ≫
        LS.map (Functor.OplaxMonoidal.δ DY P Q) =
      Functor.OplaxMonoidal.δ DX (LR.obj P) (LR.obj Q) ≫
        (b.inv.app P ⊗ₘ b.inv.app Q) ≫
        Functor.LaxMonoidal.μ LS (DY.obj P) (DY.obj Q) := by
  have h := NatTrans.IsMonoidal.tensor (τ := b.inv) P Q
  simp only [Functor.LaxMonoidal.comp_μ] at h
  apply (cancel_epi (Functor.LaxMonoidal.μ DX (LR.obj P) (LR.obj Q))).1
  rw [reassoc_of% h, Functor.Monoidal.μ_δ_assoc, ← LS.map_comp,
    Functor.Monoidal.μ_δ, LS.map_id, Category.comp_id]

private theorem inverseProjectionMateSquare
    {C₁ D₁ C₂ D₂ : Type*} [Category* C₁] [Category* D₁]
    [Category* C₂] [Category* D₂]
    [MonoidalCategory C₁] [MonoidalCategory D₁]
    [MonoidalCategory C₂] [MonoidalCategory D₂]
    (FR : C₁ ⥤ D₁) (FS : C₂ ⥤ D₂) (LR : D₁ ⥤ C₁) (LS : D₂ ⥤ C₂)
    (ar : FR ⊣ LR) (as' : FS ⊣ LS) (DX : C₁ ⥤ C₂) (DY : D₁ ⥤ D₂)
    [LR.Monoidal] [LS.Monoidal] [DX.Monoidal] [DY.Monoidal]
    (b : DY ⋙ LS ≅ LR ⋙ DX) [NatTrans.IsMonoidal b.hom]
    (q : FR ⋙ DY ≅ DX ⋙ FS)
    (hq : (mateEquiv ar as' (.mk _ _ _ _ q.inv)).natTrans = b.inv)
    (K : C₁) (M : D₁)
    [IsIso (ar.projectionComparison K M)]
    [IsIso (as'.projectionComparison (DX.obj K) (DY.obj M))] :
    Functor.OplaxMonoidal.δ DY (FR.obj K) M ≫
        (q.hom.app K ⊗ₘ 𝟙 (DY.obj M)) ≫
        inv (as'.projectionComparison (DX.obj K) (DY.obj M)) =
      DY.map (inv (ar.projectionComparison K M)) ≫
        q.hom.app (K ⊗ LR.obj M) ≫
        FS.map (Functor.OplaxMonoidal.δ DX K (LR.obj M)) ≫
        FS.map (𝟙 (DX.obj K) ⊗ₘ b.inv.app M) := by
  have hu (K : C₁) : as'.unit.app (DX.obj K) ≫ LS.map (q.inv.app K) =
      DX.map (ar.unit.app K) ≫ b.inv.app (FR.obj K) := by
    simpa only [hq, Functor.id_obj, Functor.comp_obj, TwoSquare.mk] using (unit_mateEquiv ar as'
      (.mk _ _ _ _ q.inv) K).symm
  have hd := mixedTensor LR LS DY DX b
  have h := Adjunction.projectionMap_mate ar as' LR LS
    (Functor.LaxMonoidal.μNatTrans LR) (Functor.LaxMonoidal.μNatTrans LS)
    (Functor.OplaxMonoidal.δNatTrans DX) (Functor.OplaxMonoidal.δNatTrans DY)
    b.inv b.inv q.inv hu (by
      intro P Q
      simpa only [Functor.LaxMonoidal.μNatTrans,
        Functor.OplaxMonoidal.δNatTrans, curriedTensor_obj_obj,
        curriedTensor_map_app, curriedTensor_obj_map, MonoidalCategory.tensorHom_def,
        Category.assoc, ← tensorHom_comp_tensorHom, Category.comp_id,
        Category.id_comp] using hd P Q) K M
  have hh : q.inv.app (K ⊗ LR.obj M) ≫ DY.map (ar.projectionComparison K M) ≫
      Functor.OplaxMonoidal.δ DY (FR.obj K) M =
    FS.map (Functor.OplaxMonoidal.δ DX K (LR.obj M)) ≫
      FS.map (𝟙 (DX.obj K) ⊗ₘ b.inv.app M) ≫
      as'.projectionComparison (DX.obj K) (DY.obj M) ≫
      (q.inv.app K ⊗ₘ 𝟙 (DY.obj M)) := by
    convert h using 1 <;>
      simp only [Adjunction.projectionComparison, Adjunction.projectionMap_app_app,
      Adjunction.projectionMapTranspose_app_app, Functor.LaxMonoidal.μNatTrans,
      Functor.OplaxMonoidal.δNatTrans,
      Adjunction.homEquiv_counit, curriedTensor_obj_obj, curriedTensor_obj_map,
        curriedTensor_map_app,
      tensorHom_id, id_tensorHom, Category.assoc] <;> rfl
  have he := congrArg (fun t ↦ DY.map (inv (ar.projectionComparison K M)) ≫
    q.hom.app (K ⊗ LR.obj M) ≫ t ≫
    (q.hom.app K ⊗ₘ 𝟙 (DY.obj M)) ≫
    inv (as'.projectionComparison (DX.obj K) (DY.obj M))) hh
  simp only [Category.assoc, Iso.hom_inv_id_app_assoc,
    ← DY.map_comp_assoc, IsIso.inv_hom_id] at he
  simpa [Category.assoc, ← DY.map_comp_assoc,
    ← MonoidalCategory.comp_whiskerRight_assoc] using he

private theorem mate_ofNatIsoLeft
    {C₁ D₁ C₂ D₂ : Type*} [Category* C₁] [Category* D₁]
    [Category* C₂] [Category* D₂]
    {LR LR' : C₁ ⥤ D₁} {FR : D₁ ⥤ C₁} {LS LS' : C₂ ⥤ D₂} {FS : D₂ ⥤ C₂}
    (ar : LR ⊣ FR) (as' : LS ⊣ FS) (eR : LR ≅ LR') (eS : LS ≅ LS')
    (U : C₁ ⥤ C₂) (V : D₁ ⥤ D₂) (σ : U ⋙ LS ⟶ LR ⋙ V) :
    mateEquiv (ar.ofNatIsoLeft eR) (as'.ofNatIsoLeft eS)
      (.mk _ _ _ _ (Functor.whiskerLeft U eS.inv ≫ σ ≫ Functor.whiskerRight eR.hom V)) =
      mateEquiv ar as' (.mk _ _ _ _ σ) := by
  ext K
  simp [mateEquiv_apply, Adjunction.ofNatIsoLeft_unit, Adjunction.ofNatIsoLeft_counit,
    Category.assoc]




private theorem scalarRingComm (A : CondensedRing.ScalarSixRing.{u}) :
    IsCommMonObj A.X := by
  exact A.comm
private theorem scalarRingCommToMon (A : CondensedRing.ScalarSixRing.{u}) :
    IsCommMonObj A.toMon.X := by
  exact A.comm
private theorem scalarMapMon {A B : CondensedRing.ScalarSixRing.{u}} (a : A ⟶ B) :
    IsMonHom a.hom.hom := by
  exact a.hom.isMonHom_hom
attribute [local instance] scalarRingComm scalarRingCommToMon scalarMapMon


private def exactPullIso
    (A : CondensedRing.ScalarSixRing.{u}) {X Y : Scheme.{u}} (f : X ⟶ Y) :
    L A.X f ≅ (CondensedRing.upperStar A.X f).mapDerivedCategory := by
  unfold L CondensedRing.moduleObjectDerivedPullback
  exact CondensedRing.leftDerivedUpperStarIsoMapDerivedCategory A.X f

set_option maxHeartbeats 1600000 in
-- Match the two prescribed geometric adjunctions through their computation counits.
private theorem geometricAdjunctionExact
    (A : CondensedRing.ScalarSixRing.{u}) {X Y : Scheme.{u}} (f : X ⟶ Y) :
    CondensedRing.derivedUpperStarLowerStarAdjunction A.X f =
      (RootCoordinateFace.adjunction A.X f).ofNatIsoLeft
        (CondensedRing.leftDerivedUpperStarIsoMapDerivedCategory A.X f).symm := by
  unfold CondensedRing.derivedUpperStarLowerStarAdjunction RootCoordinateFace.adjunction
    Adjunction.derivedAdjunction Adjunction.mapDerivedCategoryRightDerivedAdjunction
    CondensedRing.leftDerivedUpperStarIsoMapDerivedCategory
  exact ((CondensedRing.upperStarLowerStarAdjunction A.X f).mapHomotopyCategory (.up
    ℤ)).derived_eq_ofNatIsoLeft _ _ _ _ _
      (CondensedRing.upperStar A.X f).leftDerivedFunctorIsoMapDerivedCategory
      (CondensedRing.upperStar A.X f).leftDerivedFunctorIsoMapDerivedCategory_hom_fac.symm

private def scalarTheta {A B : CondensedRing.ScalarSixRing.{u}} (a : A ⟶ B)
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (CondensedRing.upperStar A.X f).mapDerivedCategory ⋙ D (Λ := A.X) (Λ' := B.X) a.hom.hom X ≅
      D (Λ := A.X) (Λ' := B.X) a.hom.hom Y ⋙ (CondensedRing.upperStar B.X f).mapDerivedCategory
        := by
  unfold D
  exact CondensedRing.scalarDirectImagePullbackData.theta a f

set_option maxHeartbeats 1600000 in
-- The square retains the chosen derived adjunctions and localization comparisons.
private theorem scalarSixPull_inverse
    {A B : CondensedRing.ScalarSixRing.{u}} (a : A ⟶ B)
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (b : D (Λ := A.X) (Λ' := B.X) a.hom.hom Y ⋙ L B.X f ≅
      L A.X f ⋙ D (Λ := A.X) (Λ' := B.X) a.hom.hom X)
    (hb : PullNormalized (Λ := A.X) (Λ' := B.X) a.hom.hom f b)
    (N : DerivedCategory (Modules A.X Y)) :
    b.inv.app N =
      (D (Λ := A.X) (Λ' := B.X) a.hom.hom X).map
          ((exactPullIso A f).hom.app N) ≫
        (scalarTheta a f).hom.app N ≫
        (exactPullIso B f).inv.app
          ((D (Λ := A.X) (Λ' := B.X) a.hom.hom Y).obj N) := by
  let eR : L A.X f ≅ (CondensedRing.upperStar A.X f).mapDerivedCategory := by
    unfold L CondensedRing.moduleObjectDerivedPullback
    exact CondensedRing.leftDerivedUpperStarIsoMapDerivedCategory A.X f
  let eS : (CondensedRing.upperStar B.X f).mapDerivedCategory ≅ L B.X f := by
    unfold L CondensedRing.moduleObjectDerivedPullback
    exact (CondensedRing.leftDerivedUpperStarIsoMapDerivedCategory B.X f).symm
  let t := (mateEquiv (scalarAdj (Λ := A.X) (Λ' := B.X) a.hom.hom Y) (scalarAdj (Λ := A.X) (Λ'
    := B.X) a.hom.hom X)).symm
    (TwoSquare.mk _ _ _ _ (CondensedRing.derivedComapUpperStarIso (Λ := A.X) (Λ' := B.X)
      a.hom.hom f).inv)
  have he : (t.whiskerTop eR.hom).whiskerBottom eS.hom =
      (mateEquiv (scalarAdj (Λ := A.X) (Λ' := B.X) a.hom.hom Y) (scalarAdj (Λ := A.X) (Λ' :=
        B.X) a.hom.hom X)).symm
        (TwoSquare.mk _ _ _ _ (normalizationRestrictionPull (Λ := A.X) (Λ' := B.X) a.hom.hom
          f).inv) := by
    apply (mateEquiv (scalarAdj (Λ := A.X) (Λ' := B.X) a.hom.hom Y) (scalarAdj (Λ := A.X) (Λ' :=
      B.X) a.hom.hom X)).injective
    dsimp only [eR, eS, id_eq]
    rw [mateEquiv_whiskerTop_whiskerBottom]
    dsimp only [t, TwoSquare.mk, TwoSquare.natTrans]
    simp only [Equiv.apply_symm_apply]
    ext M
    delta normalizationRestrictionPull
    dsimp only [eR, eS, id, TwoSquare.whiskerRight, TwoSquare.whiskerLeft]
    delta L CondensedRing.moduleObjectDerivedPullback
    dsimp only [TwoSquare.mk, TwoSquare.natTrans, V, V₀]
    simp only [Iso.trans_inv, Functor.isoWhiskerRight_inv, Functor.isoWhiskerLeft_inv,
      Iso.symm_inv, Iso.symm_hom, NatTrans.comp_app, Functor.whiskerRight_app,
      Functor.whiskerLeft_app, Category.assoc]
  have hc := congrArg (fun z ↦ z.natTrans.app N) he
  rw [← normalized_inverse (Λ := A.X) (Λ' := B.X) a.hom.hom f b hb] at hc
  unfold scalarTheta
  dsimp only [id_eq]
  rw [CondensedRing.scalarDirectImagePullbackData.thetaNormalization]
  convert hc.symm using 1
  simp only [t, TwoSquare.whiskerTop, TwoSquare.whiskerBottom, NatTrans.comp_app,
    Functor.whiskerRight_app, Functor.whiskerLeft_app, Category.assoc, eR, eS,
    CondensedRing.scalarSixPullHom, Adjunction.pushHomOfComapIso, scalarAdj,
    D,
    extension, exactPullIso, L, CondensedRing.moduleObjectDerivedPullback, id_eq,
    CondensedRing.scalarSixPull, Iso.symm_hom, TwoSquare.mk, TwoSquare.natTrans]


set_option maxHeartbeats 1600000 in
-- Taking the two mates retains the fixed scalar and open adjunction data.
private theorem scalarOpenMate_exact
    {A B : CondensedRing.ScalarSixRing.{u}} (a : A ⟶ B)
    {X Z : Scheme.{u}} (j : X ⟶ Z) [IsOpenImmersion j] :
    (mateEquiv (CondensedRing.derivedOpenImmersionLowerShriekUpperStarAdjunction A.X j)
      (CondensedRing.derivedOpenImmersionLowerShriekUpperStarAdjunction B.X j)
      (TwoSquare.mk _ _ _ _ (CondensedRing.derivedOpenImmersionShriekIso (Λ := A.X) (Λ' := B.X)
        a.hom.hom j).inv)).natTrans = CondensedRing.scalarSixPullHom a j := by
  have h := congrArg Iso.inv ((conjugateIsoEquiv
    ((Mod.derivedExtendMapDerivedCategoryAdjunction (coefficientMap (Λ := A.X) (Λ' := B.X)
      a.hom.hom X)).comp
      (CondensedRing.derivedOpenImmersionLowerShriekUpperStarAdjunction B.X j))
    ((CondensedRing.derivedOpenImmersionLowerShriekUpperStarAdjunction A.X j).comp
      (Mod.derivedExtendMapDerivedCategoryAdjunction (coefficientMap (Λ := A.X) (Λ' := B.X)
        a.hom.hom Z)))).apply_symm_apply (CondensedRing.derivedComapUpperStarIso (Λ := A.X) (Λ'
        := B.X) a.hom.hom j))
  change conjugateEquiv
    ((CondensedRing.derivedOpenImmersionLowerShriekUpperStarAdjunction A.X j).comp
      (Mod.derivedExtendMapDerivedCategoryAdjunction (coefficientMap (Λ := A.X) (Λ' := B.X)
        a.hom.hom Z)))
    ((Mod.derivedExtendMapDerivedCategoryAdjunction (coefficientMap (Λ := A.X) (Λ' := B.X)
      a.hom.hom X)).comp
      (CondensedRing.derivedOpenImmersionLowerShriekUpperStarAdjunction B.X j))
    (CondensedRing.derivedOpenImmersionShriekIso (Λ := A.X) (Λ' := B.X) a.hom.hom j).inv = _ at h
  rw [conjugateEquiv_comp_eq_mateEquiv_mateEquiv] at h
  have he := (Equiv.eq_symm_apply _).2 h
  convert congrArg TwoSquare.natTrans he using 1
  simp only [CondensedRing.scalarSixPullHom, Adjunction.pushHomOfComapIso,
    CondensedRing.scalarSixPull, TwoSquare.mk, TwoSquare.natTrans]
  rfl


set_option maxHeartbeats 1600000 in
-- Transport through the fixed exact-pullback computation isomorphism.
private theorem scalarOpenMate
    {A B : CondensedRing.ScalarSixRing.{u}} (a : A ⟶ B)
    {X Z : Scheme.{u}} (j : X ⟶ Z) [IsOpenImmersion j]
    (b : D (Λ := A.X) (Λ' := B.X) a.hom.hom Z ⋙ L B.X j ≅
      L A.X j ⋙ D (Λ := A.X) (Λ' := B.X) a.hom.hom X)
    (hb : PullNormalized (Λ := A.X) (Λ' := B.X) a.hom.hom j b) :
    (mateEquiv
      (CondensedRing.derivedOpenImmersionLowerShriekLeftDerivedUpperStarAdjunction A.X j)
      (CondensedRing.derivedOpenImmersionLowerShriekLeftDerivedUpperStarAdjunction B.X j)
      (TwoSquare.mk _ _ _ _
        (CondensedRing.derivedOpenImmersionShriekIso (Λ := A.X) (Λ' := B.X) a.hom.hom
          j).inv)).natTrans =
      b.inv := by
  ext N
  rw [CondensedRing.derivedOpenImmersionLowerShriekLeftDerivedUpperStarAdjunction,
    CondensedRing.derivedOpenImmersionLowerShriekLeftDerivedUpperStarAdjunction,
    mateEquiv_ofNatIsoRight]
  dsimp only [TwoSquare.whiskerTop, TwoSquare.whiskerBottom, NatTrans.comp_app,
    Functor.whiskerRight_app, Functor.whiskerLeft_app, Category.assoc,
    TwoSquare.whiskerRight, TwoSquare.whiskerLeft]
  rw [scalarOpenMate_exact]
  convert (scalarSixPull_inverse a j b hb N).symm using 1
  simp only [exactPullIso, Iso.symm_inv, Iso.symm_hom, id_eq, scalarTheta,
    CondensedRing.scalarDirectImagePullbackData.thetaNormalization,
    CondensedRing.leftDerivedUpperStarIsoMapDerivedCategory_of_isOpenImmersion,
    CondensedRing.leftDerivedUpperStarIsoMapDerivedCategory, D, extension, L,
    CondensedRing.moduleObjectDerivedPullback]

private theorem properProjection_eq_actual
    {A : CondensedRing.ScalarSixRing.{u}} {X Y : Scheme.{u}} (p : X ⟶ Y)
    (K : DerivedCategory (Modules A.X X)) (N : DerivedCategory (Modules A.X Y)) :
    CondensedRing.properProjectionMorphism A.X p K N = actualProjection p K N := by
  rfl

private theorem projectionMorphism_eq_actual
    {A : CondensedRing.ScalarSixRing.{u}} {X Y : Scheme.{u}} (p : X ⟶ Y)
    (K : DerivedCategory (Modules A.X X)) (N : DerivedCategory (Modules A.X Y)) :
    (CondensedRing.derivedUpperStarLowerStarAdjunction A.X p).projectionMorphism K N =
      actualProjection p K N := by
  rfl

private theorem compactPullTensor_δ
    (A : CondensedRing.ScalarSixRing.{u}) {X Y : Scheme.{u}} (f : X ⟶ Y)
    (P Q : DerivedCategory (Modules A.X Y)) :
    pullProjectionTensor f P Q = Functor.OplaxMonoidal.δ (L A.X f) P Q := by
  rfl

set_option maxHeartbeats 1600000 in
-- Specialize the generic inverse projection identity to the prescribed open mate.
private theorem openProjectionSquare
    {A B : CondensedRing.ScalarSixRing.{u}} (a : A ⟶ B)
    {X Z : Scheme.{u}} (j : X ⟶ Z) [IsOpenImmersion j]
    (b : D (Λ := A.X) (Λ' := B.X) a.hom.hom Z ⋙ L B.X j ≅
      L A.X j ⋙ D (Λ := A.X) (Λ' := B.X) a.hom.hom X)
    (hb : PullNormalized (Λ := A.X) (Λ' := B.X) a.hom.hom j b)
    (K : DerivedCategory (Modules A.X X)) (M : DerivedCategory (Modules A.X Z)) :
    scalarProjectionTensor (Λ := A.X) (Λ' := B.X) a.hom.hom Z
        ((CondensedRing.openImmersionLowerShriek A.X j).mapDerivedCategory.obj K) M ≫
      ((CondensedRing.derivedOpenImmersionShriekIso
        (Λ := A.X) (Λ' := B.X) a.hom.hom j).hom.app K ⊗ₘ
        𝟙 ((D (Λ := A.X) (Λ' := B.X) a.hom.hom Z).obj M)) ≫
      inv (CondensedRing.openImmersionProjectionComparison B.X j
        ((D (Λ := A.X) (Λ' := B.X) a.hom.hom X).obj K) ((D (Λ := A.X) (Λ' := B.X) a.hom.hom
          Z).obj M)) =
    (D (Λ := A.X) (Λ' := B.X) a.hom.hom Z).map (inv
      (CondensedRing.openImmersionProjectionComparison A.X j K M)) ≫
      (CondensedRing.derivedOpenImmersionShriekIso
        (Λ := A.X) (Λ' := B.X) a.hom.hom j).hom.app (K ⊗ (L A.X j).obj M) ≫
      (CondensedRing.openImmersionLowerShriek B.X j).mapDerivedCategory.map
        (scalarProjectionTensor (Λ := A.X) (Λ' := B.X) a.hom.hom X K ((L A.X j).obj M)) ≫
      (CondensedRing.openImmersionLowerShriek B.X j).mapDerivedCategory.map
        (𝟙 ((D (Λ := A.X) (Λ' := B.X) a.hom.hom X).obj K) ⊗ₘ b.inv.app M) := by
  let : NatTrans.IsMonoidal b.hom := by
    apply NatTrans.IsMonoidal.of_isIso_of_δ
    intro P Q
    have h := (condensedScalarProjectionCoherence (Λ := A.X) (Λ' := B.X) a.hom.hom j b hb).1 P Q
    simpa only [Functor.OplaxMonoidal.comp_δ, scalarProjectionTensor, Category.assoc,
      ← compactPullTensor_δ] using h
  let : IsIso ((CondensedRing.derivedOpenImmersionLowerShriekLeftDerivedUpperStarAdjunction
      A.X j).projectionComparison K M) :=
    CondensedRing.isIso_openImmersionProjectionComparison A.X j K M
  let : IsIso ((CondensedRing.derivedOpenImmersionLowerShriekLeftDerivedUpperStarAdjunction
      B.X j).projectionComparison ((D (Λ := A.X) (Λ' := B.X) a.hom.hom X).obj K) ((D (Λ := A.X)
        (Λ' := B.X) a.hom.hom Z).obj M)) :=
    CondensedRing.isIso_openImmersionProjectionComparison B.X j _ _
  have h := inverseProjectionMateSquare
    (CondensedRing.openImmersionLowerShriek A.X j).mapDerivedCategory
    (CondensedRing.openImmersionLowerShriek B.X j).mapDerivedCategory
    (L A.X j) (L B.X j)
    (CondensedRing.derivedOpenImmersionLowerShriekLeftDerivedUpperStarAdjunction A.X j)
    (CondensedRing.derivedOpenImmersionLowerShriekLeftDerivedUpperStarAdjunction B.X j)
    (D (Λ := A.X) (Λ' := B.X) a.hom.hom X) (D (Λ := A.X) (Λ' := B.X) a.hom.hom Z) b
    (CondensedRing.derivedOpenImmersionShriekIso
      (Λ := A.X) (Λ' := B.X) a.hom.hom j) (scalarOpenMate a j b hb) K M
  simpa only [scalarProjectionTensor, CondensedRing.openImmersionProjectionComparison]
    using h

set_option maxHeartbeats 1600000 in
-- Compare the exact and total-derived mates without assuming scalar extension exact.
private theorem properScalarMate
    {A B : CondensedRing.ScalarSixRing.{u}} (a : A ⟶ B)
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (b : D (Λ := A.X) (Λ' := B.X) a.hom.hom Y ⋙ L B.X f ≅
      L A.X f ⋙ D (Λ := A.X) (Λ' := B.X) a.hom.hom X)
    (hb : PullNormalized (Λ := A.X) (Λ' := B.X) a.hom.hom f b) :
    rho (Λ := A.X) (Λ' := B.X) a.hom.hom f b = CondensedRing.scalarDirectImageMate a f := by
  let t : D (Λ := A.X) (Λ' := B.X) a.hom.hom Y ⋙ L B.X f ≅ L A.X f ⋙ D (Λ := A.X) (Λ' := B.X)
    a.hom.hom X :=
    Functor.isoWhiskerLeft (D (Λ := A.X) (Λ' := B.X) a.hom.hom Y) (exactPullIso B f) ≪≫
      (scalarTheta a f).symm ≪≫
      Functor.isoWhiskerRight (exactPullIso A f).symm (D (Λ := A.X) (Λ' := B.X) a.hom.hom X)
  have ht : b = t := by
    have hi : b.symm = t.symm := by
      apply Iso.ext
      ext N
      simpa only [t, Iso.symm_hom, Iso.trans_inv, Functor.isoWhiskerLeft_inv,
        Functor.isoWhiskerRight_inv, Iso.symm_inv, NatTrans.comp_app,
        Functor.whiskerLeft_app, Functor.whiskerRight_app, Category.assoc] using
        scalarSixPull_inverse a f b hb N
    simpa only [Iso.symm_symm_eq] using congrArg Iso.symm hi
  rw [ht]
  unfold rho adj
  dsimp only [id_eq]
  rw [geometricAdjunctionExact A f, geometricAdjunctionExact B f]
  dsimp only [t, Iso.trans_hom, Functor.isoWhiskerLeft_hom,
    Functor.isoWhiskerRight_hom, Iso.symm_hom, scalarTheta, id_eq, exactPullIso]
  erw [mate_ofNatIsoLeft]
  rfl

private def bareProjection
    (A : CondensedRing.ScalarSixRing.{u}) {X Z Y : Scheme.{u}}
    (j : X ⟶ Z) [IsOpenImmersion j] (p : Z ⟶ Y)
    (K : DerivedCategory (Modules A.X X)) (N : DerivedCategory (Modules A.X Y)) :
    (F A.X p).obj ((CondensedRing.openImmersionLowerShriek A.X j).mapDerivedCategory.obj K)
      ⊗ N ⟶
    (F A.X p).obj ((CondensedRing.openImmersionLowerShriek A.X j).mapDerivedCategory.obj
      (K ⊗ (L A.X j).obj ((L A.X p).obj N))) :=
  actualProjection p
      ((CondensedRing.openImmersionLowerShriek A.X j).mapDerivedCategory.obj K) N ≫
    (F A.X p).map
      (inv (CondensedRing.openImmersionProjectionComparison A.X j K ((L A.X p).obj N)))

private def bareScalarComparison
    {A B : CondensedRing.ScalarSixRing.{u}} (a : A ⟶ B)
    {X Z Y : Scheme.{u}} (j : X ⟶ Z) [IsOpenImmersion j] (p : Z ⟶ Y)
    (bp : D (Λ := A.X) (Λ' := B.X) a.hom.hom Y ⋙ L B.X p ≅
      L A.X p ⋙ D (Λ := A.X) (Λ' := B.X) a.hom.hom Z)
    (K : DerivedCategory (Modules A.X X)) :
    (D (Λ := A.X) (Λ' := B.X) a.hom.hom Y).obj
        ((F A.X p).obj
          ((CondensedRing.openImmersionLowerShriek A.X j).mapDerivedCategory.obj K)) ⟶
      (F B.X p).obj ((CondensedRing.openImmersionLowerShriek B.X j).mapDerivedCategory.obj
        ((D (Λ := A.X) (Λ' := B.X) a.hom.hom X).obj K)) :=
  (rho (Λ := A.X) (Λ' := B.X) a.hom.hom p bp).app
      ((CondensedRing.openImmersionLowerShriek A.X j).mapDerivedCategory.obj K) ≫
    (F B.X p).map ((CondensedRing.derivedOpenImmersionShriekIso
      (Λ := A.X) (Λ' := B.X) a.hom.hom j).hom.app K)

set_option maxHeartbeats 1600000 in
-- Paste only the specified proper and open projection arrows and their naturalities.
private theorem bareProjectionSquare
    {A B : CondensedRing.ScalarSixRing.{u}} (a : A ⟶ B)
    {X Z Y : Scheme.{u}} (j : X ⟶ Z) [IsOpenImmersion j] (p : Z ⟶ Y)
    (bj : D (Λ := A.X) (Λ' := B.X) a.hom.hom Z ⋙ L B.X j ≅
      L A.X j ⋙ D (Λ := A.X) (Λ' := B.X) a.hom.hom X)
    (bp : D (Λ := A.X) (Λ' := B.X) a.hom.hom Y ⋙ L B.X p ≅
      L A.X p ⋙ D (Λ := A.X) (Λ' := B.X) a.hom.hom Z)
    (hj : PullNormalized (Λ := A.X) (Λ' := B.X) a.hom.hom j bj)
    (hp : PullNormalized (Λ := A.X) (Λ' := B.X) a.hom.hom p bp)
    (K : DerivedCategory (Modules A.X X)) (N : DerivedCategory (Modules A.X Y)) :
    scalarProjectionTensor (Λ := A.X) (Λ' := B.X) a.hom.hom Y
        ((F A.X p).obj
          ((CondensedRing.openImmersionLowerShriek A.X j).mapDerivedCategory.obj K)) N ≫
      (bareScalarComparison a j p bp K ⊗ₘ 𝟙 ((D (Λ := A.X) (Λ' := B.X) a.hom.hom Y).obj N)) ≫
      bareProjection B j p ((D (Λ := A.X) (Λ' := B.X) a.hom.hom X).obj K) ((D (Λ := A.X) (Λ' :=
        B.X) a.hom.hom Y).obj N) =
    (D (Λ := A.X) (Λ' := B.X) a.hom.hom Y).map (bareProjection A j p K N) ≫
      bareScalarComparison a j p bp (K ⊗ (L A.X j).obj ((L A.X p).obj N)) ≫
      (F B.X p).map
        ((CondensedRing.openImmersionLowerShriek B.X j).mapDerivedCategory.map
          (scalarProjectionTensor (Λ := A.X) (Λ' := B.X) a.hom.hom X K ((L A.X j).obj ((L A.X
            p).obj N)) ≫
            (𝟙 ((D (Λ := A.X) (Λ' := B.X) a.hom.hom X).obj K) ⊗ₘ bj.inv.app ((L A.X p).obj N)) ≫
            (𝟙 ((D (Λ := A.X) (Λ' := B.X) a.hom.hom X).obj K) ⊗ₘ (L B.X j).map (bp.inv.app N))))
              := by
  let JR := (CondensedRing.openImmersionLowerShriek A.X j).mapDerivedCategory
  let JS := (CondensedRing.openImmersionLowerShriek B.X j).mapDerivedCategory
  let GR := F A.X p
  let GS := F B.X p
  let DZ := D (Λ := A.X) (Λ' := B.X) a.hom.hom Z
  let q := CondensedRing.derivedOpenImmersionShriekIso
    (Λ := A.X) (Λ' := B.X) a.hom.hom j
  let r := rho (Λ := A.X) (Λ' := B.X) a.hom.hom p bp
  let g := inv (CondensedRing.openImmersionProjectionComparison A.X j K ((L A.X p).obj N))
  have hproper := (condensedScalarProjectionCoherence (Λ := A.X) (Λ' := B.X) a.hom.hom p bp
    hp).2.2.2.2.2.2
    (JR.obj K) N
  have hopen := openProjectionSquare a j bj hj K ((L A.X p).obj N)
  have hr := r.naturality g
  have hn := CondensedRing.inv_openImmersionProjectionComparison_natural_right B.X j
    ((D (Λ := A.X) (Λ' := B.X) a.hom.hom X).obj K) (bp.inv.app N)
  have hpn := (CondensedRing.derivedUpperStarLowerStarAdjunction B.X
    p).projectionMorphism_natural_left (q.hom.app K) ((D (Λ := A.X) (Λ' := B.X) a.hom.hom Y).obj N)
  simp only [projectionMorphism_eq_actual] at hpn
  simp only [tensorHom_id, id_tensorHom] at hproper hopen
  have ho := congrArg GS.map hopen
  have hng := congrArg GS.map hn
  have hm := congrArg GS.map (MonoidalCategory.whisker_exchange (q.hom.app K) (bp.inv.app N))
  simp only [Functor.map_comp] at ho hng hm
  dsimp only [Functor.comp_map, Functor.comp_obj] at hr
  symm
  dsimp only [bareProjection, bareScalarComparison]
  simp only [Functor.map_comp, Category.assoc, tensorHom_id, id_tensorHom]
  erw [reassoc_of% hr, ← reassoc_of% ho, ← hng,
    ← reassoc_of% hm, ← reassoc_of% hproper, ← reassoc_of% hpn]
  simp only [MonoidalCategory.comp_whiskerRight, Category.assoc]
  dsimp only [JR, GS, q, F, CondensedRing.moduleObjectDerivedPushforward, D, id_eq]
  rfl

attribute [local irreducible] CondensedRing.leftDerivedUpperStarComp
  CondensedRing.leftDerivedUpperStarCompactificationIso

private def compactPullIso (A : CondensedRing.ScalarSixRing.{u})
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f) :
    L A.X f ≅ L A.X c.g ⋙ L A.X c.i := by
  unfold L CondensedRing.moduleObjectDerivedPullback
  exact CondensedRing.leftDerivedUpperStarCompactificationIso A.X c

private theorem compactPullIso_eq (A : CondensedRing.ScalarSixRing.{u})
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f) :
    compactPullIso A c = CondensedRing.leftDerivedUpperStarCompactificationIso A.X c := by
  rfl

private theorem inverseObjectTransport
    {I C D : Type*} [Category* C] [Category* D]
    (R : I → C) (S : I → D) (U : C ⥤ D) (b : ∀ i, U.obj (R i) ⟶ S i)
    {i j : I} (h : i = j) :
    U.map (eqToIso (congrArg R h)).inv ≫ b i =
      b j ≫ (eqToIso (congrArg S h)).inv := by
  subst h
  simp only [eqToIso_refl, Iso.refl_inv, U.map_id, Category.id_comp, Category.comp_id]

private theorem inverseObjectPaste
    {C D : Type*} [Category* C] [Category* D] (U : C ⥤ D)
    {A B E : C} {P Q R S : D}
    (s : A ≅ B) (r : B ≅ E) (t : P ≅ Q) (u : Q ≅ R)
    (f : U.obj A ⟶ P) (g : U.obj B ⟶ Q)
    (h₁ : U.obj E ⟶ S) (h₂ : S ⟶ R)
    (hc : U.map s.inv ≫ f = g ≫ t.inv)
    (hg : g = U.map r.hom ≫ h₁ ≫ h₂ ≫ u.inv) :
    U.map (r.inv ≫ s.inv) ≫ f = h₁ ≫ h₂ ≫ u.inv ≫ t.inv := by
  rw [U.map_comp]
  simp only [Category.assoc]
  rw [hc, hg]
  simp only [Category.assoc]
  rw [← U.map_comp_assoc, r.inv_hom_id, U.map_id, Category.id_comp]

private theorem transportInvApp
    {I C D : Type*} [Category* C] [Category* D]
    (F : I → C ⥤ D) {i j : I} (h : i = j) (P : C) :
    (eqToIso (congrArg F h)).inv.app P =
      (eqToIso (congrArg (fun t ↦ (F t).obj P) h)).inv := by
  subst h
  rfl

private theorem inverseFactorApp
    {I C D : Type*} [Category* C] [Category* D]
    (R : I → C ⥤ D) {i j : I} (h : i = j) {G : C ⥤ D}
    (r : R j ≅ G) (v : R i ≅ G)
    (hv : v = eqToIso (congrArg R h) ≪≫ r) (N : C) :
    v.inv.app N = r.inv.app N ≫
      (eqToIso (congrArg (fun t ↦ (R t).obj N) h)).inv := by
  rw [hv, Iso.trans_inv, NatTrans.comp_app, transportInvApp R h N]

private theorem compactPullIso_factor (A : CondensedRing.ScalarSixRing.{u})
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f) :
    compactPullIso A c = eqToIso (congrArg
      (fun t : X ⟶ Y ↦ (CondensedRing.upperStar A.X t).leftDerivedFunctor) c.comm) ≪≫
      CondensedRing.leftDerivedUpperStarComp A.X c.i c.g := by
  rw [compactPullIso_eq]
  unfold CondensedRing.leftDerivedUpperStarCompactificationIso
  rfl

private theorem compactPullIso_inv_factor (A : CondensedRing.ScalarSixRing.{u})
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (N : DerivedCategory (Modules A.X Y)) :
    (compactPullIso A c).inv.app N =
      (CondensedRing.leftDerivedUpperStarComp A.X c.i c.g).inv.app N ≫
        (eqToIso (congrArg (fun t : X ⟶ Y ↦
          (CondensedRing.upperStar A.X t).leftDerivedFunctor.obj N) c.comm)).inv := by
  exact inverseFactorApp
    (fun t : X ⟶ Y ↦ (CondensedRing.upperStar A.X t).leftDerivedFunctor) c.comm
    (CondensedRing.leftDerivedUpperStarComp A.X c.i c.g) (compactPullIso A c)
    (compactPullIso_factor A c) N

attribute [local irreducible] compactPullIso

set_option maxHeartbeats 3200000 in
-- Cancel the geometric compositors in the normalized inverse comparison law.
private theorem comparison_compactification
    {A B : CondensedRing.ScalarSixRing.{u}} (a : A ⟶ B)
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (b : ∀ {U V : Scheme.{u}} (t : U ⟶ V),
      D (Λ := A.X) (Λ' := B.X) a.hom.hom V ⋙ L B.X t ≅
        L A.X t ⋙ D (Λ := A.X) (Λ' := B.X) a.hom.hom U)
    (hb : ∀ {U V : Scheme.{u}} (t : U ⟶ V),
      PullNormalized (Λ := A.X) (Λ' := B.X) a.hom.hom t (b t))
    (N : DerivedCategory (Modules A.X Y)) :
    (D (Λ := A.X) (Λ' := B.X) a.hom.hom X).map ((compactPullIso A c).inv.app N) ≫ (b f).inv.app N =
      (b c.i).inv.app ((L A.X c.g).obj N) ≫
        (L B.X c.i).map ((b c.g).inv.app N) ≫
        (compactPullIso B c).inv.app ((D (Λ := A.X) (Λ' := B.X) a.hom.hom Y).obj N) := by
  have hi := NatTrans.congr_app
    (scalar_comp_inv (Λ := A.X) (Λ' := B.X) a.hom.hom c.i c.g b hb) N
  dsimp only [compositeInverse, Iso.trans_hom, Functor.isoWhiskerLeft_hom,
    Functor.isoWhiskerRight_hom, Functor.associator_hom_app,
    Functor.associator_inv_app, NatTrans.comp_app, Functor.whiskerLeft_app,
    Functor.whiskerRight_app, Category.id_comp, Iso.symm_hom] at hi
  unfold scalarPullbackComposition at hi
  dsimp only [id_eq] at hi
  simp only [Category.id_comp (obj := DerivedCategory (Modules B.X X))] at hi
  have hc := inverseObjectTransport
    (fun t : X ⟶ Y ↦ (CondensedRing.upperStar A.X t).leftDerivedFunctor.obj N)
    (fun t : X ⟶ Y ↦ (CondensedRing.upperStar B.X t).leftDerivedFunctor.obj
      ((D (Λ := A.X) (Λ' := B.X) a.hom.hom Y).obj N))
    (D (Λ := A.X) (Λ' := B.X) a.hom.hom X) (fun t ↦ (b t).inv.app N) c.comm
  have ht := inverseObjectPaste (D (Λ := A.X) (Λ' := B.X) a.hom.hom X)
    (eqToIso (congrArg (fun t : X ⟶ Y ↦
      (CondensedRing.upperStar A.X t).leftDerivedFunctor.obj N) c.comm))
    ((CondensedRing.leftDerivedUpperStarComp A.X c.i c.g).app N)
    (eqToIso (congrArg (fun t : X ⟶ Y ↦
      (CondensedRing.upperStar B.X t).leftDerivedFunctor.obj
        ((D (Λ := A.X) (Λ' := B.X) a.hom.hom Y).obj N)) c.comm))
    ((CondensedRing.leftDerivedUpperStarComp B.X c.i c.g).app
      ((D (Λ := A.X) (Λ' := B.X) a.hom.hom Y).obj N))
    ((b f).inv.app N) ((b (c.i ≫ c.g)).inv.app N)
    ((b c.i).inv.app ((L A.X c.g).obj N)) ((L B.X c.i).map ((b c.g).inv.app N)) hc hi
  erw [compactPullIso_inv_factor A c N,
    compactPullIso_inv_factor B c ((D (Λ := A.X) (Λ' := B.X) a.hom.hom Y).obj N)]
  exact ht


attribute [local irreducible] CondensedRing.scalarDirectImageMate
  CondensedRing.derivedOpenImmersionShriekIso

attribute [local irreducible] actualProjection compactScalarProjection bareProjection
  bareScalarComparison
  CondensedRing.exceptionalProjectionMorphismOfCompactification
  CondensedRing.properProjectionMorphism CondensedRing.openImmersionProjectionComparison

set_option maxHeartbeats 1600000 in
-- Normalize only the pullback/pushforward wrappers at the compactification endpoints.
private theorem compactProjection_factor
    (A : CondensedRing.ScalarSixRing.{u})
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (K : DerivedCategory (Modules A.X X)) (N : DerivedCategory (Modules A.X Y)) :
    compactScalarProjection (Λ := A.X) c K N = bareProjection A c.i c.g K N ≫
      (F A.X c.g).map
        ((CondensedRing.openImmersionLowerShriek A.X c.i).mapDerivedCategory.map
          (𝟙 K ⊗ₘ (compactPullIso A c).inv.app N)) := by
  unfold compactScalarProjection bareProjection
  dsimp only [id_eq]
  rw [CondensedRing.exceptionalProjectionMorphismOfCompactification,
    Functor.map_comp, Category.assoc]
  simp only [properProjection_eq_actual (A := A) c.g, ← compactPullIso_eq A c,
    id_tensorHom]
  dsimp only [F, L, CondensedRing.moduleObjectDerivedPushforward,
    CondensedRing.moduleObjectDerivedPullback, id_eq]

private theorem compactComparison_factor
    {A B : CondensedRing.ScalarSixRing.{u}} (a : A ⟶ B)
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (bp : D (Λ := A.X) (Λ' := B.X) a.hom.hom Y ⋙ L B.X c.g ≅
      L A.X c.g ⋙ D (Λ := A.X) (Λ' := B.X) a.hom.hom c.Z)
    (hp : PullNormalized (Λ := A.X) (Λ' := B.X) a.hom.hom c.g bp)
    (K : DerivedCategory (Modules A.X X)) :
    actualCompactScalarComparison a c K = bareScalarComparison a c.i c.g bp K := by
  have h := properScalarMate a c.g bp hp
  simp only [actualCompactScalarComparison, bareScalarComparison,
    CondensedRing.scalarCompactSupportMap, NatTrans.comp_app, id_eq,
    Functor.whiskerLeft_app, Functor.whiskerRight_app, Functor.associator_inv_app,
    Functor.associator_hom_app, Category.id_comp, Category.comp_id, h]
  dsimp only [F, RootCoordinateFace.lower, CondensedRing.moduleObjectDerivedPushforward, id_eq]

private theorem pastedNaturality
    {C₁ C₂ C₃ C₄ C₅ C₆ : Type*}
    [Category* C₁] [Category* C₂] [Category* C₃]
    [Category* C₄] [Category* C₅] [Category* C₆]
    (JR : C₁ ⥤ C₂) (FR : C₂ ⥤ C₃) (DY : C₃ ⥤ C₆)
    (DX : C₁ ⥤ C₄) (JS : C₄ ⥤ C₅) (FS : C₅ ⥤ C₆) (DZ : C₂ ⥤ C₅)
    (r : FR ⋙ DY ⟶ DZ ⋙ FS) (q : JR ⋙ DZ ⟶ DX ⋙ JS)
    {K H : C₁} (g : K ⟶ H) :
    DY.map (FR.map (JR.map g)) ≫ (r.app (JR.obj H) ≫ FS.map (q.app H)) =
      (r.app (JR.obj K) ≫ FS.map (q.app K)) ≫ FS.map (JS.map (DX.map g)) := by
  have hr := r.naturality (JR.map g)
  have hq := congrArg FS.map (q.naturality g)
  simp only [Functor.comp_map, Functor.map_comp] at hr hq
  rw [← Category.assoc, hr]
  simpa only [Category.assoc] using
    congrArg (fun z ↦ r.app (JR.obj K) ≫ z) hq

private theorem bareScalar_naturality
    {A B : CondensedRing.ScalarSixRing.{u}} (a : A ⟶ B)
    {X Z Y : Scheme.{u}} (j : X ⟶ Z) [IsOpenImmersion j] (p : Z ⟶ Y)
    (bp : D (Λ := A.X) (Λ' := B.X) a.hom.hom Y ⋙ L B.X p ≅
      L A.X p ⋙ D (Λ := A.X) (Λ' := B.X) a.hom.hom Z)
    {K H : DerivedCategory (Modules A.X X)} (g : K ⟶ H) :
    (D (Λ := A.X) (Λ' := B.X) a.hom.hom Y).map ((F A.X p).map
        ((CondensedRing.openImmersionLowerShriek A.X j).mapDerivedCategory.map g)) ≫
        bareScalarComparison a j p bp H =
      bareScalarComparison a j p bp K ≫
        (F B.X p).map
          ((CondensedRing.openImmersionLowerShriek B.X j).mapDerivedCategory.map
            ((D (Λ := A.X) (Λ' := B.X) a.hom.hom X).map g)) := by
  delta bareScalarComparison
  exact pastedNaturality
    (CondensedRing.openImmersionLowerShriek A.X j).mapDerivedCategory
    (F A.X p) (D (Λ := A.X) (Λ' := B.X) a.hom.hom Y)
    (D (Λ := A.X) (Λ' := B.X) a.hom.hom X)
    (CondensedRing.openImmersionLowerShriek B.X j).mapDerivedCategory (F B.X p)
    (D (Λ := A.X) (Λ' := B.X) a.hom.hom Z)
    (rho (Λ := A.X) (Λ' := B.X) a.hom.hom p bp)
    (CondensedRing.derivedOpenImmersionShriekIso
      (Λ := A.X) (Λ' := B.X) a.hom.hom j).hom g

private theorem tensorMapFactor
    {C₁ C₂ : Type*} [Category* C₁] [Category* C₂]
    [MonoidalCategory C₁] [MonoidalCategory C₂]
    (U : C₁ ⥤ C₂) [U.OplaxMonoidal]
    (K : C₁) {P Q : C₁} {R S T : C₂} (e : P ⟶ Q)
    (f : U.obj Q ⟶ T) (r₁ : U.obj P ⟶ R) (r₂ : R ⟶ S) (r₃ : S ⟶ T)
    (h : U.map e ≫ f = r₁ ≫ r₂ ≫ r₃) :
    U.map (𝟙 K ⊗ₘ e) ≫ Functor.OplaxMonoidal.δ U K Q ≫ (𝟙 (U.obj K) ⊗ₘ f) =
      Functor.OplaxMonoidal.δ U K P ≫ (𝟙 (U.obj K) ⊗ₘ r₁) ≫
        (𝟙 (U.obj K) ⊗ₘ r₂) ≫ (𝟙 (U.obj K) ⊗ₘ r₃) := by
  simp only [id_tensorHom]
  rw [← Functor.OplaxMonoidal.δ_natural_right_assoc,
    ← MonoidalCategory.whiskerLeft_comp, h]
  simp only [MonoidalCategory.whiskerLeft_comp]

set_option maxHeartbeats 1600000 in
-- Naturality of the scalar tensorator transports the inverse pullback compositor.
private theorem compactTarget_factor
    {A B : CondensedRing.ScalarSixRing.{u}} (a : A ⟶ B)
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (b : ∀ {U V : Scheme.{u}} (t : U ⟶ V),
      D (Λ := A.X) (Λ' := B.X) a.hom.hom V ⋙ L B.X t ≅
        L A.X t ⋙ D (Λ := A.X) (Λ' := B.X) a.hom.hom U)
    (hb : ∀ {U V : Scheme.{u}} (t : U ⟶ V),
      PullNormalized (Λ := A.X) (Λ' := B.X) a.hom.hom t (b t))
    (K : DerivedCategory (Modules A.X X)) (N : DerivedCategory (Modules A.X Y)) :
    (D (Λ := A.X) (Λ' := B.X) a.hom.hom X).map (𝟙 K ⊗ₘ (compactPullIso A c).inv.app N) ≫
        scalarProjectionTensor (Λ := A.X) (Λ' := B.X) a.hom.hom X K ((L A.X f).obj N) ≫
        (𝟙 ((D (Λ := A.X) (Λ' := B.X) a.hom.hom X).obj K) ⊗ₘ (b f).inv.app N) =
      scalarProjectionTensor (Λ := A.X) (Λ' := B.X) a.hom.hom X K ((L A.X c.i).obj ((L A.X
        c.g).obj N)) ≫
        (𝟙 ((D (Λ := A.X) (Λ' := B.X) a.hom.hom X).obj K) ⊗ₘ (b c.i).inv.app ((L A.X c.g).obj N)) ≫
        (𝟙 ((D (Λ := A.X) (Λ' := B.X) a.hom.hom X).obj K) ⊗ₘ (L B.X c.i).map ((b c.g).inv.app N)) ≫
        (𝟙 ((D (Λ := A.X) (Λ' := B.X) a.hom.hom X).obj K) ⊗ₘ
          (compactPullIso B c).inv.app ((D (Λ := A.X) (Λ' := B.X) a.hom.hom Y).obj N)) := by
  exact tensorMapFactor (D (Λ := A.X) (Λ' := B.X) a.hom.hom X) K
    ((compactPullIso A c).inv.app N) ((b f).inv.app N)
    ((b c.i).inv.app ((L A.X c.g).obj N)) ((L B.X c.i).map ((b c.g).inv.app N))
    ((compactPullIso B c).inv.app ((D (Λ := A.X) (Λ' := B.X) a.hom.hom Y).obj N))
    (comparison_compactification a c b hb N)

set_option maxHeartbeats 1600000 in
-- Append the geometric compositor to the proved proper/open paste.
private theorem compactProjectionSquare
    {A B : CondensedRing.ScalarSixRing.{u}} (a : A ⟶ B)
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (b : ∀ {U V : Scheme.{u}} (t : U ⟶ V),
      D (Λ := A.X) (Λ' := B.X) a.hom.hom V ⋙ L B.X t ≅
        L A.X t ⋙ D (Λ := A.X) (Λ' := B.X) a.hom.hom U)
    (hb : ∀ {U V : Scheme.{u}} (t : U ⟶ V),
      PullNormalized (Λ := A.X) (Λ' := B.X) a.hom.hom t (b t))
    (K : DerivedCategory (Modules A.X X)) (N : DerivedCategory (Modules A.X Y)) :
    scalarProjectionTensor (Λ := A.X) (Λ' := B.X) a.hom.hom Y
        ((CondensedRing.rightDerivedLowerShriekOfCompactification A.X c).obj K) N ≫
        (actualCompactScalarComparison a c K ⊗ₘ 𝟙 ((D (Λ := A.X) (Λ' := B.X) a.hom.hom Y).obj N)) ≫
        compactScalarProjection (Λ := B.X) c
          ((D (Λ := A.X) (Λ' := B.X) a.hom.hom X).obj K)
          ((D (Λ := A.X) (Λ' := B.X) a.hom.hom Y).obj N) =
      (D (Λ := A.X) (Λ' := B.X) a.hom.hom Y).map (compactScalarProjection (Λ := A.X) c K N) ≫
        actualCompactScalarComparison a c (K ⊗ (L A.X f).obj N) ≫
        (CondensedRing.rightDerivedLowerShriekOfCompactification B.X c).map
          (scalarProjectionTensor (Λ := A.X) (Λ' := B.X) a.hom.hom X K ((L A.X f).obj N)) ≫
        (CondensedRing.rightDerivedLowerShriekOfCompactification B.X c).map
          (𝟙 ((D (Λ := A.X) (Λ' := B.X) a.hom.hom X).obj K) ⊗ₘ (b f).inv.app N) := by
  have hn := bareScalar_naturality a c.i c.g (b c.g)
    (𝟙 K ⊗ₘ (compactPullIso A c).inv.app N)
  have ht := congrArg
    (CondensedRing.rightDerivedLowerShriekOfCompactification B.X c).map
    (compactTarget_factor a c b hb K N)
  have hs := bareProjectionSquare a c.i c.g (b c.i) (b c.g) (hb c.i) (hb c.g) K N
  simp only [CondensedRing.rightDerivedLowerShriekOfCompactification,
    Functor.comp_map, Functor.map_comp] at ht hs
  simp only [compactComparison_factor a c (b c.g) (hb c.g)]
  symm
  rw [compactProjection_factor A c K N]
  simp only [Functor.map_comp, Category.assoc]
  erw [reassoc_of% hn]
  dsimp only [CondensedRing.rightDerivedLowerShriekOfCompactification,
    Functor.comp_map, Functor.comp_obj]
  erw [ht]
  have he := congrArg (fun t ↦ t ≫ (F B.X c.g).map
    ((CondensedRing.openImmersionLowerShriek B.X c.i).mapDerivedCategory.map
      (𝟙 ((D (Λ := A.X) (Λ' := B.X) a.hom.hom X).obj K) ⊗ₘ
        (compactPullIso B c).inv.app ((D (Λ := A.X) (Λ' := B.X) a.hom.hom Y).obj N)))) hs
  erw [compactProjection_factor B c
    ((D (Λ := A.X) (Λ' := B.X) a.hom.hom X).obj K)
    ((D (Λ := A.X) (Λ' := B.X) a.hom.hom Y).obj N)]
  simpa only [F, CondensedRing.moduleObjectDerivedPushforward, Category.assoc] using he.symm

private theorem normalized_unique
    {A B : CondensedRing.ScalarSixRing.{u}} (a : A ⟶ B)
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (b d : D (Λ := A.X) (Λ' := B.X) a.hom.hom Y ⋙ L B.X f ≅
      L A.X f ⋙ D (Λ := A.X) (Λ' := B.X) a.hom.hom X)
    (hb : PullNormalized (Λ := A.X) (Λ' := B.X) a.hom.hom f b)
    (hd : PullNormalized (Λ := A.X) (Λ' := B.X) a.hom.hom f d) : b = d := by
  have hi : b.symm = d.symm := Iso.ext
    ((normalized_inverse (Λ := A.X) (Λ' := B.X) a.hom.hom f b hb).trans
      (normalized_inverse (Λ := A.X) (Λ' := B.X) a.hom.hom f d hd).symm)
  simpa only [Iso.symm_symm_eq] using congrArg Iso.symm hi

set_option maxHeartbeats 1600000 in
-- Choose the uniquely normalized comparisons only inside this proof.
private theorem compactProjectionSquare_normalized
    {A B : CondensedRing.ScalarSixRing.{u}} (a : A ⟶ B)
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (b : D (Λ := A.X) (Λ' := B.X) a.hom.hom Y ⋙ L B.X f ≅
      L A.X f ⋙ D (Λ := A.X) (Λ' := B.X) a.hom.hom X)
    (hb : PullNormalized (Λ := A.X) (Λ' := B.X) a.hom.hom f b)
    (K : DerivedCategory (Modules A.X X)) (N : DerivedCategory (Modules A.X Y)) :
    scalarProjectionTensor (Λ := A.X) (Λ' := B.X) a.hom.hom Y
        ((CondensedRing.rightDerivedLowerShriekOfCompactification A.X c).obj K) N ≫
        (actualCompactScalarComparison a c K ⊗ₘ 𝟙 ((D (Λ := A.X) (Λ' := B.X) a.hom.hom Y).obj N)) ≫
        compactScalarProjection (Λ := B.X) c
          ((D (Λ := A.X) (Λ' := B.X) a.hom.hom X).obj K)
          ((D (Λ := A.X) (Λ' := B.X) a.hom.hom Y).obj N) =
      (D (Λ := A.X) (Λ' := B.X) a.hom.hom Y).map (compactScalarProjection (Λ := A.X) c K N) ≫
        actualCompactScalarComparison a c (K ⊗ (L A.X f).obj N) ≫
        (CondensedRing.rightDerivedLowerShriekOfCompactification B.X c).map
          (scalarProjectionTensor (Λ := A.X) (Λ' := B.X) a.hom.hom X K ((L A.X f).obj N)) ≫
        (CondensedRing.rightDerivedLowerShriekOfCompactification B.X c).map
          (𝟙 ((D (Λ := A.X) (Λ' := B.X) a.hom.hom X).obj K) ⊗ₘ b.inv.app N) := by
  classical
  let : ∀ T : Scheme.{u}, IsGrothendieckAbelian.{u + 1}
      (ModuleRingedComparison.modules A.X T) :=
    fun T ↦ IsGrothendieckAbelian.of_equivalence (ModuleRingedComparison.equivalence A.X T)
  let : ∀ T : Scheme.{u}, IsGrothendieckAbelian.{u + 1}
      (ModuleRingedComparison.modules B.X T) :=
    fun T ↦ IsGrothendieckAbelian.of_equivalence (ModuleRingedComparison.equivalence B.X T)
  let : ∀ T : Scheme.{u}, HasDerivedCategory.{u + 1}
      (ModuleRingedComparison.modules A.X T) :=
    fun _ ↦ HasDerivedCategory.ofIsGrothendieckAbelian _
  let : ∀ T : Scheme.{u}, HasDerivedCategory.{u + 1}
      (ModuleRingedComparison.modules B.X T) :=
    fun _ ↦ HasDerivedCategory.ofIsGrothendieckAbelian _
  let ex : ∀ {U V : Scheme.{u}} (t : U ⟶ V),
      ∃ d : D (Λ := A.X) (Λ' := B.X) a.hom.hom V ⋙ L B.X t ≅
        L A.X t ⋙ D (Λ := A.X) (Λ' := B.X) a.hom.hom U,
        PullNormalized (Λ := A.X) (Λ' := B.X) a.hom.hom t d :=
    fun t ↦ internal_pull_normalization_exists (Λ := A.X) (Λ' := B.X) a.hom.hom t
  let d {U V : Scheme.{u}} (t : U ⟶ V) := Classical.choose (ex t)
  have hd {U V : Scheme.{u}} (t : U ⟶ V) :
      PullNormalized (Λ := A.X) (Λ' := B.X) a.hom.hom t (d t) :=
    Classical.choose_spec (ex t)
  have heq := normalized_unique a f b (d f) hb (hd f)
  rw [heq]
  exact compactProjectionSquare a c d (fun t ↦ hd t) K N


set_option maxHeartbeats 1600000 in
-- Expose the scalar-six maps at their fixed internal-module endpoints.
/-- The same projection square for the specified compact-support coefficient comparison,
on its compactification model. The equation uses the actual proper/open paste, rather
than an unspecified isomorphism of the two functors.
Source: blueprint latest, lem-fix-operation-reduction.proof.md, paragraph 3;
det-prop-scalar-six-compact-support.proof.md, proper/open construction
(blueprint: lem-fix-condensed-scalar-projection-coherence).

Proof:
4. The specified scalar/open comparison is the conjugate of the inverse-image
comparison through the composite scalar and open adjunctions. The mate-of-composite
identity and the normalized inverse-pullback characterization identify its inverse
mate with b.inv. Transport along the fixed exact/derived pullback computation
isomorphisms, apply the projection-mate identity, and cancel the open projection
isomorphisms. This gives the forward open projection square on the ambient categories.
5. The exact and total-derived geometric adjunctions agree after transport along their
computation maps, so the specified proper scalar map is rho. Expand the compact-support
comparison and projection into their actual proper/open factors. Naturality of rho,
the open square, the ordinary proper square, and naturality of the proper projection
paste to give the desired square before its final pullback compositor. The normalized
inverse-pullback composition law, including equality transport along c.comm, identifies
that final factor with b.inv. Naturality of the scalar tensorator appends the compositor.
Comparisons for the two compactification factors exist and are uniquely determined by
their normalization; choosing them inside the proof therefore leaves the supplied b
unchanged. Only open projection and pullback comparison isomorphisms are inverted. -/
theorem condensedScalarCompactProjectionCoherence
    (ell : ℕ) [Fact ell.Prime] (k : Type u) [Field k]
    [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ell)]
    (_hcd : BaseFieldFiniteCD ell k)
    {A B : CondensedRing.ScalarSixRing.{u}} (a : A ⟶ B)
    (_ha : CondensedRing.ListedCoefficientMap ell a)
    {X Y : Over (Spec (.of k))}
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
    [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
    (f : X ⟶ Y) (c : Compactification f.left)
    (b : D (Λ := A.X) (Λ' := B.X) a.hom.hom Y.left ⋙ L B.X f.left ≅
      L A.X f.left ⋙ D (Λ := A.X) (Λ' := B.X) a.hom.hom X.left)
    (_hb : PullNormalized (Λ := A.X) (Λ' := B.X) a.hom.hom f.left b)
    (K : DerivedCategory (Modules A.X X.left)) (N : DerivedCategory (Modules A.X Y.left)) :
    scalarProjectionTensor (Λ := A.X) (Λ' := B.X) a.hom.hom Y.left
        ((CondensedRing.rightDerivedLowerShriekOfCompactification A.X c).obj K) N ≫
        (actualCompactScalarComparison a c K ⊗ₘ
          𝟙 ((D (Λ := A.X) (Λ' := B.X) a.hom.hom Y.left).obj N)) ≫
        compactScalarProjection c ((D (Λ := A.X) (Λ' := B.X) a.hom.hom X.left).obj K)
          ((D (Λ := A.X) (Λ' := B.X) a.hom.hom Y.left).obj N) =
      (D (Λ := A.X) (Λ' := B.X) a.hom.hom Y.left).map (compactScalarProjection c K N) ≫
        actualCompactScalarComparison a c (K ⊗ (L A.X f.left).obj N) ≫
        (CondensedRing.rightDerivedLowerShriekOfCompactification B.X c).map
          (scalarProjectionTensor (Λ := A.X) (Λ' := B.X) a.hom.hom X.left
            K ((L A.X f.left).obj N)) ≫
        (CondensedRing.rightDerivedLowerShriekOfCompactification B.X c).map
          (𝟙 ((D (Λ := A.X) (Λ' := B.X) a.hom.hom X.left).obj K) ⊗ₘ b.inv.app N) := by
  exact compactProjectionSquare_normalized a c b _hb K N

end AlgebraicGeometry.ProEtale.QuotientChange
