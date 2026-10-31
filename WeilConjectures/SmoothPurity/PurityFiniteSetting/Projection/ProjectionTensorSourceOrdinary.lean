/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurityFiniteSetting.Projection.ProjectionTensorOrdinaryData

import all WeilConjectures.SmoothPurity.PurityFiniteSetting.SmoothPurityMap
import all WeilConjectures.AlgebraicGeometry.FiniteEtaleTateTwist
import all WeilConjectures.AlgebraicGeometry.Sites.Kummer
import all Mathlib.Algebra.Module.ZMod
import all Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
import all Mathlib.CategoryTheory.Sites.Monoidal
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import all WeilConjectures.AlgebraicGeometry.EtaleConstantRingModuleEquivalence
import all WeilConjectures.CategoryTheory.RingedSiteModules
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import all WeilConjectures.AlgebraicGeometry.VectorIntegrationSite.FiniteSiteCoordinates
import all WeilConjectures.SmoothPurity.PurityFiniteSetting.Affine.AffineDiagonalTensorCoordinates
import all WeilConjectures.AlgebraicGeometry.AffineOrderedIntegration.AffineOrderedIntegrationData
import all WeilConjectures.AlgebraicGeometry.AffineSpacePurity.AffineSpacePurityComparison
import all WeilConjectures.SmoothPurity.PurityFiniteSetting.Projection.ProjectionPurityCoordinates

/-! # The ordinary source of the projection tensor calculation

Source: projection purity agreement, final canonical reassociations.
(blueprint: lem-pur-projection-tensor-source-ordinary)
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.Functor
namespace WeilConjectures.PurityFiniteSetting
open ProEtale ProEtale.AffineSpacePurity ProEtale.VectorIntegrationSite

attribute [local semireducible] baseExponentComparison orderedSource twistAction
  AffineLinePurity.projectionSourceObject AffineLinePurity.ordinarySourceObject
  AffineLinePurity.proSourceObject

set_option linter.auxLemma false in
attribute [local instance 100000] Etale.DerivedCategoryModule._proof_1
  Etale.DerivedCategoryModule._proof_2
  AffineSpacePurity.C._proof_1 AffineSpacePurity.C._proof_2
attribute [local instance high] SymmetricCategory.toBraidedCategory
attribute [local instance 20000] Etale.sheafBraidedCategory

attribute [local irreducible] Padic.coefficientExtensionIntegers

attribute [local irreducible] HasDerivedCategory.ofIsGrothendieckAbelian
  Scheme.finiteEtaleTateLine DerivedCategory.TStructure.t
  Functor.leftDerivedFunctor Functor.mapDerivedCategory DerivedCategory.singleFunctors

private theorem action_rec_compare
    {B : Type*} [Category B] [MonoidalCategory B]
    (L R : ℕ → B) (line : B) (e0 : L 0 ≅ 𝟙_ B) (f0 : R 0 ≅ 𝟙_ B)
    (es : ∀ d, L (d + 1) ≅ L d ⊗ line)
    (fs : ∀ d, R (d + 1) ≅ R d ⊗ line) (v : ∀ d, L d ≅ R d)
    (h0 : (v 0).hom ≫ f0.hom = e0.hom)
    (hs : ∀ d, (v (d + 1)).hom ≫ (fs d).hom =
      (es d).hom ≫ (v d).hom ▷ line) (M : B) (d : ℕ) :
    M ◁ (v d).hom ≫ (projectionTensorActionGeneric B R line f0 fs M d).hom =
      (projectionTensorActionGeneric B L line e0 es M d).hom := by
  induction d with
  | zero =>
    change M ◁ (v 0).hom ≫ (M ◁ f0.hom ≫ (ρ_ M).hom) =
      M ◁ e0.hom ≫ (ρ_ M).hom
    rw [← whiskerLeft_comp_assoc, h0]
  | succ d ih =>
    change M ◁ (v (d + 1)).hom ≫ (M ◁ (fs d).hom ≫
      (α_ M (R d) line).inv ≫
      (projectionTensorActionGeneric B R line f0 fs M d).hom ▷ line) =
      M ◁ (es d).hom ≫ (α_ M (L d) line).inv ≫
        (projectionTensorActionGeneric B L line e0 es M d).hom ▷ line
    rw [← whiskerLeft_comp_assoc, hs, whiskerLeft_comp_assoc,
      associator_inv_naturality_middle_assoc]
    rw [← comp_whiskerRight, ih]

private theorem action_rec_natural
    {B : Type*} [Category B] [MonoidalCategory B]
    (L : ℕ → B) (line : B) (e0 : L 0 ≅ 𝟙_ B)
    (es : ∀ d, L (d + 1) ≅ L d ⊗ line) {M M' : B} (f : M ⟶ M') (d : ℕ) :
    f ▷ L d ≫ (projectionTensorActionGeneric B L line e0 es M' d).hom =
      (projectionTensorActionGeneric B L line e0 es M d).hom ≫
        (action ((curriedTensor B).flip.obj line) d).map f := by
  induction d with
  | zero =>
    change f ▷ L 0 ≫ (M' ◁ e0.hom ≫ (ρ_ M').hom) =
      (M ◁ e0.hom ≫ (ρ_ M).hom) ≫ f
    rw [← whisker_exchange_assoc, rightUnitor_naturality, Category.assoc]
  | succ d ih =>
    change f ▷ L (d + 1) ≫ (M' ◁ (es d).hom ≫
      (α_ M' (L d) line).inv ≫
      (projectionTensorActionGeneric B L line e0 es M' d).hom ▷ line) =
      (M ◁ (es d).hom ≫ (α_ M (L d) line).inv ≫
        (projectionTensorActionGeneric B L line e0 es M d).hom ▷ line) ≫
        (action ((curriedTensor B).flip.obj line) d).map f ▷ line
    rw [← whisker_exchange_assoc, associator_inv_naturality_left_assoc,
      ← comp_whiskerRight, ih, comp_whiskerRight]
    simp only [Category.assoc]

private theorem root_transition_eq
    (F : FiniteFieldDatum.{u}) (C : F.CoefficientDatum)
    (E : IntermediateField (Padic C.l) C.Qbar) [FiniteDimensional (Padic C.l) E]
    (n : ℕ) (T : Scheme.{u}) (aT : T ⟶ Spec (.of F.k)) :
    projectionRootTransition F C E n T aT =
      exponentTransition C.l E n T
        (AffineLinePurity.primeUnit (projectionSetting F C E n) T aT)
        n (n + 1) (Nat.le_succ n) (projectionSetting F C E n).diagonalExponent_annihilates
        (annihilates (projectionSetting F C E n)) 1 := by
  apply (projectionRootTransition_existsUnique F C E n T aT).unique
  · exact (projectionRootTransition_existsUnique F C E n T aT).exists.choose_spec
  · unfold exponentTransition
    exact ((Scheme.finite_tate_site_descent C.l E n).choose_spec.2.2.1 T
      (AffineLinePurity.primeUnit (projectionSetting F C E n) T aT)
      n (n + 1) (Nat.le_succ n) (projectionSetting F C E n).diagonalExponent_annihilates
      (annihilates (projectionSetting F C E n)) 1).exists.choose_spec.1

private theorem coefficient_action_generic
    (A : Type (u + 1)) [CommRing A] [Finite A]
    (N : ℕ) (hA : (N : A) = 0) (T : Scheme.{u}) (M : AffineSpacePurity.C A T) (d : ℕ) :
    AffineOrderedIntegration.coefficientActionComparison A N hA T M d =
      projectionTensorActionGeneric (AffineSpacePurity.C A T)
        (fun i ↦ (comparison A T).obj (Etale.affineLinearBaseCoefficient A N hA T i))
        ((comparison A T).obj ((Etale.ordinaryFiniteLine A N hA T)⟦(2 : ℤ)⟧))
        (AffineLinePurity.coefficientUnitIso (ModuleCat.{u + 1} A) T)
        (fun i ↦ tensorComparison A T (Etale.affineLinearBaseCoefficient A N hA T i)
          ((Etale.ordinaryFiniteLine A N hA T)⟦(2 : ℤ)⟧)) M d := by
  induction d with
  | zero =>
    change AffineLinePurity.moduleRightUnit A T M =
      ((curriedTensor (AffineSpacePurity.C A T)).obj M).mapIso
        (AffineLinePurity.coefficientUnitIso (ModuleCat.{u + 1} A) T) ≪≫ ρ_ M
    unfold AffineLinePurity.moduleRightUnit AffineLinePurity.coefficientRightUnit
    rfl
  | succ d ih =>
    simp only [AffineOrderedIntegration.coefficientActionComparison,
      projectionTensorActionGeneric, ih]
    unfold AffineOrderedIntegration.reassociate ProEtale.projectionActionAssociator
      AffineSpacePurity.tensorIso
    simp only [Functor.mapIso_refl, Iso.trans_refl]
    rfl

private theorem coefficient_action_natural
    (A : Type (u + 1)) [CommRing A] [Finite A]
    (N : ℕ) (hA : (N : A) = 0) (T : Scheme.{u})
    {M M' : AffineSpacePurity.C A T} (f : M ⟶ M') (d : ℕ) :
    f ▷ (comparison A T).obj (Etale.affineLinearBaseCoefficient A N hA T d) ≫
        (AffineOrderedIntegration.coefficientActionComparison A N hA T M' d).hom =
      (AffineOrderedIntegration.coefficientActionComparison A N hA T M d).hom ≫
        (action ((AffineSpacePurity.tensor A T).flip.obj
          ((comparison A T).obj ((Etale.ordinaryFiniteLine A N hA T)⟦(2 : ℤ)⟧))) d).map f := by
  rw [coefficient_action_generic, coefficient_action_generic]
  exact action_rec_natural
    (fun i ↦ (comparison A T).obj (Etale.affineLinearBaseCoefficient A N hA T i))
    ((comparison A T).obj ((Etale.ordinaryFiniteLine A N hA T)⟦(2 : ℤ)⟧))
    (AffineLinePurity.coefficientUnitIso (ModuleCat.{u + 1} A) T)
    (fun i ↦ tensorComparison A T (Etale.affineLinearBaseCoefficient A N hA T i)
      ((Etale.ordinaryFiniteLine A N hA T)⟦(2 : ℤ)⟧)) f d

private theorem coefficient_unit_natural
    (A : Type (u + 1)) [CommRing A] (T : Scheme.{u})
    {M M' : AffineSpacePurity.C A T} (f : M ⟶ M') :
    f ▷ unit A T ≫ (AffineLinePurity.moduleRightUnit A T M').hom =
      (AffineLinePurity.moduleRightUnit A T M).hom ≫ f := by
  unfold AffineLinePurity.moduleRightUnit AffineLinePurity.coefficientRightUnit
  change f ▷ unit A T ≫
      (M' ◁ (AffineLinePurity.coefficientUnitIso (ModuleCat.{u + 1} A) T).hom ≫
        (ρ_ M').hom) =
    (M ◁ (AffineLinePurity.coefficientUnitIso (ModuleCat.{u + 1} A) T).hom ≫
      (ρ_ M).hom) ≫ f
  erw [← whisker_exchange_assoc, rightUnitor_naturality, Category.assoc]
  rfl

private theorem tensor_action_spec
    (F : FiniteFieldDatum.{u}) (C : F.CoefficientDatum)
    (E : IntermediateField (Padic C.l) C.Qbar) [FiniteDimensional (Padic C.l) E]
    (n : ℕ) (T : Scheme.{u}) (aT : T ⟶ Spec (.of F.k))
    (M : AffineSpacePurity.C (projectionSetting F C E n).Coefficient T) (d : ℕ) :
    projectionTensorActionIso F C E n T aT M d =
      projectionTensorActionGeneric
        (AffineSpacePurity.C (projectionSetting F C E n).Coefficient T)
        ((projectionSetting F C E n).diagonalTwist T) (projectionShiftedLine F C E n T)
        (projectionDiagonalUnit F C E n T) (projectionTensorStep F C E n T aT) M d := by
  exact eq_of_heq ((projectionTensorActionIso_existsUnique F C E n T aT M d).exists.choose_spec
    _ _ _ _ (fun _ ↦ HEq.rfl) HEq.rfl HEq.rfl (fun _ ↦ HEq.rfl))

private theorem tensor_step_spec
    (F : FiniteFieldDatum.{u}) (C : F.CoefficientDatum)
    (E : IntermediateField (Padic C.l) C.Qbar) [FiniteDimensional (Padic C.l) E]
    (n : ℕ) (T : Scheme.{u}) (aT : T ⟶ Spec (.of F.k)) (d : ℕ) :
    projectionTensorStep F C E n T aT d =
      (projectionTensorStepFromSheaf (projectionSetting F C E n).Coefficient T
        ((projectionSetting F C E n).diagonalTwistEtale T d)
        (projectionRootTransition F C E n T aT).symm).2.2 := by
  exact eq_of_heq ((projectionTensorStep_existsUnique F C E n T aT d).exists.choose_spec
    _ _ _ _ _ HEq.rfl HEq.rfl HEq.rfl HEq.rfl HEq.rfl HEq.rfl)

private theorem tensor_comparison_map
    (A : Type (u + 1)) [CommRing A] [Finite A] (T : Scheme.{u})
    {M M' N N' : Etale.DerivedCategoryModule A T} (e : M ≅ M') (f : N ≅ N') :
    (comparison A T).map (Etale.ordinaryFiniteTensorRightMapIso A T e f).hom ≫
        (tensorComparison A T M' N').hom =
      (tensorComparison A T M N).hom ≫
        (AffineSpacePurity.tensorIso A T
          ((comparison A T).mapIso e) ((comparison A T).mapIso f)).hom := by
  let : IsNoetherianRing A := isNoetherian_of_finite A A
  let : (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) T).PreservesFlat :=
    ProEtale.preservesFlat_comparisonUpperStar
  unfold Etale.ordinaryFiniteTensorRightMapIso AffineSpacePurity.tensorIso tensorComparison
  change (comparison A T).map
      (((Etale.derivedTensor (ModuleCat.{u + 1} A) T).map e.hom).app N ≫
        ((Etale.derivedTensor (ModuleCat.{u + 1} A) T).obj M').map f.hom) ≫
      (ProEtale.derivedTensorObjCompMapDerivedCategoryComparisonUpperStarIso
        (ModuleCat.{u + 1} A) M').hom.app N' =
    (ProEtale.derivedTensorObjCompMapDerivedCategoryComparisonUpperStarIso
      (ModuleCat.{u + 1} A) M).hom.app N ≫
      (((ProEtale.derivedTensor (ModuleCat.{u + 1} A) T).map
        ((comparison A T).map e.hom)).app ((comparison A T).obj N) ≫
      ((ProEtale.derivedTensor (ModuleCat.{u + 1} A) T).obj
        ((comparison A T).obj M')).map ((comparison A T).map f.hom))
  have hn : (comparison A T).map
      (((Etale.derivedTensor (ModuleCat.{u + 1} A) T).obj M').map f.hom) ≫
      (ProEtale.derivedTensorObjCompMapDerivedCategoryComparisonUpperStarIso
        (ModuleCat.{u + 1} A) M').hom.app N' =
    (ProEtale.derivedTensorObjCompMapDerivedCategoryComparisonUpperStarIso
      (ModuleCat.{u + 1} A) M').hom.app N ≫
      ((ProEtale.derivedTensor (ModuleCat.{u + 1} A) T).obj
        ((comparison A T).obj M')).map ((comparison A T).map f.hom) := by
    exact (ProEtale.derivedTensorObjCompMapDerivedCategoryComparisonUpperStarIso
      (ModuleCat.{u + 1} A) M').hom.naturality f.hom
  rw [Functor.map_comp, Category.assoc, hn, ← Category.assoc,
    comparisonTensor_naturality, Category.assoc]

private theorem diagonal_unit_eq
    (F : FiniteFieldDatum.{u}) (C : F.CoefficientDatum)
    (E : IntermediateField (Padic C.l) C.Qbar) [FiniteDimensional (Padic C.l) E]
    (n : ℕ) (T : Scheme.{u}) :
    projectionDiagonalUnit F C E n T =
      AffineLinePurity.coefficientUnitIso
        (ModuleCat.{u + 1} (projectionSetting F C E n).Coefficient) T := by
  change projectionChooseUnique (projectionDiagonalUnit_existsUnique F C E n T) = _
  have h := (projectionDiagonalUnit_existsUnique F C E n T).exists.choose_spec
  change HEq (projectionChooseUnique (projectionDiagonalUnit_existsUnique F C E n T))
    (projectionUnitRaw (projectionSetting F C E n).Coefficient T) at h
  rw [eq_of_heq h]
  unfold AffineLinePurity.coefficientUnitIso
  rfl

private theorem iso_inverse_square
    {B : Type*} [Category B] {L L' L'' X Y : B}
    (b : L ≅ L') (r : L' ≅ L'') (a : X ≅ Y) (Q : X ≅ L) (q : Y ≅ L'')
    (h : a.hom ≫ q.hom = Q.hom ≫ b.hom ≫ r.hom) :
    a.inv ≫ Q.hom = (q.hom ≫ r.inv) ≫ b.inv := by
  apply a.inv_comp_eq.mpr
  simp only [Category.assoc]
  rw [← Category.assoc, ← Category.assoc, h]
  simp only [Category.assoc]
  rw [Iso.hom_inv_id_assoc, Iso.hom_inv_id, Category.comp_id]

private theorem tensor_comparison_map_inverse
    (A : Type (u + 1)) [CommRing A] [Finite A] (T : Scheme.{u})
    {M M' N N' : Etale.DerivedCategoryModule A T} (e : M ≅ M') (f : N ≅ N') :
    (comparison A T).map (Etale.ordinaryFiniteTensorRightMapIso A T e f).inv ≫
        (tensorComparison A T M N).hom =
      ((tensorComparison A T M' N').hom ≫
        ((AffineSpacePurity.tensor A T).obj ((comparison A T).obj M')).map
          ((comparison A T).map f.inv)) ≫
        ((AffineSpacePurity.tensor A T).map ((comparison A T).map e.inv)).app
          ((comparison A T).obj N) := by
  let V := AffineSpacePurity.tensor A T
  let bV := (V.mapIso ((comparison A T).mapIso e)).app ((comparison A T).obj N)
  let rV := (V.obj ((comparison A T).obj M')).mapIso ((comparison A T).mapIso f)
  have ht : (AffineSpacePurity.tensorIso A T
      ((comparison A T).mapIso e) ((comparison A T).mapIso f)).hom =
      bV.hom ≫ rV.hom := by
    rfl
  have hn := (tensor_comparison_map A T e f).trans
    (congrArg (fun g ↦ (tensorComparison A T M N).hom ≫ g) ht)
  exact iso_inverse_square bV rV
    ((comparison A T).mapIso (Etale.ordinaryFiniteTensorRightMapIso A T e f))
    (tensorComparison A T M N) (tensorComparison A T M' N') hn

private theorem tensor_comparison_map_inverse_of_eq
    (A : Type (u + 1)) [CommRing A] [Finite A] (T : Scheme.{u})
    {M M' N N' : Etale.DerivedCategoryModule A T} (e : M ≅ M') (f : N ≅ N')
    (a : ((Etale.ordinaryFiniteTensor A T).obj M).obj N ≅
      ((Etale.ordinaryFiniteTensor A T).obj M').obj N')
    (s : (comparison A T).obj (((Etale.ordinaryFiniteTensor A T).obj M').obj N') ≅
      ((AffineSpacePurity.tensor A T).obj ((comparison A T).obj M')).obj
        ((comparison A T).obj N))
    (ha : a = Etale.ordinaryFiniteTensorRightMapIso A T e f)
    (hs : s.hom = (tensorComparison A T M' N').hom ≫
      ((AffineSpacePurity.tensor A T).obj ((comparison A T).obj M')).map
        ((comparison A T).map f.inv)) :
    (comparison A T).map a.inv ≫ (tensorComparison A T M N).hom =
      s.hom ≫ ((AffineSpacePurity.tensor A T).map ((comparison A T).map e.inv)).app
        ((comparison A T).obj N) := by
  rw [ha, hs]
  exact tensor_comparison_map_inverse A T e f

set_option maxHeartbeats 250000 in
-- Check the ordered coefficient recursion separately from comparison monoidality.
private theorem base_step_root_eq
    (F : FiniteFieldDatum.{u}) (C : F.CoefficientDatum)
    (E : IntermediateField (Padic C.l) C.Qbar) [FiniteDimensional (Padic C.l) E]
    (n : ℕ) (T : Scheme.{u}) (aT : T ⟶ Spec (.of F.k)) (d : ℕ) :
    let P := projectionSetting F C E n
    let S := DerivedCategory.singleFunctor
      (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} P.Coefficient)) 0
    let J := shiftFunctor (Etale.DerivedCategoryModule P.Coefficient T) (2 : ℤ)
    baseExponentComparison C.l E n T (AffineLinePurity.primeUnit P T aT)
      n (n + 1) (Nat.le_succ n) P.diagonalExponent_annihilates (annihilates P) (d + 1) =
      Etale.ordinaryFiniteTensorRightMapIso P.Coefficient T
        (baseExponentComparison C.l E n T (AffineLinePurity.primeUnit P T aT)
          n (n + 1) (Nat.le_succ n) P.diagonalExponent_annihilates (annihilates P) d)
        (J.mapIso (S.mapIso (projectionRootTransition F C E n T aT))) := by
  intro P S J
  let b := baseExponentComparison C.l E n T (AffineLinePurity.primeUnit P T aT)
    n (n + 1) (Nat.le_succ n) P.diagonalExponent_annihilates (annihilates P) d
  let r := J.mapIso (S.mapIso (projectionRootTransition F C E n T aT))
  let r₀ := J.mapIso (S.mapIso
    (exponentTransition C.l E n T (AffineLinePurity.primeUnit P T aT)
      n (n + 1) (Nat.le_succ n) P.diagonalExponent_annihilates (annihilates P) 1))
  have hr : r = r₀ := congrArg J.mapIso
    (congrArg S.mapIso (root_transition_eq F C E n T aT))
  have hb₀ : baseExponentComparison C.l E n T (AffineLinePurity.primeUnit P T aT)
      n (n + 1) (Nat.le_succ n) P.diagonalExponent_annihilates (annihilates P) (d + 1) =
      Etale.ordinaryFiniteTensorRightMapIso P.Coefficient T b r₀ := by
    rfl
  exact hb₀.trans
    (congrArg (Etale.ordinaryFiniteTensorRightMapIso P.Coefficient T b) hr.symm)

set_option maxHeartbeats 250000 in
-- Check the prescribed sheaf step with the shifted root map before specializing naturality.
private theorem tensor_step_root_hom
    (F : FiniteFieldDatum.{u}) (C : F.CoefficientDatum)
    (E : IntermediateField (Padic C.l) C.Qbar) [FiniteDimensional (Padic C.l) E]
    (n : ℕ) (T : Scheme.{u}) (aT : T ⟶ Spec (.of F.k)) (d : ℕ) :
    let P := projectionSetting F C E n
    let S := DerivedCategory.singleFunctor
      (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} P.Coefficient)) 0
    let J := shiftFunctor (Etale.DerivedCategoryModule P.Coefficient T) (2 : ℤ)
    let r := J.mapIso (S.mapIso (projectionRootTransition F C E n T aT))
    (projectionTensorStep F C E n T aT d).hom =
      (tensorComparison P.Coefficient T (P.diagonalTwistEtale T d)
        ((Etale.ordinaryFiniteLine P.Coefficient P.diagonalExponent
          P.diagonalExponent_annihilates T)⟦(2 : ℤ)⟧)).hom ≫
        P.diagonalTwist T d ◁ (comparison P.Coefficient T).map r.inv := by
  intro P S J r
  have hs₀ : (projectionTensorStepFromSheaf P.Coefficient T (P.diagonalTwistEtale T d)
        (projectionRootTransition F C E n T aT).symm).2.2.hom =
      (tensorComparison P.Coefficient T (P.diagonalTwistEtale T d)
        ((Etale.ordinaryFiniteLine P.Coefficient P.diagonalExponent
          P.diagonalExponent_annihilates T)⟦(2 : ℤ)⟧)).hom ≫
        P.diagonalTwist T d ◁ (comparison P.Coefficient T).map r.inv := by
    unfold projectionTensorStepFromSheaf projectionTensorStepFromSheafGeneric
      projectionTensorStepGeneric projectionSingleShiftIso tensorComparison
    rfl
  exact (congrArg Iso.hom (tensor_step_spec F C E n T aT d)).trans hs₀

set_option maxHeartbeats 250000 in
-- The abstract inverse square now uses the separately checked coordinate formulas.
private theorem root_step_eq
    (F : FiniteFieldDatum.{u}) (C : F.CoefficientDatum)
    (E : IntermediateField (Padic C.l) C.Qbar) [FiniteDimensional (Padic C.l) E]
    (n : ℕ) (T : Scheme.{u}) (aT : T ⟶ Spec (.of F.k)) (d : ℕ) :
    let P := projectionSetting F C E n
    (comparison P.Coefficient T).map
        (projectionCoefficientRootIso F C E n T aT (d + 1)).hom ≫
        (tensorComparison P.Coefficient T
          (Etale.affineLinearBaseCoefficient P.Coefficient
            (AffineOrderedIntegration.exponent P) (annihilates P) T d)
          ((Etale.ordinaryFiniteLine P.Coefficient
            (AffineOrderedIntegration.exponent P) (annihilates P) T)⟦(2 : ℤ)⟧)).hom =
      (projectionTensorStep F C E n T aT d).hom ≫
        (comparison P.Coefficient T).map
          (projectionCoefficientRootIso F C E n T aT d).hom ▷
            projectionShiftedLine F C E n T := by
  intro P
  let b := baseExponentComparison C.l E n T (AffineLinePurity.primeUnit P T aT)
    n (n + 1) (Nat.le_succ n) P.diagonalExponent_annihilates (annihilates P) d
  let S := DerivedCategory.singleFunctor
    (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} P.Coefficient)) 0
  let J := shiftFunctor (Etale.DerivedCategoryModule P.Coefficient T) (2 : ℤ)
  let r := J.mapIso (S.mapIso (projectionRootTransition F C E n T aT))
  exact tensor_comparison_map_inverse_of_eq P.Coefficient T b r
    (baseExponentComparison C.l E n T (AffineLinePurity.primeUnit P T aT)
      n (n + 1) (Nat.le_succ n) P.diagonalExponent_annihilates (annihilates P) (d + 1))
    (projectionTensorStep F C E n T aT d)
    (base_step_root_eq F C E n T aT d) (tensor_step_root_hom F C E n T aT d)

private theorem root_unit_eq
    (F : FiniteFieldDatum.{u}) (C : F.CoefficientDatum)
    (E : IntermediateField (Padic C.l) C.Qbar) [FiniteDimensional (Padic C.l) E]
    (n : ℕ) (T : Scheme.{u}) (aT : T ⟶ Spec (.of F.k)) :
    let P := projectionSetting F C E n
    (comparison P.Coefficient T).map
        (projectionCoefficientRootIso F C E n T aT 0).hom ≫
        (AffineLinePurity.coefficientUnitIso (ModuleCat.{u + 1} P.Coefficient) T).hom =
      (projectionDiagonalUnit F C E n T).hom := by
  intro P
  change (comparison P.Coefficient T).map (𝟙 (Etale.ordinaryFiniteUnit P.Coefficient T)) ≫
      (AffineLinePurity.coefficientUnitIso (ModuleCat.{u + 1} P.Coefficient) T).hom =
    (projectionDiagonalUnit F C E n T).hom
  erw [CategoryTheory.Functor.map_id, Category.id_comp]
  exact congrArg Iso.hom (diagonal_unit_eq F C E n T).symm

private theorem root_big_annihilates (P : PurityFiniteSetting.{u}) :
    (AffineOrderedIntegration.exponent P : P.Coefficient) = 0 := by
  have h := P.diagonalExponent_annihilates
  change ((P.coefficients.l ^ P.level : ℕ) : P.Coefficient) = 0 at h
  change ((P.coefficients.l ^ (P.level + 1) : ℕ) : P.Coefficient) = 0
  rw [pow_succ, Nat.cast_mul, h, zero_mul]

-- Keep all objects and constraints in one cached derived monoidal category.
private def root_small_family (P : PurityFiniteSetting.{u}) (T : Scheme.{u}) :
    ℕ → AffineSpacePurity.C P.Coefficient T := P.diagonalTwist T

private def root_big_family (P : PurityFiniteSetting.{u}) (T : Scheme.{u}) :
    ℕ → AffineSpacePurity.C P.Coefficient T :=
  fun d ↦ (comparison P.Coefficient T).obj
    (Etale.affineLinearBaseCoefficient P.Coefficient
      (AffineOrderedIntegration.exponent P) (root_big_annihilates P) T d)

private def root_line (P : PurityFiniteSetting.{u}) (T : Scheme.{u}) :
    AffineSpacePurity.C P.Coefficient T :=
  (comparison P.Coefficient T).obj
    ((Etale.ordinaryFiniteLine P.Coefficient
      (AffineOrderedIntegration.exponent P) (root_big_annihilates P) T)⟦(2 : ℤ)⟧)

private def root_big_unit (P : PurityFiniteSetting.{u}) (T : Scheme.{u}) :
    root_big_family P T 0 ≅ 𝟙_ (AffineSpacePurity.C P.Coefficient T) :=
  AffineLinePurity.coefficientUnitIso (ModuleCat.{u + 1} P.Coefficient) T

private def root_big_step (P : PurityFiniteSetting.{u}) (T : Scheme.{u}) (d : ℕ) :
    root_big_family P T (d + 1) ≅ root_big_family P T d ⊗ root_line P T :=
  tensorComparison P.Coefficient T
    (Etale.affineLinearBaseCoefficient P.Coefficient
      (AffineOrderedIntegration.exponent P) (root_big_annihilates P) T d)
    ((Etale.ordinaryFiniteLine P.Coefficient
      (AffineOrderedIntegration.exponent P) (root_big_annihilates P) T)⟦(2 : ℤ)⟧)

private def root_small_unit
    (F : FiniteFieldDatum.{u}) (C : F.CoefficientDatum)
    (E : IntermediateField (Padic C.l) C.Qbar) [FiniteDimensional (Padic C.l) E]
    (n : ℕ) (T : Scheme.{u}) :
    let P := projectionSetting F C E n
    root_small_family P T 0 ≅ 𝟙_ (AffineSpacePurity.C P.Coefficient T) := by
  exact projectionDiagonalUnit F C E n T

set_option maxHeartbeats 250000 in
-- The prescribed successor with its tensor endpoint cached explicitly.
private def root_small_step
    (F : FiniteFieldDatum.{u}) (C : F.CoefficientDatum)
    (E : IntermediateField (Padic C.l) C.Qbar) [FiniteDimensional (Padic C.l) E]
    (n : ℕ) (T : Scheme.{u}) (aT : T ⟶ Spec (.of F.k)) (d : ℕ) :
    let P := projectionSetting F C E n
    root_small_family P T (d + 1) ≅ root_small_family P T d ⊗ root_line P T := by
  exact projectionTensorStep F C E n T aT d

set_option maxHeartbeats 250000 in
-- Cache the endpoints before using the root comparisons as an indexed family.
private def compared_root_iso
    (F : FiniteFieldDatum.{u}) (C : F.CoefficientDatum)
    (E : IntermediateField (Padic C.l) C.Qbar) [FiniteDimensional (Padic C.l) E]
    (n : ℕ) (T : Scheme.{u}) (aT : T ⟶ Spec (.of F.k)) (d : ℕ) :
    let P := projectionSetting F C E n
    root_small_family P T d ≅ root_big_family P T d := by
  intro P
  exact (comparison P.Coefficient T).mapIso
    (projectionCoefficientRootIso F C E n T aT d)

private theorem compared_root_unit
    (F : FiniteFieldDatum.{u}) (C : F.CoefficientDatum)
    (E : IntermediateField (Padic C.l) C.Qbar) [FiniteDimensional (Padic C.l) E]
    (n : ℕ) (T : Scheme.{u}) (aT : T ⟶ Spec (.of F.k)) :
    let P := projectionSetting F C E n
    (compared_root_iso F C E n T aT 0).hom ≫ (root_big_unit P T).hom =
      (root_small_unit F C E n T).hom := by
  exact root_unit_eq F C E n T aT

set_option maxHeartbeats 250000 in
-- Reuse the checked successor equation with the cached endpoints.
private theorem compared_root_step
    (F : FiniteFieldDatum.{u}) (C : F.CoefficientDatum)
    (E : IntermediateField (Padic C.l) C.Qbar) [FiniteDimensional (Padic C.l) E]
    (n : ℕ) (T : Scheme.{u}) (aT : T ⟶ Spec (.of F.k)) (d : ℕ) :
    let P := projectionSetting F C E n
    (compared_root_iso F C E n T aT (d + 1)).hom ≫ (root_big_step P T d).hom =
      (root_small_step F C E n T aT d).hom ≫
        (compared_root_iso F C E n T aT d).hom ▷ root_line P T := by
  exact root_step_eq F C E n T aT d

set_option maxHeartbeats 400000 in
-- Specialize the abstract induction using only objects and maps with cached types.
private theorem root_action_generic
    (F : FiniteFieldDatum.{u}) (C : F.CoefficientDatum)
    (E : IntermediateField (Padic C.l) C.Qbar) [FiniteDimensional (Padic C.l) E]
    (n : ℕ) (T : Scheme.{u}) (aT : T ⟶ Spec (.of F.k))
    (M : AffineSpacePurity.C (projectionSetting F C E n).Coefficient T) (d : ℕ) :
    let P := projectionSetting F C E n
    M ◁ (compared_root_iso F C E n T aT d).hom ≫
        (projectionTensorActionGeneric (AffineSpacePurity.C P.Coefficient T)
          (root_big_family P T) (root_line P T) (root_big_unit P T)
          (root_big_step P T) M d).hom =
      (projectionTensorActionGeneric (AffineSpacePurity.C P.Coefficient T)
        (root_small_family P T) (root_line P T) (root_small_unit F C E n T)
        (root_small_step F C E n T aT) M d).hom := by
  intro P
  exact action_rec_compare (B := AffineSpacePurity.C P.Coefficient T)
    (root_small_family P T) (root_big_family P T) (root_line P T)
    (root_small_unit F C E n T) (root_big_unit P T)
    (root_small_step F C E n T aT) (root_big_step P T)
    (fun i ↦ compared_root_iso F C E n T aT i)
    (compared_root_unit F C E n T aT)
    (fun i ↦ compared_root_step F C E n T aT i) M d

private theorem comp_iso_hom_eq_of_eq
    {B : Type*} [Category B] {X Y Z : B} (f : X ⟶ Y)
    {a b : Y ≅ Z} {p q : X ≅ Z} (ha : a = b) (hp : p = q)
    (h : f ≫ b.hom = q.hom) : f ≫ a.hom = p.hom := by
  rw [ha, hp]
  exact h

set_option maxHeartbeats 400000 in
-- Replace the two generic action isomorphisms using their checked specifications.
private theorem coefficient_root_action
    (F : FiniteFieldDatum.{u}) (C : F.CoefficientDatum)
    (E : IntermediateField (Padic C.l) C.Qbar) [FiniteDimensional (Padic C.l) E]
    (n : ℕ) (T : Scheme.{u}) (aT : T ⟶ Spec (.of F.k))
    (M : AffineSpacePurity.C (projectionSetting F C E n).Coefficient T) (d : ℕ) :
    let P := projectionSetting F C E n
    M ◁ (comparison P.Coefficient T).map
        (projectionCoefficientRootIso F C E n T aT d).hom ≫
        (AffineOrderedIntegration.coefficientActionComparison P.Coefficient
          (AffineOrderedIntegration.exponent P) (annihilates P) T M d).hom =
      (projectionTensorActionIso F C E n T aT M d).hom := by
  intro P
  exact comp_iso_hom_eq_of_eq
    (M ◁ (comparison P.Coefficient T).map
      (projectionCoefficientRootIso F C E n T aT d).hom)
    (coefficient_action_generic P.Coefficient
      (AffineOrderedIntegration.exponent P) (annihilates P) T M d)
    (tensor_action_spec F C E n T aT M d)
    (root_action_generic F C E n T aT M d)

private theorem iso_hom_three
    {B : Type*} [Category B] {X₀ X₁ X₂ X₃ X₄ : B}
    (a : X₀ ≅ X₁) (b : X₁ ≅ X₂) (c : X₂ ≅ X₃) (d : X₃ ⟶ X₄) :
    (a ≪≫ b ≪≫ c).hom ≫ d = a.hom ≫ b.hom ≫ c.hom ≫ d := by
  simp only [Iso.trans_hom, Category.assoc]

private theorem conjugate_cancel
    {B : Type*} [Category B] {X Y X' Y' : B}
    (a : X ≅ Y) (b : X' ≅ Y') (f : X ⟶ X') (g : Y ⟶ Y')
    (h : f ≫ b.hom = a.hom ≫ g) : a.hom ≫ g ≫ b.inv = f := by
  rw [← Category.assoc, ← h, Category.assoc, Iso.hom_inv_id, Category.comp_id]

private theorem bifunctor_map_three
    {A B C : Type*} [Category A] [Category B] [Category C]
    (T : A ⥤ B ⥤ C) {M₀ M₁ M₂ M₃ : A}
    (f : M₀ ⟶ M₁) (g : M₁ ⟶ M₂) (h : M₂ ⟶ M₃) (V : B) :
    (T.map f).app V ≫ (T.map g).app V ≫ (T.map h).app V =
      (T.map (f ≫ g ≫ h)).app V := by
  simp only [Functor.map_comp, NatTrans.comp_app]

private theorem inverse_chain
    {B : Type*} [Category B] {X Y Z T U V : B}
    (a : X ≅ Y) (b : Y ≅ Z) (c : Z ≅ T) (d : T ≅ U) (e : U ≅ V) :
    (a ≪≫ b ≪≫ c ≪≫ d ≪≫ e).symm =
      e.symm ≪≫ (b ≪≫ c ≪≫ d).symm ≪≫ a.symm := by
  simp only [Iso.trans_symm, Iso.trans_assoc]

private theorem inverse_square_cancel
    {A B : Type*} [Category A] [Category B] (F G : A ⥤ B) (q : F ≅ G)
    {H K : A} (e : H ≅ K) {U V : B} (t : G.obj H ≅ U) (r : U ≅ V) :
    (G.map e.inv ≫ t.hom ≫ r.hom) ≫
        (r.inv ≫ t.inv ≫ q.inv.app H) ≫ F.map e.hom = q.inv.app K := by
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  rw [← q.inv.naturality e.hom, ← Functor.map_comp_assoc]
  simp only [Iso.inv_hom_id, CategoryTheory.Functor.map_id, Category.id_comp]

private theorem site_pullback_eq
    (A : Type u) [CommRing A] {X Y : Scheme.{u}} (f : X ⟶ Y) :
    ProEtale.sfComparisonPullbackIso A f =
      ProEtale.comparisonUpperStarCompUpperStarIso
        (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) f := by
  rfl

private theorem ordinary_pullback_eq
    (P : PurityFiniteSetting.{u}) {X Y : Scheme.{u}} (f : X ⟶ Y) :
    pullback P.Coefficient f =
      Functor.isoWhiskerRight
        (Etale.leftDerivedUpperStarIsoMapDerivedCategory
          (ModuleCat.{u + 1} P.Coefficient) f) (comparison P.Coefficient X) ≪≫
      (ProEtale.sfDerivedComparisonPullbackIso P.Ring f).symm ≪≫
      Functor.isoWhiskerLeft (comparison P.Coefficient Y)
        (ProEtale.leftDerivedUpperStarIsoMapDerivedCategory
          (ModuleCat.{u + 1} P.Coefficient) f).symm := by
  unfold VectorIntegrationSite.pullback ProEtale.geoP1PullComparison
    ProEtale.sfDerivedComparisonPullbackIso
  erw [site_pullback_eq]
  exact inverse_chain _ _ _ _ _

private theorem pullback_comparison_cancel
    (P : PurityFiniteSetting.{u}) {X Y : Scheme.{u}} (f : X ⟶ Y)
    (K : AffineSpacePurity.C P.Coefficient Y)
    (H : Etale.DerivedCategoryModule P.Coefficient Y)
    (e : (comparison P.Coefficient Y).obj H ≅ K) :
    (P.smoothPurityPullbackComparison f K H e).hom ≫
        (pullback P.Coefficient f).hom.app H ≫
        (ProEtale.upperStar (ModuleCat.{u + 1} P.Coefficient) f).leftDerivedFunctor.map
          e.hom =
      (ProEtale.leftDerivedUpperStarIsoMapDerivedCategory
        (ModuleCat.{u + 1} P.Coefficient) f).inv.app K := by
  erw [ordinary_pullback_eq]
  exact inverse_square_cancel
    (ProEtale.upperStar (ModuleCat.{u + 1} P.Coefficient) f).leftDerivedFunctor
    (P.smoothPurityPullback f)
    (ProEtale.leftDerivedUpperStarIsoMapDerivedCategory
      (ModuleCat.{u + 1} P.Coefficient) f) e
    ((ProEtale.sfDerivedComparisonPullbackIso P.Ring f).app H)
    ((comparison P.Coefficient X).mapIso
      ((Etale.leftDerivedUpperStarIsoMapDerivedCategory
        (ModuleCat.{u + 1} P.Coefficient) f).app H).symm)

private theorem tensor_realization_cancel
    (P : PurityFiniteSetting.{u}) {X Y : Scheme.{u}} (f : X ⟶ Y)
    [HasCompactification f] (K : AffineSpacePurity.C P.Coefficient Y)
    (H : Etale.DerivedCategoryModule P.Coefficient Y)
    (e : (comparison P.Coefficient Y).obj H ≅ K)
    (W : Etale.DerivedCategoryModule P.Coefficient X) :
    (P.smoothPurityCoefficientComparison f K H e W).hom ≫
        (AffineOrderedIntegration.realizeTensorSource P.Coefficient f K H W e).hom =
      (ProEtale.leftDerivedUpperStarIsoMapDerivedCategory
        (ModuleCat.{u + 1} P.Coefficient) f).inv.app K ▷
        (comparison P.Coefficient X).obj W := by
  let T := smoothPurityTensor P.Coefficient X
  let V := (comparison P.Coefficient X).obj W
  let s := P.smoothPurityPullbackComparison f K H e
  let b := (pullback P.Coefficient f).app H
  let J := (ProEtale.upperStar (ModuleCat.{u + 1} P.Coefficient) f).leftDerivedFunctor
  have ht : smoothPurityComparisonTensor P.Coefficient X
      ((Etale.ordinaryFinitePullback P.Coefficient f).obj H) W =
      tensorComparison P.Coefficient X
        ((Etale.ordinaryFinitePullback P.Coefficient f).obj H) W := by
    unfold smoothPurityComparisonTensor tensorComparison
    rfl
  unfold AffineOrderedIntegration.realizeTensorSource AffineLinePurity.realizedTensorComparison
    tensorPullbackComparison
  change ((T.map s.hom).app V ≫
      (smoothPurityComparisonTensor P.Coefficient X
        ((Etale.ordinaryFinitePullback P.Coefficient f).obj H) W).inv) ≫
      (((tensorComparison P.Coefficient X
        ((Etale.ordinaryFinitePullback P.Coefficient f).obj H) W).hom ≫
        (T.map b.hom).app V) ≫ (T.map (J.map e.hom)).app V) =
      (T.map ((ProEtale.leftDerivedUpperStarIsoMapDerivedCategory
        (ModuleCat.{u + 1} P.Coefficient) f).inv.app K)).app V
  erw [ht]
  repeat' erw [Category.assoc]
  erw [Iso.inv_hom_id_assoc]
  exact (bifunctor_map_three T s.hom b.hom (J.map e.hom) V).trans
    (congrArg (fun g ↦ (T.map g).app V) (pullback_comparison_cancel P f K H e))

private theorem pullback_identity_cancel
    (P : PurityFiniteSetting.{u}) (Y : Scheme.{u})
    (K : AffineSpacePurity.C P.Coefficient Y) :
    (ProEtale.leftDerivedUpperStarIsoMapDerivedCategory
        (ModuleCat.{u + 1} P.Coefficient) (𝟙 Y)).inv.app K ≫
        (inverseImageId P.Coefficient Y).hom.app K =
      (Functor.mapDerivedCategoryNatIso
        (ProEtale.upperStarId (ModuleCat.{u + 1} P.Coefficient) Y) ≪≫
        Functor.mapDerivedCategoryIdIso _).hom.app K := by
  unfold inverseImageId ProEtale.leftDerivedUpperStarId Functor.leftDerivedFunctorNatIso
    ProEtale.leftDerivedUpperStarIsoMapDerivedCategory
  simp only [Iso.trans_hom, NatTrans.comp_app, Iso.symm_hom,
    Category.assoc, Iso.inv_hom_id_app_assoc]

private theorem unit_inverse_natural
    {B : Type*} [Category B] [MonoidalCategory B] {J K U : B}
    (e : J ≅ K) (uK : K ⊗ U ≅ K) (uJ : J ⊗ U ≅ J)
    (h : e.inv ▷ U ≫ uJ.hom = uK.hom ≫ e.inv) :
    e.hom ≫ (uK.inv ≫ (e.inv ▷ U ≫ J ◁ (𝟙 U))) = uJ.inv := by
  simp only [whiskerLeft_id, Category.comp_id]
  apply (cancel_mono uJ.hom).mp
  simp only [Category.assoc]
  rw [h, Iso.inv_hom_id_assoc, Iso.hom_inv_id, Iso.inv_hom_id]

private theorem zero_source_cancel
    (P : PurityFiniteSetting.{u}) (Y : Scheme.{u})
    (K : AffineSpacePurity.C P.Coefficient Y) :
    (inverseImageId P.Coefficient Y).hom.app K ≫
        (AffineOrderedIntegration.zeroSourceComparison P.Coefficient Y K).hom =
      (AffineLinePurity.moduleRightUnit P.Coefficient Y
        ((inverseImage P.Coefficient (𝟙 Y)).obj K)).inv := by
  let e := (inverseImageId P.Coefficient Y).app K
  let J := (inverseImage P.Coefficient (𝟙 Y)).obj K
  let uK := AffineLinePurity.moduleRightUnit P.Coefficient Y K
  let uJ := AffineLinePurity.moduleRightUnit P.Coefficient Y J
  have hn := coefficient_unit_natural P.Coefficient Y e.inv
  unfold AffineOrderedIntegration.zeroSourceComparison AffineSpacePurity.tensorIso
  change e.hom ≫ (uK.inv ≫ ((e.inv ▷ unit P.Coefficient Y) ≫
      ((AffineSpacePurity.tensor P.Coefficient Y).obj J).map
        (𝟙 (unit P.Coefficient Y)))) = uJ.inv
  exact unit_inverse_natural e uK uJ hn

private theorem replace_composite
    {B : Type*} [Category B] {X₀ X₁ X₂ X₃ X₄ X₅ : B}
    (a : X₀ ⟶ X₁) (b : X₁ ⟶ X₂) (c : X₂ ⟶ X₃) (d : X₃ ⟶ X₄)
    (e : X₂ ⟶ X₄) (f : X₄ ⟶ X₅) (g : X₃ ⟶ X₅)
    (h : c ≫ d = e) (k : d ≫ f = g) :
    (a ≫ b ≫ e) ≫ f = a ≫ b ≫ c ≫ g := by
  rw [← h]
  simp only [Category.assoc]
  rw [k]

set_option maxHeartbeats 400000 in
-- Normalize the protected source aliases while retaining the cached category instances.
private theorem source_normalization
    (F : FiniteFieldDatum.{u}) (C : F.CoefficientDatum)
    (E : IntermediateField (Padic C.l) C.Qbar) [FiniteDimensional (Padic C.l) E]
    (n : ℕ) (Y : Scheme.{u}) (aY : Y ⟶ Spec (.of F.k))
    (K : AffineSpacePurity.C (projectionSetting F C E n).Coefficient Y) (d : ℕ) :
    let P := projectionSetting F C E n
    let X := iteratedAffineLine Y d
    let p := iteratedAffineLineProj Y d
    let M := (P.smoothPurityPullback p).obj K
    let J := (inverseImage P.Coefficient p).obj K
    (projectionSourceIso F C E n Y aY K d).hom ≫
        (AffineOrderedIntegration.sourceComparison P Y K d).hom =
      (P.smoothPurityReassociation X d M).hom ≫
        (projectionTensorActionIso F C E n X (towerBase aY d) M d).hom ≫
        (action ((AffineSpacePurity.tensor P.Coefficient X).flip.obj (shiftedLine P X)) d).map
          ((ProEtale.leftDerivedUpperStarIsoMapDerivedCategory
            (ModuleCat.{u + 1} P.Coefficient) p).inv.app K) ≫
        (AffineOrderedIntegration.coefficientActionComparison P.Coefficient
          (AffineOrderedIntegration.exponent P) (annihilates P) X J d).inv := by
  dsimp only
  cases d with
  | zero =>
    have hp : projectionSourceIso F C E n Y aY K 0 =
        (projectionSourceRaw F C E n Y aY K 0).2.2 := by
      exact eq_of_heq
        (projectionSourceIso_existsUnique F C E n Y aY K 0).exists.choose_spec
    have hs := eq_of_heq
      (AffineOrderedIntegration.sourceComparison_existsUnique
        (projectionSetting F C E n) Y K 0).exists.choose_spec
    erw [hp, hs]
    change (((projectionSetting F C E n).smoothPurityReassociation Y 0
      (((projectionSetting F C E n).smoothPurityPullback (𝟙 Y)).obj K)).hom ≫
      (projectionTensorActionIso F C E n Y aY _ 0).hom ≫
      (Functor.mapDerivedCategoryNatIso
        (ProEtale.upperStarId (ModuleCat.{u + 1} (projectionSetting F C E n).Coefficient) Y)
          ≪≫ Functor.mapDerivedCategoryIdIso _).hom.app K) ≫
      (AffineOrderedIntegration.zeroSourceComparison
        (projectionSetting F C E n).Coefficient Y K).hom = _
    let P := projectionSetting F C E n
    exact replace_composite
      (P.smoothPurityReassociation Y 0 ((P.smoothPurityPullback (𝟙 Y)).obj K)).hom
      (projectionTensorActionIso F C E n Y aY _ 0).hom
      ((ProEtale.leftDerivedUpperStarIsoMapDerivedCategory
        (ModuleCat.{u + 1} P.Coefficient) (𝟙 Y)).inv.app K)
      ((inverseImageId P.Coefficient Y).hom.app K) _
      (AffineOrderedIntegration.zeroSourceComparison P.Coefficient Y K).hom _
      (pullback_identity_cancel P Y K) (zero_source_cancel P Y K)
  | succ d =>
    have hp : projectionSourceIso F C E n Y aY K (d + 1) =
        (projectionSourceRaw F C E n Y aY K (d + 1)).2.2 := by
      exact eq_of_heq
        (projectionSourceIso_existsUnique F C E n Y aY K (d + 1)).exists.choose_spec
    have hs := eq_of_heq
      (AffineOrderedIntegration.sourceComparison_existsUnique
        (projectionSetting F C E n) Y K (d + 1)).exists.choose_spec
    erw [hp, hs]
    let P := projectionSetting F C E n
    let X := iteratedAffineLine Y (d + 1)
    let p := iteratedAffineLineProj Y (d + 1)
    let M := (P.smoothPurityPullback p).obj K
    exact iso_hom_three
      (P.smoothPurityReassociation X (d + 1) M)
      (projectionTensorActionIso F C E n X (towerBase aY (d + 1)) M (d + 1))
      ((action ((AffineSpacePurity.tensor P.Coefficient X).flip.obj (shiftedLine P X))
        (d + 1)).mapIso
        ((ProEtale.leftDerivedUpperStarIsoMapDerivedCategory
          (ModuleCat.{u + 1} P.Coefficient) p).app K).symm)
      (AffineOrderedIntegration.coefficientActionComparison P.Coefficient
        (AffineOrderedIntegration.exponent P) (annihilates P) X
        ((inverseImage P.Coefficient p).obj K) (d + 1)).inv

private theorem source_equation
    {B : Type*} [Category B] {X U V W S V' A A' : B}
    (s : X ≅ U) (z : U ≅ V) (c : V ≅ W) (t : W ≅ V')
    (p : X ≅ S) (r : S ≅ V') (a : U ≅ A) (b : V ≅ A) (b' : V' ≅ A')
    (q : V ⟶ V') (aq : A ⟶ A')
    (hr : z.hom ≫ b.hom = a.hom) (ht : c.hom ≫ t.hom = q)
    (hn : q ≫ b'.hom = b.hom ≫ aq)
    (hs : p.hom ≫ r.hom = s.hom ≫ a.hom ≫ aq ≫ b'.inv) :
    (s ≪≫ z ≪≫ c).hom = p.hom ≫ (t ≪≫ r.symm).inv := by
  apply (Iso.eq_comp_inv (t ≪≫ r.symm)).mpr
  change (s.hom ≫ z.hom ≫ c.hom) ≫ (t.hom ≫ r.inv) = p.hom
  rw [← Category.assoc]
  apply (Iso.comp_inv_eq r).mpr
  rw [hs]
  simp only [Category.assoc]
  rw [ht, ← hr]
  simp only [Category.assoc]
  rw [conjugate_cancel b b' q aq hn]

/-- The root and tensor/pullback source composite is the prescribed ordered source
coordinate followed by inverse realization. This is an identity of source maps:
it involves no trace, exceptional inverse image, integration or purity arrow.

Source: literature/blueprint/latest/blueprint/sec-smooth-purity/sk-thm-smooth-purity/
lem-pur-projection-purity-agreement.proof.md, final sentence on canonical
reassociations and even shifts; step 6 of lem-route-projection-tensor-integration.
(blueprint: lem-pur-projection-tensor-source-ordinary)

Proof: identify projectionRootTransition with exponentTransition at degree one
by uniqueness of the normalized root-power map. Induct on the ordered number of
shifted Tate factors. At zero, baseExponentComparison is identity and both
coefficient actions are tensor with the compared unit followed by the right
unitor. Their unit maps coincide by comparison monoidality. At a successor,
baseExponentComparison is ordinaryFiniteTensorRightMapIso of its preceding
comparison and the shifted degree-one root map. Naturality of the site tensor
comparison in each variable moves these maps across its tensor constraint.
Naturality of the inverse associator and the induction equation then identify
projectionTensorStep followed by the preceding action with the larger-exponent
coefficientActionComparison after the inverse root transition. No factors are
permuted. Naturality of this action in its initial object moves the exact/derived
pullback comparison through the action. The specified tensorPullbackComparison
and presentation isomorphism e give exactly smoothPurityCoefficientComparison
followed by realizeTensorSource. Cancel sourceComparison with its inverse.
Prepend the common smoothPurityReassociation. The HEq specifications of the
chosen source isomorphisms fix these literal homs. At zero, use also the
inverse-image identity comparison and the monoidal unit triangle. This argument
works for every K, including the zero object and empty schemes; it requires no
finite-Tor hypothesis or choice of a Tate-line generator. -/
theorem projection_tensor_source_ordinary
    (F : FiniteFieldDatum.{u}) (C : F.CoefficientDatum)
    (E : IntermediateField (Padic C.l) C.Qbar) [FiniteDimensional (Padic C.l) E]
    (n : ℕ) (Y : Scheme.{u}) (aY : Y ⟶ Spec (.of F.k))
    (K : ProEtale.AffineSpacePurity.C (projectionSetting F C E n).Coefficient Y)
    (H : Etale.DerivedCategoryModule (projectionSetting F C E n).Coefficient Y)
    (e : (comparison (projectionSetting F C E n).Coefficient Y).obj H ≅ K) (d : ℕ) :
    let P := projectionSetting F C E n
    (projectionTensorOrdinarySourceIso F C E n Y aY K H e d).hom =
      (projectionSourceIso F C E n Y aY K d).hom ≫
        (projectionOrdinarySourceRealization F C E n Y K H e d).inv := by
  intro _P
  let := (projection_geometry Y d).2
  let X := iteratedAffineLine Y d
  let p := iteratedAffineLineProj Y d
  let M := (_P.smoothPurityPullback p).obj K
  let J := (inverseImage _P.Coefficient p).obj K
  let W := AffineOrderedIntegration.etaleCoefficient _P Y d
  let q := (ProEtale.leftDerivedUpperStarIsoMapDerivedCategory
    (ModuleCat.{u + 1} _P.Coefficient) p).inv.app K
  have hn := coefficient_action_natural _P.Coefficient
    (AffineOrderedIntegration.exponent _P) (annihilates _P) X q d
  have hr := coefficient_root_action F C E n X (towerBase aY d) M d
  have ht := tensor_realization_cancel _P p K H e W
  exact source_equation
    (_P.smoothPurityReassociation X d M)
    (((smoothPurityTensor _P.Coefficient X).obj M).mapIso
      ((comparison _P.Coefficient X).mapIso
        (projectionCoefficientRootIso F C E n X (towerBase aY d) d)))
    (_P.smoothPurityCoefficientComparison p K H e W)
    (AffineOrderedIntegration.realizeTensorSource _P.Coefficient p K H W e)
    (projectionSourceIso F C E n Y aY K d)
    (AffineOrderedIntegration.sourceComparison _P Y K d)
    (projectionTensorActionIso F C E n X (towerBase aY d) M d)
    (AffineOrderedIntegration.coefficientActionComparison _P.Coefficient
      (AffineOrderedIntegration.exponent _P) (annihilates _P) X M d)
    (AffineOrderedIntegration.coefficientActionComparison _P.Coefficient
      (AffineOrderedIntegration.exponent _P) (annihilates _P) X J d)
    (q ▷ (comparison _P.Coefficient X).obj W)
    ((action ((AffineSpacePurity.tensor _P.Coefficient X).flip.obj (shiftedLine _P X)) d).map q)
    hr ht hn (source_normalization F C E n Y aY K d)

set_option linter.unusedVariables false in
set_option maxHeartbeats 400000 in
-- Specializing the source equations normalizes the protected coordinate aliases.
end WeilConjectures.PurityFiniteSetting
