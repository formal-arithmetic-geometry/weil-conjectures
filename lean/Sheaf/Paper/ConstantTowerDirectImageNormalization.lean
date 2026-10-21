/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q16
-/
module

public import Mathlib.CategoryTheory.Products.Basic
public import Sheaf.AlgebraicGeometry.StrictConstantTowerOperations
public import Sheaf.Paper.CompleteCoefficientDatum
public import Sheaf.Paper.CompletedRlimFunctor
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.FullyFaithful
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Sheaf.CategoryTheory.RingedStrictTowerHomotopyLimitOfUniverses
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp
public import Sheaf.AlgebraicGeometry.ProEtaleConstantRingOperations
public import Sheaf.Algebra.Homology.KFlatIndependentCoefficients
import all Sheaf.AlgebraicGeometry.ProEtaleOperations
import Sheaf.AlgebraicGeometry.ProEtaleAlgebraicInverseImage
import Sheaf.AlgebraicGeometry.ProEtaleToposFunctorialityInverseImage
import Sheaf.Algebra.Homology.RingedToposAdaptedFlatResolution
import Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients
import all Sheaf.CategoryTheory.DerivedExactSquareComposition
import all Sheaf.Paper.ResolvingRepresentativeWhiskering
import Sheaf.Paper.BoundedConstructibleTower
import all Sheaf.AlgebraicGeometry.ProEtaleRingSheafChangeAdjunction


/-!
# Constant strict towers and normalized direct image

Source: Stacks, Tags 08BJ, 070K, 0940, 0941, 0A07, 06YS, 07A4 and 0B56;
agent-supplied constant-tower normalization supporting fix-lem-exchanges, Step 5
(blueprint: lem-sf-cbc-constant-tower-direct-image-normalization).

The index n denotes positive exponent n+1. Quotients need not be finite sets.
All tower derived categories localize strict diagrams before evaluation.

## Main definitions

* `chi`: the canonical diagonal/direct-image natural isomorphism.
* `deltaLimit`: the inverse of the diagonal/derived-limit adjunction unit.
* `reduction` and `augmentation`: quotient-tower tensor and its canonical unit map.
* `projection`: the normalized whole-tower counit mate.

## Main statements

* `constantTowerDirectImageNormalization`: the four requested normalizations.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
-- Avoid replaying dependent scalar-extension calculations during tactic linting.
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option backward.isDefEq.respectTransparency.types true
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry.Scheme
namespace AlgebraicGeometry.ProEtale.StrictTower.ConstantNormalization
-- Keep the standard derived models used by the public strict-tower operations.
-- Use the constant-sheaf functor through its API rather than its sheafification model.
attribute [local irreducible] constantSheaf CochainComplex.IsKFlatIndependentCoefficients

attribute [local instance 2000] towers_hasDerivedCategory
  proEtaleRingModules_hasDerivedCategory




section GenericNormalization
universe u₁ u₂ u₃ u₄ v₁ v₂ v₃ v₄ w₁ w₂ w₃ w₄
variable {C : Type u₁} [Category.{v₁} C] [Abelian C] [HasDerivedCategory.{w₁} C]
  {D : Type u₂} [Category.{v₂} D] [Abelian D] [HasDerivedCategory.{w₂} D]
  {T : Type u₃} [Category.{v₃} T] [Abelian T] [HasDerivedCategory.{w₃} T]
  {U : Type u₄} [Category.{v₄} U] [Abelian U] [HasDerivedCategory.{w₄} U]

attribute [local irreducible] Functor.mapDerivedCategory Functor.rightDerivedFunctor

/-- The literal ordinary-square normalization on every K-injective representative.
The formula includes the exact-localization and derived-resolution comparisons.
Source: Stacks 070K (blueprint: lem-sf-cbc-constant-tower-direct-image-normalization). -/
def IsDirectImageNormalizedOnKInjectives
    (F : C ⥤ D) [F.Additive] (P : C ⥤ T) [P.Additive]
    [PreservesFiniteLimits P] [PreservesFiniteColimits P]
    (Q : D ⥤ U) [Q.Additive] [PreservesFiniteLimits Q] [PreservesFiniteColimits Q]
    (H : T ⥤ U) [H.Additive]
    [Abelian.HasKInjectiveResolutions C] [Abelian.HasKInjectiveResolutions T]
    [P.PreservesKInjectiveComplexes]
    (e : F ⋙ Q ≅ P ⋙ H)
    (χ : F.rightDerivedFunctor ⋙ Q.mapDerivedCategory ≅
      P.mapDerivedCategory ⋙ H.rightDerivedFunctor) : Prop :=
  ∀ (J : CochainComplex C ℤ) [J.IsKInjective],
    χ.hom.app (DerivedCategory.Q.obj J) ≫
        H.rightDerivedFunctor.map (P.mapDerivedCategoryFactors.hom.app J) ≫
        (H.rightDerivedFunctorObjQIso ((P.mapHomologicalComplex (.up ℤ)).obj J)).hom =
      Q.mapDerivedCategory.map (F.rightDerivedFunctorObjQIso J).hom ≫
        Q.mapDerivedCategoryFactors.hom.app ((F.mapHomologicalComplex (.up ℤ)).obj J) ≫
        DerivedCategory.Q.map ((NatIso.mapHomologicalComplex e (.up ℤ)).hom.app J)

/-- The canonical pullback/reduction square at a homotopy representative. The two
counits and exact-localization factors specify the whole-tower tensor comparison.
Source: Stacks 06YY, 07A4
(blueprint: lem-sf-cbc-constant-tower-direct-image-normalization). -/
def IsReductionPullAt
    (P : C ⥤ T) [P.Additive] (Q : D ⥤ U) [Q.Additive]
    (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (H : T ⥤ U) [H.Additive] [PreservesFiniteLimits H] [PreservesFiniteColimits H]
    (RP : DerivedCategory C ⥤ DerivedCategory T)
    (RQ : DerivedCategory D ⥤ DerivedCategory U)
    (cP : DerivedCategory.Qh ⋙ RP ⟶ P.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh)
    (cQ : DerivedCategory.Qh ⋙ RQ ⟶ Q.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh)
    (e : P ⋙ H ≅ F ⋙ Q)
    (τ : RP ⋙ H.mapDerivedCategory ≅ F.mapDerivedCategory ⋙ RQ)
    (K : HomotopyCategory C (.up ℤ)) : Prop :=
  τ.hom.app (DerivedCategory.Qh.obj K) ≫
      RQ.map (F.mapDerivedCategoryFactorsh.hom.app K) ≫
      cQ.app ((F.mapHomotopyCategory (.up ℤ)).obj K) =
    H.mapDerivedCategory.map (cP.app K) ≫
      H.mapDerivedCategoryFactorsh.hom.app ((P.mapHomotopyCategory (.up ℤ)).obj K) ≫
      DerivedCategory.Qh.map
        ((Functor.mapHomotopyCategoryCompIso e (.up ℤ)).hom.app K ≫
          (Functor.mapHomotopyCategoryCompIso (Iso.refl (F ⋙ Q)) (.up ℤ)).inv.app K)

private theorem quotient_hom_id {B : Type*} [Category B] [Abelian B]
    [HasDerivedCategory B] (J : CochainComplex B ℤ) :
    (DerivedCategory.quotientCompQhIso B).hom.app J = 𝟙 _ := rfl

private theorem quotient_inv_id {B : Type*} [Category B] [Abelian B]
    [HasDerivedCategory B] (J : CochainComplex B ℤ) :
    (DerivedCategory.quotientCompQhIso B).inv.app J = 𝟙 _ := rfl

private theorem homotopyFactors_inv_id {B E : Type*} [Category B] [Category E]
    [Abelian B] [Abelian E] (F : B ⥤ E) [F.Additive] (J : CochainComplex B ℤ) :
    (F.mapHomotopyCategoryFactors (.up ℤ)).inv.app J = 𝟙 _ := rfl

set_option backward.isDefEq.respectTransparency false in
private theorem factorsh_hom {B E : Type*} [Category B] [Category E]
    [Abelian B] [Abelian E] [HasDerivedCategory B] [HasDerivedCategory E]
    (F : B ⥤ E) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (J : CochainComplex B ℤ) :
    F.mapDerivedCategoryFactorsh.hom.app ((HomotopyCategory.quotient _ _).obj J) =
      F.mapDerivedCategoryFactors.hom.app J := by
  simp only [Functor.mapDerivedCategoryFactorsh_hom_app, quotient_hom_id, quotient_inv_id,
    homotopyFactors_inv_id, CategoryTheory.Functor.map_id, Category.id_comp]
  erw [DerivedCategory.Qh.map_id, Category.comp_id, Category.comp_id]

set_option backward.isDefEq.respectTransparency false in
private theorem objQIso_inv {B E : Type*} [Category B] [Category E]
    [Abelian B] [Abelian E] [HasDerivedCategory B] [HasDerivedCategory E]
    [Abelian.HasKInjectiveResolutions B] (F : B ⥤ E) [F.Additive]
    (J : CochainComplex B ℤ) [J.IsKInjective] :
    (F.rightDerivedFunctorObjQIso J).inv =
      F.rightDerivedFunctorUnit.app ((HomotopyCategory.quotient _ _).obj J) := by
  simp only [Functor.rightDerivedFunctorObjQIso, Iso.trans_inv, Iso.symm_inv,
    Functor.mapIso_inv, Iso.app_inv, asIso_hom, Iso.app_hom,
    quotient_inv_id, quotient_hom_id, CategoryTheory.Functor.map_id,
    Category.id_comp]
  erw [Category.comp_id]

private theorem squareComparison_unit
    (F : C ⥤ D) [F.Additive] (P : C ⥤ T) [P.Additive]
    [PreservesFiniteLimits P] [PreservesFiniteColimits P]
    (Q : D ⥤ U) [Q.Additive] [PreservesFiniteLimits Q] [PreservesFiniteColimits Q]
    (H : T ⥤ U) [H.Additive]
    [Abelian.HasKInjectiveResolutions C] [Abelian.HasKInjectiveResolutions T]
    [P.PreservesKInjectiveComplexes]
    (e : F ⋙ Q ≅ P ⋙ H) (K : HomotopyCategory C (.up ℤ)) :
    Q.mapDerivedCategory.map (F.rightDerivedFunctorUnit.app K) ≫
        ((Functor.rightDerivedFunctorCompMapDerivedCategoryIso F Q).symm ≪≫
          Functor.rightDerivedFunctorNatIso e ≪≫
          Functor.rightDerivedFunctorCompIso P H ≪≫
          Functor.isoWhiskerRight P.rightDerivedFunctorIsoMapDerivedCategory
            H.rightDerivedFunctor).hom.app (DerivedCategory.Qh.obj K) ≫
        H.rightDerivedFunctor.map (P.mapDerivedCategoryFactorsh.hom.app K) =
      Q.mapDerivedCategoryFactorsh.hom.app ((F.mapHomotopyCategory (.up ℤ)).obj K) ≫
        DerivedCategory.Qh.map ((NatTrans.mapHomotopyCategory e.hom (.up ℤ)).app K) ≫
        H.rightDerivedFunctorUnit.app ((P.mapHomotopyCategory (.up ℤ)).obj K) := by
  have hcomp (F : C ⥤ D) [F.Additive] (Q : D ⥤ U) [Q.Additive] :
      (Functor.mapHomotopyCategoryCompIso (Iso.refl (F ⋙ Q)) (.up ℤ)).inv.app K =
        𝟙 _ := by
    have h := Iso.hom_inv_id_app
      (Functor.mapHomotopyCategoryCompIso (Iso.refl (F ⋙ Q)) (.up ℤ)) K
    rw [Functor.mapHomotopyCategoryCompIso_refl_hom_app, Category.id_comp] at h
    exact h
  have hcomp' :
      (Functor.mapHomotopyCategoryCompIso (Iso.refl (P ⋙ H)) (.up ℤ)).inv.app K =
        𝟙 _ := by
    have h := Iso.hom_inv_id_app
      (Functor.mapHomotopyCategoryCompIso (Iso.refl (P ⋙ H)) (.up ℤ)) K
    rw [Functor.mapHomotopyCategoryCompIso_refl_hom_app, Category.id_comp] at h
    exact h
  have h₁ :
      Q.mapDerivedCategoryFactorsh.inv.app ((F.mapHomotopyCategory (.up ℤ)).obj K) ≫
          Q.mapDerivedCategory.map (F.rightDerivedFunctorUnit.app K) ≫
          (Functor.rightDerivedFunctorCompMapDerivedCategoryIso F Q).inv.app
            (DerivedCategory.Qh.obj K) = (F ⋙ Q).rightDerivedFunctorUnit.app K := by
    have h := Functor.rightDerivedNatTrans_app
      (F.rightDerivedFunctor ⋙ Q.mapDerivedCategory) (F ⋙ Q).rightDerivedFunctor
      (Functor.rightDerivedFunctorCompMapDerivedCategoryUnit F Q)
      (F ⋙ Q).rightDerivedFunctorUnit (HomotopyCategory.quasiIso C (.up ℤ))
      (𝟙 _) K
    simpa [Functor.rightDerivedFunctorCompMapDerivedCategoryIso,
      Functor.rightDerivedFunctorCompMapDerivedCategoryUnit, hcomp, Category.assoc] using h
  have h₂ : (F ⋙ Q).rightDerivedFunctorUnit.app K ≫
      (Functor.rightDerivedFunctorNatIso e).hom.app (DerivedCategory.Qh.obj K) =
      DerivedCategory.Qh.map ((NatTrans.mapHomotopyCategory e.hom (.up ℤ)).app K) ≫
        (P ⋙ H).rightDerivedFunctorUnit.app K := by
    simp [Functor.rightDerivedFunctorNatIso, Functor.rightDerivedFunctorNatTrans]
  have h₃ : (P ⋙ H).rightDerivedFunctorUnit.app K ≫
      (Functor.rightDerivedFunctorCompIso P H).hom.app (DerivedCategory.Qh.obj K) =
      H.rightDerivedFunctorUnit.app ((P.mapHomotopyCategory (.up ℤ)).obj K) ≫
        H.rightDerivedFunctor.map (P.rightDerivedFunctorUnit.app K) := by
    simp [Functor.rightDerivedFunctorCompIso, Functor.rightDerivedFunctorCompUnit, hcomp']
  have h₄ : P.rightDerivedFunctorUnit.app K ≫
      P.rightDerivedFunctorIsoMapDerivedCategory.hom.app (DerivedCategory.Qh.obj K) =
      P.mapDerivedCategoryFactorsh.inv.app K := by
    exact congr_app P.rightDerivedFunctorIsoMapDerivedCategory_hom_fac K
  apply (cancel_epi (Q.mapDerivedCategoryFactorsh.inv.app
    ((F.mapHomotopyCategory (.up ℤ)).obj K))).mp
  simp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    Functor.isoWhiskerRight_hom, Functor.whiskerRight_app, Category.assoc]
  rw [reassoc_of% h₁, reassoc_of% h₂, reassoc_of% h₃]
  simp only [← H.rightDerivedFunctor.map_comp]
  rw [reassoc_of% h₄]
  simp


set_option backward.isDefEq.respectTransparency false in
private theorem squareComparison_normalized
    (F : C ⥤ D) [F.Additive] (P : C ⥤ T) [P.Additive]
    [PreservesFiniteLimits P] [PreservesFiniteColimits P]
    (Q : D ⥤ U) [Q.Additive] [PreservesFiniteLimits Q] [PreservesFiniteColimits Q]
    (H : T ⥤ U) [H.Additive]
    [Abelian.HasKInjectiveResolutions C] [Abelian.HasKInjectiveResolutions T]
    [P.PreservesKInjectiveComplexes]
    (e : F ⋙ Q ≅ P ⋙ H) :
    IsDirectImageNormalizedOnKInjectives F P Q H e
      ((Functor.rightDerivedFunctorCompMapDerivedCategoryIso F Q).symm ≪≫
        Functor.rightDerivedFunctorNatIso e ≪≫
        Functor.rightDerivedFunctorCompIso P H ≪≫
        Functor.isoWhiskerRight P.rightDerivedFunctorIsoMapDerivedCategory
          H.rightDerivedFunctor) := by
  intro J _
  have h := squareComparison_unit F P Q H e
    ((HomotopyCategory.quotient _ (.up ℤ)).obj J)
  apply (cancel_mono
    (H.rightDerivedFunctorObjQIso ((P.mapHomologicalComplex (.up ℤ)).obj J)).inv).mp
  simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
  apply (cancel_epi (Q.mapDerivedCategory.map (F.rightDerivedFunctorObjQIso J).inv)).mp
  simp only [← Q.mapDerivedCategory.map_comp_assoc, Iso.inv_hom_id,
    CategoryTheory.Functor.map_id, Category.id_comp]
  erw [objQIso_inv, objQIso_inv]
  erw [factorsh_hom, factorsh_hom] at h
  exact h


omit [HasDerivedCategory C] [HasDerivedCategory D] [HasDerivedCategory U] in
private theorem homotopy_comp_inv_id (F : C ⥤ D) [F.Additive]
    (Q : D ⥤ U) [Q.Additive] (K : HomotopyCategory C (.up ℤ)) :
    (Functor.mapHomotopyCategoryCompIso (Iso.refl (F ⋙ Q)) (.up ℤ)).inv.app K =
      𝟙 _ := by
  have h := Iso.hom_inv_id_app
    (Functor.mapHomotopyCategoryCompIso (Iso.refl (F ⋙ Q)) (.up ℤ)) K
  rw [Functor.mapHomotopyCategoryCompIso_refl_hom_app, Category.id_comp] at h
  exact h

set_option backward.isDefEq.respectTransparency false in
private theorem squareComparison_eq_mate
    (F : C ⥤ D) [F.Additive] (P : C ⥤ T) [P.Additive]
    [PreservesFiniteLimits P] [PreservesFiniteColimits P]
    (Q : D ⥤ U) [Q.Additive] [PreservesFiniteLimits Q] [PreservesFiniteColimits Q]
    (H : T ⥤ U) [H.Additive]
    (LF : D ⥤ C) [LF.Additive] [PreservesFiniteLimits LF] [PreservesFiniteColimits LF]
    (LH : U ⥤ T) [LH.Additive] [PreservesFiniteLimits LH] [PreservesFiniteColimits LH]
    [Abelian.HasKInjectiveResolutions C] [Abelian.HasKInjectiveResolutions T]
    [P.PreservesKInjectiveComplexes]
    (a : LF ⊣ F) (b : LH ⊣ H) (s : Q ⋙ LH ≅ LF ⋙ P) (e : F ⋙ Q ≅ P ⋙ H)
    (he : (mateEquiv a b (TwoSquare.mk _ _ _ _ s.hom)).natTrans = e.hom) :
    ((Functor.rightDerivedFunctorCompMapDerivedCategoryIso F Q).symm ≪≫
      Functor.rightDerivedFunctorNatIso e ≪≫
      Functor.rightDerivedFunctorCompIso P H ≪≫
      Functor.isoWhiskerRight P.rightDerivedFunctorIsoMapDerivedCategory
        H.rightDerivedFunctor).hom =
    (mateEquiv a.mapDerivedCategoryRightDerivedAdjunction
      b.mapDerivedCategoryRightDerivedAdjunction
      (TwoSquare.mk _ _ _ _
        ((Functor.mapDerivedCategoryCompIso Q LH).symm ≪≫
          Functor.mapDerivedCategoryNatIso s ≪≫
            Functor.mapDerivedCategoryCompIso LF P).hom)).natTrans := by
  apply Functor.rightDerived_ext (F.rightDerivedFunctor ⋙ Q.mapDerivedCategory)
    (Functor.rightDerivedFunctorCompMapDerivedCategoryUnit F Q)
    (HomotopyCategory.quasiIso C (.up ℤ))
  apply NatTrans.ext
  funext K
  dsimp only [Functor.rightDerivedFunctorCompMapDerivedCategoryUnit,
    NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.associator_hom_app, Functor.associator_inv_app]
  simp only [homotopy_comp_inv_id, CategoryTheory.Functor.map_id, Category.id_comp]
  repeat' first | erw [Category.id_comp] | erw [Category.comp_id]
  apply (cancel_epi (Q.mapDerivedCategoryFactorsh.hom.app
    ((F.mapHomotopyCategory (.up ℤ)).obj K))).mp
  simp only [Category.assoc]
  erw [Iso.hom_inv_id_app_assoc, Iso.hom_inv_id_app_assoc]
  apply (cancel_mono (H.rightDerivedFunctor.map
    (P.mapDerivedCategoryFactorsh.hom.app K))).mp
  simp only [Category.assoc]
  rw [squareComparison_unit]
  have h := _root_.derived_mate_factorsh a b s K
  rw [he] at h
  simp only [Functor.mapHomotopyCategoryCompIso_refl_hom_app, homotopy_comp_inv_id,
    Category.comp_id] at h
  repeat' first | erw [Category.id_comp] at h | erw [Category.comp_id] at h
  exact h.symm

end GenericNormalization

set_option backward.isDefEq.respectTransparency false in
private theorem comparison_of_resolving
    {B E V : Type*} [Category B] [Category E] [Category V]
    (W : MorphismProperty B) [W.HasRightCalculusOfFractions]
    (q : B ⥤ E) [q.IsLocalization W] (P : ObjectProperty B)
    (res : ∀ X : B, ∃ (Y : P.FullSubcategory) (s : Y.obj ⟶ X), W s)
    (F G : E ⥤ V) (H : B ⥤ V)
    (a : q ⋙ F ⟶ H) (b : q ⋙ G ⟶ H)
    (ha : ∀ X, P X → IsIso (a.app X))
    (hb : ∀ X, P X → IsIso (b.app X)) :
    ∃ e : F ≅ G, (∀ X, e.hom.app (q.obj X) ≫ b.app X = a.app X) ∧
      ∀ e' : F ≅ G, (∀ X, P X → e'.hom.app (q.obj X) ≫ b.app X = a.app X) → e' = e := by
  classical
  let := CategoryTheory.restriction_localization W q P res
  let ff := Localization.fullyFaithfulWhiskeringLeft (P.ι ⋙ q)
    (W.inverseImage P.ι) V
  let a' : P.ι ⋙ q ⋙ F ≅ P.ι ⋙ H :=
    NatIso.ofComponents (fun X ↦ @asIso _ _ _ _ (a.app X.obj) (ha X.obj X.property))
      (fun s ↦ a.naturality s.hom)
  let b' : P.ι ⋙ q ⋙ G ≅ P.ι ⋙ H :=
    NatIso.ofComponents (fun X ↦ @asIso _ _ _ _ (b.app X.obj) (hb X.obj X.property))
      (fun s ↦ b.naturality s.hom)
  let e : F ≅ G := ff.preimageIso (a' ≪≫ b'.symm)
  have he (X : P.FullSubcategory) :
      e.hom.app (q.obj X.obj) ≫ b.app X.obj = a.app X.obj := by
    have h := congrArg (fun t ↦ t.app X) (ff.map_preimage (a' ≪≫ b'.symm).hom)
    have := hb X.obj X.property
    change e.hom.app (q.obj X.obj) = a.app X.obj ≫ inv (b.app X.obj) at h
    rw [h, Category.assoc, IsIso.inv_hom_id, Category.comp_id]
  have he' (X : B) : e.hom.app (q.obj X) ≫ b.app X = a.app X := by
    obtain ⟨Y, s, hs⟩ := res X
    have := Localization.inverts q W s hs
    apply (cancel_epi (F.map (q.map s))).mp
    have hb' : G.map (q.map s) ≫ b.app X = b.app Y.obj ≫ H.map s := b.naturality s
    rw [← Category.assoc, e.hom.naturality, Category.assoc, hb', ← Category.assoc, he]
    exact (a.naturality s).symm
  refine ⟨e, he', ?_⟩
  intro e' heq
  apply Iso.ext
  apply ff.map_injective
  ext X
  have := hb X.obj X.property
  exact (cancel_mono (b.app X.obj)).mp ((heq X.obj X.property).trans (he X).symm)


private theorem const_mate {B E J : Type*} [Category B] [Category E] [Category J]
    (L : B ⥤ E) (R : E ⥤ B) (a : L ⊣ R) :
    (mateEquiv a (a.whiskerRight J)
      (TwoSquare.mk _ _ _ _ (Functor.compConstIso J L).inv)).natTrans =
      (Functor.compConstIso J R).hom := by
  ext M j
  simp only [mateEquiv_apply, TwoSquare.mk, TwoSquare.natTrans, NatTrans.comp_app,
    Functor.whiskerLeft_app, Functor.whiskerRight_app, Functor.associator_hom_app,
    Functor.associator_inv_app, Functor.rightUnitor_inv_app, Functor.leftUnitor_hom_app,
    Category.id_comp]
  erw [Adjunction.whiskerRight_unit_app_app]
  change a.unit.app (R.obj M) ≫ 𝟙 _ ≫ R.map (𝟙 _) ≫ 𝟙 _ ≫
    R.map (a.counit.app M) ≫ 𝟙 _ = 𝟙 _
  simp only [Category.id_comp, Category.comp_id]
  erw [R.map_id, Category.id_comp]
  exact a.right_triangle_components M


private theorem limit_comparison_diagonal
    {B D T U : Type*} [Category B] [Category D] [Category T] [Category U]
    {p : B ⥤ D} {r : D ⥤ B} {g : T ⥤ U} {s : U ⥤ T}
    {dx : D ⥤ U} {lx : U ⥤ D} {dy : B ⥤ T} {ly : T ⥤ B}
    (a : p ⊣ r) (b : g ⊣ s) (ax : dx ⊣ lx) (ay : dy ⊣ ly)
    (e : dy ⋙ g ≅ p ⋙ dx) (χ : r ⋙ dy ≅ dx ⋙ s)
    (hχ : χ.hom = (mateEquiv a b (TwoSquare.mk _ _ _ _ e.hom)).natTrans)
    [IsIso ax.unit] [IsIso ay.unit] (M : D) :
    r.map (ax.unit.app M) ≫
        (conjugateIsoEquiv (a.comp ax) (ay.comp b) e).hom.app (dx.obj M) ≫
        ly.map (χ.inv.app M) ≫ inv (ay.unit.app (r.obj M)) = 𝟙 _ := by
  let α := TwoSquare.mk _ _ _ _ e.hom
  have hh := unit_mateEquiv ax ay (mateEquiv a b α) M
  have hl : (mateEquiv ax ay (mateEquiv a b α)).natTrans =
      (conjugateIsoEquiv (a.comp ax) (ay.comp b) e).hom :=
    iterated_mateEquiv_conjugateEquiv a b ay ax α
  change r.map (ax.unit.app M) ≫
      (mateEquiv ax ay (mateEquiv a b α)).natTrans.app (dx.obj M) =
    ay.unit.app (r.obj M) ≫ ly.map ((mateEquiv a b α).natTrans.app M) at hh
  rw [hl, ← hχ] at hh
  rw [reassoc_of% hh]
  simp only [← ly.map_comp_assoc, Iso.hom_inv_id_app]
  erw [ly.map_id, Category.id_comp, IsIso.hom_inv_id]
  rfl

section ExactTriangle
universe a₁ a₂ a₃ a₄ b₁ b₂ b₃ b₄ c₁ c₂ c₃ c₄
variable {C : Type a₁} [Category.{b₁} C] [Abelian C] [HasDerivedCategory.{c₁} C]
  {D : Type a₂} [Category.{b₂} D] [Abelian D] [HasDerivedCategory.{c₂} D]
  {T : Type a₃} [Category.{b₃} T] [Abelian T] [HasDerivedCategory.{c₃} T]
  {U : Type a₄} [Category.{b₄} U] [Abelian U] [HasDerivedCategory.{c₄} U]
  (P : C ⥤ T) (Q : D ⥤ U) (F : C ⥤ D) (H : T ⥤ U)
  (E : T ⥤ C) (V : U ⥤ D)
  [P.Additive] [Q.Additive] [F.Additive] [H.Additive] [E.Additive] [V.Additive]
  [PreservesFiniteLimits P] [PreservesFiniteColimits P]
  [PreservesFiniteLimits Q] [PreservesFiniteColimits Q]
  [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  [PreservesFiniteLimits H] [PreservesFiniteColimits H]
  [PreservesFiniteLimits E] [PreservesFiniteColimits E]
  [PreservesFiniteLimits V] [PreservesFiniteColimits V]
attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits
attribute [local irreducible] Functor.mapDerivedCategory

set_option backward.isDefEq.respectTransparency false in
private theorem exact_triangle_square (e : P ⋙ H ≅ F ⋙ Q)
    (k : E ⋙ F ≅ H ⋙ V) (u : P ⋙ E ≅ 𝟭 C) (v : Q ⋙ V ≅ 𝟭 D)
    (h : ∀ N, F.map (u.inv.app N) ≫ k.hom.app (P.obj N) ≫
      V.map (e.hom.app N) = v.inv.app (F.obj N)) (M : DerivedCategory C) :
    (Functor.mapDerivedCategorySquareIso k).hom.app (P.mapDerivedCategory.obj M) ≫
      V.mapDerivedCategory.map ((Functor.mapDerivedCategorySquareIso e).hom.app M) ≫
      ((Functor.mapDerivedCategoryCompIso Q V).symm ≪≫
        Functor.mapDerivedCategoryNatIso v ≪≫ Functor.mapDerivedCategoryIdIso D).hom.app
          (F.mapDerivedCategory.obj M) =
    F.mapDerivedCategory.map
      (((Functor.mapDerivedCategoryCompIso P E).symm ≪≫
        Functor.mapDerivedCategoryNatIso u ≪≫ Functor.mapDerivedCategoryIdIso C).hom.app M) := by
  let u' := (Functor.mapDerivedCategoryCompIso P E).symm ≪≫
    Functor.mapDerivedCategoryNatIso u ≪≫ Functor.mapDerivedCategoryIdIso C
  let v' := (Functor.mapDerivedCategoryCompIso Q V).symm ≪≫
    Functor.mapDerivedCategoryNatIso v ≪≫ Functor.mapDerivedCategoryIdIso D
  let c := Functor.mapDerivedCategoryTriangleIso u.symm
  let d := Functor.mapDerivedCategoryTriangleIso v.symm
  have hd := Functor.exactSquare_comp_forward P E (𝟭 C) Q V (𝟭 D) F H F
    e k (Iso.refl F) u.symm v.symm (fun N ↦ by simpa using h N) M
  have hu : c.hom.app M ≫ u'.hom.app M =
      (Functor.mapDerivedCategoryIdIso C).hom.app M := by
    simp only [c, u', Functor.mapDerivedCategoryTriangleIso, Iso.trans_hom,
      Iso.symm_hom, NatTrans.comp_app, Functor.mapDerivedCategoryNatIso_symm,
      Category.assoc, Iso.hom_inv_id_app_assoc, Iso.inv_hom_id_app_assoc]
  have hv : d.hom.app (F.mapDerivedCategory.obj M) ≫
      v'.hom.app (F.mapDerivedCategory.obj M) =
      (Functor.mapDerivedCategoryIdIso D).hom.app (F.mapDerivedCategory.obj M) := by
    simp only [d, v', Functor.mapDerivedCategoryTriangleIso, Iso.trans_hom,
      Iso.symm_hom, NatTrans.comp_app, Functor.mapDerivedCategoryNatIso_symm,
      Category.assoc, Iso.hom_inv_id_app_assoc, Iso.inv_hom_id_app_assoc]
  have hi := congr_app (Functor.mapDerivedCategoryCompIso_id_comp F) M
  have hj := congr_app (Functor.mapDerivedCategoryCompIso_comp_id F) M
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    NatTrans.id_app] at hi hj
  have hid : (Functor.mapDerivedCategorySquareIso (F₁ := 𝟭 C) (F₂ := F)
      (G₁ := F) (G₂ := 𝟭 D) (Iso.refl F)).hom.app M ≫
      (Functor.mapDerivedCategoryIdIso D).hom.app (F.mapDerivedCategory.obj M) =
      F.mapDerivedCategory.map ((Functor.mapDerivedCategoryIdIso C).hom.app M) := by
    simp only [Functor.mapDerivedCategorySquareIso, Iso.trans_hom, Iso.symm_hom,
      NatTrans.comp_app, Category.assoc]
    rw [hj]
    have hr := congr_app (Functor.mapDerivedCategoryNatIso_refl (F := F)) M
    erw [hr]
    repeat' first | erw [Category.id_comp] | erw [Category.comp_id]
    apply (cancel_epi ((Functor.mapDerivedCategoryCompIso (𝟭 C) F).hom.app M)).mp
    rw [Iso.hom_inv_id_app]
    exact hi.symm
  change _ = F.mapDerivedCategory.map (u'.hom.app M)
  apply (cancel_epi (F.mapDerivedCategory.map (c.hom.app M))).mp
  try simp only [Category.assoc]
  rw [reassoc_of% hd, hv, hid, ← F.mapDerivedCategory.map_comp, hu]

end ExactTriangle

section ReductionComparison
universe a₁ a₂ a₃ a₄ b₁ b₂ b₃ b₄ c₁ c₂ c₃ c₄
variable {C : Type a₁} [Category.{b₁} C] [Abelian C] [HasDerivedCategory.{c₁} C]
  {D : Type a₂} [Category.{b₂} D] [Abelian D] [HasDerivedCategory.{c₂} D]
  {T : Type a₃} [Category.{b₃} T] [Abelian T] [HasDerivedCategory.{c₃} T]
  {U : Type a₄} [Category.{b₄} U] [Abelian U] [HasDerivedCategory.{c₄} U]
attribute [local irreducible] Functor.mapDerivedCategory

set_option backward.isDefEq.respectTransparency false in
private theorem reductionComparison
    (P : C ⥤ T) [P.Additive] (Q : D ⥤ U) [Q.Additive]
    (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (H : T ⥤ U) [H.Additive] [PreservesFiniteLimits H] [PreservesFiniteColimits H]
    (RP : DerivedCategory C ⥤ DerivedCategory T)
    (RQ : DerivedCategory D ⥤ DerivedCategory U)
    (cP : DerivedCategory.Qh ⋙ RP ⟶ P.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh)
    (cQ : DerivedCategory.Qh ⋙ RQ ⟶ Q.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh)
    (e : P ⋙ H ≅ F ⋙ Q)
    (K : ObjectProperty (HomotopyCategory C (.up ℤ)))
    (res : ∀ Z : HomotopyCategory C (.up ℤ),
      ∃ (V : K.FullSubcategory) (s : V.obj ⟶ Z), HomotopyCategory.quasiIso C (.up ℤ) s)
    (hP : ∀ Z, K Z → IsIso (cP.app Z))
    (hQ : ∀ Z, K Z → IsIso (cQ.app ((F.mapHomotopyCategory (.up ℤ)).obj Z))) :
    ∃ τ : RP ⋙ H.mapDerivedCategory ≅ F.mapDerivedCategory ⋙ RQ,
      (∀ Z, IsReductionPullAt P Q F H RP RQ cP cQ e τ Z) ∧
      ∀ τ' : RP ⋙ H.mapDerivedCategory ≅ F.mapDerivedCategory ⋙ RQ,
        (∀ Z, K Z → IsReductionPullAt P Q F H RP RQ cP cQ e τ' Z) → τ' = τ := by
  let q := DerivedCategory.Qh (C := C)
  let e' := Functor.mapHomotopyCategoryCompIso e (.up ℤ) ≪≫
    (Functor.mapHomotopyCategoryCompIso (Iso.refl (F ⋙ Q)) (.up ℤ)).symm
  let V := F.mapHomotopyCategory (.up ℤ) ⋙ Q.mapHomotopyCategory (.up ℤ) ⋙
    DerivedCategory.Qh
  let a : q ⋙ (RP ⋙ H.mapDerivedCategory) ⟶ V :=
    Functor.whiskerRight cP H.mapDerivedCategory ≫
      Functor.whiskerLeft (P.mapHomotopyCategory (.up ℤ)) H.mapDerivedCategoryFactorsh.hom ≫
      Functor.whiskerRight e'.hom DerivedCategory.Qh
  let b : q ⋙ (F.mapDerivedCategory ⋙ RQ) ⟶ V :=
    Functor.whiskerRight F.mapDerivedCategoryFactorsh.hom RQ ≫
      Functor.whiskerLeft (F.mapHomotopyCategory (.up ℤ)) cQ
  have ha (Z) (hZ : K Z) : IsIso (a.app Z) := by
    have := hP Z hZ
    dsimp only [a, NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app]
    infer_instance
  have hb (Z) (hZ : K Z) : IsIso (b.app Z) := by
    have := hQ Z hZ
    dsimp only [b, NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app]
    infer_instance
  obtain ⟨τ, hτ, huniq⟩ := comparison_of_resolving
    (HomotopyCategory.quasiIso C (.up ℤ)) q K res
    (RP ⋙ H.mapDerivedCategory) (F.mapDerivedCategory ⋙ RQ) V a b ha hb
  refine ⟨τ, ?_, ?_⟩
  · intro Z
    simpa only [IsReductionPullAt, a, b, q, e', NatTrans.comp_app,
      Functor.whiskerRight_app, Functor.whiskerLeft_app, Iso.trans_hom, Iso.symm_hom] using hτ Z
  · intro τ' hτ'
    apply huniq τ'
    intro Z hZ
    simpa only [IsReductionPullAt, a, b, q, e', NatTrans.comp_app,
      Functor.whiskerRight_app, Functor.whiskerLeft_app, Iso.trans_hom, Iso.symm_hom] using hτ' Z hZ


set_option backward.isDefEq.respectTransparency false in
private theorem reductionComparison_on_complexes
    (P : C ⥤ T) [P.Additive] (Q : D ⥤ U) [Q.Additive]
    (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (H : T ⥤ U) [H.Additive] [PreservesFiniteLimits H] [PreservesFiniteColimits H]
    (RP : DerivedCategory C ⥤ DerivedCategory T)
    (RQ : DerivedCategory D ⥤ DerivedCategory U)
    (cP : DerivedCategory.Qh ⋙ RP ⟶ P.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh)
    (cQ : DerivedCategory.Qh ⋙ RQ ⟶ Q.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh)
    (e : P ⋙ H ≅ F ⋙ Q)
    (S : ObjectProperty (CochainComplex C ℤ)) (V : ObjectProperty (CochainComplex D ℤ))
    (res : ∀ E : CochainComplex C ℤ, ∃ (K : CochainComplex C ℤ) (s : K ⟶ E),
      S K ∧ QuasiIso s ∧ V ((F.mapHomologicalComplex (.up ℤ)).obj K))
    (hP : ∀ E, S E → IsIso (cP.app ((HomotopyCategory.quotient _ (.up ℤ)).obj E)))
    (hQ : ∀ E, V E → IsIso (cQ.app ((HomotopyCategory.quotient _ (.up ℤ)).obj E))) :
    ∃! τ : RP ⋙ H.mapDerivedCategory ≅ F.mapDerivedCategory ⋙ RQ,
      ∀ E : CochainComplex C ℤ, S E →
        IsReductionPullAt P Q F H RP RQ cP cQ e τ
          ((HomotopyCategory.quotient _ (.up ℤ)).obj E) := by
  let W := HomotopyCategory.quasiIso C (.up ℤ)
  let K : ObjectProperty (HomotopyCategory C (.up ℤ)) := fun Z ↦
    ∃ E : CochainComplex C ℤ, S E ∧ V ((F.mapHomologicalComplex (.up ℤ)).obj E) ∧
      (HomotopyCategory.quotient _ (.up ℤ)).obj E = Z
  have hres (Z : HomotopyCategory C (.up ℤ)) :
      ∃ (V : K.FullSubcategory) (s : V.obj ⟶ Z), W s := by
    obtain ⟨E, rfl⟩ := Z.quotient_obj_surjective
    obtain ⟨V, s, hV, hs, hImage⟩ := res E
    exact ⟨⟨(HomotopyCategory.quotient _ (.up ℤ)).obj V, V, hV, hImage, rfl⟩,
      (HomotopyCategory.quotient _ (.up ℤ)).map s,
      (HomotopyCategory.quotient_map_mem_quasiIso_iff s).2 hs⟩
  have hP' (Z) (hZ : K Z) : IsIso (cP.app Z) := by
    obtain ⟨E, hE, hImage, rfl⟩ := hZ
    exact hP E hE
  have hQ' (Z) (hZ : K Z) :
      IsIso (cQ.app ((F.mapHomotopyCategory (.up ℤ)).obj Z)) := by
    obtain ⟨E, hE, hImage, rfl⟩ := hZ
    exact (NatTrans.isIso_app_iff_of_iso cQ
      ((F.mapHomotopyCategoryFactors (.up ℤ)).app E)).mp
        (hQ ((F.mapHomologicalComplex (.up ℤ)).obj E) hImage)
  obtain ⟨τ, hτ, huniq⟩ := reductionComparison P Q F H RP RQ cP cQ e K hres hP' hQ'
  refine ⟨τ, ?_, ?_⟩
  · intro E hE
    exact hτ ((HomotopyCategory.quotient _ (.up ℤ)).obj E)
  · intro τ' hτ'
    apply huniq τ'
    intro Z hZ
    obtain ⟨E, hE, hImage, rfl⟩ := hZ
    exact hτ' E hE

set_option backward.isDefEq.respectTransparency false in
private theorem exact_square_factorsh
    (P : C ⥤ T) (Q : D ⥤ U) (F : C ⥤ D) (H : T ⥤ U)
    [P.Additive] [Q.Additive] [F.Additive] [H.Additive]
    [PreservesFiniteLimits P] [PreservesFiniteColimits P]
    [PreservesFiniteLimits Q] [PreservesFiniteColimits Q]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits H] [PreservesFiniteColimits H]
    (e : P ⋙ H ≅ F ⋙ Q) (K : HomotopyCategory C (.up ℤ)) :
    (Functor.mapDerivedCategorySquareIso e).hom.app (DerivedCategory.Qh.obj K) ≫
        Q.mapDerivedCategory.map (F.mapDerivedCategoryFactorsh.hom.app K) ≫
        Q.mapDerivedCategoryFactorsh.hom.app ((F.mapHomotopyCategory (.up ℤ)).obj K) =
      H.mapDerivedCategory.map (P.mapDerivedCategoryFactorsh.hom.app K) ≫
        H.mapDerivedCategoryFactorsh.hom.app ((P.mapHomotopyCategory (.up ℤ)).obj K) ≫
        DerivedCategory.Qh.map
          ((Functor.mapHomotopyCategoryCompIso e (.up ℤ)).hom.app K ≫
            (Functor.mapHomotopyCategoryCompIso (Iso.refl (F ⋙ Q)) (.up ℤ)).inv.app K) := by
  have h := Functor.mapDerivedCategorySquareIso_hom_app_Qh_obj e K
  apply (cancel_epi (H.mapDerivedCategoryFactorsh.inv.app
    ((P.mapHomotopyCategory (.up ℤ)).obj K) ≫
      H.mapDerivedCategory.map (P.mapDerivedCategoryFactorsh.inv.app K))).mp
  simp only [Category.assoc]
  rw [h]
  simp only [← H.mapDerivedCategory.map_comp_assoc, Iso.inv_hom_id_app]
  erw [CategoryTheory.Functor.map_id]
  repeat' first | erw [Category.id_comp] | erw [Category.comp_id]
  erw [Iso.inv_hom_id_app_assoc]

set_option backward.isDefEq.respectTransparency false in
private theorem augmentation_comparison_at
    (P₀ P : C ⥤ T) (Q₀ Q : D ⥤ U) (F : C ⥤ D) (H : T ⥤ U)
    [P₀.Additive] [P.Additive] [Q₀.Additive] [Q.Additive] [F.Additive] [H.Additive]
    [PreservesFiniteLimits P₀] [PreservesFiniteColimits P₀]
    [PreservesFiniteLimits Q₀] [PreservesFiniteColimits Q₀]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits H] [PreservesFiniteColimits H]
    (RP : DerivedCategory C ⥤ DerivedCategory T)
    (RQ : DerivedCategory D ⥤ DerivedCategory U)
    (cP : DerivedCategory.Qh ⋙ RP ⟶ P.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh)
    (cQ : DerivedCategory.Qh ⋙ RQ ⟶ Q.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh)
    (e : P ⋙ H ≅ F ⋙ Q) (s : P₀ ⋙ H ≅ F ⋙ Q₀)
    (τ : RP ⋙ H.mapDerivedCategory ≅ F.mapDerivedCategory ⋙ RQ)
    (α : P₀.mapHomotopyCategory (.up ℤ) ⟶ P.mapHomotopyCategory (.up ℤ))
    (β : Q₀.mapHomotopyCategory (.up ℤ) ⟶ Q.mapHomotopyCategory (.up ℤ))
    (δ : P₀.mapDerivedCategory ⟶ RP) (ε : Q₀.mapDerivedCategory ⟶ RQ)
    (hd : ∀ K, δ.app (DerivedCategory.Qh.obj K) ≫ cP.app K =
      P₀.mapDerivedCategoryFactorsh.hom.app K ≫ DerivedCategory.Qh.map (α.app K))
    (he : ∀ K, ε.app (DerivedCategory.Qh.obj K) ≫ cQ.app K =
      Q₀.mapDerivedCategoryFactorsh.hom.app K ≫ DerivedCategory.Qh.map (β.app K))
    (K : HomotopyCategory C (.up ℤ))
    [IsIso (cQ.app ((F.mapHomotopyCategory (.up ℤ)).obj K))]
    (ht : IsReductionPullAt P Q F H RP RQ cP cQ e τ K)
    (hc : (H.mapHomotopyCategory (.up ℤ)).map (α.app K) ≫
      ((Functor.mapHomotopyCategoryCompIso e (.up ℤ)).hom.app K ≫
        (Functor.mapHomotopyCategoryCompIso (Iso.refl (F ⋙ Q)) (.up ℤ)).inv.app K) =
      ((Functor.mapHomotopyCategoryCompIso s (.up ℤ)).hom.app K ≫
        (Functor.mapHomotopyCategoryCompIso (Iso.refl (F ⋙ Q₀)) (.up ℤ)).inv.app K) ≫
          β.app ((F.mapHomotopyCategory (.up ℤ)).obj K)) :
    H.mapDerivedCategory.map (δ.app (DerivedCategory.Qh.obj K)) ≫
        τ.hom.app (DerivedCategory.Qh.obj K) =
      (Functor.mapDerivedCategorySquareIso s).hom.app (DerivedCategory.Qh.obj K) ≫
        ε.app (F.mapDerivedCategory.obj (DerivedCategory.Qh.obj K)) := by
  apply (cancel_mono (RQ.map (F.mapDerivedCategoryFactorsh.hom.app K) ≫
    cQ.app ((F.mapHomotopyCategory (.up ℤ)).obj K))).mp
  simp only [Category.assoc]
  rw [ht, ← H.mapDerivedCategory.map_comp_assoc, hd, H.mapDerivedCategory.map_comp]
  have hn := H.mapDerivedCategoryFactorsh.hom.naturality (α.app K)
  change H.mapDerivedCategory.map (DerivedCategory.Qh.map (α.app K)) ≫
      H.mapDerivedCategoryFactorsh.hom.app ((P.mapHomotopyCategory (.up ℤ)).obj K) =
    H.mapDerivedCategoryFactorsh.hom.app ((P₀.mapHomotopyCategory (.up ℤ)).obj K) ≫
      DerivedCategory.Qh.map ((H.mapHomotopyCategory (.up ℤ)).map (α.app K)) at hn
  rw [Category.assoc, reassoc_of% hn, ← DerivedCategory.Qh.map_comp, hc,
    DerivedCategory.Qh.map_comp]
  have hnε := ε.naturality (F.mapDerivedCategoryFactorsh.hom.app K)
  change Q₀.mapDerivedCategory.map (F.mapDerivedCategoryFactorsh.hom.app K) ≫
      ε.app (DerivedCategory.Qh.obj ((F.mapHomotopyCategory (.up ℤ)).obj K)) =
    ε.app (F.mapDerivedCategory.obj (DerivedCategory.Qh.obj K)) ≫
      RQ.map (F.mapDerivedCategoryFactorsh.hom.app K) at hnε
  rw [← reassoc_of% hnε, he]
  simpa only [Category.assoc] using congrArg
    (fun t ↦ t ≫ DerivedCategory.Qh.map (β.app ((F.mapHomotopyCategory (.up ℤ)).obj K)))
    (exact_square_factorsh P₀ Q₀ F H s K).symm

set_option backward.isDefEq.respectTransparency false in
private theorem natTrans_ext_on_resolving_complexes
    (S : ObjectProperty (CochainComplex C ℤ))
    (res : ∀ E : CochainComplex C ℤ, ∃ (K : CochainComplex C ℤ) (t : K ⟶ E),
      S K ∧ QuasiIso t)
    {V : Type*} [Category V] {F G : DerivedCategory C ⥤ V} (α β : F ⟶ G)
    (h : ∀ K, S K → α.app (DerivedCategory.Q.obj K) = β.app (DerivedCategory.Q.obj K)) :
    α = β := by
  refine Localization.natTrans_ext DerivedCategory.Qh
    (HomotopyCategory.quasiIso C (.up ℤ)) (fun Z ↦ ?_)
  obtain ⟨E, rfl⟩ := Z.quotient_obj_surjective
  obtain ⟨K, t, hK, ht⟩ := res E
  have := ht
  change α.app (DerivedCategory.Q.obj E) = β.app (DerivedCategory.Q.obj E)
  apply (cancel_epi (F.map (DerivedCategory.Q.map t))).mp
  rw [α.naturality, β.naturality, h K hK]

omit [Abelian C] [HasDerivedCategory C] [Abelian D] [HasDerivedCategory D]
  [Abelian T] [HasDerivedCategory T] [Abelian U] [HasDerivedCategory U] in
set_option backward.isDefEq.respectTransparency false in
private theorem homotopy_square_naturality
    [Preadditive C] [Preadditive D] [Preadditive T] [Preadditive U]
    (P₀ P : C ⥤ T) (Q₀ Q : D ⥤ U) (F : C ⥤ D) (H : T ⥤ U)
    [P₀.Additive] [P.Additive] [Q₀.Additive] [Q.Additive] [F.Additive] [H.Additive]
    (α : P₀ ⟶ P) (β : Q₀ ⟶ Q) (e : P ⋙ H ≅ F ⋙ Q) (s : P₀ ⋙ H ≅ F ⋙ Q₀)
    (h : Functor.whiskerRight α H ≫ e.hom =
      s.hom ≫ Functor.whiskerLeft F β)
    (K : HomotopyCategory C (.up ℤ)) :
    (H.mapHomotopyCategory (.up ℤ)).map
        ((NatTrans.mapHomotopyCategory α (.up ℤ)).app K) ≫
      ((Functor.mapHomotopyCategoryCompIso e (.up ℤ)).hom.app K ≫
        (Functor.mapHomotopyCategoryCompIso (Iso.refl (F ⋙ Q)) (.up ℤ)).inv.app K) =
      ((Functor.mapHomotopyCategoryCompIso s (.up ℤ)).hom.app K ≫
        (Functor.mapHomotopyCategoryCompIso (Iso.refl (F ⋙ Q₀)) (.up ℤ)).inv.app K) ≫
          (NatTrans.mapHomotopyCategory β (.up ℤ)).app
            ((F.mapHomotopyCategory (.up ℤ)).obj K) := by
  obtain ⟨V, rfl⟩ := K.quotient_obj_surjective
  have c₁ : (Functor.mapHomotopyCategoryCompIso (Iso.refl (F ⋙ Q)) (.up ℤ)).inv.app
      ((HomotopyCategory.quotient _ (.up ℤ)).obj V) = 𝟙 _ := rfl
  have c₂ : (Functor.mapHomotopyCategoryCompIso (Iso.refl (F ⋙ Q₀)) (.up ℤ)).inv.app
      ((HomotopyCategory.quotient _ (.up ℤ)).obj V) = 𝟙 _ := rfl
  erw [c₁, c₂, Category.comp_id, Category.comp_id]
  change (H.mapHomotopyCategory (.up ℤ)).map
        ((HomotopyCategory.quotient _ (.up ℤ)).map
          ((NatTrans.mapHomologicalComplex α (.up ℤ)).app V)) ≫
      (HomotopyCategory.quotient _ (.up ℤ)).map
        ((Functor.mapHomologicalComplexCompIso e (.up ℤ)).hom.app V) =
    (HomotopyCategory.quotient _ (.up ℤ)).map
        ((Functor.mapHomologicalComplexCompIso s (.up ℤ)).hom.app V) ≫
      (HomotopyCategory.quotient _ (.up ℤ)).map
        ((NatTrans.mapHomologicalComplex β (.up ℤ)).app
          ((F.mapHomologicalComplex (.up ℤ)).obj V))
  rw [Functor.mapHomotopyCategory_map, ← CategoryTheory.Functor.map_comp,
    ← CategoryTheory.Functor.map_comp]
  congr 1
  ext n
  exact congr_app h (V.X n)

set_option backward.isDefEq.respectTransparency false in
private theorem augmentation_comparison_on_complexes
    (P₀ P : C ⥤ T) (Q₀ Q : D ⥤ U) (F : C ⥤ D) (H : T ⥤ U)
    [P₀.Additive] [P.Additive] [Q₀.Additive] [Q.Additive] [F.Additive] [H.Additive]
    [PreservesFiniteLimits P₀] [PreservesFiniteColimits P₀]
    [PreservesFiniteLimits Q₀] [PreservesFiniteColimits Q₀]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits H] [PreservesFiniteColimits H]
    (RP : DerivedCategory C ⥤ DerivedCategory T)
    (RQ : DerivedCategory D ⥤ DerivedCategory U)
    (cP : DerivedCategory.Qh ⋙ RP ⟶ P.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh)
    (cQ : DerivedCategory.Qh ⋙ RQ ⟶ Q.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh)
    (e : P ⋙ H ≅ F ⋙ Q) (s : P₀ ⋙ H ≅ F ⋙ Q₀)
    (τ : RP ⋙ H.mapDerivedCategory ≅ F.mapDerivedCategory ⋙ RQ)
    (α : P₀ ⟶ P) (β : Q₀ ⟶ Q)
    (δ : P₀.mapDerivedCategory ⟶ RP) (ε : Q₀.mapDerivedCategory ⟶ RQ)
    (hd : Functor.whiskerLeft DerivedCategory.Qh δ ≫ cP =
      P₀.mapDerivedCategoryFactorsh.hom ≫ Functor.whiskerRight
        (NatTrans.mapHomotopyCategory α (.up ℤ)) DerivedCategory.Qh)
    (he : Functor.whiskerLeft DerivedCategory.Qh ε ≫ cQ =
      Q₀.mapDerivedCategoryFactorsh.hom ≫ Functor.whiskerRight
        (NatTrans.mapHomotopyCategory β (.up ℤ)) DerivedCategory.Qh)
    (S : ObjectProperty (CochainComplex C ℤ)) (V : ObjectProperty (CochainComplex D ℤ))
    (res : ∀ E : CochainComplex C ℤ, ∃ (K : CochainComplex C ℤ) (t : K ⟶ E),
      S K ∧ QuasiIso t ∧ V ((F.mapHomologicalComplex (.up ℤ)).obj K))
    (hQ : ∀ E, V E → IsIso (cQ.app ((HomotopyCategory.quotient _ (.up ℤ)).obj E)))
    (ht : ∀ E, S E → IsReductionPullAt P Q F H RP RQ cP cQ e τ
      ((HomotopyCategory.quotient _ (.up ℤ)).obj E))
    (hc : Functor.whiskerRight α H ≫ e.hom =
      s.hom ≫ Functor.whiskerLeft F β) :
    Functor.whiskerRight δ H.mapDerivedCategory ≫ τ.hom =
      (Functor.mapDerivedCategorySquareIso s).hom ≫ Functor.whiskerLeft F.mapDerivedCategory ε := by
  apply natTrans_ext_on_resolving_complexes
    (fun E ↦ S E ∧ V ((F.mapHomologicalComplex (.up ℤ)).obj E)) (fun E ↦ by
      obtain ⟨K, t, hK, ht, hF⟩ := res E
      exact ⟨K, t, ⟨hK, hF⟩, ht⟩)
  intro E hE
  let K := (HomotopyCategory.quotient _ (.up ℤ)).obj E
  have : IsIso (cQ.app ((F.mapHomotopyCategory (.up ℤ)).obj K)) :=
    (NatTrans.isIso_app_iff_of_iso cQ ((F.mapHomotopyCategoryFactors (.up ℤ)).app E)).mp
      (hQ _ hE.2)
  exact augmentation_comparison_at P₀ P Q₀ Q F H RP RQ cP cQ e s τ
    (NatTrans.mapHomotopyCategory α (.up ℤ))
    (NatTrans.mapHomotopyCategory β (.up ℤ)) δ ε
    (fun Z ↦ congr_app hd Z) (fun Z ↦ congr_app he Z) K
    (ht E hE.1) (homotopy_square_naturality P₀ P Q₀ Q F H α β e s hc K)

end ReductionComparison

set_option backward.isDefEq.respectTransparency false in
private theorem mates_naturality
    {B C D E : Type*} [Category B] [Category C] [Category D] [Category E]
    {p : B ⥤ C} {r : C ⥤ B} {g : D ⥤ E} {s : E ⥤ D}
    (a : p ⊣ r) (b : g ⊣ s) {dy ry : B ⥤ D} {dx rx : C ⥤ E}
    (α : dy ⟶ ry) (β : dx ⟶ rx)
    (e : dy ⋙ g ⟶ p ⋙ dx) (t : ry ⋙ g ⟶ p ⋙ rx)
    (h : ∀ N, g.map (α.app N) ≫ t.app N = e.app N ≫ β.app (p.obj N))
    (M : C) :
    α.app (r.obj M) ≫ (mateEquiv a b (TwoSquare.mk _ _ _ _ t)).app M =
      (mateEquiv a b (TwoSquare.mk _ _ _ _ e)).app M ≫ s.map (β.app M) := by
  simp only [mateEquiv, Equiv.coe_fn_mk, NatTrans.comp_app,
    Functor.rightUnitor_inv_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_hom_app, Functor.associator_inv_app, Functor.leftUnitor_hom_app,
    Category.id_comp]
  repeat' first | erw [Category.id_comp] | erw [Category.comp_id]
  change α.app (r.obj M) ≫ b.unit.app (ry.obj (r.obj M)) ≫
      s.map (t.app (r.obj M)) ≫ s.map (rx.map (a.counit.app M)) =
    (b.unit.app (dy.obj (r.obj M)) ≫ s.map (e.app (r.obj M)) ≫
      s.map (dx.map (a.counit.app M))) ≫ s.map (β.app M)
  rw [← b.unit_naturality_assoc, ← s.map_comp_assoc, h, s.map_comp,
    Category.assoc, Category.assoc, ← s.map_comp, ← β.naturality, s.map_comp]
  simp only [Category.assoc]
  rfl

set_option backward.isDefEq.respectTransparency false in
private theorem mate_trivial
    {B C : Type*} [Category B] [Category C] {p : B ⥤ C} {r : C ⥤ B}
    (a : p ⊣ r) (dy : B ⥤ B) (dx : C ⥤ C)
    (uy : dy ≅ 𝟭 B) (ux : dx ≅ 𝟭 C) (e : dy ⋙ p ⟶ p ⋙ dx)
    (h : ∀ N, e.app N ≫ ux.hom.app (p.obj N) = p.map (uy.hom.app N))
    (M : C) :
    (mateEquiv a a (TwoSquare.mk _ _ _ _ e)).app M ≫ r.map (ux.hom.app M) =
      uy.hom.app (r.obj M) := by
  simp only [mateEquiv, Equiv.coe_fn_mk, NatTrans.comp_app,
    Functor.rightUnitor_inv_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_hom_app, Functor.associator_inv_app, Functor.leftUnitor_hom_app,
    Category.id_comp]
  repeat' first | erw [Category.id_comp] | erw [Category.comp_id]
  change (a.unit.app (dy.obj (r.obj M)) ≫ r.map (e.app (r.obj M)) ≫
    r.map (dx.map (a.counit.app M))) ≫ r.map (ux.hom.app M) = uy.hom.app (r.obj M)
  have hn := ux.hom.naturality (a.counit.app M)
  change dx.map (a.counit.app M) ≫ ux.hom.app M =
    ux.hom.app (p.obj (r.obj M)) ≫ a.counit.app M at hn
  rw [Category.assoc, Category.assoc, ← r.map_comp, hn, r.map_comp]
  try simp only [Category.assoc]
  rw [← r.map_comp_assoc, h]
  have hy := a.unit.naturality (uy.hom.app (r.obj M))
  change uy.hom.app (r.obj M) ≫ a.unit.app (r.obj M) =
    a.unit.app (dy.obj (r.obj M)) ≫ r.map (p.map (uy.hom.app (r.obj M))) at hy
  rw [← Category.assoc, ← hy, Category.assoc, a.right_triangle_components]
  erw [Category.comp_id]

set_option backward.isDefEq.respectTransparency false in
private theorem mates_evaluation
    {B C D E : Type*} [Category B] [Category C] [Category D] [Category E]
    {p : B ⥤ C} {r : C ⥤ B} {g : D ⥤ E} {s : E ⥤ D}
    (a : p ⊣ r) (b : g ⊣ s) (dy : B ⥤ D) (dx : C ⥤ E)
    (ey : D ⥤ B) (ex : E ⥤ C) (u : dy ⋙ ey ≅ 𝟭 B) (v : dx ⋙ ex ≅ 𝟭 C)
    (e : dy ⋙ g ⟶ p ⋙ dx) (k : ey ⋙ p ⟶ g ⋙ ex)
    (h : ∀ N, k.app (dy.obj N) ≫ ex.map (e.app N) ≫ v.hom.app (p.obj N) =
      p.map (u.hom.app N)) (M : C) :
    ey.map ((mateEquiv a b (TwoSquare.mk _ _ _ _ e)).app M) ≫
        (mateEquiv b a (TwoSquare.mk _ _ _ _ k)).app (dx.obj M) ≫
        r.map (v.hom.app M) = u.hom.app (r.obj M) := by
  let α := TwoSquare.mk _ _ _ _ e
  let β := TwoSquare.mk _ _ _ _ k
  have hp := mate_trivial a (dy ⋙ ey) (dx ⋙ ex) u v (α.hComp β).natTrans
    (fun N ↦ by
      simpa only [TwoSquare.hComp, TwoSquare.mk, TwoSquare.natTrans,
        NatTrans.comp_app, Functor.associator_hom_app, Functor.associator_inv_app,
        Functor.whiskerLeft_app, Functor.whiskerRight_app, Category.id_comp,
        Category.comp_id, Category.assoc] using h N) M
  have hm := congrArg (fun w ↦ w.natTrans.app M) (mateEquiv_vcomp a b a α β)
  rw [hm] at hp
  simpa only [TwoSquare.vComp, TwoSquare.mk, TwoSquare.natTrans,
    NatTrans.comp_app, Functor.associator_hom_app, Functor.associator_inv_app,
    Functor.whiskerLeft_app, Functor.whiskerRight_app, Category.id_comp,
    Category.comp_id, Category.assoc] using hp


private theorem unit_hom_ext {B C : Type*} [Category B] [Category C]
    {L : B ⥤ C} {R : C ⥤ B} (a : L ⊣ R) {M : B} {N : C}
    {f g : L.obj M ⟶ N}
    (h : a.unit.app M ≫ R.map f = a.unit.app M ≫ R.map g) : f = g := by
  apply (a.homEquiv _ _).injective
  simpa only [Adjunction.homEquiv_unit] using h

private theorem unit_transpose {B C : Type*} [Category B] [Category C]
    {L : B ⥤ C} {R : C ⥤ B} (a : L ⊣ R) {M : B} {N : C}
    (f : M ⟶ R.obj N) :
    a.unit.app M ≫ R.map ((a.homEquiv M N).symm f) = f := by
  simpa only [Adjunction.homEquiv_unit] using (a.homEquiv M N).apply_symm_apply f

private theorem existsUnique_natTrans {C D : Type*} [Category C] [Category D]
    (F G : C ⥤ D) (P : ∀ M, (F.obj M ⟶ G.obj M) → Prop)
    (ex : ∀ M, ∃ f, P M f)
    (nat : ∀ {M N} (a : M ⟶ N) (f : F.obj M ⟶ G.obj M) (g : F.obj N ⟶ G.obj N),
      P M f → P N g → F.map a ≫ g = f ≫ G.map a)
    (uniq : ∀ M (f g : F.obj M ⟶ G.obj M), P M f → P M g → f = g) :
    ∃! τ : F ⟶ G, ∀ M, P M (τ.app M) := by
  classical
  let f M := (ex M).choose
  have hf M : P M (f M) := (ex M).choose_spec
  let τ : F ⟶ G :=
    { app := f
      naturality := by
        intro M N a
        exact nat a _ _ (hf _) (hf _) }
  refine ⟨τ, hf, ?_⟩
  intro τ' hτ'
  apply NatTrans.ext
  funext M
  exact uniq M _ _ (hτ' M) (hf M)


-- Use the functors through their comparison APIs, without unfolding their models.
attribute [local irreducible] Functor.mapDerivedCategory Functor.rightDerivedFunctor

variable (A : Type (u + 1)) [CommRing A]

set_option backward.isDefEq.respectTransparency false in
private theorem pullback_adapted_resolution {X Y : Scheme.{u}} (f : X ⟶ Y)
    (P : CochainComplex (Modules A Y) ℤ) :
    ∃ (K : CochainComplex (Modules A Y) ℤ) (s : K ⟶ P),
      CochainComplex.IsKFlatIndependentCoefficients (R := coefficients A Y) K ∧
      QuasiIso s ∧ CochainComplex.IsKFlatIndependentCoefficients (R := coefficients A X)
        (((modulePullback A f).mapHomologicalComplex (.up ℤ)).obj K) := by
  let : PreservesFiniteLimits (proEtaleSheafInverseImage f (Type (u + 1))) :=
    (AlgebraicGeometry.ProEtale.toposFunctorialityInverseImage f (𝟙 Y)).2.2.2.1
  obtain ⟨I, hI⟩ := proEtaleAlgebraicInverseImage_exists f (coefficients A Y)
  let E := AlgebraicGeometry.Scheme.proEtaleRingExtension f
    (coefficients A Y) (coefficients A X) (constantRingIso A f)
  have hfun : modulePullback A f = I.modules ⋙ E := by
    rw [hI]
    rfl
  have hobj (M : Modules A Y) : (modulePullback A f).obj M =
      SheafOfModules.changeOfRings (constantRingIso A f).hom (I.modules.obj M) :=
    Functor.congr_obj hfun M
  have hmap {M N : Modules A Y} (a : M ⟶ N) :
      (modulePullback A f).map a = eqToHom (hobj M) ≫
        SheafOfModules.changeOfRingsHom (constantRingIso A f).hom
          (I.modules.obj M) (I.modules.map a) ≫ eqToHom (hobj N).symm :=
    Functor.congr_hom hfun a
  obtain ⟨K, s, hK, _, hs, hImage⟩ :=
    SheafOfModules.exists_pullback_adapted_flat_resolution
      (proEtaleSheafInverseImage f (Type (u + 1)))
      (proEtaleSheafDirectImage f (Type (u + 1)))
      (proEtaleSheafAdjunction f (Type (u + 1))) I (constantRingIso A f).hom
      (modulePullback A f) hobj @hmap P
  exact ⟨K, s, hK, hs, hImage⟩

attribute [local irreducible] proEtaleRingModulePullbackObj
  proEtaleRingModulePullbackMap proEtaleRingModuleAdjunction

section ScalarPullback
variable {X Y : Scheme.{u}} (f : X ⟶ Y)
  (RY SY : Sheaf (ProEt.topology Y) CommRingCat.{u + 1})
  (RX SX : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
  (aY : RY ⟶ SY) (aX : RX ⟶ SX)
  (cR : (proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj RY ≅ RX)
  (cS : (proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj SY ≅ SX)
  (comm : cR.hom ≫ aX =
    (proEtaleSheafInverseImage f CommRingCat.{u + 1}).map aY ≫ cS.hom)

private def extensionPullInv :
    proEtaleRingModulePullback f RY RX cR ⋙ pbcExtend aX ⟶
      pbcExtend aY ⋙ proEtaleRingModulePullback f SY SX cS :=
  (mateEquiv (pbcScalarAdjunction aY) (pbcScalarAdjunction aX)).symm
    (proEtaleRingRestrictionPullbackInv f RY SY RX SX aY aX cR cS comm)

set_option backward.isDefEq.respectTransparency false in
private theorem extensionPullInv_isIso :
    IsIso (extensionPullInv f RY SY RX SX aY aX cR cS comm) := by
  let av := pbcScalarAdjunction aY
  let au := pbcScalarAdjunction aX
  let ar := proEtaleRingModuleAdjunction f RY RX cR
  let az := proEtaleRingModuleAdjunction f SY SX cS
  let b := proEtaleRingRestrictionPullbackInv f RY SY RX SX aY aX cR cS comm
  let d := proEtaleRingRestrictionDirectImage f RY SY RX SX aY aX cR cS comm
  let α := TwoSquare.mk _ _ _ _ b
  let γ := (mateEquiv av au).symm α
  have hm : mateEquiv av au γ = α := (mateEquiv av au).apply_symm_apply α
  have hmate : (mateEquiv az ar α).natTrans = d.hom :=
    AlgebraicGeometry.Scheme.restrictionPullback_mate
      f RY SY RX SX aY aX cR cS comm
  have hc : IsIso (conjugateEquiv (av.comp az) (ar.comp au) γ.natTrans) := by
    rw [← iterated_mateEquiv_conjugateEquiv av au ar az γ, hm, hmate]
    infer_instance
  exact conjugateEquiv_of_iso (av.comp az) (ar.comp au) γ.natTrans


set_option backward.isDefEq.respectTransparency false in
private theorem restrictionPullback_unit
    (M : proEtaleRingModules Y SY) (U : Y.ProEt) (m : M.val.obj (op U)) :
    ((proEtaleRingRestrictionPullbackInv f RY SY RX SX aY aX cR cS comm).app M).val.app
        (op ((proEtaleBaseChange f).obj U))
        (((proEtaleRingModuleAdjunction f RY RX cR).unit.app
          ((proEtaleRingRestrictScalars aY).obj M)).val.app (op U) m) =
      ((proEtaleRingModuleAdjunction f SY SX cS).unit.app M).val.app (op U) m := by
  let b := proEtaleRingRestrictionPullbackInv f RY SY RX SX aY aX cR cS comm
  let d := proEtaleRingRestrictionDirectImage f RY SY RX SX aY aX cR cS comm
  have h := unit_mateEquiv (proEtaleRingModuleAdjunction f SY SX cS)
    (proEtaleRingModuleAdjunction f RY RX cR) (TwoSquare.mk _ _ _ _ b) M
  have hm : (mateEquiv (proEtaleRingModuleAdjunction f SY SX cS)
      (proEtaleRingModuleAdjunction f RY RX cR) (TwoSquare.mk _ _ _ _ b)).natTrans =
      d.hom := AlgebraicGeometry.Scheme.restrictionPullback_mate
        f RY SY RX SX aY aX cR cS comm
  have hmapp : (mateEquiv (proEtaleRingModuleAdjunction f SY SX cS)
      (proEtaleRingModuleAdjunction f RY RX cR) (TwoSquare.mk _ _ _ _ b)).app
        ((proEtaleRingModulePullback f SY SX cS).obj M) =
      d.hom.app ((proEtaleRingModulePullback f SY SX cS).obj M) := congr_app hm _
  rw [hmapp] at h
  change (proEtaleRingRestrictScalars aY).map
      ((proEtaleRingModuleAdjunction f SY SX cS).unit.app M) ≫
        d.hom.app ((proEtaleRingModulePullback f SY SX cS).obj M) =
      (proEtaleRingModuleAdjunction f RY RX cR).unit.app
          ((proEtaleRingRestrictScalars aY).obj M) ≫
        (proEtaleRingModuleDirectImage f RY RX cR).map (b.app M) at h
  have h' := congrArg (fun t ↦ (t.val.app (op U)) m) h
  have hd := (Classical.choose_spec (proEtaleRingRestrictionDirectImage_existsUnique
    f RY SY RX SX aY aX cR cS comm)).1
  change (d.hom.app ((proEtaleRingModulePullback f SY SX cS).obj M)).val.app (op U)
      (((proEtaleRingModuleAdjunction f SY SX cS).unit.app M).val.app (op U) m) =
    (b.app M).val.app (op ((proEtaleBaseChange f).obj U))
      (((proEtaleRingModuleAdjunction f RY RX cR).unit.app
        ((proEtaleRingRestrictScalars aY).obj M)).val.app (op U) m) at h' 
  have hd' : ∀ (N : proEtaleRingModules X SX) (W : Y.ProEtᵒᵖ)
      (z : N.val.obj ((proEtaleBaseChange f).op.obj W)),
      (d.hom.app N).val.app W z = z := hd
  erw [hd'] at h'
  exact h'.symm

end ScalarPullback

/-- Exact diagonal, using the existing strict tower category.
Source: Stacks 0941 (blueprint: lem-sf-cbc-constant-tower-direct-image-normalization). -/
abbrev delta (X : Scheme.{u}) :=
  (Functor.const ℕᵒᵖ : Modules A X ⥤ Towers A X).mapDerivedCategory

/-- Ordinary direct image in the same identified constant coefficients.
Source: Stacks 07A5 (blueprint: lem-sf-cbc-constant-tower-direct-image-normalization). -/
abbrev push {X Y : Scheme.{u}} (f : X ⟶ Y) := (moduleDirectImage A f).rightDerivedFunctor

/-- Ordinary exact inverse image.
Source: Stacks 03EK (blueprint: lem-sf-cbc-constant-tower-direct-image-normalization). -/
abbrev pull {X Y : Scheme.{u}} (f : X ⟶ Y) := (modulePullback A f).mapDerivedCategory

/-- The existing unbounded derived inverse limit on the original small site.
Source: Stacks 0941 (blueprint: lem-sf-cbc-constant-tower-direct-image-normalization). -/
abbrev L (X : Scheme.{u}) := completedRlim X (coefficients A X)

/-- The canonical ordinary constant/inverse-image square, with identity components.
Source: Stacks 00YV (blueprint: lem-sf-cbc-constant-tower-direct-image-normalization). -/
def deltaPull {X Y : Scheme.{u}} (f : X ⟶ Y) :
    delta A Y ⋙ G A f ≅ pull A f ⋙ delta A X :=
  (Functor.mapDerivedCategoryCompIso _ _).symm ≪≫
    Functor.mapDerivedCategoryNatIso (Functor.compConstIso ℕᵒᵖ (modulePullback A f)).symm ≪≫
      Functor.mapDerivedCategoryCompIso _ _

/-- Derived diagonal/limit adjunction, with its ordinary diagonal unit.
Source: Stacks 0941 (blueprint: lem-sf-cbc-constant-tower-direct-image-normalization). -/
def deltaAdj (X : Scheme.{u}) : delta A X ⊣ L A X :=
  (constLimAdj : (Functor.const ℕᵒᵖ : Modules A X ⥤ Towers A X) ⊣
    completedTowerLimit X (coefficients A X)).mapDerivedCategoryRightDerivedAdjunction

/-- The common-direct-image comparison is the conjugate of the identity-component square.
This retains the canonical comparison of Tag 0A07, including its unit normalization.
Source: Stacks 0A07 (blueprint: lem-sf-cbc-constant-tower-direct-image-normalization). -/
def limitPush {X Y : Scheme.{u}} (f : X ⟶ Y) :
    L A X ⋙ push A f ≅ R A f ⋙ L A Y :=
  conjugateIsoEquiv
    ((proEtaleRingDerivedAdjunction f (coefficients A Y) (coefficients A X)
      (constantRingIso A f)).comp (deltaAdj A X))
    ((deltaAdj A Y).comp (adj A f)) (deltaPull A f)

/-- The exact diagonal preserves K-injectives because it is right adjoint to exact
terminal-index evaluation. Source: Stacks 08BJ
(blueprint: lem-sf-cbc-constant-tower-direct-image-normalization).
Proof: a map from a tower to a constant tower is uniquely determined at index zero;
all other components are its composites with the transitions to zero. This gives
an adjunction from exact evaluation to the diagonal. Transport a map from an acyclic
complex through that adjunction and use K-injectivity to null-homotope it. -/
@[instance] theorem delta_preservesKInjective (X : Scheme.{u}) :
    (Functor.const ℕᵒᵖ : Modules A X ⥤ Towers A X).PreservesKInjectiveComplexes := by
  let adj₀ : (evaluation ℕᵒᵖ (Modules A X)).obj (op 0) ⊣ Functor.const ℕᵒᵖ :=
    { unit :=
        { app := fun M ↦
            { app := fun n ↦ M.map (homOfLE (Nat.zero_le n.unop)).op
              naturality := by
                intro i j f
                change M.map f ≫ M.map _ = M.map _ ≫ 𝟙 _
                rw [Category.comp_id, ← M.map_comp]
                congr 1 }
          naturality := by
            intro M N f
            apply NatTrans.ext
            funext n
            exact (f.naturality _).symm }
      counit := 𝟙 _
      left_triangle_components := by intro M; simp
      right_triangle_components := by intro M; ext n; simp }
  exact adj₀.preservesKInjectiveComplexes

/-- The canonical derived direct-image/diagonal isomorphism. Both composition
comparisons retain their universal derived units; the middle comparison has identity
components on ordinary modules.
Source: Stacks 08BJ, 070K
(blueprint: lem-sf-cbc-constant-tower-direct-image-normalization). -/
def chi {X Y : Scheme.{u}} (f : X ⟶ Y) :
    push A f ⋙ delta A Y ≅ delta A X ⋙ R A f :=
  (Functor.rightDerivedFunctorCompMapDerivedCategoryIso (moduleDirectImage A f)
    (Functor.const ℕᵒᵖ)).symm ≪≫
  Functor.rightDerivedFunctorNatIso (Functor.compConstIso ℕᵒᵖ (moduleDirectImage A f)) ≪≫
  Functor.rightDerivedFunctorCompIso (Functor.const ℕᵒᵖ) (towerDirectImage A f) ≪≫
  Functor.isoWhiskerRight
    (Functor.rightDerivedFunctorIsoMapDerivedCategory (Functor.const ℕᵒᵖ)) (R A f)

/-- Evaluation of a diagonal is canonically the identity.
Source: Stacks 0941 (blueprint: lem-sf-cbc-constant-tower-direct-image-normalization). -/
def deltaEval (X : Scheme.{u}) (n : ℕ) : delta A X ⋙ ev A X n ≅ 𝟭 _ :=
  (Functor.mapDerivedCategoryCompIso _ _).symm ≪≫
    Functor.mapDerivedCategoryNatIso
      (Functor.constCompEvaluationObj (D := Modules A X) (op n)) ≪≫
      Functor.mapDerivedCategoryIdIso _

/-- The constant-tower unit is invertible for every unbounded complex.
Source: Stacks 0941 (blueprint: lem-sf-cbc-constant-tower-direct-image-normalization).
Proof: take a K-injective representative J. The diagonal of J is K-injective by
terminal-index evaluation. Its ordinary inverse limit is J, with identity cone.
The derived adjunction unit is the ordinary unit on this representative, hence is
invertible. Naturality and resolving quasi-isomorphisms give every derived object. -/
theorem deltaUnit_isIso (X : Scheme.{u}) : IsIso (deltaAdj A X).unit := by
  have hff : (Functor.const ℕᵒᵖ : Modules A X ⥤ Towers A X).rightDerivedFunctor.Full :=
    inferInstance
  have hfa : (Functor.const ℕᵒᵖ : Modules A X ⥤ Towers A X).rightDerivedFunctor.Faithful :=
    inferInstance
  have : (delta A X).Full := Functor.Full.of_iso
    (Functor.rightDerivedFunctorIsoMapDerivedCategory
      (Functor.const ℕᵒᵖ : Modules A X ⥤ Towers A X))
  have : (delta A X).Faithful := Functor.Faithful.of_iso
    (Functor.rightDerivedFunctorIsoMapDerivedCategory
      (Functor.const ℕᵒᵖ : Modules A X ⥤ Towers A X))
  exact (deltaAdj A X).unit_isIso_of_L_fully_faithful

/-- The specified identification Rlim(delta M) = M, inverse to the canonical unit.
Source: Stacks 0941 (blueprint: lem-sf-cbc-constant-tower-direct-image-normalization). -/
def deltaLimit (X : Scheme.{u}) : delta A X ⋙ L A X ≅ 𝟭 _ :=
  (@asIso _ _ _ _ (deltaAdj A X).unit (deltaUnit_isIso A X)).symm


set_option backward.isDefEq.respectTransparency false in
private theorem chi_normalized {X Y : Scheme.{u}} (f : X ⟶ Y) :
    IsDirectImageNormalizedOnKInjectives (moduleDirectImage A f)
      (Functor.const ℕᵒᵖ : Modules A X ⥤ Towers A X)
      (Functor.const ℕᵒᵖ : Modules A Y ⥤ Towers A Y) (towerDirectImage A f)
      (Functor.compConstIso ℕᵒᵖ (moduleDirectImage A f)) (chi A f) :=
  squareComparison_normalized (moduleDirectImage A f) (Functor.const ℕᵒᵖ)
    (Functor.const ℕᵒᵖ) (towerDirectImage A f)
    (Functor.compConstIso ℕᵒᵖ (moduleDirectImage A f))

set_option backward.isDefEq.respectTransparency false in
private theorem chi_mate {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (chi A f).hom = (mateEquiv
      (proEtaleRingDerivedAdjunction f (coefficients A Y) (coefficients A X)
        (constantRingIso A f)) (adj A f)
      (TwoSquare.mk _ _ _ _ (deltaPull A f).hom)).natTrans := by
  let a := proEtaleRingModuleAdjunction f (coefficients A Y) (coefficients A X)
    (constantRingIso A f)
  exact squareComparison_eq_mate (moduleDirectImage A f) (Functor.const ℕᵒᵖ)
    (Functor.const ℕᵒᵖ) (towerDirectImage A f) (modulePullback A f) (towerPullback A f)
    a (a.whiskerRight ℕᵒᵖ) (Functor.compConstIso ℕᵒᵖ (modulePullback A f)).symm
    (Functor.compConstIso ℕᵒᵖ (moduleDirectImage A f)) (const_mate _ _ a)

set_option backward.isDefEq.respectTransparency false in
private theorem evaluation_pull_diagonal {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ)
    (M : DerivedCategory (Modules A Y)) :
    (evalG A f n).inv.app ((delta A Y).obj M) ≫
        (ev A X n).map ((deltaPull A f).hom.app M) ≫
        (deltaEval A X n).hom.app ((pull A f).obj M) =
      (pull A f).map ((deltaEval A Y n).hom.app M) := by
  have h := exact_triangle_square
    (Functor.const ℕᵒᵖ : Modules A Y ⥤ Towers A Y)
    (Functor.const ℕᵒᵖ : Modules A X ⥤ Towers A X)
    (modulePullback A f) (towerPullback A f)
    ((evaluation ℕᵒᵖ (Modules A Y)).obj (op n))
    ((evaluation ℕᵒᵖ (Modules A X)).obj (op n))
    (Functor.compConstIso ℕᵒᵖ (modulePullback A f)).symm
    (eqToIso (evaluationPullback A f n)).symm
    (Functor.constCompEvaluationObj (D := Modules A Y) (op n))
    (Functor.constCompEvaluationObj (D := Modules A X) (op n)) (fun N ↦ by
      change (modulePullback A f).map (𝟙 N) ≫ 𝟙 _ ≫ 𝟙 _ = 𝟙 _
      rw [CategoryTheory.Functor.map_id, Category.id_comp, Category.id_comp]) M
  simpa only [deltaPull, deltaEval, evalG, Functor.mapDerivedCategorySquareIso,
    Iso.trans_hom, Iso.trans_inv, Iso.symm_hom, Iso.symm_inv, NatTrans.comp_app,
    Functor.mapDerivedCategoryNatIso_symm, Category.assoc] using h


set_option backward.isDefEq.respectTransparency false in
private theorem chi_evaluation {X Y : Scheme.{u}} (f : X ⟶ Y)
    (hc : (chi A f).hom = (mateEquiv
      (proEtaleRingDerivedAdjunction f (coefficients A Y) (coefficients A X)
        (constantRingIso A f)) (adj A f)
      (TwoSquare.mk _ _ _ _ (deltaPull A f).hom)).natTrans)
    (M : DerivedCategory (Modules A X)) (n : ℕ) :
    (ev A Y n).map ((chi A f).hom.app M) ≫
        (evalR A f n).app ((delta A X).obj M) ≫
        (push A f).map ((deltaEval A X n).hom.app M) =
      (deltaEval A Y n).hom.app ((push A f).obj M) := by
  have h := mates_evaluation
    (proEtaleRingDerivedAdjunction f (coefficients A Y) (coefficients A X)
      (constantRingIso A f)) (adj A f) (delta A Y) (delta A X)
    (ev A Y n) (ev A X n) (deltaEval A Y n) (deltaEval A X n)
    (deltaPull A f).hom (evalG A f n).inv (evaluation_pull_diagonal A f n) M
  have hc' := congr_app hc M
  change (chi A f).hom.app M = (mateEquiv
    (proEtaleRingDerivedAdjunction f (coefficients A Y) (coefficients A X)
      (constantRingIso A f)) (adj A f)
      (TwoSquare.mk _ _ _ _ (deltaPull A f).hom)).app M at hc'
  rw [← hc'] at h
  simpa only [evalR, push, moduleDirectImage, proEtaleRingDerivedAdjunction,
    proEtaleRingDerivedDirectImage] using h


set_option backward.isDefEq.respectTransparency false in
private theorem chi_limit {X Y : Scheme.{u}} (f : X ⟶ Y)
    (M : DerivedCategory (Modules A X)) :
    (push A f).map ((deltaLimit A X).inv.app M) ≫
        (limitPush A f).hom.app ((delta A X).obj M) ≫
        (L A Y).map ((chi A f).inv.app M) ≫
        (deltaLimit A Y).hom.app ((push A f).obj M) = 𝟙 _ := by
  have := deltaUnit_isIso A X
  have := deltaUnit_isIso A Y
  have h := limit_comparison_diagonal
    (proEtaleRingDerivedAdjunction f (coefficients A Y) (coefficients A X)
      (constantRingIso A f)) (adj A f) (deltaAdj A X) (deltaAdj A Y)
    (deltaPull A f) (chi A f) (chi_mate A f) M
  simpa only [deltaLimit, Iso.symm_inv, Iso.symm_hom, asIso_hom, asIso_inv,
    NatIso.isIso_inv_app, push, moduleDirectImage, limitPush,
    proEtaleRingDerivedDirectImage] using h

private theorem scalar_obj (X : Scheme.{u})
    {R S : Sheaf (ProEt.topology X) CommRingCat.{u + 1}} (φ : R ⟶ S)
    (M : reductionModules X R) :
    (reductionChange X φ).obj M = SheafOfModules.changeOfRings.{u, u + 1, u + 1} φ M :=
  (reductionChangeExistence X φ).choose_spec.choose M

open scoped ChangeOfRings in
private theorem scalar_tensor (X : Scheme.{u})
    {R S : Sheaf (ProEt.topology X) CommRingCat.{u + 1}} (φ : R ⟶ S)
    (M : reductionModules X R) (U : X.ProEtᵒᵖ) (s : S.obj.obj U) (x : M.val.obj U) :
    reductionTensorSection X φ M U s x =
      (eqToHom (scalar_obj X φ M).symm).val.app U
        ((toSheafify (ProEt.topology X)
          (SheafOfModules.changeOfRingsPresheaf.{u, u + 1, u + 1} φ M).presheaf).app U
            (s ⊗ₜ[R.obj.obj U, (φ.hom.app U).hom] x)) := rfl

private theorem scalar_quasiIso (X : Scheme.{u})
    {R S : Sheaf (ProEt.topology X) CommRingCat.{u + 1}} (φ : R ⟶ S)
    {P Q : CochainComplex (reductionModules X R) ℤ} (a : P ⟶ Q)
    (hP : CochainComplex.IsKFlatIndependentCoefficients (R := R) P)
    (hQ : CochainComplex.IsKFlatIndependentCoefficients (R := R) Q) (ha : QuasiIso a) :
    QuasiIso (((reductionChange X φ).mapHomologicalComplex (.up ℤ)).map a) :=
  (reductionChangeExistence X φ).choose_spec.choose_spec.choose_spec.choose_spec.1
    a hP hQ ha

-- Keep the chosen scalar-extension functor folded behind its proved equations.
attribute [local irreducible] completedAdicChange

variable {A} (I : Ideal A)

/-- The genuine quotient map of constant coefficient sheaves at positive exponent n+1.
Source: Stacks 099M (blueprint: lem-sf-cbc-constant-tower-direct-image-normalization). -/
def quotient (X : Scheme.{u}) (n : ℕ) :
    coefficients A X ⟶ coefficients (A ⧸ I ^ (n + 1)) X :=
  (constantSheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1}).map
    (CommRingCat.ofHom (Ideal.Quotient.mk _))

/-- The quotient transition of constant sheaves, including its coefficient action.
Source: Stacks 099M (blueprint: lem-sf-cbc-constant-tower-direct-image-normalization). -/
def quotientStep (X : Scheme.{u}) (n : ℕ) :
    coefficients (A ⧸ I ^ (n + 2)) X ⟶ coefficients (A ⧸ I ^ (n + 1)) X :=
  (constantSheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1}).map
    (CommRingCat.ofHom (Ideal.Quotient.factorPow I (Nat.le_succ (n + 1))))

/-- Ordinary tensor with a quotient, restricted back to the original coefficients.
Source: Stacks 06YY (blueprint: lem-sf-cbc-constant-tower-direct-image-normalization). -/
def level (X : Scheme.{u}) (n : ℕ) : Modules A X ⥤ Modules A X :=
  reductionChange X (quotient I X n) ⋙ reductionRestrict X (quotient I X n)


open scoped ChangeOfRings in
set_option backward.isDefEq.respectTransparency false in
private theorem tensorSection_smul (X : Scheme.{u})
    {R S : Sheaf (ProEt.topology X) CommRingCat.{u + 1}}
    (φ : R ⟶ S) (M : reductionModules X R)
    (U : X.ProEtᵒᵖ) (s t : S.obj.obj U)
    (x : M.val.obj U) :
    s • reductionTensorSection X φ M U t x =
      reductionTensorSection X φ M U (s * t) x := by
  let T := SheafOfModules.changeOfRingsPresheaf.{u, u + 1, u + 1} φ M
  let b : T ⟶ ((reductionChange X φ).obj M).val :=
    (PresheafOfModules.sheafificationAdjunction.{u + 1}
      (𝟙 (reductionModuleRing X S).obj)).unit.app T ≫
      (eqToHom (scalar_obj X φ M).symm).val
  rw [scalar_tensor, scalar_tensor]
  change s • b.app U (t ⊗ₜ[R.obj.obj U, (φ.hom.app U).hom] x) = _
  rw [← map_smul]
  rfl

open scoped ChangeOfRings in
set_option backward.isDefEq.respectTransparency false in
private def levelUnitMap (X : Scheme.{u}) (n : ℕ) (M : Modules A X) :
    M ⟶ (level I X n).obj M :=
  (pbcScalarAdjunction (quotient I X n)).unit.app M

private theorem levelUnitMap_apply (X : Scheme.{u}) (n : ℕ) (M : Modules A X)
    (U : X.ProEtᵒᵖ) (x : M.val.obj U) :
    (levelUnitMap I X n M).val.app U x =
      reductionTensorSection X (quotient I X n) M U 1 x :=
  (pbcScalarAdjunction_exists (quotient I X n)).exists.choose_spec M U x

open scoped ChangeOfRings in
private theorem tensorSection_map (X : Scheme.{u}) (n : ℕ)
    {M N : Modules A X} (a : M ⟶ N) (U : X.ProEtᵒᵖ)
    (s : (coefficients (A ⧸ I ^ (n + 1)) X).obj.obj U) (x : M.val.obj U) :
    ((level I X n).map a).val.app U
        (reductionTensorSection X (quotient I X n) M U s x) =
      reductionTensorSection X (quotient I X n) N U s (a.val.app U x) := by
  let φ := quotient I X n
  let η := (pbcScalarAdjunction φ).unit
  have hn := congrArg (fun t ↦ t.val.app U x) (η.naturality a)
  change (η.app N).val.app U (a.val.app U x) =
    (((reductionChange X φ).map a).val.app U) ((η.app M).val.app U x) at hn
  have huM := (pbcScalarAdjunction_exists φ).exists.choose_spec M U x
  have huN := (pbcScalarAdjunction_exists φ).exists.choose_spec N U (a.val.app U x)
  change (η.app M).val.app U x = reductionTensorSection X φ M U 1 x at huM
  change (η.app N).val.app U (a.val.app U x) =
    reductionTensorSection X φ N U 1 (a.val.app U x) at huN
  rw [huM, huN] at hn
  change (((reductionChange X φ).map a).val.app U)
      (reductionTensorSection X φ M U s x) = _
  rw [show reductionTensorSection X φ M U s x =
      s • reductionTensorSection X φ M U 1 x by
        simpa only [mul_one] using (tensorSection_smul X φ M U s 1 x).symm]
  erw [(((reductionChange X φ).map a).val.app U).hom.map_smul]
  rw [← hn, tensorSection_smul, mul_one]

open scoped ChangeOfRings in
set_option backward.isDefEq.respectTransparency false in
private theorem level_hom_ext (X : Scheme.{u})
    {R S : Sheaf (ProEt.topology X) CommRingCat.{u + 1}}
    (φ : R ⟶ S) (M N : reductionModules X R)
    (f g : (reductionRestrict X φ).obj ((reductionChange X φ).obj M) ⟶ N)
    (h : ∀ (U : X.ProEtᵒᵖ)
      (s : S.obj.obj U) (x : M.val.obj U),
      f.val.app U (reductionTensorSection X φ M U s x) =
        g.val.app U (reductionTensorSection X φ M U s x)) : f = g := by
  let hM := scalar_obj X φ M
  apply (SheafOfModules.toSheaf (reductionModuleRing X R)).map_injective
  let j := (SheafOfModules.toSheaf _).map (eqToHom hM.symm)
  apply (cancel_epi j).mp
  apply Sheaf.hom_ext
  apply sheafify_hom_ext (ProEt.topology X) _ _
    ((SheafOfModules.toSheaf (reductionModuleRing X R)).obj N).property
  ext U t
  induction t using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | add t t' ht ht' => simp only [map_add, ht, ht']
  | tmul s x =>
      have ht := h U s x
      erw [scalar_tensor] at ht
      exact ht

private theorem quotient_pull_comm {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ) :
    (constantRingIso A f).hom ≫ quotient I X n =
      (proEtaleSheafInverseImage f CommRingCat.{u + 1}).map (quotient I Y n) ≫
        (constantRingIso (A ⧸ I ^ (n + 1)) f).hom := by
  simpa only [constantRingIso, asIso_hom, quotient] using
    (proEtaleConstantInverseImageMap_naturality f
      (a := CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (n + 1))))).symm

private def restrictionPull {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ) :=
  proEtaleRingRestrictionPullbackInv f (coefficients A Y)
    (coefficients (A ⧸ I ^ (n + 1)) Y) (coefficients A X)
    (coefficients (A ⧸ I ^ (n + 1)) X) (quotient I Y n) (quotient I X n)
    (constantRingIso A f) (constantRingIso (A ⧸ I ^ (n + 1)) f)
    (quotient_pull_comm I f n)

private def extensionPull {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ) :
    reductionChange Y (quotient I Y n) ⋙ modulePullback (A ⧸ I ^ (n + 1)) f ≅
      modulePullback A f ⋙ reductionChange X (quotient I X n) := by
  have := extensionPullInv_isIso f (coefficients A Y)
    (coefficients (A ⧸ I ^ (n + 1)) Y) (coefficients A X)
    (coefficients (A ⧸ I ^ (n + 1)) X) (quotient I Y n) (quotient I X n)
    (constantRingIso A f) (constantRingIso (A ⧸ I ^ (n + 1)) f)
    (quotient_pull_comm I f n)
  exact (asIso (extensionPullInv f (coefficients A Y)
    (coefficients (A ⧸ I ^ (n + 1)) Y) (coefficients A X)
    (coefficients (A ⧸ I ^ (n + 1)) X) (quotient I Y n) (quotient I X n)
    (constantRingIso A f) (constantRingIso (A ⧸ I ^ (n + 1)) f)
    (quotient_pull_comm I f n))).symm

private def levelPull {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ) :
    level I Y n ⋙ modulePullback A f ≅ modulePullback A f ⋙ level I X n := by
  have : IsIso (restrictionPull I f n) :=
    proEtaleRingRestrictionPullbackInv_isIso f (coefficients A Y)
    (coefficients (A ⧸ I ^ (n + 1)) Y) (coefficients A X)
    (coefficients (A ⧸ I ^ (n + 1)) X) (quotient I Y n) (quotient I X n)
    (constantRingIso A f) (constantRingIso (A ⧸ I ^ (n + 1)) f)
    (quotient_pull_comm I f n)
  exact Functor.isoWhiskerLeft (reductionChange Y (quotient I Y n))
      (asIso (restrictionPull I f n)) ≪≫
    Functor.isoWhiskerRight (extensionPull I f n) (reductionRestrict X (quotient I X n))

set_option backward.isDefEq.respectTransparency false in
private theorem levelPull_unit {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ)
    (M : Modules A Y) :
    (modulePullback A f).map ((pbcScalarAdjunction (quotient I Y n)).unit.app M) ≫
      (levelPull I f n).hom.app M =
    (pbcScalarAdjunction (quotient I X n)).unit.app ((modulePullback A f).obj M) := by
  have h := unit_mateEquiv_symm (pbcScalarAdjunction (quotient I Y n))
    (pbcScalarAdjunction (quotient I X n))
    (TwoSquare.mk _ _ _ _ (restrictionPull I f n)) M
  change (modulePullback A f).map
      ((pbcScalarAdjunction (quotient I Y n)).unit.app M) ≫
        (restrictionPull I f n).app ((reductionChange Y (quotient I Y n)).obj M) =
      (pbcScalarAdjunction (quotient I X n)).unit.app ((modulePullback A f).obj M) ≫
        (reductionRestrict X (quotient I X n)).map ((extensionPull I f n).inv.app M) at h
  change (modulePullback A f).map
      ((pbcScalarAdjunction (quotient I Y n)).unit.app M) ≫
        (restrictionPull I f n).app ((reductionChange Y (quotient I Y n)).obj M) ≫
        (reductionRestrict X (quotient I X n)).map ((extensionPull I f n).hom.app M) = _
  rw [← Category.assoc, h, Category.assoc, ← Functor.map_comp, Iso.inv_hom_id_app]
  erw [CategoryTheory.Functor.map_id, Category.comp_id]


private theorem scalarUnit_section (X : Scheme.{u})
    {RY SY : Sheaf (ProEt.topology X) CommRingCat.{u + 1}} (a : RY ⟶ SY)
    (M : reductionModules X RY) (U : X.ProEtᵒᵖ) (x : M.val.obj U) :
    ((pbcScalarAdjunction a).unit.app M).val.app U x =
      reductionTensorSection X a M U 1 x :=
  (pbcScalarAdjunction_exists a).exists.choose_spec M U x

set_option backward.isDefEq.respectTransparency false in
private theorem constantRingDirectImageMap {X Y : Scheme.{u}} (f : X ⟶ Y) :
    proEtaleRingDirectImageMap f (coefficients A Y) (coefficients A X)
        (constantRingIso A f) =
      proEtaleConstantDirectImageMap f CommRingCat.{u + 1} (CommRingCat.of A) := by
  let a := proEtaleSheafAdjunction f CommRingCat.{u + 1}
  change a.unit.app _ ≫ (proEtaleSheafDirectImage f CommRingCat.{u + 1}).map
    (proEtaleConstantInverseImageMap f CommRingCat.{u + 1} (CommRingCat.of A)) = _
  have h := (a.homEquiv _ _).apply_symm_apply
    (proEtaleConstantDirectImageMap f CommRingCat.{u + 1} (CommRingCat.of A))
  simpa only [Adjunction.homEquiv_unit, Adjunction.homEquiv_counit,
    proEtaleConstantInverseImageMap] using h

set_option backward.isDefEq.respectTransparency false in
private theorem levelPull_one {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ)
    (M : Modules A Y) (U : Y.ProEt) (x : M.val.obj (op U)) :
    ((levelPull I f n).hom.app M).val.app (op ((proEtaleBaseChange f).obj U))
      (((proEtaleRingModuleAdjunction f (coefficients A Y) (coefficients A X)
        (constantRingIso A f)).unit.app ((level I Y n).obj M)).val.app (op U)
          (reductionTensorSection Y (quotient I Y n) M (op U) 1 x)) =
    reductionTensorSection X (quotient I X n) ((modulePullback A f).obj M)
      (op ((proEtaleBaseChange f).obj U)) 1
      (((proEtaleRingModuleAdjunction f (coefficients A Y) (coefficients A X)
        (constantRingIso A f)).unit.app M).val.app (op U) x) := by
  let a := (pbcScalarAdjunction (quotient I Y n)).unit.app M
  let η := (proEtaleRingModuleAdjunction f (coefficients A Y) (coefficients A X)
    (constantRingIso A f)).unit
  have hn := η.naturality a
  have hn' := congrArg (fun t ↦ (t.val.app (op U)) x) hn
  change (η.app ((level I Y n).obj M)).val.app (op U) (a.val.app (op U) x) =
    ((modulePullback A f).map a).val.app (op ((proEtaleBaseChange f).obj U))
      ((η.app M).val.app (op U) x) at hn'
  have h := congrArg
    (fun t ↦ (t.val.app (op ((proEtaleBaseChange f).obj U)))
      ((η.app M).val.app (op U) x)) (levelPull_unit I f n M)
  change ((levelPull I f n).hom.app M).val.app (op ((proEtaleBaseChange f).obj U))
      (((modulePullback A f).map a).val.app (op ((proEtaleBaseChange f).obj U))
        ((η.app M).val.app (op U) x)) =
    ((pbcScalarAdjunction (quotient I X n)).unit.app ((modulePullback A f).obj M)).val.app
      (op ((proEtaleBaseChange f).obj U)) ((η.app M).val.app (op U) x) at h
  rw [← hn', scalarUnit_section, scalarUnit_section] at h
  exact h


set_option backward.isDefEq.respectTransparency false in
private theorem levelPull_formula {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ)
    (M : Modules A Y) (U : Y.ProEt)
    (s : (coefficients (A ⧸ I ^ (n + 1)) Y).obj.obj (op U))
    (x : M.val.obj (op U)) :
    ((levelPull I f n).hom.app M).val.app (op ((proEtaleBaseChange f).obj U))
      (((proEtaleRingModuleAdjunction f (coefficients A Y) (coefficients A X)
        (constantRingIso A f)).unit.app ((level I Y n).obj M)).val.app (op U)
          (reductionTensorSection Y (quotient I Y n) M (op U) s x)) =
    reductionTensorSection X (quotient I X n) ((modulePullback A f).obj M)
      (op ((proEtaleBaseChange f).obj U))
      ((proEtaleConstantDirectImageMap f CommRingCat.{u + 1}
        (CommRingCat.of (A ⧸ I ^ (n + 1)))).hom.app (op U) s)
      (((proEtaleRingModuleAdjunction f (coefficients A Y) (coefficients A X)
        (constantRingIso A f)).unit.app M).val.app (op U) x) := by
  let B := A ⧸ I ^ (n + 1)
  let E := (reductionChange Y (quotient I Y n)).obj M
  let η := (proEtaleRingModuleAdjunction f (coefficients B Y) (coefficients B X)
    (constantRingIso B f)).unit
  let θ := (extensionPull I f n).hom.app M
  let b := (restrictionPull I f n).app E
  let V := op ((proEtaleBaseChange f).obj U)
  let z := reductionTensorSection Y (quotient I Y n) M (op U) 1 x
  have hunit (t : (coefficients B Y).obj.obj (op U)) :
      b.val.app V
        (((proEtaleRingModuleAdjunction f (coefficients A Y) (coefficients A X)
          (constantRingIso A f)).unit.app ((level I Y n).obj M)).val.app (op U)
            (reductionTensorSection Y (quotient I Y n) M (op U) t x)) =
        (η.app E).val.app (op U)
          (reductionTensorSection Y (quotient I Y n) M (op U) t x) :=
    restrictionPullback_unit f (coefficients A Y) (coefficients B Y)
      (coefficients A X) (coefficients B X) (quotient I Y n) (quotient I X n)
      (constantRingIso A f) (constantRingIso B f) (quotient_pull_comm I f n) E U _
  have ho := levelPull_one I f n M U x
  change θ.val.app V (b.val.app V
    (((proEtaleRingModuleAdjunction f (coefficients A Y) (coefficients A X)
      (constantRingIso A f)).unit.app ((level I Y n).obj M)).val.app (op U) z)) = _ at ho
  rw [hunit 1] at ho
  have ht : reductionTensorSection Y (quotient I Y n) M (op U) s x = s • z := by
    simpa only [mul_one] using (tensorSection_smul Y (quotient I Y n) M (op U) s 1 x).symm
  have hu : (η.app E).val.app (op U) (s • z) =
      @SMul.smul ((coefficients B X).obj.obj V)
        (((modulePullback B f).obj E).val.obj V) inferInstance
        ((proEtaleConstantDirectImageMap f CommRingCat.{u + 1} (CommRingCat.of B)).hom.app
          (op U) s) ((η.app E).val.app (op U) z) := by
    rw [← constantRingDirectImageMap (A := B) f]
    exact ((η.app E).val.app (op U)).hom.map_smul s z
  change θ.val.app V (b.val.app V
    (((proEtaleRingModuleAdjunction f (coefficients A Y) (coefficients A X)
      (constantRingIso A f)).unit.app ((level I Y n).obj M)).val.app (op U)
        (reductionTensorSection Y (quotient I Y n) M (op U) s x))) = _
  rw [hunit s, ht, hu]
  erw [(θ.val.app V).hom.map_smul]
  rw [ho]
  simpa only [mul_one] using tensorSection_smul X (quotient I X n)
    ((modulePullback A f).obj M) V _ 1 _

open scoped ChangeOfRings in
set_option backward.isDefEq.respectTransparency false in
private theorem step_map_exists (X : Scheme.{u})
    {R S T : Sheaf (ProEt.topology X) CommRingCat.{u + 1}}
    (φ : R ⟶ S) (ψ : R ⟶ T) (q : S ⟶ T) (hcomp : φ ≫ q = ψ)
    (M : reductionModules X R) (unitMap : M ⟶ (reductionRestrict X ψ).obj
      ((reductionChange X ψ).obj M))
    (hunit : ∀ (U : X.ProEtᵒᵖ) (x : M.val.obj U),
      unitMap.val.app U x = reductionTensorSection X ψ M U 1 x) :
    ∃ b : (reductionRestrict X φ).obj ((reductionChange X φ).obj M) ⟶
        (reductionRestrict X ψ).obj ((reductionChange X ψ).obj M),
      ∀ (U : X.ProEtᵒᵖ) (s : S.obj.obj U) (x : M.val.obj U),
        b.val.app U (reductionTensorSection X φ M U s x) =
          reductionTensorSection X ψ M U (q.hom.app U s) x := by
  let N := (reductionRestrict X q).obj ((reductionChange X ψ).obj M)
  have hq (U : X.ProEtᵒᵖ) (r : R.obj.obj U) :
      q.hom.app U (φ.hom.app U r) = ψ.hom.app U r :=
    ConcreteCategory.congr_hom (congrArg (fun k ↦ k.hom.app U) hcomp) r
  let ua := (PresheafOfModules.toPresheaf (reductionModuleRing X R).obj).map unitMap.val
  let a : M ⟶ (reductionRestrict X φ).obj N :=
    ⟨PresheafOfModules.homMk ua (by
        intro U r x
        have h := (unitMap.val.app U).hom.map_smul r x
        change unitMap.val.app U (r • x) =
          q.hom.app U (φ.hom.app U r) •
            (show ((reductionChange X ψ).obj M).val.obj U from unitMap.val.app U x)
        rw [hq]
        exact h)⟩
  let adj₀ := pbcScalarAdjunction φ
  let b := (adj₀.homEquiv M N).symm a
  let ub := (PresheafOfModules.toPresheaf (reductionModuleRing X S).obj).map b.val
  let c : (reductionRestrict X φ).obj ((reductionChange X φ).obj M) ⟶
      (reductionRestrict X ψ).obj ((reductionChange X ψ).obj M) :=
    ⟨PresheafOfModules.homMk ub (by
        intro U r x
        have h := (b.val.app U).hom.map_smul (φ.hom.app U r) x
        change b.val.app U ((φ.hom.app U r) •
            (show ((reductionChange X φ).obj M).val.obj U from x)) =
          ψ.hom.app U r •
            (show ((reductionChange X ψ).obj M).val.obj U from b.val.app U x)
        rw [← hq]
        exact h)⟩
  refine ⟨c, ?_⟩
  intro U s x
  change b.val.app U (reductionTensorSection X φ M U s x) = _
  have hb := unit_transpose adj₀ a
  have hb' := congrArg (fun k ↦ k.val.app U x) hb
  change b.val.app U ((adj₀.unit.app M).val.app U x) = a.val.app U x at hb'
  have hu := (pbcScalarAdjunction_exists φ).exists.choose_spec M U x
  change (adj₀.unit.app M).val.app U x = reductionTensorSection X φ M U 1 x at hu
  rw [hu] at hb'
  rw [show reductionTensorSection X φ M U s x =
      s • reductionTensorSection X φ M U 1 x by
        simpa only [mul_one] using (tensorSection_smul X φ M U s 1 x).symm]
  erw [(b.val.app U).hom.map_smul]
  rw [hb']
  change q.hom.app U s •
    (show ((reductionChange X ψ).obj M).val.obj U from unitMap.val.app U x) = _
  rw [hunit, tensorSection_smul, mul_one]

private theorem quotientStep_comp (X : Scheme.{u}) (n : ℕ) :
    quotient I X (n + 1) ≫ quotientStep I X n = quotient I X n := by
  dsimp only [quotient, quotientStep]
  rw [← Functor.map_comp]
  congr 1

/-- Quotient transitions are the unique maps on sheafified pure tensors.
Source: Stacks 06YY (blueprint: lem-sf-cbc-constant-tower-direct-image-normalization).
Proof: quotient maps commute with the scalar maps from A, so s tensor x maps to
q(s) tensor x by a balanced linear map. Sheafification extends it uniquely. The
formula proves compatibility with site restrictions and naturality in the module. -/
theorem step_existsUnique (X : Scheme.{u}) (n : ℕ) :
    ∃! τ : level I X (n + 1) ⟶ level I X n,
      ∀ (M : Modules A X) (U : X.ProEtᵒᵖ)
        (s : (coefficients (A ⧸ I ^ (n + 2)) X).obj.obj U) (x : M.val.obj U),
        (τ.app M).val.app U (reductionTensorSection X (quotient I X (n + 1)) M U s x) =
          reductionTensorSection X (quotient I X n) M U
            ((quotientStep I X n).hom.app U s) x := by
  apply existsUnique_natTrans (level I X (n + 1)) (level I X n)
    (fun M b ↦ ∀ (U : X.ProEtᵒᵖ)
      (s : (coefficients (A ⧸ I ^ (n + 2)) X).obj.obj U) (x : M.val.obj U),
      b.val.app U (reductionTensorSection X (quotient I X (n + 1)) M U s x) =
        reductionTensorSection X (quotient I X n) M U ((quotientStep I X n).hom.app U s) x)
  · intro M
    exact step_map_exists X (quotient I X (n + 1)) (quotient I X n)
      (quotientStep I X n) (quotientStep_comp I X n) M (levelUnitMap I X n M)
      (levelUnitMap_apply I X n M)
  · intro M N a f g hf hg
    apply level_hom_ext X (quotient I X (n + 1)) M
    intro U s x
    change g.val.app U (((level I X (n + 1)).map a).val.app U
      (reductionTensorSection X (quotient I X (n + 1)) M U s x)) =
      ((level I X n).map a).val.app U
        (f.val.app U (reductionTensorSection X (quotient I X (n + 1)) M U s x))
    rw [tensorSection_map, hg, hf, tensorSection_map]
  · intro M f g hf hg
    apply level_hom_ext X (quotient I X (n + 1)) M
    intro U s x
    exact (hf U s x).trans (hg U s x).symm


/-- The strict reduction functor, including all coefficient transition maps.
Source: Stacks 099M (blueprint: lem-sf-cbc-constant-tower-direct-image-normalization). -/
def reductionModule (X : Scheme.{u}) : Modules A X ⥤ Towers A X :=
  (Functor.ofOpSequence (fun n ↦ (step_existsUnique I X n).exists.choose)).flip

/-- Reduction is additive before localization.
Source: Stacks 06YY (blueprint: lem-sf-cbc-constant-tower-direct-image-normalization).
Proof: every level is scalar extension followed by additive scalar restriction.
Evaluation jointly detects equality of maps of strict diagrams. -/
@[instance] theorem reductionModule_additive (X : Scheme.{u}) :
    (reductionModule I X).Additive := by
  constructor
  intro M N f g
  apply NatTrans.ext
  funext n
  have : (level I X n.unop).Additive := by
    dsimp [level]
    infer_instance
  exact (level I X n.unop).map_add

/-- The homotopy functor to be left derived.
Source: Stacks 06YY (blueprint: lem-sf-cbc-constant-tower-direct-image-normalization). -/
def reductionHomotopy (X : Scheme.{u}) :
    HomotopyCategory (Modules A X) (.up ℤ) ⥤ Derived A X :=
  (reductionModule I X).mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh

set_option genSizeOf false in
set_option genInjectivity false in
/-- A derived reduction pair, retaining its determining universal property and K-flat
computation. Source: Stacks 06YS, 06YY
(blueprint: lem-sf-cbc-constant-tower-direct-image-normalization). -/
structure ReductionModel (X : Scheme.{u}) where
  functor : DerivedCategory (Modules A X) ⥤ Derived A X
  counit : DerivedCategory.Qh ⋙ functor ⟶ reductionHomotopy I X
  universal : functor.IsLeftDerivedFunctor counit
    (HomotopyCategory.quasiIso (Modules A X) (.up ℤ))
  computes : ∀ P : CochainComplex (Modules A X) ℤ,
    CochainComplex.IsKFlatIndependentCoefficients (R := coefficients A X) P →
    IsIso (counit.app ((HomotopyCategory.quotient _ (.up ℤ)).obj P))

/-- Universal derived reduction, with its K-flat representative normalization.
Source: Stacks 06YS, 06YY (blueprint: lem-sf-cbc-constant-tower-direct-image-normalization).
Proof: choose flat-term K-flat resolutions. Their diagonal is K-flat: tensoring an
acyclic tower evaluates to tensoring an acyclic complex with the K-flat model at
every level. Evaluations are exact and jointly detect acyclicity. The strict
quotient construction therefore inverts resolving quasi-isomorphisms. The resolving
class left-derived theorem gives the universal counit, invertible on these models.
This universal property determines the derived pair up to its unique comparison. -/
theorem reduction_exists (X : Scheme.{u}) : Nonempty (ReductionModel I X) := by
  let H := HomotopyCategory.quotient (Modules A X) (.up ℤ)
  let F := reductionHomotopy I X
  let S : Set (HomotopyCategory (Modules A X) (.up ℤ)) :=
    { K | ∃ P : CochainComplex (Modules A X) ℤ,
      CochainComplex.IsKFlatIndependentCoefficients (R := coefficients A X) P ∧ H.obj P = K }
  have hres (K : HomotopyCategory (Modules A X) (.up ℤ)) :
      ∃ (K' : HomotopyCategory (Modules A X) (.up ℤ)) (s : K' ⟶ K),
        K' ∈ S ∧ HomotopyCategory.quasiIso (Modules A X) (.up ℤ) s := by
    obtain ⟨E, rfl⟩ := K.quotient_obj_surjective
    obtain ⟨P, s, hP, _, hs, _⟩ :=
      CochainComplex.exists_isKFlatResolutionIndependentCoefficients E
    exact ⟨H.obj P, H.map s, ⟨P, hP, rfl⟩,
      (HomotopyCategory.quotient_map_mem_quasiIso_iff s).2 hs⟩
  have hinv (K K' : HomotopyCategory (Modules A X) (.up ℤ)) (s : K ⟶ K')
      (hK : K ∈ S) (hK' : K' ∈ S)
      (hs : HomotopyCategory.quasiIso (Modules A X) (.up ℤ) s) :
      IsIso (F.map s) := by
    obtain ⟨P, hP, rfl⟩ := hK
    obtain ⟨P', hP', rfl⟩ := hK'
    obtain ⟨a, rfl⟩ := H.map_surjective s
    have ha := (HomotopyCategory.quotient_map_mem_quasiIso_iff a).1 hs
    have hred : QuasiIso (((reductionModule I X).mapHomologicalComplex (.up ℤ)).map a) := by
      rw [HomologicalComplex.quasiIso_iff_evaluation]
      intro n
      let φ := quotient I X n.unop
      have hchange : QuasiIso
          (((reductionChange X φ).mapHomologicalComplex (.up ℤ)).map a) :=
        scalar_quasiIso X φ a hP hP' ha
      let U := reductionRestrict X φ
      have : PreservesFiniteLimits U := pbcRestrict_limits φ
      have : PreservesFiniteColimits U := pbcRestrict_colimits φ
      change QuasiIso ((U.mapHomologicalComplex (.up ℤ)).map
        (((reductionChange X φ).mapHomologicalComplex (.up ℤ)).map a))
      infer_instance
    dsimp only [F, reductionHomotopy, Functor.comp_map, Functor.mapHomotopyCategory_map]
    apply Localization.inverts DerivedCategory.Qh (HomotopyCategory.quasiIso _ _)
    exact (HomotopyCategory.quotient_map_mem_quasiIso_iff _).2 hred
  let : F.CommShift ℤ := by dsimp [F, reductionHomotopy]; infer_instance
  have : F.IsTriangulated := by dsimp [F, reductionHomotopy]; infer_instance
  obtain ⟨_, LF, ε, hLF, _, hε⟩ :=
    Functor.leftDerived_from_resolvingClass (Modules A X) (Derived A X) F S hres hinv
  exact ⟨⟨LF, ε, hLF, fun P hP ↦ hε (H.obj P) ⟨P, hP, rfl⟩⟩⟩

/-- Select the derived pair by its universal property, retaining its comparison.
Source: Stacks 06YY (blueprint: lem-sf-cbc-constant-tower-direct-image-normalization). -/
def reductionModel (X : Scheme.{u}) : ReductionModel I X :=
  Classical.choice (reduction_exists I X)

/-- Reduction is the functor of the universal derived pair.
Source: Stacks 06YY (blueprint: lem-sf-cbc-constant-tower-direct-image-normalization). -/
def reduction (X : Scheme.{u}) : DerivedCategory (Modules A X) ⥤ Derived A X :=
  (reductionModel I X).functor

/-- The universal reduction counit, retained rather than forgotten.
Source: Stacks 06YY (blueprint: lem-sf-cbc-constant-tower-direct-image-normalization). -/
def reductionCounit (X : Scheme.{u}) :
    DerivedCategory.Qh ⋙ reduction I X ⟶ reductionHomotopy I X :=
  (reductionModel I X).counit

/-- Ordinary quotient augmentation, uniquely fixed by the tensor unit at every level.
Source: Stacks 06YY (blueprint: lem-sf-cbc-constant-tower-direct-image-normalization).
Proof: insert 1 tensor x. Quotient transitions preserve 1 and their pure tensor
formula therefore makes these maps a strict tower map, natural in the module.
The formula on all sections determines every component uniquely. -/
theorem ordinaryAugmentation_existsUnique (X : Scheme.{u}) :
    ∃! η : (Functor.const ℕᵒᵖ : Modules A X ⥤ Towers A X) ⟶ reductionModule I X,
      ∀ (M : Modules A X) (n : ℕ) (U : X.ProEtᵒᵖ) (x : M.val.obj U),
        ((η.app M).app (op n)).val.app U x =
          reductionTensorSection X (quotient I X n) M U 1 x := by
  let η : (Functor.const ℕᵒᵖ : Modules A X ⥤ Towers A X) ⟶ reductionModule I X :=
    { app := fun M ↦ NatTrans.ofOpSequence (fun n ↦ levelUnitMap I X n M) (by
        intro n
        change levelUnitMap I X n M = levelUnitMap I X (n + 1) M ≫
          ((Functor.ofOpSequence (fun k ↦ (step_existsUnique I X k).exists.choose)).map
            (homOfLE (n.le_add_right 1)).op).app M
        rw [Functor.ofOpSequence_map_homOfLE_succ]
        ext U x
        change (levelUnitMap I X n M).val.app U x =
          (((step_existsUnique I X n).exists.choose).app M).val.app U
            ((levelUnitMap I X (n + 1) M).val.app U x)
        rw [levelUnitMap_apply, levelUnitMap_apply,
          (step_existsUnique I X n).exists.choose_spec]
        simp only [map_one])
      naturality := by
        intro M N a
        apply NatTrans.ext
        funext n
        exact (pbcScalarAdjunction (quotient I X n.unop)).unit.naturality a }
  refine ⟨η, ?_, ?_⟩
  · intro M n U x
    exact levelUnitMap_apply I X n M U x
  · intro η' hη'
    apply NatTrans.ext
    funext M
    apply NatTrans.ext
    funext n
    ext U x
    exact (hη' M n.unop U x).trans (levelUnitMap_apply I X n.unop M U x).symm

/-- The actual ordinary quotient augmentation.
Source: Stacks 06YY (blueprint: lem-sf-cbc-constant-tower-direct-image-normalization). -/
def ordinaryAugmentation (X : Scheme.{u}) :
    (Functor.const ℕᵒᵖ : Modules A X ⥤ Towers A X) ⟶ reductionModule I X :=
  (ordinaryAugmentation_existsUnique I X).exists.choose

/-- The ordinary augmentation after homotopy localization, with the diagonal
localization factor. Source: Stacks 06YY
(blueprint: lem-sf-cbc-constant-tower-direct-image-normalization). -/
def augmentationHomotopy (X : Scheme.{u}) :
    DerivedCategory.Qh ⋙ delta A X ⟶ reductionHomotopy I X :=
  (Functor.const ℕᵒᵖ : Modules A X ⥤ Towers A X).mapDerivedCategoryFactorsh.hom ≫
    Functor.whiskerRight (NatTrans.mapHomotopyCategory (ordinaryAugmentation I X) (.up ℤ))
      DerivedCategory.Qh

/-- The specified tensor-with-quotient map i_M, constructed by the determining
universal property of derived reduction. Its factorization is the ordinary
x maps to 1 tensor x formula after homotopy localization.
Source: Stacks 06YY (blueprint: lem-sf-cbc-constant-tower-direct-image-normalization). -/
def augmentation (X : Scheme.{u}) : delta A X ⟶ reduction I X :=
  have : (reduction I X).IsLeftDerivedFunctor (reductionCounit I X)
      (HomotopyCategory.quasiIso (Modules A X) (.up ℤ)) := (reductionModel I X).universal
  (reduction I X).leftDerivedLift (reductionCounit I X)
    (HomotopyCategory.quasiIso (Modules A X) (.up ℤ)) (delta A X)
    (augmentationHomotopy I X)


private theorem step_formula (X : Scheme.{u}) (n : ℕ) (M : Modules A X)
    (U : X.ProEtᵒᵖ) (s : (coefficients (A ⧸ I ^ (n + 2)) X).obj.obj U)
    (x : M.val.obj U) :
    (((step_existsUnique I X n).exists.choose).app M).val.app U
        (reductionTensorSection X (quotient I X (n + 1)) M U s x) =
      reductionTensorSection X (quotient I X n) M U
        ((quotientStep I X n).hom.app U s) x :=
  (step_existsUnique I X n).exists.choose_spec M U s x

private theorem quotientStep_pull_comm {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ) :
    (constantRingIso (A ⧸ I ^ (n + 2)) f).hom ≫ quotientStep I X n =
      (proEtaleSheafInverseImage f CommRingCat.{u + 1}).map (quotientStep I Y n) ≫
        (constantRingIso (A ⧸ I ^ (n + 1)) f).hom := by
  simpa only [constantRingIso, asIso_hom, quotientStep] using
    (proEtaleConstantInverseImageMap_naturality f
      (a := CommRingCat.ofHom (Ideal.Quotient.factorPow I (Nat.le_succ (n + 1))))).symm

set_option backward.isDefEq.respectTransparency false in
private theorem quotientStep_direct_comm {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ)
    (U : Y.ProEt) (s : (coefficients (A ⧸ I ^ (n + 2)) Y).obj.obj (op U)) :
    (proEtaleConstantDirectImageMap f CommRingCat.{u + 1}
      (CommRingCat.of (A ⧸ I ^ (n + 1)))).hom.app (op U)
        ((quotientStep I Y n).hom.app (op U) s) =
    (quotientStep I X n).hom.app (op ((proEtaleBaseChange f).obj U))
      ((proEtaleConstantDirectImageMap f CommRingCat.{u + 1}
        (CommRingCat.of (A ⧸ I ^ (n + 2)))).hom.app (op U) s) := by
  have h := AlgebraicGeometry.Scheme.restrictionDirectImageMap_square f
    (coefficients (A ⧸ I ^ (n + 2)) Y) (coefficients (A ⧸ I ^ (n + 1)) Y)
    (coefficients (A ⧸ I ^ (n + 2)) X) (coefficients (A ⧸ I ^ (n + 1)) X)
    (quotientStep I Y n) (quotientStep I X n)
    (constantRingIso (A ⧸ I ^ (n + 2)) f) (constantRingIso (A ⧸ I ^ (n + 1)) f)
    (quotientStep_pull_comm I f n)
  rw [constantRingDirectImageMap, constantRingDirectImageMap] at h
  exact congrArg (fun a ↦ (a.hom.app (op U)) s) h

set_option backward.isDefEq.respectTransparency false in
private theorem levelPull_step {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ)
    (M : Modules A Y) :
    (modulePullback A f).map (((step_existsUnique I Y n).exists.choose).app M) ≫
        (levelPull I f n).hom.app M =
      (levelPull I f (n + 1)).hom.app M ≫
        (((step_existsUnique I X n).exists.choose).app ((modulePullback A f).obj M)) := by
  let a := proEtaleRingModuleAdjunction f (coefficients A Y) (coefficients A X)
    (constantRingIso A f)
  let t := ((step_existsUnique I Y n).exists.choose).app M
  apply unit_hom_ext a
  apply level_hom_ext Y (quotient I Y (n + 1)) M
  intro U s x
  obtain ⟨U⟩ := U
  have hn := a.unit.naturality t
  have hn' := congrArg (fun t ↦ (t.val.app (op U))
    (reductionTensorSection Y (quotient I Y (n + 1)) M (op U) s x)) hn
  change (a.unit.app ((level I Y n).obj M)).val.app (op U)
      (t.val.app (op U) (reductionTensorSection Y (quotient I Y (n + 1)) M (op U) s x)) =
    ((modulePullback A f).map t).val.app (op ((proEtaleBaseChange f).obj U))
      ((a.unit.app ((level I Y (n + 1)).obj M)).val.app (op U)
        (reductionTensorSection Y (quotient I Y (n + 1)) M (op U) s x)) at hn'
  change ((levelPull I f n).hom.app M).val.app (op ((proEtaleBaseChange f).obj U))
      (((modulePullback A f).map t).val.app (op ((proEtaleBaseChange f).obj U))
        ((a.unit.app ((level I Y (n + 1)).obj M)).val.app (op U)
          (reductionTensorSection Y (quotient I Y (n + 1)) M (op U) s x))) =
    ((((step_existsUnique I X n).exists.choose).app ((modulePullback A f).obj M))).val.app
      (op ((proEtaleBaseChange f).obj U))
      (((levelPull I f (n + 1)).hom.app M).val.app (op ((proEtaleBaseChange f).obj U))
        ((a.unit.app ((level I Y (n + 1)).obj M)).val.app (op U)
          (reductionTensorSection Y (quotient I Y (n + 1)) M (op U) s x)))
  rw [← hn', step_formula, levelPull_formula, levelPull_formula, step_formula]
  rw [quotientStep_direct_comm]

/-- Ordinary tensor/pullback comparison on the entire strict quotient tower.
Its formula is imposed on all inverse-image generators, not only constant sections.
Source: Stacks 07A4, 03EL
(blueprint: lem-sf-cbc-constant-tower-direct-image-normalization).
Proof: pullback of each constant quotient ring is its canonical constant sheaf.
The scalar square commutes on constants and therefore on the sheafifications.
Tensor balancing sends the inverse image of s tensor x to the inverse image of s
 tensored with the inverse image of x. The reverse reassociation is inverse.
The quotient transition formulas make these maps a strict diagram isomorphism.
Local generation of inverse-image sections and sheafification prove uniqueness. -/
theorem ordinaryReductionPull_existsUnique {X Y : Scheme.{u}} (f : X ⟶ Y) :
    ∃! σ : reductionModule I Y ⋙ towerPullback A f ≅
        modulePullback A f ⋙ reductionModule I X,
      ∀ (M : Modules A Y) (n : ℕ) (U : Y.ProEt)
        (s : (coefficients (A ⧸ I ^ (n + 1)) Y).obj.obj (op U))
        (x : M.val.obj (op U)),
        ((σ.hom.app M).app (op n)).val.app (op ((proEtaleBaseChange f).obj U))
            (((proEtaleRingModuleAdjunction f (coefficients A Y) (coefficients A X)
              (constantRingIso A f)).unit.app ((level I Y n).obj M)).val.app (op U)
                (reductionTensorSection Y (quotient I Y n) M (op U) s x)) =
          reductionTensorSection X (quotient I X n) ((modulePullback A f).obj M)
            (op ((proEtaleBaseChange f).obj U))
            ((proEtaleConstantDirectImageMap f CommRingCat.{u + 1}
              (CommRingCat.of (A ⧸ I ^ (n + 1)))).hom.app (op U) s)
            (((proEtaleRingModuleAdjunction f (coefficients A Y) (coefficients A X)
              (constantRingIso A f)).unit.app M).val.app (op U) x) := by
  let σ : reductionModule I Y ⋙ towerPullback A f ⟶
      modulePullback A f ⋙ reductionModule I X :=
    { app := fun M ↦ NatTrans.ofOpSequence
        (fun n ↦ (levelPull I f n).hom.app M) (by
          intro n
          change (modulePullback A f).map
              (((Functor.ofOpSequence (fun k ↦ (step_existsUnique I Y k).exists.choose)).map
                (homOfLE (n.le_add_right 1)).op).app M) ≫ _ =
            _ ≫ (((Functor.ofOpSequence (fun k ↦ (step_existsUnique I X k).exists.choose)).map
              (homOfLE (n.le_add_right 1)).op).app ((modulePullback A f).obj M))
          rw [Functor.ofOpSequence_map_homOfLE_succ, Functor.ofOpSequence_map_homOfLE_succ]
          exact levelPull_step I f n M)
      naturality := by
        intro M N a
        apply NatTrans.ext
        funext n
        exact (levelPull I f n.unop).hom.naturality a }
  have (M : Modules A Y) : IsIso (σ.app M) := by
    have (n : ℕᵒᵖ) : IsIso ((σ.app M).app n) := by
      change IsIso ((levelPull I f n.unop).hom.app M)
      infer_instance
    exact NatIso.isIso_of_isIso_app _
  have : IsIso σ := NatIso.isIso_of_isIso_app _
  refine ⟨asIso σ, ?_, ?_⟩
  · intro M n U s x
    exact levelPull_formula I f n M U s x
  · intro τ hτ
    apply Iso.ext
    apply NatTrans.ext
    funext M
    apply NatTrans.ext
    funext n
    let a := proEtaleRingModuleAdjunction f (coefficients A Y) (coefficients A X)
      (constantRingIso A f)
    apply unit_hom_ext a
    apply level_hom_ext Y (quotient I Y n.unop) M
    intro U s x
    obtain ⟨U⟩ := U
    change ((τ.hom.app M).app n).val.app (op ((proEtaleBaseChange f).obj U))
        ((a.unit.app ((level I Y n.unop).obj M)).val.app (op U)
          (reductionTensorSection Y (quotient I Y n.unop) M (op U) s x)) =
      ((levelPull I f n.unop).hom.app M).val.app (op ((proEtaleBaseChange f).obj U))
        ((a.unit.app ((level I Y n.unop).obj M)).val.app (op U)
          (reductionTensorSection Y (quotient I Y n.unop) M (op U) s x))
    exact (hτ M n.unop U s x).trans (levelPull_formula I f n.unop M U s x).symm

/-- The normalized ordinary comparison, retaining its strict transition maps.
Source: Stacks 07A4 (blueprint: lem-sf-cbc-constant-tower-direct-image-normalization). -/
def ordinaryReductionPull {X Y : Scheme.{u}} (f : X ⟶ Y) :=
  (ordinaryReductionPull_existsUnique I f).exists.choose

set_option backward.isDefEq.respectTransparency false in
private theorem ordinary_augmentation_pull {X Y : Scheme.{u}} (f : X ⟶ Y) :
    Functor.whiskerRight (ordinaryAugmentation I Y) (towerPullback A f) ≫
        (ordinaryReductionPull I f).hom =
      (Functor.compConstIso ℕᵒᵖ (modulePullback A f)).inv ≫
        Functor.whiskerLeft (modulePullback A f) (ordinaryAugmentation I X) := by
  apply NatTrans.ext
  funext M
  apply NatTrans.ext
  funext n
  let a := proEtaleRingModuleAdjunction f (coefficients A Y) (coefficients A X)
    (constantRingIso A f)
  apply unit_hom_ext a
  ext U x
  obtain ⟨U⟩ := U
  let α := ((ordinaryAugmentation I Y).app M).app n
  have hn := congrArg (fun t ↦ (t.val.app (op U)) x) (a.unit.naturality α)
  change (a.unit.app ((level I Y n.unop).obj M)).val.app (op U)
      (α.val.app (op U) x) =
    ((modulePullback A f).map α).val.app (op ((proEtaleBaseChange f).obj U))
      ((a.unit.app M).val.app (op U) x) at hn
  change (((ordinaryReductionPull I f).hom.app M).app n).val.app
      (op ((proEtaleBaseChange f).obj U))
        (((modulePullback A f).map α).val.app (op ((proEtaleBaseChange f).obj U))
          ((a.unit.app M).val.app (op U) x)) = _
  rw [← hn]
  have hy := (ordinaryAugmentation_existsUnique I Y).exists.choose_spec M n.unop (op U) x
  change α.val.app (op U) x = _ at hy
  rw [hy]
  erw [(ordinaryReductionPull_existsUnique I f).exists.choose_spec]
  change reductionTensorSection X (quotient I X n.unop) ((modulePullback A f).obj M)
      (op ((proEtaleBaseChange f).obj U)) _ _ =
    (((ordinaryAugmentation I X).app ((modulePullback A f).obj M)).app n).val.app
      (op ((proEtaleBaseChange f).obj U)) ((a.unit.app M).val.app (op U) x)
  erw [(ordinaryAugmentation_existsUnique I X).exists.choose_spec]
  congr 1
  exact map_one _


private theorem reductionCounit_isIso (X : Scheme.{u})
    (P : CochainComplex (Modules A X) ℤ)
    (hP : CochainComplex.IsKFlatIndependentCoefficients (R := coefficients A X) P) :
    IsIso ((reductionCounit I X).app ((HomotopyCategory.quotient _ (.up ℤ)).obj P)) :=
  (reductionModel I X).computes P hP

section
attribute [local irreducible] modulePullback reductionModule reduction reductionCounit
  reductionModel
/-- Derived tensor/pullback comparison characterized on K-flat representatives.
Source: Stacks 06YS, 07A4
(blueprint: lem-sf-cbc-constant-tower-direct-image-normalization).
Proof: a flat-term K-flat model P remains K-flat with flat terms after exact
constant-coefficient inverse image. The reduction counits are invertible there.
Conjugate the ordinary strict comparison by these counits and the localization
factors. This descends through chain maps, homotopies and resolving
quasi-isomorphisms. Every object has such a model, proving uniqueness. -/
theorem reductionPull_existsUnique {X Y : Scheme.{u}} (f : X ⟶ Y) :
    ∃! τ : reduction I Y ⋙ G A f ≅ pull A f ⋙ reduction I X,
      ∀ P : CochainComplex (Modules A Y) ℤ,
        CochainComplex.IsKFlatIndependentCoefficients (R := coefficients A Y) P →
        IsReductionPullAt (reductionModule I Y) (reductionModule I X)
          (modulePullback A f) (towerPullback A f) (reduction I Y) (reduction I X)
          (reductionCounit I Y) (reductionCounit I X) (ordinaryReductionPull I f) τ
          ((HomotopyCategory.quotient _ (.up ℤ)).obj P) := by
  exact reductionComparison_on_complexes (reductionModule I Y) (reductionModule I X)
    (modulePullback A f) (towerPullback A f) (reduction I Y) (reduction I X)
    (reductionCounit I Y) (reductionCounit I X) (ordinaryReductionPull I f)
    (fun E ↦ CochainComplex.IsKFlatIndependentCoefficients (R := coefficients A Y) E)
    (fun E ↦ CochainComplex.IsKFlatIndependentCoefficients (R := coefficients A X) E)
    (pullback_adapted_resolution A f) (reductionCounit_isIso I Y) (reductionCounit_isIso I X)

end

/-- The canonical whole-tower tensor/pullback comparison.
Source: Stacks 07A4 (blueprint: lem-sf-cbc-constant-tower-direct-image-normalization). -/
def reductionPull {X Y : Scheme.{u}} (f : X ⟶ Y) :=
  (reductionPull_existsUnique I f).exists.choose

/-- The projection map h, defined by its counit-tensor adjunction mate. The comparison
being transposed is the canonical tensor balancing map on the full quotient diagram.
Its source therefore includes precisely the diagonal identification chi.
Source: Stacks 0B56 (blueprint: lem-sf-cbc-constant-tower-direct-image-normalization). -/
def projection {X Y : Scheme.{u}} (f : X ⟶ Y) :
    push A f ⋙ reduction I Y ⟶ reduction I X ⋙ R A f :=
  mateEquiv
    (proEtaleRingDerivedAdjunction f (coefficients A Y) (coefficients A X)
      (constantRingIso A f)) (adj A f) (reductionPull I f).hom

private theorem augmentation_fac_nat (X : Scheme.{u}) :
    Functor.whiskerLeft DerivedCategory.Qh (augmentation I X) ≫ reductionCounit I X =
      augmentationHomotopy I X := by
  have : (reduction I X).IsLeftDerivedFunctor (reductionCounit I X)
      (HomotopyCategory.quasiIso (Modules A X) (.up ℤ)) := (reductionModel I X).universal
  exact (reduction I X).leftDerived_fac (reductionCounit I X)
    (HomotopyCategory.quasiIso (Modules A X) (.up ℤ)) (delta A X)
    (augmentationHomotopy I X)

private theorem augmentation_fac_nat_normalized (X : Scheme.{u}) :
    Functor.whiskerLeft DerivedCategory.Qh (augmentation I X) ≫ reductionCounit I X =
      (Functor.const ℕᵒᵖ : Modules A X ⥤ Towers A X).mapDerivedCategoryFactorsh.hom ≫
        Functor.whiskerRight
          (NatTrans.mapHomotopyCategory (ordinaryAugmentation I X) (.up ℤ))
          DerivedCategory.Qh := augmentation_fac_nat I X

private theorem reductionPull_normalization {X Y : Scheme.{u}} (f : X ⟶ Y)
    (E : CochainComplex (Modules A Y) ℤ)
    (hE : CochainComplex.IsKFlatIndependentCoefficients (R := coefficients A Y) E) :
    IsReductionPullAt (reductionModule I Y) (reductionModule I X)
      (modulePullback A f) (towerPullback A f) (reduction I Y) (reduction I X)
      (reductionCounit I Y) (reductionCounit I X) (ordinaryReductionPull I f)
      (reductionPull I f) ((HomotopyCategory.quotient _ (.up ℤ)).obj E) :=
  (reductionPull_existsUnique I f).exists.choose_spec E hE

section
attribute [local irreducible] modulePullback reductionModule reduction reductionCounit
  reductionModel augmentation
  ordinaryAugmentation ordinaryReductionPull reductionPull
set_option backward.isDefEq.respectTransparency false in
private theorem augmentation_pull_localized {X Y : Scheme.{u}} (f : X ⟶ Y) :
    Functor.whiskerRight (augmentation I Y) (towerPullback A f).mapDerivedCategory ≫
        (reductionPull I f).hom =
      (Functor.mapDerivedCategorySquareIso
        (Functor.compConstIso ℕᵒᵖ (modulePullback A f)).symm).hom ≫
          Functor.whiskerLeft (modulePullback A f).mapDerivedCategory (augmentation I X) := by
  exact augmentation_comparison_on_complexes
    (C := Modules A Y) (D := Modules A X) (T := Towers A Y) (U := Towers A X)
    (Functor.const ℕᵒᵖ) (reductionModule I Y)
    (Functor.const ℕᵒᵖ) (reductionModule I X) (modulePullback A f) (towerPullback A f)
    (reduction I Y) (reduction I X) (reductionCounit I Y) (reductionCounit I X)
    (ordinaryReductionPull I f) (Functor.compConstIso ℕᵒᵖ (modulePullback A f)).symm
    (reductionPull I f)
    (ordinaryAugmentation I Y) (ordinaryAugmentation I X)
    (augmentation I Y) (augmentation I X)
    (augmentation_fac_nat_normalized I Y) (augmentation_fac_nat_normalized I X)
    (fun E ↦ CochainComplex.IsKFlatIndependentCoefficients (R := coefficients A Y) E)
    (fun E ↦ CochainComplex.IsKFlatIndependentCoefficients (R := coefficients A X) E)
    (pullback_adapted_resolution A f) (reductionCounit_isIso I X)
    (reductionPull_normalization I f)
    (ordinary_augmentation_pull I f)


private theorem augmentation_pull {X Y : Scheme.{u}} (f : X ⟶ Y) :
    Functor.whiskerRight (augmentation I Y) (G A f) ≫ (reductionPull I f).hom =
      (deltaPull A f).hom ≫ Functor.whiskerLeft (pull A f) (augmentation I X) :=
  augmentation_pull_localized I f

end

set_option backward.isDefEq.respectTransparency false in
private theorem chi_projection {X Y : Scheme.{u}} (f : X ⟶ Y)
    (hc : (chi A f).hom = (mateEquiv
      (proEtaleRingDerivedAdjunction f (coefficients A Y) (coefficients A X)
        (constantRingIso A f)) (adj A f)
      (TwoSquare.mk _ _ _ _ (deltaPull A f).hom)).natTrans)
    (M : DerivedCategory (Modules A X)) :
    (augmentation I Y).app ((push A f).obj M) ≫ (projection I f).app M =
      (chi A f).hom.app M ≫ (R A f).map ((augmentation I X).app M) := by
  have h := mates_naturality
    (proEtaleRingDerivedAdjunction f (coefficients A Y) (coefficients A X)
      (constantRingIso A f)) (adj A f)
    (augmentation I Y) (augmentation I X) (deltaPull A f).hom (reductionPull I f).hom
    (fun N ↦ congr_app (augmentation_pull I f) N) M
  have hc' := congr_app hc M
  change (chi A f).hom.app M = (mateEquiv
    (proEtaleRingDerivedAdjunction f (coefficients A Y) (coefficients A X)
      (constantRingIso A f)) (adj A f)
      (TwoSquare.mk _ _ _ _ (deltaPull A f).hom)).app M at hc'
  rw [← hc'] at h
  exact h


/-- Constant strict towers have normalized derived direct image, evaluation, inverse
limit and quotient augmentation, for the given coefficient datum and every object.
Source: agent argument supporting fix-lem-exchanges Step 5, using Stacks 08BJ, 070K,
0940, 0941, 0A07, 06YS, 07A4 and 0B56
(blueprint: lem-sf-cbc-constant-tower-direct-image-normalization).

Proof plan:
1. Realize strict towers on the diagram site. Exact evaluation detects exactness.
Choose a K-injective model J of M. Terminal-index evaluation is left adjoint to
constant towers and is exact, so delta J is K-injective (08BJ). Exact constant-ring
inverse image makes f_* preserve K-injectives as well. The comparison chi is the
universal derived comparison of f_* delta J = delta f_* J (070K). This proves its
representative formula and the identity at every evaluation.
2. The inverse limit of the diagonal K-injective model is J. The two canonical
units identify its derived limit with M. The common-direct-image comparison is the
ordinary f_* lim = lim f_* comparison (0A07). On the diagonal this is the literal
identity, so the displayed conjugated composite is identity.
3. Independently choose a flat-term K-flat model P of M (06YS). The diagonal is
K-flat by levelwise tensoring and joint detection of acyclicity. The strict tensor
of this model with the entire quotient tower represents reduction and its quotient
augmentation. Exact inverse image carries the whole quotient diagram to the same
quotient diagram on X, compatibly with every quotient map (00YV, 07A4). The
normalized comparison reductionPull is thus the diagram-site tensor comparison.
Its adjoint projection is exactly the counit-tensor map of 0B56, with source
identified by chi; no arbitrary projection isomorphism is chosen.
4. Naturality in the coefficient argument applied to the strict quotient map and
the tensor-unit normalization of ringedProjectionMateExact give the last equation
before taking any inverse limit. This is equality of strict derived tower maps,
including all transitions, and uses no boundedness or finiteness of quotient sets. -/
theorem constantTowerDirectImageNormalization
    (d : CompleteCoefficientDatum A) {X Y : Scheme.{u}} (f : X ⟶ Y) :
    IsDirectImageNormalizedOnKInjectives (moduleDirectImage A f)
      (Functor.const ℕᵒᵖ : Modules A X ⥤ Towers A X)
      (Functor.const ℕᵒᵖ : Modules A Y ⥤ Towers A Y) (towerDirectImage A f)
      (Functor.compConstIso ℕᵒᵖ (moduleDirectImage A f)) (chi A f) ∧
    (∀ (M : DerivedCategory (Modules A X)) (n : ℕ),
      (ev A Y n).map ((chi A f).hom.app M) ≫
          (evalR A f n).app ((delta A X).obj M) ≫
          (push A f).map ((deltaEval A X n).hom.app M) =
        (deltaEval A Y n).hom.app ((push A f).obj M)) ∧
    (∀ M : DerivedCategory (Modules A X),
      (push A f).map ((deltaLimit A X).inv.app M) ≫
          (limitPush A f).hom.app ((delta A X).obj M) ≫
          (L A Y).map ((chi A f).inv.app M) ≫
          (deltaLimit A Y).hom.app ((push A f).obj M) = 𝟙 _) ∧
    (∀ M : DerivedCategory (Modules A X),
      (augmentation d.ideal Y).app ((push A f).obj M) ≫
          (projection d.ideal f).app M =
        (chi A f).hom.app M ≫ (R A f).map ((augmentation d.ideal X).app M)) := by
  exact ⟨chi_normalized A f, chi_evaluation A f (chi_mate A f), chi_limit A f,
    chi_projection d.ideal f (chi_mate A f)⟩

end AlgebraicGeometry.ProEtale.StrictTower.ConstantNormalization
