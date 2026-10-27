/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q129
-/
module

public import Sheaf.Paper.InternalScalarPullbackNormalization
public import Sheaf.Paper.RestrictedCoefficientPullbackData
public import Sheaf.Paper.ModuleRingedToposDerivedComparison
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible
public import WeilConjectures.CategoryTheory.ModuleObjects.DerivedExtendScalars
import Sheaf.Paper.FlatCoefficientSquareNormalization
import all Sheaf.Paper.ProEtaleSectionModuleFunctors
import Mathlib.CategoryTheory.Adjunction.Mates
import Sheaf.UpstreamExtra.WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Monoidal
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.SingleFunctor
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperStarUnitCoherence
import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasDerivedCategory

/-! # The restricted coefficient mate and the projection map

Source: blueprint main-20261015, proper-base-change rational proof, paragraph (1),
canonical scalar comparison; Stacks Tags 07A4, 07A6 and 0B56
(blueprint: lem-sfb-restricted-coefficient-mate-projection).
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

attribute [local irreducible] AlgebraicGeometry.ProEtale.upperStarFromPoint
  DerivedCategory.monoidalClosed CategoryTheory.Mod.monoidalClosed
  CategoryTheory.Functor.leftDerivedFunctor
  CategoryTheory.Functor.rightDerivedFunctor CategoryTheory.Functor.mapDerivedCategory

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped CategoryTheory.Obj
open AlgebraicGeometry.ProEtale.QuotientChange

namespace AlgebraicGeometry.ProEtale.RestrictedCoefficientMate

variable {R S : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
  [MonObj R] [IsCommMonObj R] [MonObj S] [IsCommMonObj S]

variable [∀ T : Scheme.{u},
  HasDerivedCategory.{u + 1} (ModuleRingedComparison.modules R T)]

variable (a : R ⟶ S) [IsMonHom a]
  [∀ T : Scheme.{u}, PreservesFiniteLimits (Mod.extendScalars (coefficientMap a T))]

/-- The existing coefficient push mate with its scalar functor names exposed.
This is the recorded derivedPushHom itself, with no new mate or adjunction choice.
Source: blueprint rational proper-base-change proof (1); Stacks 07A6
(blueprint: lem-sfb-restricted-coefficient-mate-projection). -/
def scalarMate {X Y : Scheme.{u}} (f : X ⟶ Y) :
    F R f ⋙ D a Y ⟶
      D a X ⋙ F S f := by
  unfold D F CondensedRing.moduleObjectDerivedPushforward
  exact CondensedRing.derivedPushHom a f

/-- The recorded d with the same explicit derived-pushforward interface as h.
Source: blueprint rational proper-base-change proof (1); Stacks 0D6E
(blueprint: lem-sfb-restricted-coefficient-mate-projection). -/
def restrictionPushIso {X Y : Scheme.{u}} (f : X ⟶ Y) :
    F S f ⋙ V a Y ≅
      V a X ⋙ F R f := by
  unfold F CondensedRing.moduleObjectDerivedPushforward
  exact CondensedRing.derivedComapLowerStarIso a f

/-- The recorded projection arrow with the named geometric functors exposed.
Source: Stacks 0B56 (blueprint: lem-sfb-restricted-coefficient-mate-projection). -/
def projection {X Y : Scheme.{u}} (f : X ⟶ Y)
    (K : DerivedCategory (Modules R X)) (C : DerivedCategory (Modules R Y)) :
    (F R f).obj K ⊗ C ⟶ (F R f).obj (K ⊗ (L R f).obj C) := by
  unfold F L CondensedRing.moduleObjectDerivedPullback
    CondensedRing.moduleObjectDerivedPushforward
  exact ModuleRingedComparison.internalProjection R f K C

/-- The recorded tensor comparison with the named geometric functor exposed.
Source: Stacks 07A4 (blueprint: lem-sfb-restricted-coefficient-mate-projection). -/
def tensorPull {X Y : Scheme.{u}} (f : X ⟶ Y)
    (M C : DerivedCategory (Modules R Y)) :
    (L R f).obj (M ⊗ C) ⟶ (L R f).obj M ⊗ (L R f).obj C := by
  unfold L CondensedRing.moduleObjectDerivedPullback
  exact ((ModuleRingedComparison.internalDelta R f).app M).app C

/-- The specified h, with coefficient on the right. The input tensor presentations
are the normalized presentations of lem-sfb-internal-scalar-pullback-normalization;
no replacement of the actual scalar mate or restriction/direct-image comparison occurs.
Source: blueprint rational proper-base-change proof (1); Stacks 07A6
(blueprint: lem-sfb-restricted-coefficient-mate-projection). -/
def restrictedMap {X Y : Scheme.{u}} (f : X ⟶ Y)
    (eX : TensorNormalization a X) (eY : TensorNormalization a Y)
    (K : DerivedCategory (Modules R X)) :
    (F R f).obj K ⊗ B a Y ⟶ (F R f).obj (K ⊗ B a X) :=
  eY.derived.inv.app ((F R f).obj K) ≫
    (V a Y).map ((scalarMate a f).app K) ≫
    (restrictionPushIso a f).hom.app ((D a X).obj K) ≫
    (F R f).map (eX.derived.hom.app K)

private theorem push_eq_mate_pull_inv
    {A B A' B' : Type*} [Category A] [Category B] [Category A'] [Category B']
    {T : A ⥤ B} {U : B ⥤ A} {T' : A' ⥤ B'} {U' : B' ⥤ A'}
    {l : A' ⥤ A} {r : A ⥤ A'} {l' : B' ⥤ B} {r' : B ⥤ B'}
    (a₁ : T ⊣ U) (a₂ : T' ⊣ U') (b₁ : l ⊣ r) (b₂ : l' ⊣ r')
    (e : r' ⋙ U' ≅ U ⋙ r) :
    Adjunction.pushHomOfComapIso a₁ a₂ e =
      (mateEquiv b₁ b₂ (TwoSquare.mk _ _ _ _
        (Adjunction.pullIsoOfComapIso a₁ a₂ b₁ b₂ e).inv)).natTrans := by
  have h := iterated_mateEquiv_conjugateEquiv_symm b₁ b₂ a₂ a₁
    (TwoSquare.mk _ _ _ _ e.inv)
  apply (TwoSquare.equivNatTrans _ _ _ _).symm.injective
  apply (mateEquiv b₁ b₂).symm.injective
  change (mateEquiv b₁ b₂).symm ((mateEquiv a₁ a₂).symm (.mk _ _ _ _ e.inv)) =
    (mateEquiv b₁ b₂).symm
      (mateEquiv b₁ b₂ (.mk _ _ _ _ (Adjunction.pullIsoOfComapIso a₁ a₂ b₁ b₂ e).inv))
  rw [Equiv.symm_apply_apply]
  exact h

section MateProof

set_option allowUnsafeReducibility true
attribute [local reducible] D L F adj CondensedRing.moduleObjectDerivedPullback
  CondensedRing.moduleObjectDerivedPushforward

omit [∀ T : Scheme.{u},
  HasDerivedCategory.{u + 1} (ModuleRingedComparison.modules R T)] in
private theorem scalarMate_eq {X Y : Scheme.{u}} (f : X ⟶ Y) :
    scalarMate a f = rho a f (flatScalarTheta a f) := by
  have h := push_eq_mate_pull_inv
    (Mod.derivedExtendMapDerivedCategoryAdjunction (coefficientMap a X))
    (Mod.derivedExtendMapDerivedCategoryAdjunction (coefficientMap a Y))
    (CondensedRing.derivedUpperStarLowerStarAdjunction R f)
    (CondensedRing.derivedUpperStarLowerStarAdjunction S f)
    (CondensedRing.derivedComapLowerStarIso a f)
  dsimp only [scalarMate, rho, flatScalarTheta, adj, D, L, F, Iso.symm_hom,
    CondensedRing.derivedPushHom, CondensedRing.derivedPullIso, id,
    CondensedRing.moduleObjectDerivedPullback, CondensedRing.moduleObjectDerivedPushforward]
  exact h

end MateProof

section ProofHelpers

omit [∀ T : Scheme.{u},
  HasDerivedCategory.{u + 1} (ModuleRingedComparison.modules R T)]
  [∀ T : Scheme.{u}, PreservesFiniteLimits (Mod.extendScalars (coefficientMap a T))]

set_option allowUnsafeReducibility true
attribute [local instance 20000] sheafBraidedCategory
attribute [local reducible] sheafBraidedCategory sheafSymmetricCategory
  Mod.monoidalCategory Mod.monoidalCategoryStruct Monoidal.induced

attribute [local reducible] L F adj CondensedRing.moduleObjectDerivedPullback
  CondensedRing.moduleObjectDerivedPushforward ModuleRingedComparison.internalDerivedPullback
  ModuleRingedComparison.internalDerivedPushforward

attribute [local irreducible] Functor.leftDerivedTensorComparison
  CondensedRing.leftDerivedUpperStarUnitIso regularPullback regularPullback₀

omit [∀ T : Scheme.{u},
  HasDerivedCategory.{u + 1} (ModuleRingedComparison.modules R T)] in
private theorem pullMonoidal_eq {X Y : Scheme.{u}} (f : X ⟶ Y) :
    ModuleRingedComparison.internalPullMonoidal R f = CondensedRing.monoidal_upperStar R f := by
  apply Functor.Monoidal.toOplaxMonoidal_injective
  change ModuleRingedComparison.internalPullOplax R f = _
  exact ModuleRingedComparison.internalPullOplax_eq_canonical R f

attribute [local irreducible] Mod.monoidalCategory
attribute [local reducible] Mod.derivedMonoidalCategory
  DerivedCategory.monoidalCategoryOfMonoidalClosedBraidedCategory

private theorem tensorPull_eq {X Y : Scheme.{u}} (f : X ⟶ Y)
    (M N : DerivedCategory (Modules R Y)) :
    tensorPull (R := R) f M N = scalarTensorPull f M N := by
  have h := congrArg (fun t ↦ (t.app M).app N)
    (CondensedRing.leftDerivedUpperStarTensor_eq_leftDerivedTensorComparison R f)
  unfold tensorPull scalarTensorPull ModuleRingedComparison.internalDelta
  dsimp only [id]
  apply Eq.trans ?_ h.symm
  congr 3
  exact pullMonoidal_eq (R := R) f

attribute [local reducible] Mod.monoidalCategory

attribute [local irreducible] Functor.mapDerivedCategoryCompIso
  Functor.mapDerivedCategoryNatIso Functor.mapDerivedCategorySingleFunctor
  CondensedRing.leftDerivedUpperStarIsoMapDerivedCategory
  Functor.singleFunctorCompLeftDerivedFunctorIso
  Functor.leftDerivedFunctorIsoMapDerivedCategory
  CondensedRing.comapUpperStarIso

private theorem coefficientUnit_hom (T : Scheme.{u}) :
    (scalarCoefficientUnit a T).hom =
      ((V₀ a T).mapDerivedCategorySingleFunctor 0).hom.app
        (Mod.regular (condensedRingObj S T)) := by
  rw [Functor.mapDerivedCategorySingleFunctor_hom_app_eq]
  rfl

private theorem restriction_single {X Y : Scheme.{u}} (f : X ⟶ Y)
    (M : Modules S Y) :
    (CondensedRing.derivedComapUpperStarIso a f).hom.app
        ((DerivedCategory.singleFunctor _ 0).obj M) ≫
      (CondensedRing.upperStar R f).mapDerivedCategory.map
        (((V₀ a Y).mapDerivedCategorySingleFunctor 0).hom.app M) ≫
      ((CondensedRing.upperStar R f).mapDerivedCategorySingleFunctor 0).hom.app
        ((V₀ a Y).obj M) =
    (V a X).map
        (((CondensedRing.upperStar S f).mapDerivedCategorySingleFunctor 0).hom.app M) ≫
      ((V₀ a X).mapDerivedCategorySingleFunctor 0).hom.app
        ((CondensedRing.upperStar S f).obj M) ≫
      (DerivedCategory.singleFunctor _ 0).map
        ((CondensedRing.comapUpperStarIso a f).hom.app M) := by
  apply (cancel_epi ((Functor.mapDerivedCategoryCompIso
    (CondensedRing.upperStar S f) (V₀ a X)).hom.app
      ((DerivedCategory.singleFunctor _ 0).obj M))).mp
  dsimp only [CondensedRing.derivedComapUpperStarIso, Iso.trans_hom,
    Iso.symm_hom, NatTrans.comp_app]
  simp only [Category.assoc, Iso.hom_inv_id_app_assoc]
  rw [Functor.mapDerivedCategoryCompIso_hom_app_singleFunctor]
  rw [Functor.mapDerivedCategoryNatIso_hom_app_singleFunctor]
  rw [← reassoc_of% (Functor.mapDerivedCategoryCompIso_hom_app_singleFunctor
    (CondensedRing.upperStar S f) (V₀ a X) M)]

omit [∀ T : Scheme.{u},
  HasDerivedCategory.{u + 1} (ModuleRingedComparison.modules R T)]
  [∀ T : Scheme.{u}, PreservesFiniteLimits (Mod.extendScalars (coefficientMap a T))] in
set_option backward.isDefEq.respectTransparency false in
private theorem leftDerived_single_hom
    {C E : Type*} [Category C] [Category E] [Abelian C] [Abelian E]
    [HasDerivedCategory C] [HasDerivedCategory E]
    (G : C ⥤ E) [G.Additive] [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    (LG : DerivedCategory C ⥤ DerivedCategory E)
    (c : DerivedCategory.Qh ⋙ LG ⟶ G.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh)
    (e : LG ≅ G.mapDerivedCategory)
    (he : Functor.whiskerLeft DerivedCategory.Qh e.hom ≫
      G.mapDerivedCategoryFactorsh.hom = c)
    (A : C) (Z : E) (φ : G.obj A ⟶ Z) :
    c.app ((HomotopyCategory.quotient C (.up ℤ)).obj
        ((CochainComplex.singleFunctor C 0).obj A)) ≫
      DerivedCategory.Qh.map (G.mapHomotopyCategorySingleHom φ) =
    e.hom.app ((DerivedCategory.singleFunctor C 0).obj A) ≫
      (G.mapDerivedCategorySingleFunctor 0).hom.app A ≫
      (DerivedCategory.singleFunctor E 0).map φ := by
  rw [← he]
  dsimp only [NatTrans.comp_app, Functor.whiskerLeft_app]
  simp only [Category.assoc]
  apply congrArg (_ ≫ ·)
  rw [Functor.mapDerivedCategorySingleFunctor_hom_app_eq]
  erw [Functor.mapDerivedCategoryFactorsh_hom_app]
  simp only [Functor.mapHomotopyCategorySingleHom,
    Functor.mapHomotopyCategoryFactors_hom_app_eq_id]
  have h₁ : ∀ K, (DerivedCategory.quotientCompQhIso C).hom.app K = 𝟙 _ :=
    fun _ ↦ rfl
  have h₂ : ∀ K, (DerivedCategory.quotientCompQhIso E).inv.app K = 𝟙 _ :=
    fun _ ↦ rfl
  erw [h₁, h₂, CategoryTheory.Functor.map_id, Category.id_comp, Category.id_comp]
  have h₄ : ∀ K, (G.mapHomotopyCategoryFactors
      (.up ℤ)).inv.app K = 𝟙 _ := fun _ ↦ rfl
  erw [h₄, CategoryTheory.Functor.map_id, Category.comp_id, Category.id_comp]
  simp only [Category.assoc]
  congr 1
  change _ = DerivedCategory.Q.map _ ≫ DerivedCategory.Q.map _
  rw [← DerivedCategory.Q.map_comp]
  have h := DerivedCategory.quotientCompQhIso_hom_naturality
    ((G.mapCochainComplexSingleFunctor 0).hom.app
      A ≫
        (CochainComplex.singleFunctor _ 0).map
          φ)
  have h₃ : ∀ K, (DerivedCategory.quotientCompQhIso E).hom.app K = 𝟙 _ :=
    fun _ ↦ rfl
  erw [h₃, h₃, Category.id_comp, Category.comp_id] at h
  exact h


attribute [local instance 21000] CondensedRing.monoidal_upperStar
attribute [local reducible] Mod.derivedMonoidalCategory
  DerivedCategory.monoidalCategoryOfMonoidalClosedBraidedCategory
attribute [local semireducible] DerivedCategory.monoidalClosed Mod.monoidalClosed

private theorem pull_unit {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (CondensedRing.leftDerivedUpperStarIsoMapDerivedCategory S f).hom.app
        (𝟙_ (DerivedCategory (Modules S Y))) ≫
      ((CondensedRing.upperStar S f).mapDerivedCategorySingleFunctor 0).hom.app
        (Mod.regular (condensedRingObj S Y)) ≫
      (DerivedCategory.singleFunctor (Modules S X) 0).map
        (Functor.Monoidal.εIso (CondensedRing.upperStar S f)).inv =
    (CondensedRing.leftDerivedUpperStarUnitIso S f).hom := by
  rw [CondensedRing.leftDerivedUpperStarUnitIso_hom_eq]
  have h := leftDerived_single_hom (C := Modules S Y) (E := Modules S X)
    (CondensedRing.upperStar S f) (CondensedRing.upperStar S f).leftDerivedFunctor
    (CondensedRing.upperStar S f).leftDerivedFunctorCounit
    (CondensedRing.upperStar S f).leftDerivedFunctorIsoMapDerivedCategory
    (CondensedRing.upperStar S f).leftDerivedFunctorIsoMapDerivedCategory_hom_fac
    (Mod.regular (condensedRingObj S Y)) _
    (Functor.Monoidal.εIso (CondensedRing.upperStar S f)).inv
  unfold CondensedRing.leftDerivedUpperStarIsoMapDerivedCategory
  convert h.symm using 1 <;> rfl


private theorem regular₀_hom_eq {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (regularPullback₀ a f).hom =
      (CondensedRing.comapUpperStarIso a f).inv.app (Mod.regular (condensedRingObj S Y)) ≫
        (V₀ a X).map (Functor.Monoidal.εIso (CondensedRing.upperStar S f)).inv := by
  have he := congrArg (fun t ↦ t.η)
    (ModuleRingedComparison.internalPullOplax_eq_canonical S f)
  unfold regularPullback₀
  dsimp only [Iso.trans_hom, Iso.symm_hom, Iso.app_hom, Functor.mapIso_hom]
  all_goals congr 1
  all_goals exact congrArg ((V₀ a X).map) he
private theorem regular₀_comp {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (CondensedRing.comapUpperStarIso a f).hom.app (Mod.regular (condensedRingObj S Y)) ≫
        (regularPullback₀ a f).hom =
      (V₀ a X).map (Functor.Monoidal.εIso (CondensedRing.upperStar S f)).inv := by
  rw [regular₀_hom_eq a f, Iso.hom_inv_id_app_assoc]

-- The hom of the displayed composite isomorphism unfolds through degree zero.
set_option backward.defeqAttrib.useBackward true in
private theorem regularPullback_hom {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (regularPullback a f).hom =
      (CondensedRing.leftDerivedUpperStarIsoMapDerivedCategory R f).hom.app (B a Y) ≫
        ((CondensedRing.upperStar R f).mapDerivedCategorySingleFunctor 0).hom.app
          (B₀ a Y) ≫
        (DerivedCategory.singleFunctor _ 0).map (regularPullback₀ a f).hom := by
  unfold regularPullback
  dsimp only [id, Iso.trans_hom, Iso.app_hom, Functor.mapIso_hom]
  rw [Functor.map_comp]
  rw [Functor.mapDerivedCategorySingleFunctor_hom_app_eq
    (CondensedRing.upperStar R f) (B₀ a Y)]
  simp only [Category.assoc]
  rfl

-- Cancellation reduces the derived coefficient comparison to its ordinary one.
set_option backward.defeqAttrib.useBackward true in
set_option linter.unusedSectionVars false in
set_option linter.unusedSimpArgs false in
private theorem regularPullback_eq {X Y : Scheme.{u}} (f : X ⟶ Y) :
    regularPullback a f = scalarCoefficientPull a f := by
  apply Iso.ext
  apply (cancel_epi ((scalarRestrictionPull a f).hom.app (𝟙_ _) ≫
    (L R f).map (scalarCoefficientUnit a Y).hom)).mp
  dsimp only [scalarCoefficientPull, Iso.trans_hom, Functor.mapIso_hom,
    Iso.symm_hom, Iso.app_hom, id]
  simp only [Category.assoc, ← Functor.map_comp_assoc, Iso.hom_inv_id,
    CategoryTheory.Functor.map_id, Category.id_comp, Iso.hom_inv_id_app_assoc]
  rw [coefficientUnit_hom, coefficientUnit_hom]
  rw [regularPullback_hom a f]
  erw [NatTrans.naturality_assoc]
  dsimp only [scalarRestrictionPull, Iso.trans_hom, Iso.app_hom,
    Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom,
    Functor.whiskerRight_app, Functor.whiskerLeft_app, NatTrans.comp_app, Iso.symm_hom, id]
  simp only [Category.assoc, Iso.inv_hom_id_app_assoc]
  erw [reassoc_of% (restriction_single a f (Mod.regular (condensedRingObj S Y)))]
  conv_lhs =>
    enter [2, 2, 2]
    rw [← Functor.map_comp, regular₀_comp a f]
  have hn := ((V₀ a X).mapDerivedCategorySingleFunctor 0).hom.naturality
    (Functor.Monoidal.εIso (CondensedRing.upperStar S f)).inv
  dsimp only [Functor.comp_map] at hn
  conv_lhs =>
    enter [2, 2]
    exact hn.symm
  rw [← Functor.map_comp_assoc, ← Functor.map_comp_assoc]
  conv_lhs =>
    enter [1, 2]
    exact (Category.assoc _ _ _).trans (pull_unit (S := S) f)
  rfl

attribute [local irreducible] Mod.derivedMonoidalCategory Mod.monoidalCategory
  DerivedCategory.monoidalCategoryOfMonoidalClosedBraidedCategory

set_option maxHeartbeats 800000 in
-- Comparing the chosen derived tensor structures requires more elaboration heartbeats.
private theorem projection_eq {X Y : Scheme.{u}} (f : X ⟶ Y)
    (K : DerivedCategory (Modules R X)) (C : DerivedCategory (Modules R Y)) :
    projection (R := R) f K C = CondensedRing.moduleObjectProjectionMap R f K C := by
  change (adj R f).homEquiv _ _
    (tensorPull (R := R) f ((F R f).obj K) C ≫
      ((CondensedRing.derivedTensor R X).map ((adj R f).counit.app K)).app
        ((L R f).obj C)) = _
  rw [tensorPull_eq (R := R) f ((F R f).obj K) C]
  unfold scalarTensorPull
  rfl

private theorem projection_transpose {X Y : Scheme.{u}} (f : X ⟶ Y)
    (K : DerivedCategory (Modules R X)) (C : DerivedCategory (Modules R Y)) :
    ((adj R f).homEquiv _ _).symm (projection (R := R) f K C) =
      tensorPull (R := R) f ((F R f).obj K) C ≫
        ((CondensedRing.derivedTensor R X).map ((adj R f).counit.app K)).app
          ((L R f).obj C) := by
  change ((adj R f).homEquiv _ _).symm ((adj R f).homEquiv _ _ _) = _
  exact Equiv.symm_apply_apply _ _

private theorem projection_postcomp_transpose
    {C E : Type*} [Category C] [Category E]
    {L : C ⥤ E} {F : E ⥤ C} (d : L ⊣ F) (T : E ⥤ E ⥤ E)
    {A : C} {K B B' : E} (r : B ⟶ B')
    (π : A ⟶ F.obj ((T.obj K).obj B))
    (μ : L.obj A ⟶ (T.obj (L.obj (F.obj K))).obj B)
    (hπ : (d.homEquiv _ _).symm π = μ ≫ (T.map (d.counit.app K)).app B) :
    (d.homEquiv _ _).symm (π ≫ F.map ((T.obj K).map r)) =
      μ ≫ (T.obj (L.obj (F.obj K))).map r ≫ (T.map (d.counit.app K)).app B' := by
  rw [d.homEquiv_naturality_right_symm, hπ, Category.assoc]
  exact congrArg (μ ≫ ·) ((T.map (d.counit.app K)).naturality r).symm

end ProofHelpers


set_option allowUnsafeReducibility true
attribute [local semireducible] L F adj CondensedRing.moduleObjectDerivedPullback
  CondensedRing.moduleObjectDerivedPushforward ModuleRingedComparison.internalDerivedPullback
  ModuleRingedComparison.internalDerivedPushforward
attribute [local irreducible] Mod.derivedMonoidalCategory Mod.monoidalCategory
  DerivedCategory.monoidalCategoryOfMonoidalClosedBraidedCategory
  regularPullback regularPullback₀ scalarProjection scalarRestrictionPush
  scalarMate rho flatScalarTheta restrictionPushIso adj projection tensorPull

/-- Restricting the actual coefficient push mate gives exactly the counit projection
map with the restricted regular coefficient, naturally in every unbounded K.
The normalization hypotheses specify the canonical balanced e maps already named in
this statement; they impose no geometric or cohomological restriction.

Source: blueprint main-20261015, rational proper-base-change proof (1), canonical
scalar comparison; Stacks Tags 07A4, 07A6, 0D6E and 0B56
(blueprint: lem-sfb-restricted-coefficient-mate-projection).

Proof:
1. Apply the iterated-mate equivalence to the specified scalar and geometric
adjunctions. This identifies the actual derivedPushHom with rho of flatScalarTheta.
2. Flat coefficient square normalization supplies the actual restriction/direct-image
comparison and PullNormalized. Apply internal_scalar_mate_projection and cancel the
balanced tensor presentation to identify restrictedMap with scalarProjection.
3. Identify the internal and canonical ordinary pullback monoidal structures using
uniqueness of their oplax structures, then use the existing derived tensor comparison.
Compare the two regular-coefficient pullback isomorphisms by exact-localization
naturality and the composition, degree-zero and unit comparison identities.
4. Expanding scalarProjection with these identifications gives the second clause.
Naturality of the adjunction hom equivalence and of the tensor bifunctor gives its
stated transpose. Transport the naturality of scalarProjection through restrictedMap's
identification to obtain the final clause. No invertibility of restrictedMap is used. -/
theorem restricted_coefficient_mate_projection
    (ℓ p : ℕ) [Fact ℓ.Prime] (k : Type u) [Field k] [CharP k p]
    (_hp : 0 < p) (_hne : p ≠ ℓ)
    {X Y : Over (Scheme.Spec.obj (Opposite.op (CommRingCat.of k)))}
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
    [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
    (f : X ⟶ Y) (eX : TensorNormalization a X.left) (eY : TensorNormalization a Y.left)
    (_heX : TensorNormalized a X.left eX) (_heY : TensorNormalized a Y.left eY) :
    (∀ K : DerivedCategory (Modules R X.left),
      ((adj R f.left).homEquiv _ _).symm
          (restrictedMap a f.left eX eY K) =
        tensorPull (R := R) f.left ((F R f.left).obj K) (B a Y.left) ≫
        ((CondensedRing.derivedTensor R X.left).obj
          ((L R f.left).obj
            ((F R f.left).obj K))).map
              (regularPullback a f.left).hom ≫
        ((CondensedRing.derivedTensor R X.left).map
          ((adj R f.left).counit.app K)).app
            (B a X.left)) ∧
    (∀ K : DerivedCategory (Modules R X.left),
      restrictedMap a f.left eX eY K =
        projection (R := R) f.left K (B a Y.left) ≫
          (F R f.left).map
            (((CondensedRing.derivedTensor R X.left).obj K).map
              (regularPullback a f.left).hom)) ∧
    (∀ (K K' : DerivedCategory (Modules R X.left)) (q : K ⟶ K'),
      ((CondensedRing.derivedTensor R Y.left).map
        ((F R f.left).map q)).app (B a Y.left) ≫
          restrictedMap a f.left eX eY K' =
        restrictedMap a f.left eX eY K ≫
          (F R f.left).map (((CondensedRing.derivedTensor R X.left).map q).app (B a X.left))) := by
  let : ∀ T : Scheme.{u},
      HasDerivedCategory.{u + 1} (ModuleRingedComparison.modules S T) := fun T ↦ by
    have := IsGrothendieckAbelian.of_equivalence (ModuleRingedComparison.equivalence S T)
    exact HasDerivedCategory.ofIsGrothendieckAbelian _
  have hn := flat_coefficient_square_normalization a ℓ p k _hp _hne f eX eY _heX _heY
  have hm := internal_scalar_mate_projection a f.left eX eY (flatScalarTheta a f.left)
    _heX _heY hn.2.2.2.2.2.2.2.1
  have hd : (restrictionPushIso a f.left).hom = scalarRestrictionPush a f.left :=
    by simpa only [restrictionPushIso, flatScalarDirectImage] using hn.2.2.2.2.2.2.1
  have he (K : DerivedCategory (Modules R X.left)) :
      restrictedMap a f.left eX eY K = scalarProjection a f.left K := by
    have hmate := congrArg (V a Y.left).map
      (NatTrans.congr_app (scalarMate_eq a f.left) K)
    have hdir := NatTrans.congr_app hd ((D a X.left).obj K)
    have hc := congrArg₂
      (fun m d ↦ eY.derived.inv.app ((F R f.left).obj K) ≫ m ≫ d ≫
        (F R f.left).map (eX.derived.hom.app K)) hmate hdir
    refine hc.trans ?_
    have hK := congrArg (eY.derived.inv.app ((F R f.left).obj K) ≫ ·) (hm.2.2.1 K)
    simpa only [Category.assoc, Iso.inv_hom_id_app_assoc] using hK
  have hpj (K : DerivedCategory (Modules R X.left)) :
      scalarProjection a f.left K =
        projection (R := R) f.left K (B a Y.left) ≫
          (F R f.left).map
            (((CondensedRing.derivedTensor R X.left).obj K).map
              (regularPullback a f.left).hom) := by
    unfold scalarProjection
    apply congrArg₂ (· ≫ ·)
    · exact (projection_eq f.left K (B a Y.left)).symm
    · have hreg := congrArg
        (fun e : (L R f.left).obj (B a Y.left) ≅ B a X.left ↦ e.hom)
        (regularPullback_eq a f.left).symm
      exact congrArg (F R f.left).map
        (congrArg ((CondensedRing.derivedTensor R X.left).obj K).map hreg)
  refine ⟨?_, ?_, ?_⟩
  · intro K
    apply Eq.trans (congrArg ((adj R f.left).homEquiv _ _).symm
      ((he K).trans (hpj K)))
    exact projection_postcomp_transpose (adj R f.left)
      (CondensedRing.derivedTensor R X.left) (regularPullback a f.left).hom
      (projection (R := R) f.left K (B a Y.left))
      (tensorPull (R := R) f.left ((F R f.left).obj K) (B a Y.left))
      (projection_transpose (R := R) f.left K (B a Y.left))
  · intro K
    exact (he K).trans (hpj K)
  · intro K K' q
    exact (congrArg
      (((CondensedRing.derivedTensor R Y.left).map ((F R f.left).map q)).app
        (B a Y.left) ≫ ·) (he K')).trans
      ((hm.2.2.2.2.2 K K' q).trans
        (congrArg (· ≫ (F R f.left).map
          (((CondensedRing.derivedTensor R X.left).map q).app (B a X.left))) (he K).symm))

end AlgebraicGeometry.ProEtale.RestrictedCoefficientMate
