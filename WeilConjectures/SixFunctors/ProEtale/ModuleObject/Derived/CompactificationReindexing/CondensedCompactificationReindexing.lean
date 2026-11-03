/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedPullbackCoherence
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.ModuleObjectProjectionMap
public import WeilConjectures.CategoryTheory.SuppliedExchangeProjection.ExchangeProjectionSuppliedDomains
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CondensedOpenBaseChangeArbitrary
public import WeilConjectures.Compactification.BaseChange
public import WeilConjectures.Compactification.RefinementCategory
public import WeilConjectures.PoincareDuality.ProjectionFormula
public import WeilConjectures.ConstructibleSheaf.ProEtaleModule.DerivedCategory
public import WeilConjectures.CategoryTheory.Right.RightDerivedFunctorOfQuasiIsoResolutions
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.ContinuousMapCondensedRingSupplement
public import WeilConjectures.AlgebraicGeometry.Finite.FiniteDiscreteCoefficientTriangulated
public import Mathlib.CategoryTheory.Monoidal.CommMon_
public import WeilConjectures.CategoryTheory.CommutativeSiteDerivedConstantModuleFunctor
public import WeilConjectures.CategoryTheory.Constant.ConstantModuleFiniteTypeReflection
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import WeilConjectures.CategoryTheory.ModuleObjects.ConstantRingSheaf
public import Mathlib.Algebra.TrivSqZeroExt.Basic
public import Mathlib.LinearAlgebra.Finsupp.VectorSpace
public import Mathlib.RingTheory.Finiteness.Cardinality
public import Mathlib.Data.ZMod.Basic
public import Mathlib.FieldTheory.IsSepClosed
public import WeilConjectures.ConstructibleSheaf.ProEtaleModule.Def
public import WeilConjectures.CategoryTheory.RingObjects.RingPresheaf
public import WeilConjectures.CategoryTheory.RingObjects.Ab
public import WeilConjectures.CategoryTheory.SheafTensor
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.RingTheory.Finiteness.Defs
public import WeilConjectures.CategoryTheory.SiteConstantModuleFunctorGeneral
public import Mathlib.CategoryTheory.Sites.Limits
public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.GlobalSections
public import WeilConjectures.CategoryTheory.ModuleObjects.Free
public import WeilConjectures.CategoryTheory.ModuleObjects.MapMod
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Mod
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Free
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import Mathlib.CategoryTheory.Monoidal.Mod
public import WeilConjectures.CategoryTheory.InternalAbelianSheafModuleEquivalence
public import WeilConjectures.CategoryTheory.Site.SiteConstantModuleHomSupplement
public import WeilConjectures.CategoryTheory.ProEtaleCoefficients.SectionActionInternal
public import WeilConjectures.CategoryTheory.ModuleObjects.ConstantRingPresheaf
public import Mathlib.CategoryTheory.Sites.Sheafification
public import Mathlib.CategoryTheory.Sites.PreservesSheafification
public import WeilConjectures.AlgebraicGeometry.ProEtaleObjectPullbackRestriction
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Generators
public import WeilConjectures.ConstructibleSheaf.ProEtaleModule.IsoClosed
public import Mathlib.Algebra.Field.ULift
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LowerShriek
public import Mathlib.CategoryTheory.Adjunction.Mates

import WeilConjectures.AlgebraicGeometry.Open.OpenSectionClopen
import WeilConjectures.AlgebraicGeometry.ModuleObjectRingedComparison.InternalSectionTensorLocalization
import all WeilConjectures.SmoothPurity.CompactSupportCondensedRealization.CondensedOpenRestrictedCounit
import WeilConjectures.CategoryTheory.Adjunction.ExchangeRightPaste
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OpenClosedConservative
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.BaseChange
public import WeilConjectures.CategoryTheory.Adjunction.MateCube
public import WeilConjectures.ProEtaleCoefficients.BoundedConstructibleCounterexample.NonFiniteMultiplicationKernel
public import WeilConjectures.SixFunctors.CompactificationCommonRefinement
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.WeaklyEtale
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CompactificationReindexing.CondensedCompactificationExchange

/-!
# Native condensed compactification reindexing

Source: literature/blueprint/latest/blueprint/sec-six-functors/sk-rem-sf-pf-done/
lem-fix-weil-operations.proof.md, paragraphs 1--3.
(blueprint: lem-fix-condensed-compactification-reindexing).

All operations below are aliases or composites of the native ordinary unbounded
internal-module operations. The clopen adjunction is uniquely normalized by the
inverse open unit; its unit is the projection onto the distinguished component.
-/

@[expose] public noncomputable section
set_option autoImplicit false
-- Keep native proof elaboration sequential to control peak memory.
set_option Elab.async false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped CategoryTheory.Obj CategoryTheory.Functor
open AlgebraicGeometry AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.ProEtale.CondensedRing.CompactificationReindexing

attribute [local irreducible] Functor.leftDerivedFunctor Functor.rightDerivedFunctor
  Functor.mapDerivedCategory derivedUpperStarLowerStarAdjunction
  leftDerivedUpperStarTensor leftDerivedUpperStarComp pullbackSquareComparison

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]

/-- Native ambient category, with coefficients pulled back from the point.
Source: the source proof, paragraph 1
(blueprint: lem-fix-condensed-compactification-reindexing). -/
abbrev D (T : Scheme.{u}) :=
  DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1})
    (condensedRingObj Λ T))

/-- Native ordinary derived pullback, without completion.
Source: the source proof, paragraph 1
(blueprint: lem-fix-condensed-compactification-reindexing). -/
abbrev P {A B : Scheme.{u}} (a : A ⟶ B) : D Λ B ⥤ D Λ A :=
  (upperStar Λ a).leftDerivedFunctor

/-- Native ordinary derived direct image.
Source: the source proof, paragraph 1
(blueprint: lem-fix-condensed-compactification-reindexing). -/
abbrev R {A B : Scheme.{u}} (a : A ⟶ B) : D Λ A ⥤ D Λ B :=
  (lowerStar Λ a).rightDerivedFunctor

/-- Native exact open extension on the derived category.
Source: the source proof, paragraph 1
(blueprint: lem-fix-condensed-compactification-reindexing). -/
abbrev J {A B : Scheme.{u}} (j : A ⟶ B) [IsOpenImmersion j] : D Λ A ⥤ D Λ B :=
  (openImmersionLowerShriek Λ j).mapDerivedCategory

/-- The supplied compactification model, not the derived underived composite.
Source: the source proof, paragraph 1
(blueprint: lem-fix-condensed-compactification-reindexing). -/
abbrev F {A B : Scheme.{u}} {f : A ⟶ B} (c : Compactification f) : D Λ A ⥤ D Λ B :=
  rightDerivedLowerShriekOfCompactification Λ c

/-- The native open adjunction, with total derived pullback as right adjoint.
Source: the source proof, paragraph 1
(blueprint: lem-fix-condensed-compactification-reindexing). -/
abbrev oa {A B : Scheme.{u}} (j : A ⟶ B) [IsOpenImmersion j] : J Λ j ⊣ P Λ j :=
  derivedOpenImmersionLowerShriekLeftDerivedUpperStarAdjunction Λ j

/-- Invertibility of the native open unit.
Source: the source proof, paragraph 1
(blueprint: lem-fix-condensed-compactification-reindexing).
Proof: exact extension by zero is fully faithful, with restriction its right adjoint.
Its unit is the identity on sections on the open. Localization and the native
exact-to-total-derived identification preserve this unit and its inverse. -/
theorem openUnit_isIso {A B : Scheme.{u}} (j : A ⟶ B) [IsOpenImmersion j] :
    IsIso (oa Λ j).unit := by
  have : IsIso (openImmersionLowerShriekUpperStarAdjunction Λ j).unit := inferInstance
  have : IsIso (derivedOpenImmersionLowerShriekUpperStarAdjunction Λ j).unit :=
    Adjunction.isIso_mapDerivedCategoryAdjunction_unit _
  have hff := (derivedOpenImmersionLowerShriekUpperStarAdjunction Λ j).fullyFaithfulLOfIsIsoUnit
  have := hff.full
  have := hff.faithful
  exact (oa Λ j).unit_isIso_of_L_fully_faithful

/-- The inverse direction of the open exchange, with its native mate normalization.
Source: the source proof, paragraph 1
(blueprint: lem-fix-condensed-compactification-reindexing). -/
@[irreducible] def openMate {A B A' B' : Scheme.{u}}
    {j : A ⟶ B} {j' : A' ⟶ B'} {w : A' ⟶ A} {v : B' ⟶ B}
    [IsOpenImmersion j] [IsOpenImmersion j'] (sq : CommSq w j' j v) :
    P Λ w ⋙ J Λ j' ⟶ J Λ j ⋙ P Λ v :=
  ((mateEquiv (oa Λ j) (oa Λ j')).symm
    (TwoSquare.mk _ _ _ _ (pullbackSquareComparison Λ sq).inv)).natTrans

/-- Arbitrary-open base change for the normalized native inverse mate.
Source: the source proof, paragraph 1; native weakly etale base change
(blueprint: lem-fix-condensed-compactification-reindexing).
Proof: transpose the Cartesian square. Its open edges are weakly etale, so the
native derived direct-image exchange is invertible on every unbounded input.
The iterated-mate identity identifies this exchange with the conjugate of the
specified inverse open mate under the two composite adjunctions. Conjugation
reflects invertibility, proving the assertion for exactly the specified mate. -/
theorem openMate_isIso {A B A' B' : Scheme.{u}}
    {j : A ⟶ B} {j' : A' ⟶ B'} {w : A' ⟶ A} {v : B' ⟶ B}
    [IsOpenImmersion j] [IsOpenImmersion j'] (sq : IsPullback w j' j v) :
    IsIso (openMate Λ sq.toCommSq) := by
  unfold openMate
  apply isIso_inverse_mate_aux (oa Λ j) (oa Λ j')
    (derivedUpperStarLowerStarAdjunction Λ w) (derivedUpperStarLowerStarAdjunction Λ v)
    (pullbackSquareComparison Λ sq.toCommSq).symm
  have hρ : IsIso (baseChangeMap Λ sq.toCommSq.flip) :=
    isIso_baseChangeMap_of_weaklyEtale Λ sq.flip
  rw [baseChangeMap, Adjunction.exchangeRight_eq_mateEquiv,
    pullbackSquareComparison_flip] at hρ
  exact hρ

/-- The open comparison is exactly the inverse of the normalized open mate.
Source: the source proof, paragraph 1
(blueprint: lem-fix-condensed-compactification-reindexing). -/
@[irreducible] def beta {A B A' B' : Scheme.{u}}
    {j : A ⟶ B} {j' : A' ⟶ B'} {w : A' ⟶ A} {v : B' ⟶ B}
    [IsOpenImmersion j] [IsOpenImmersion j'] (sq : IsPullback w j' j v) :
    J Λ j ⋙ P Λ v ≅ P Λ w ⋙ J Λ j' :=
  @Iso.symm _ _ _ _ (@asIso _ _ _ _ (openMate Λ sq.toCommSq) (openMate_isIso Λ sq))

/-- A compactification square retains its actual open Cartesian square and its
proper-factor square; no invertibility of the latter exchange is part of the data.
Source: the source proof, paragraphs 1 and 3
(blueprint: lem-fix-condensed-compactification-reindexing). -/
structure Square {X Y X' Y' : Scheme.{u}} {f : X ⟶ Y} {f' : X' ⟶ Y'}
    (c : Compactification f) (c' : Compactification f') (w : X' ⟶ X) (v : Y' ⟶ Y) where
  middle : c'.Z ⟶ c.Z
  openSquare : IsPullback w c'.i c.i middle
  properSquare : CommSq middle c'.g c.g v

/-- The specified proper/open exchange on a supplied diagram, including noninvertible faces.
Source: the source proof, paragraphs 1 and 3
(blueprint: lem-fix-condensed-compactification-reindexing). -/
@[irreducible] def squareExchange {X Y X' Y' : Scheme.{u}} {f : X ⟶ Y} {f' : X' ⟶ Y'}
    {c : Compactification f} {c' : Compactification f'} {w : X' ⟶ X} {v : Y' ⟶ Y}
    (sq : Square c c' w v) : F Λ c ⋙ P Λ v ⟶ P Λ w ⋙ F Λ c' :=
  CategoryTheory.SuppliedExchangeProjection.compactificationExchangeFromData
    (J Λ c.i) (J Λ c'.i) (P Λ c.g) (R Λ c.g)
    (derivedUpperStarLowerStarAdjunction Λ c.g)
    (P Λ c'.g) (R Λ c'.g) (derivedUpperStarLowerStarAdjunction Λ c'.g)
    (P Λ v) (P Λ w) (P Λ sq.middle)
    (pullbackSquareComparison Λ sq.properSquare) (beta Λ sq.openSquare)

/-- Proper exchange followed by proper image of the open comparison.
Source: the source proof, paragraph 1
(blueprint: lem-fix-condensed-compactification-reindexing). -/
@[irreducible] def exchange {X Y Y' : Scheme.{u}} {f : X ⟶ Y}
    (c : Compactification f) (v : Y' ⟶ Y) :
    F Λ c ⋙ P Λ v ⟶ P Λ (pullback.fst f v) ⋙ F Λ (c.baseChange v) :=
  squareExchange Λ
    { middle := pullback.fst c.g v
      openSquare := c.isPullback_i_ofIsPullback (IsPullback.of_hasPullback f v)
      properSquare := (IsPullback.of_hasPullback c.g v).toCommSq }

/-- Common-refinement comparison on an object property, with ambient input hypotheses.
Source: the source proof, paragraphs 1 and 3
(blueprint: lem-fix-condensed-compactification-reindexing).
Proof: apply the generic input-functor comparison to the full-subcategory inclusion.
Its object map sends an input to its underlying object. Evaluate the comparison
normalization and uniqueness on that object. These transports are checked before
specializing the ambient functors. -/
private theorem comparison_on_property
    {X Y : Scheme.{u}} (f : X ⟶ Y) [QuasiCompact f]
    {C D : Type*} [Category C] [Category D]
    (P : ObjectProperty C) (F : Compactification f → C ⥤ D)
    (ρ : ∀ {a b : Compactification f}, (a ⟶ b) → (F b ⟶ F a))
    (hcomp : ∀ {a b c : Compactification f} (r : a ⟶ b) (s : b ⟶ c),
      ρ (r ≫ s) = ρ s ≫ ρ r)
    (hiso : ∀ {a b : Compactification f} (r : a ⟶ b) (K : C),
      P K → IsIso ((ρ r).app K)) :
    ∃ τ : ∀ a b, P.ι ⋙ F a ≅ P.ι ⋙ F b,
      (∀ a b d (r : d ⟶ a) (s : d ⟶ b) (K : P.FullSubcategory),
        (τ a b).hom.app K ≫ (ρ s).app K.obj = (ρ r).app K.obj) ∧
      (∀ a, τ a a = Iso.refl _) ∧
      (∀ a b c, τ a b ≪≫ τ b c = τ a c) ∧
      (∀ σ : ∀ a b, P.ι ⋙ F a ≅ P.ι ⋙ F b,
        (∀ a b d (r : d ⟶ a) (s : d ⟶ b) (K : P.FullSubcategory),
          (σ a b).hom.app K ≫ (ρ s).app K.obj = (ρ r).app K.obj) → σ = τ) := by
  obtain ⟨τ, hτ, hid, htrans, huniq⟩ :=
    compactification_common_refinement_on_inputs f P.ι F ρ hcomp
      (fun r K ↦ hiso r K.obj K.property)
  refine ⟨τ, ?_, hid, htrans, ?_⟩
  · intro a b d r s K
    exact hτ a b d r s K
  · intro σ hσ
    apply huniq σ
    intro a b d r s K
    exact hσ a b d r s K

private def modelIso {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f) :
    F Λ c ≅ J Λ c.i ⋙ R Λ c.g := Iso.refl _

private def compositeExchange
    {A B C A' B' C' : Type*} [Category A] [Category B] [Category C]
    [Category A'] [Category B'] [Category C']
    (J : A ⥤ B) (R : B ⥤ C) (J' : A' ⥤ B') (R' : B' ⥤ C')
    (G : C ⥤ C') (H : A ⥤ A') (M : B ⥤ B')
    (r : R ⋙ G ⟶ M ⋙ R') (β : J ⋙ M ≅ H ⋙ J') :
    (J ⋙ R) ⋙ G ⟶ H ⋙ (J' ⋙ R') :=
  (Functor.associator J R G).hom ≫ Functor.whiskerLeft J r ≫
    (Functor.associator J M R').inv ≫ Functor.whiskerRight β.hom R' ≫
    (Functor.associator H J' R').hom

private theorem compositeExchange_app
    {A B C A' B' C' : Type*} [Category A] [Category B] [Category C]
    [Category A'] [Category B'] [Category C']
    (J : A ⥤ B) (R : B ⥤ C) (J' : A' ⥤ B') (R' : B' ⥤ C')
    (G : C ⥤ C') (H : A ⥤ A') (M : B ⥤ B')
    (r : R ⋙ G ⟶ M ⋙ R') (β : J ⋙ M ≅ H ⋙ J') (K : A) :
    (compositeExchange J R J' R' G H M r β).app K =
      r.app (J.obj K) ≫ R'.map (β.hom.app K) := by
  simp only [compositeExchange, NatTrans.comp_app, Functor.whiskerLeft_app,
    Functor.whiskerRight_app, Functor.associator_hom_app, Functor.associator_inv_app,
    Category.id_comp, Category.comp_id]

private theorem square_exchange_model_comp {X Y X' Y' : Scheme.{u}}
    {f : X ⟶ Y} {f' : X' ⟶ Y'} {c : Compactification f} {c' : Compactification f'}
    {w : X' ⟶ X} {v : Y' ⟶ Y} (sq : Square c c' w v) :
    squareExchange Λ sq = Functor.whiskerRight (modelIso Λ c).hom (P Λ v) ≫
      compositeExchange (J Λ c.i) (R Λ c.g) (J Λ c'.i) (R Λ c'.g)
        (P Λ v) (P Λ w) (P Λ sq.middle) (baseChangeMap Λ sq.properSquare)
        (beta Λ sq.openSquare) ≫ Functor.whiskerLeft (P Λ w) (modelIso Λ c').inv := by
  unfold squareExchange modelIso compositeExchange baseChangeMap
  rw [Adjunction.exchangeRight_eq_mateEquiv]
  simp only [SuppliedExchangeProjection.compactificationExchangeFromData,
    Iso.refl_hom, Iso.refl_inv, Functor.whiskerRight_id', Functor.whiskerLeft_id',
    Category.id_comp, Category.comp_id]

private theorem square_exchange_model {X Y X' Y' : Scheme.{u}}
    {f : X ⟶ Y} {f' : X' ⟶ Y'} {c : Compactification f} {c' : Compactification f'}
    {w : X' ⟶ X} {v : Y' ⟶ Y} (sq : Square c c' w v) :
    squareExchange Λ sq =
      Functor.whiskerRight (modelIso Λ c).hom (P Λ v) ≫
        SuppliedExchangeProjection.compactificationExchangeFromData
          (J Λ c.i) (J Λ c'.i) (P Λ c.g) (R Λ c.g)
          (derivedUpperStarLowerStarAdjunction Λ c.g)
          (P Λ c'.g) (R Λ c'.g) (derivedUpperStarLowerStarAdjunction Λ c'.g)
          (P Λ v) (P Λ w) (P Λ sq.middle)
          (pullbackSquareComparison Λ sq.properSquare) (beta Λ sq.openSquare) ≫
        Functor.whiskerLeft (P Λ w) (modelIso Λ c').inv := by
  unfold squareExchange modelIso
  simp only [Iso.refl_hom, Iso.refl_inv, Functor.whiskerRight_id', Functor.whiskerLeft_id',
    Category.id_comp, Category.comp_id]

private theorem compactification_exchange_app_aux
    {DX DB DY DX' DB' DY' : Type*}
    [Category DX] [Category DB] [Category DY]
    [Category DX'] [Category DB'] [Category DY']
    (J : DX ⥤ DB) (J' : DX' ⥤ DB')
    (P : DY ⥤ DB) (R : DB ⥤ DY) (adj : P ⊣ R)
    (P' : DY' ⥤ DB') (R' : DB' ⥤ DY') (adj' : P' ⊣ R')
    (G : DY ⥤ DY') (H : DX ⥤ DX') (B : DB ⥤ DB')
    (theta : G ⋙ P' ≅ P ⋙ B) (beta : J ⋙ B ≅ H ⋙ J') (K : DX) :
    (SuppliedExchangeProjection.compactificationExchangeFromData J J' P R adj
      P' R' adj' G H B theta beta).app K =
      (adj.exchangeRight adj' theta).app (J.obj K) ≫ R'.map (beta.hom.app K) := by
  rw [Adjunction.exchangeRight_eq_mateEquiv]
  simp (config := { dsimp := false }) only
    [SuppliedExchangeProjection.compactificationExchangeFromData,
    NatTrans.comp_app, Functor.associator_hom_app, Functor.associator_inv_app,
    Functor.whiskerLeft_app, Functor.whiskerRight_app, Category.id_comp, Category.comp_id]

private theorem compact_identity_of_model
    {DX DB DY : Type*} [Category DX] [Category DB] [Category DY]
    (F : DX ⥤ DY) (J : DX ⥤ DB) (P : DY ⥤ DB) (R : DB ⥤ DY) (adj : P ⊣ R)
    (G : DY ⥤ DY) (H : DX ⥤ DX) (B : DB ⥤ DB)
    (θ : G ⋙ P ≅ P ⋙ B) (β : J ⋙ B ≅ H ⋙ J) (χ : F ≅ J ⋙ R)
    (σ : F ⋙ G ⟶ H ⋙ F)
    (hσ : σ = Functor.whiskerRight χ.hom G ≫
      SuppliedExchangeProjection.compactificationExchangeFromData J J P R adj P R adj
        G H B θ β ≫ Functor.whiskerLeft H χ.inv)
    (IX : H ≅ 𝟭 DX) (IB : B ≅ 𝟭 DB) (IY : G ≅ 𝟭 DY)
    (hb : ∀ K, β.inv.app K ≫ IB.hom.app (J.obj K) = J.map (IX.hom.app K))
    (hp : ∀ N, (adj.exchangeRight adj θ).app N ≫ R.map (IB.hom.app N) =
      IY.hom.app (R.obj N)) (K : DX) :
    σ.app K ≫ F.map (IX.hom.app K) = IY.hom.app (F.obj K) := by
  have hb' : β.hom.app K ≫ J.map (IX.hom.app K) = IB.hom.app (J.obj K) := by
    rw [← hb K]
    simp only [Iso.hom_inv_id_app_assoc]
  have hc := χ.hom.naturality (IX.hom.app K)
  dsimp only [Functor.comp_map, Functor.id_obj] at hc
  have he := IY.hom.naturality (χ.hom.app K)
  dsimp only [Functor.id_map, Functor.comp_obj] at he
  rw [hσ]
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    compactification_exchange_app_aux]
  apply (cancel_mono (χ.hom.app K)).1
  simp only [Category.assoc]
  rw [hc, Iso.inv_hom_id_app_assoc, ← R.map_comp, hb', hp]
  exact he

/-- The two monoidal input comparisons used in the compact-support projection square.
Source: the source proof, paragraph 3
(blueprint: lem-fix-condensed-compactification-reindexing). -/
def tensorInput {X Y Y' : Scheme.{u}} {f : X ⟶ Y} (v : Y' ⟶ Y)
    (K : D Λ X) (L : D Λ Y) :
    (P Λ (pullback.fst f v)).obj (K ⊗ (P Λ f).obj L) ⟶
      (P Λ (pullback.fst f v)).obj K ⊗
        (P Λ (pullback.snd f v)).obj ((P Λ v).obj L) :=
  ((leftDerivedUpperStarTensor Λ (pullback.fst f v)).app K).app ((P Λ f).obj L) ≫
    (𝟙 _ ⊗ₘ (pullbackSquareComparison Λ
      (IsPullback.of_hasPullback f v).toCommSq).inv.app L)

private theorem directExchange_isIso {X Y X' Y' : Scheme.{u}}
    {f : X ⟶ Y} {f' : X' ⟶ Y'} {w : X' ⟶ X} {v : Y' ⟶ Y}
    [IsIso w] [IsIso v] (sq : CommSq w f' f v) :
    IsIso (baseChangeMap Λ sq) := by
  have : (P Λ w).IsEquivalence := inferInstance
  have : (P Λ v).IsEquivalence := inferInstance
  exact Adjunction.isIso_exchangeRight_of_isEquivalence
    (derivedUpperStarLowerStarAdjunction Λ f)
    (derivedUpperStarLowerStarAdjunction Λ f') (pullbackSquareComparison Λ sq)

/-- Isomorphism squares have invertible native exchanges on all ambient inputs.
Together with the identity and pasting equations this identifies the exchange of
the inverse diagram with the inverse exchange, not merely some inverse map.
Source: the source proof, paragraph 1
(blueprint: lem-fix-condensed-compactification-reindexing).
Proof: paste the diagram with its scheme-theoretic inverse in both orders. The
identity and pasting equations show that its specified inverse exchange is both a
left and a right inverse, after the native identity/composition identifications. -/
theorem square_isIso {X Y X' Y' : Scheme.{u}}
    {f : X ⟶ Y} {f' : X' ⟶ Y'} {c : Compactification f} {c' : Compactification f'}
    {w : X' ⟶ X} {v : Y' ⟶ Y} [IsIso w] [IsIso v]
    (s : Square c c' w v) [IsIso s.middle]
    (sq : CommSq w f' f v) :
    IsIso (baseChangeMap Λ sq) ∧ IsIso (squareExchange Λ s) := by
  refine ⟨directExchange_isIso Λ sq, ?_⟩
  have : (P Λ v).IsEquivalence := inferInstance
  have : (P Λ s.middle).IsEquivalence := inferInstance
  have := isIso_mateEquiv_of_isEquivalence
    (derivedUpperStarLowerStarAdjunction Λ c.g)
    (derivedUpperStarLowerStarAdjunction Λ c'.g)
    (TwoSquare.mk (P Λ v) (P Λ c.g) (P Λ c'.g) (P Λ s.middle)
      (pullbackSquareComparison Λ s.properSquare).hom)
  unfold squareExchange
    CategoryTheory.SuppliedExchangeProjection.compactificationExchangeFromData
  infer_instance

set_option maxHeartbeats 1600000 in
-- Native derived functor endpoint comparisons exceed the default heartbeat allowance.
/-- The section of the pullback of the target open along a proper refinement.
Source: the source proof, paragraph 1, clopen refinement construction
(blueprint: lem-fix-condensed-compactification-reindexing). -/
def refinementSection {X Y : Scheme.{u}} {f : X ⟶ Y} {c₁ c₂ : Compactification f}
    (u : c₁.Refinement c₂) : X ⟶ pullback c₂.i u.hom :=
  pullback.lift (𝟙 X) c₁.i (by simpa using u.i_hom.symm)

/-- The distinguished section is open and closed, even with an extra component.
Source: the source proof, paragraph 1
(blueprint: lem-fix-condensed-compactification-reindexing).
Proof: its composite with the open pullback immersion is the source open immersion,
so it is open. It is a section of a separated proper map, hence closed. This includes
the empty open and imposes neither density nor a Cartesian refinement square. -/
theorem section_clopen {X Y : Scheme.{u}} {f : X ⟶ Y}
    {c₁ c₂ : Compactification f} (u : c₁.Refinement c₂) :
    IsOpenImmersion (refinementSection u) ∧ IsClosed (Set.range (refinementSection u)) := by
  let p := pullback.fst c₂.i u.hom
  have hs : refinementSection u ≫ p = 𝟙 X := by
    dsimp [refinementSection, p]
    simp
  have hopen : IsOpenImmersion (refinementSection u) := by
    have hcomp : IsOpenImmersion
        (refinementSection u ≫ pullback.snd c₂.i u.hom) := by
      rw [show refinementSection u ≫ pullback.snd c₂.i u.hom = c₁.i by
        dsimp [refinementSection]
        simp]
      infer_instance
    exact IsOpenImmersion.of_comp (refinementSection u) (pullback.snd c₂.i u.hom)
  exact ⟨hopen, (open_section_clopen p (refinementSection u) hs).1.isClosed⟩

private theorem normalizedReverseAdjunction {C D : Type*} [Category C] [Category D]
    {J : C ⥤ D} {P : D ⥤ C} (a : J ⊣ P) [IsIso a.unit] (b : P ⊣ J) :
    ∃! c : P ⊣ J, c.counit = inv a.unit := by
  have ff := a.fullyFaithfulLOfIsIsoUnit
  have := ff.full
  have := ff.faithful
  have : IsIso b.counit := b.counit_isIso_of_R_fully_faithful
  let t : 𝟭 C ≅ 𝟭 C := asIso a.unit ≪≫ asIso b.counit
  let e : J ≅ J := (Functor.leftUnitor J).symm ≪≫
    Functor.isoWhiskerRight t J ≪≫ Functor.leftUnitor J
  let c := b.ofNatIsoRight e
  have hc : c.counit = inv a.unit := by
    ext N
    change P.map (e.inv.app N) ≫ b.counit.app N = (inv a.unit).app N
    simp only [e, Iso.trans_inv, Iso.symm_inv, NatTrans.comp_app,
      Functor.isoWhiskerRight_inv, Functor.whiskerRight_app,
      Functor.leftUnitor_hom_app, Functor.leftUnitor_inv_app,
      Functor.comp_obj, Functor.id_obj, Category.id_comp, Category.comp_id]
    have hn := b.counit.naturality (t.inv.app N)
    dsimp only [Functor.comp_map, Functor.id_map, Functor.comp_obj, Functor.id_obj] at hn
    rw [hn]
    simp [t]
  refine ⟨c, hc, ?_⟩
  intro z hz
  exact Adjunction.ext_counit (hz.trans hc.symm)

/-- The uniquely normalized reverse adjunction on a clopen immersion.
Source: the source proof, paragraph 1, clopen projection
(blueprint: lem-fix-condensed-compactification-reindexing).
Proof: decompose sheaves and complexes into the selected clopen and its complement.
Restriction is first projection and extension by zero is zero insertion. These form
an adjunction whose counit is the inverse native open unit. The counit determines the
adjunction uniquely by the adjunction triangles, so the choice below determines real
data up to equality, not an unspecified object. Localization preserves this calculation. -/
theorem clopenAdjunction_existsUnique {A B : Scheme.{u}}
    (s : A ⟶ B) [IsOpenImmersion s] (hs : IsClosed (Set.range s)) :
    ∃! a : P Λ s ⊣ J Λ s,
      a.counit = @inv _ _ _ _ (oa Λ s).unit (openUnit_isIso Λ s) := by
  have := openUnit_isIso Λ s
  let b := (WeilConjectures.CompactSupportCondensedRealization.clopenExtensionRightAdjunction
    Λ s hs).mapDerivedCategoryAdjunction
  let b' : P Λ s ⊣ J Λ s := b.ofNatIsoLeft
    (leftDerivedUpperStarIsoMapDerivedCategory Λ s).symm
  exact normalizedReverseAdjunction (oa Λ s) b'

/-- The right adjunction fixed uniquely by its counit, hence the projector (1,0).
Source: the source proof, paragraph 1, clopen projection
(blueprint: lem-fix-condensed-compactification-reindexing). -/
@[irreducible] def clopenAdjunction {A B : Scheme.{u}}
    (s : A ⟶ B) [IsOpenImmersion s] (hs : IsClosed (Set.range s)) :
    P Λ s ⊣ J Λ s :=
  (clopenAdjunction_existsUnique Λ s hs).exists.choose

/-- Transport open extension along an equality using its native adjunction.
Source: the source proof, paragraph 3
(blueprint: lem-fix-condensed-compactification-reindexing). -/
def jCongr {A B : Scheme.{u}} {j i : A ⟶ B}
    [IsOpenImmersion j] [IsOpenImmersion i] (h : j = i) : J Λ j ≅ J Λ i :=
  (oa Λ j).leftAdjointUniq
    ((oa Λ i).ofNatIsoRight (eqToIso (congrArg (P Λ) h.symm)))

/-- Composition of native open extensions, normalized by pullback composition.
Source: the source proof, paragraph 3
(blueprint: lem-fix-condensed-compactification-reindexing). -/
def jComp {A B C : Scheme.{u}} (j : A ⟶ B) (i : B ⟶ C)
    [IsOpenImmersion j] [IsOpenImmersion i] : J Λ j ⋙ J Λ i ≅ J Λ (j ≫ i) :=
  ((conjugateIsoEquiv ((oa Λ j).comp (oa Λ i)) (oa Λ (j ≫ i))).symm
    (leftDerivedUpperStarComp Λ j i).symm).symm

/-- Pull back the target open, apply the specified clopen projector, and compose opens.
Source: the source proof, paragraph 1, displayed refinement construction
(blueprint: lem-fix-condensed-compactification-reindexing). -/
@[irreducible] def refinementAdjunct {X Y : Scheme.{u}} {f : X ⟶ Y}
    {c₁ c₂ : Compactification f} (u : c₁.Refinement c₂) :
    J Λ c₂.i ⋙ P Λ u.hom ⟶ J Λ c₁.i :=
  letI := (section_clopen u).1
  let i := pullback.snd c₂.i u.hom
  let t := pullback.fst c₂.i u.hom
  let s := refinementSection u
  let st : s ≫ t = 𝟙 X := pullback.lift_fst _ _ _
  let si : s ≫ i = c₁.i := pullback.lift_snd _ _ _
  let q : P Λ t ⋙ P Λ s ≅ 𝟭 (D Λ X) :=
    (leftDerivedUpperStarComp Λ s t).symm ≪≫
      eqToIso (congrArg (P Λ) st) ≪≫ leftDerivedUpperStarId Λ X
  (beta Λ (IsPullback.of_hasPullback c₂.i u.hom)).hom ≫
    Functor.whiskerLeft (P Λ t)
      (Functor.whiskerRight (clopenAdjunction Λ s (section_clopen u).2).unit (J Λ i)) ≫
    (Functor.isoWhiskerRight q (J Λ s ⋙ J Λ i)).hom ≫
    (Functor.leftUnitor _).hom ≫ (jComp Λ s i).hom ≫
    (jCongr Λ si).hom

/-- Adjunction transpose of the clopen construction, then the direct compositor.
Source: the source proof, paragraph 1
(blueprint: lem-fix-condensed-compactification-reindexing). -/
@[irreducible] def refinement {X Y : Scheme.{u}} {f : X ⟶ Y}
    {c₁ c₂ : Compactification f} (u : c₁.Refinement c₂) : F Λ c₂ ⟶ F Λ c₁ :=
  let m : J Λ c₂.i ⟶ J Λ c₁.i ⋙ R Λ u.hom :=
    ((derivedUpperStarLowerStarAdjunction Λ u.hom).whiskerRight _).homEquiv _ _
      (refinementAdjunct Λ u)
  Functor.whiskerRight m (R Λ c₂.g) ≫
    Functor.whiskerLeft (J Λ c₁.i) ((rightDerivedLowerStarComp Λ u.hom c₂.g).hom ≫
      (eqToIso (congrArg (R Λ) u.hom_g)).hom)

/-- Refinement projection compatibility on arbitrary unbounded inputs.
Source: the source proof, paragraph 3
(blueprint: lem-fix-condensed-compactification-reindexing).
Proof: the clopen projector commutes with tensor: on the selected component it is
identity and on the complement it is zero. Arbitrary-open base change and native
monoidal coherence transport this equality to the displayed refinement adjunct.
Take its mate, apply the proper direct image, and use projection composition with
the inverse-conjugate direct compositor. This gives exactly the displayed equation. -/
theorem refinement_projection {X Y : Scheme.{u}} {f : X ⟶ Y}
    {c₁ c₂ : Compactification f} (u : c₁.Refinement c₂) (K : D Λ X) (L : D Λ Y) :
    pf Λ c₂ K L ≫ (refinement Λ u).app (K ⊗ (P Λ f).obj L) =
      ((refinement Λ u).app K ⊗ₘ 𝟙 L) ≫ pf Λ c₁ K L := by
  sorry

private theorem exchangeRight_cube_of_comparison
    {DY DX DY' DX' EY EX EY' EX' : Type*}
    [Category DY] [Category DX] [Category DY'] [Category DX']
    [Category EY] [Category EX] [Category EY'] [Category EX']
    {Lf : DY ⥤ DX} {Rf : DX ⥤ DY} {Lf' : DY' ⥤ DX'} {Rf' : DX' ⥤ DY'}
    {Mf : EY ⥤ EX} {Sf : EX ⥤ EY} {Mf' : EY' ⥤ EX'} {Sf' : EX' ⥤ EY'}
    (af : Lf ⊣ Rf) (af' : Lf' ⊣ Rf') (bf : Mf ⊣ Sf) (bf' : Mf' ⊣ Sf')
    {Gr : DY ⥤ DY'} {Hr : DX ⥤ DX'} {Gs : EY ⥤ EY'} {Hs : EX ⥤ EX'}
    {PY : DY ⥤ EY} {PX : DX ⥤ EX} {PY' : DY' ⥤ EY'} {PX' : DX' ⥤ EX'}
    (σr : Gr ⋙ Lf' ≅ Lf ⋙ Hr) (σs : Gs ⋙ Mf' ≅ Mf ⋙ Hs)
    (αf : PY ⋙ Mf ≅ Lf ⋙ PX) (αf' : PY' ⋙ Mf' ≅ Lf' ⋙ PX')
    (αg : PY ⋙ Gs ≅ Gr ⋙ PY') (αg' : PX ⋙ Hs ≅ Hr ⋙ PX')
    (h : ∀ M, σs.hom.app (PY.obj M) ≫ Hs.map (αf.hom.app M) ≫
      αg'.hom.app (Lf.obj M) = Mf'.map (αg.hom.app M) ≫
        αf'.hom.app (Gr.obj M) ≫ PX'.map (σr.hom.app M)) (K : DX) :
    PY'.map ((af.exchangeRight af' σr).app K) ≫
        (af'.exchangeRight bf' αf').app (Hr.obj K) ≫ Sf'.map (αg'.inv.app K) =
      αg.inv.app (Rf.obj K) ≫ Gs.map ((af.exchangeRight bf αf).app K) ≫
        (bf.exchangeRight bf' σs).app (PX.obj K) := by
  have hc := mateEquiv_app_cube af af' bf bf' σr.hom σs.hom αf.hom αf'.hom
    αg.hom αg'.hom (fun M ↦ (h M).symm) K
  simp only [← Adjunction.exchangeRight_eq_mateEquiv] at hc
  apply (cancel_epi (αg.hom.app (Rf.obj K))).1
  simp only [Iso.hom_inv_id_app_assoc]
  rw [reassoc_of% hc]
  simp only [← Sf'.map_comp, Iso.hom_inv_id_app]
  simp

private theorem exchangeRight_cube_nt
    {DY DX DY' DX' EY EX EY' EX' : Type*}
    [Category DY] [Category DX] [Category DY'] [Category DX']
    [Category EY] [Category EX] [Category EY'] [Category EX']
    {Lf : DY ⥤ DX} {Rf : DX ⥤ DY} {Lf' : DY' ⥤ DX'} {Rf' : DX' ⥤ DY'}
    {Mf : EY ⥤ EX} {Sf : EX ⥤ EY} {Mf' : EY' ⥤ EX'} {Sf' : EX' ⥤ EY'}
    (af : Lf ⊣ Rf) (af' : Lf' ⊣ Rf') (bf : Mf ⊣ Sf) (bf' : Mf' ⊣ Sf')
    {Gr : DY ⥤ DY'} {Hr : DX ⥤ DX'} {Gs : EY ⥤ EY'} {Hs : EX ⥤ EX'}
    {PY : DY ⥤ EY} {PX : DX ⥤ EX} {PY' : DY' ⥤ EY'} {PX' : DX' ⥤ EX'}
    (σr : Gr ⋙ Lf' ≅ Lf ⋙ Hr) (σs : Gs ⋙ Mf' ≅ Mf ⋙ Hs)
    (αf : PY ⋙ Mf ≅ Lf ⋙ PX) (αf' : PY' ⋙ Mf' ≅ Lf' ⋙ PX')
    (αg : PY ⋙ Gs ≅ Gr ⋙ PY') (αg' : PX ⋙ Hs ≅ Hr ⋙ PX')
    (h : ∀ M, σs.hom.app (PY.obj M) ≫ Hs.map (αf.hom.app M) ≫
      αg'.hom.app (Lf.obj M) = Mf'.map (αg.hom.app M) ≫
        αf'.hom.app (Gr.obj M) ≫ PX'.map (σr.hom.app M)) :
    Functor.whiskerRight (af.exchangeRight af' σr) PY' ≫
      (Functor.associator Hr Rf' PY').hom ≫
      Functor.whiskerLeft Hr (af'.exchangeRight bf' αf') ≫
      (Functor.associator Hr PX' Sf').inv ≫
      Functor.whiskerRight αg'.inv Sf' ≫ (Functor.associator PX Hs Sf').hom =
    (Functor.associator Rf Gr PY').hom ≫ Functor.whiskerLeft Rf αg.inv ≫
      (Functor.associator Rf PY Gs).inv ≫
      Functor.whiskerRight (af.exchangeRight bf αf) Gs ≫
      (Functor.associator PX Sf Gs).hom ≫
      Functor.whiskerLeft PX (bf.exchangeRight bf' σs) := by
  refine NatTrans.ext (funext fun K ↦ ?_)
  simpa only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_hom_app, Functor.associator_inv_app, Category.comp_id,
    Category.id_comp] using exchangeRight_cube_of_comparison af af' bf bf'
      σr σs αf αf' αg αg' h K

private theorem exchangeRight_cube_nt_from_nt
    {DY DX DY' DX' EY EX EY' EX' : Type*}
    [Category DY] [Category DX] [Category DY'] [Category DX']
    [Category EY] [Category EX] [Category EY'] [Category EX']
    {Lf : DY ⥤ DX} {Rf : DX ⥤ DY} {Lf' : DY' ⥤ DX'} {Rf' : DX' ⥤ DY'}
    {Mf : EY ⥤ EX} {Sf : EX ⥤ EY} {Mf' : EY' ⥤ EX'} {Sf' : EX' ⥤ EY'}
    (af : Lf ⊣ Rf) (af' : Lf' ⊣ Rf') (bf : Mf ⊣ Sf) (bf' : Mf' ⊣ Sf')
    {Gr : DY ⥤ DY'} {Hr : DX ⥤ DX'} {Gs : EY ⥤ EY'} {Hs : EX ⥤ EX'}
    {PY : DY ⥤ EY} {PX : DX ⥤ EX} {PY' : DY' ⥤ EY'} {PX' : DX' ⥤ EX'}
    (σr : Gr ⋙ Lf' ≅ Lf ⋙ Hr) (σs : Gs ⋙ Mf' ≅ Mf ⋙ Hs)
    (αf : PY ⋙ Mf ≅ Lf ⋙ PX) (αf' : PY' ⋙ Mf' ≅ Lf' ⋙ PX')
    (αg : PY ⋙ Gs ≅ Gr ⋙ PY') (αg' : PX ⋙ Hs ≅ Hr ⋙ PX')
    (h : Functor.whiskerLeft PY σs.hom ≫ (Functor.associator PY Mf Hs).inv ≫
      Functor.whiskerRight αf.hom Hs ≫ (Functor.associator Lf PX Hs).hom ≫
      Functor.whiskerLeft Lf αg'.hom =
    (Functor.associator PY Gs Mf').inv ≫ Functor.whiskerRight αg.hom Mf' ≫
      (Functor.associator Gr PY' Mf').hom ≫ Functor.whiskerLeft Gr αf'.hom ≫
      (Functor.associator Gr Lf' PX').inv ≫ Functor.whiskerRight σr.hom PX' ≫
      (Functor.associator Lf Hr PX').hom) :
    Functor.whiskerRight (af.exchangeRight af' σr) PY' ≫
      (Functor.associator Hr Rf' PY').hom ≫
      Functor.whiskerLeft Hr (af'.exchangeRight bf' αf') ≫
      (Functor.associator Hr PX' Sf').inv ≫
      Functor.whiskerRight αg'.inv Sf' ≫ (Functor.associator PX Hs Sf').hom =
    (Functor.associator Rf Gr PY').hom ≫ Functor.whiskerLeft Rf αg.inv ≫
      (Functor.associator Rf PY Gs).inv ≫
      Functor.whiskerRight (af.exchangeRight bf αf) Gs ≫
      (Functor.associator PX Sf Gs).hom ≫
      Functor.whiskerLeft PX (bf.exchangeRight bf' σs) := by
  apply exchangeRight_cube_nt af af' bf bf' σr σs αf αf' αg αg'
  intro M
  have hm := congrArg (fun α ↦ α.app M) h
  simpa only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_hom_app, Functor.associator_inv_app, Category.comp_id,
    Category.id_comp] using hm

private theorem pullback_cube_nt_of_app
    {DY DX DY' DX' EY EX EY' EX' : Type*}
    [Category DY] [Category DX] [Category DY'] [Category DX']
    [Category EY] [Category EX] [Category EY'] [Category EX']
    {Lf : DY ⥤ DX} {Lf' : DY' ⥤ DX'}
    {Mf : EY ⥤ EX} {Mf' : EY' ⥤ EX'}
    {Gr : DY ⥤ DY'} {Hr : DX ⥤ DX'} {Gs : EY ⥤ EY'} {Hs : EX ⥤ EX'}
    {PY : DY ⥤ EY} {PX : DX ⥤ EX} {PY' : DY' ⥤ EY'} {PX' : DX' ⥤ EX'}
    (σr : Gr ⋙ Lf' ≅ Lf ⋙ Hr) (σs : Gs ⋙ Mf' ≅ Mf ⋙ Hs)
    (αf : PY ⋙ Mf ≅ Lf ⋙ PX) (αf' : PY' ⋙ Mf' ≅ Lf' ⋙ PX')
    (αg : PY ⋙ Gs ≅ Gr ⋙ PY') (αg' : PX ⋙ Hs ≅ Hr ⋙ PX')
    (h : ∀ M, σs.hom.app (PY.obj M) ≫ Hs.map (αf.hom.app M) ≫
      αg'.hom.app (Lf.obj M) = Mf'.map (αg.hom.app M) ≫
        αf'.hom.app (Gr.obj M) ≫ PX'.map (σr.hom.app M)) :
    Functor.whiskerLeft PY σs.hom ≫ (Functor.associator PY Mf Hs).inv ≫
      Functor.whiskerRight αf.hom Hs ≫ (Functor.associator Lf PX Hs).hom ≫
      Functor.whiskerLeft Lf αg'.hom =
    (Functor.associator PY Gs Mf').inv ≫ Functor.whiskerRight αg.hom Mf' ≫
      (Functor.associator Gr PY' Mf').hom ≫ Functor.whiskerLeft Gr αf'.hom ≫
      (Functor.associator Gr Lf' PX').inv ≫ Functor.whiskerRight σr.hom PX' ≫
      (Functor.associator Lf Hr PX').hom := by
  refine NatTrans.ext (funext fun M ↦ ?_)
  simpa only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_hom_app, Functor.associator_inv_app, Category.comp_id,
    Category.id_comp] using h M

private theorem native_pullback_cube_nt {X Y X' Y' A B A' B' : Scheme.{u}}
    {f : X ⟶ Y} {f' : X' ⟶ Y'} {w : X' ⟶ X} {v : Y' ⟶ Y}
    {g : A ⟶ B} {g' : A' ⟶ B'} {w₀ : A' ⟶ A} {v₀ : B' ⟶ B}
    {a : A ⟶ X} {b : B ⟶ Y} {a' : A' ⟶ X'} {b' : B' ⟶ Y'}
    [IsIso a] [IsIso b] [IsIso a'] [IsIso b']
    (front : CommSq w f' f v) (back : CommSq w₀ g' g v₀)
    (left : CommSq a g f b) (right : CommSq a' g' f' b')
    (top : CommSq a' w₀ w a) (bottom : CommSq b' v₀ v b) :
    Functor.whiskerLeft (P Λ b) (pullbackSquareComparison Λ back).hom ≫
      (Functor.associator (P Λ b) (P Λ g) (P Λ w₀)).inv ≫
      Functor.whiskerRight (pullbackSquareComparison Λ left).hom (P Λ w₀) ≫
      (Functor.associator (P Λ f) (P Λ a) (P Λ w₀)).hom ≫
      Functor.whiskerLeft (P Λ f) (pullbackSquareComparison Λ top).hom =
    (Functor.associator (P Λ b) (P Λ v₀) (P Λ g')).inv ≫
      Functor.whiskerRight (pullbackSquareComparison Λ bottom).hom (P Λ g') ≫
      (Functor.associator (P Λ v) (P Λ b') (P Λ g')).hom ≫
      Functor.whiskerLeft (P Λ v) (pullbackSquareComparison Λ right).hom ≫
      (Functor.associator (P Λ v) (P Λ f') (P Λ a')).inv ≫
      Functor.whiskerRight (pullbackSquareComparison Λ front).hom (P Λ a') ≫
      (Functor.associator (P Λ f) (P Λ w) (P Λ a')).hom := by
  exact pullback_cube_nt_of_app
    (pullbackSquareComparison Λ front) (pullbackSquareComparison Λ back)
    (pullbackSquareComparison Λ left) (pullbackSquareComparison Λ right)
    (pullbackSquareComparison Λ bottom) (pullbackSquareComparison Λ top)
    (pullbackSquareComparison_cube Λ back front top left right bottom)

private theorem native_direct_cube_nt {X Y X' Y' A B A' B' : Scheme.{u}}
    {f : X ⟶ Y} {f' : X' ⟶ Y'} {w : X' ⟶ X} {v : Y' ⟶ Y}
    {g : A ⟶ B} {g' : A' ⟶ B'} {w₀ : A' ⟶ A} {v₀ : B' ⟶ B}
    {a : A ⟶ X} {b : B ⟶ Y} {a' : A' ⟶ X'} {b' : B' ⟶ Y'}
    [IsIso a] [IsIso b] [IsIso a'] [IsIso b']
    (front : CommSq w f' f v) (back : CommSq w₀ g' g v₀)
    (left : CommSq a g f b) (right : CommSq a' g' f' b')
    (top : CommSq a' w₀ w a) (bottom : CommSq b' v₀ v b) :
    Functor.whiskerRight (baseChangeMap Λ front) (P Λ b') ≫
      (Functor.associator (P Λ w) (R Λ f') (P Λ b')).hom ≫
      Functor.whiskerLeft (P Λ w) (baseChangeMap Λ right) ≫
      (Functor.associator (P Λ w) (P Λ a') (R Λ g')).inv ≫
      Functor.whiskerRight (pullbackSquareComparison Λ top).inv (R Λ g') ≫
      (Functor.associator (P Λ a) (P Λ w₀) (R Λ g')).hom =
    (Functor.associator (R Λ f) (P Λ v) (P Λ b')).hom ≫
      Functor.whiskerLeft (R Λ f) (pullbackSquareComparison Λ bottom).inv ≫
      (Functor.associator (R Λ f) (P Λ b) (P Λ v₀)).inv ≫
      Functor.whiskerRight (baseChangeMap Λ left) (P Λ v₀) ≫
      (Functor.associator (P Λ a) (R Λ g) (P Λ v₀)).hom ≫
      Functor.whiskerLeft (P Λ a) (baseChangeMap Λ back) := by
  unfold baseChangeMap
  exact exchangeRight_cube_nt_from_nt
    (derivedUpperStarLowerStarAdjunction Λ f) (derivedUpperStarLowerStarAdjunction Λ f')
    (derivedUpperStarLowerStarAdjunction Λ g) (derivedUpperStarLowerStarAdjunction Λ g')
    (pullbackSquareComparison Λ front) (pullbackSquareComparison Λ back)
    (pullbackSquareComparison Λ left) (pullbackSquareComparison Λ right)
    (pullbackSquareComparison Λ bottom) (pullbackSquareComparison Λ top)
    (native_pullback_cube_nt Λ front back left right top bottom)

set_option maxHeartbeats 1600000 in
-- Native derived endpoints require additional unification time.
/-- Direct exchanges in an isomorphism cube, with arbitrary face base maps.
Source: the source proof, paragraphs 1 and 3
(blueprint: lem-fix-condensed-compactification-reindexing).
Proof: paste the front face with the two adjacent isomorphism faces in either order.
Pullback square coherence identifies the two pasted comparisons. Taking mates and
using both pasting laws gives the equation. Only vertex comparisons are inverted;
no face exchange is inverted. -/
theorem direct_cube {X Y X' Y' A B A' B' : Scheme.{u}}
    {f : X ⟶ Y} {f' : X' ⟶ Y'} {w : X' ⟶ X} {v : Y' ⟶ Y}
    {g : A ⟶ B} {g' : A' ⟶ B'} {w₀ : A' ⟶ A} {v₀ : B' ⟶ B}
    {a : A ⟶ X} {b : B ⟶ Y} {a' : A' ⟶ X'} {b' : B' ⟶ Y'}
    [IsIso a] [IsIso b] [IsIso a'] [IsIso b']
    (front : CommSq w f' f v) (back : CommSq w₀ g' g v₀)
    (left : CommSq a g f b) (right : CommSq a' g' f' b')
    (top : CommSq a' w₀ w a) (bottom : CommSq b' v₀ v b) (K : D Λ X) :
    (P Λ b').map ((baseChangeMap Λ front).app K) ≫
        (baseChangeMap Λ right).app ((P Λ w).obj K) ≫
        (R Λ g').map ((pullbackSquareComparison Λ top).inv.app K) =
      (pullbackSquareComparison Λ bottom).inv.app ((R Λ f).obj K) ≫
        (P Λ v₀).map ((baseChangeMap Λ left).app K) ≫
        (baseChangeMap Λ back).app ((P Λ a).obj K) := by
  have h := congrArg (fun α : (R Λ f ⋙ P Λ v) ⋙ P Λ b' ⟶
      P Λ a ⋙ (P Λ w₀ ⋙ R Λ g') ↦ α.app K)
    (native_direct_cube_nt Λ front back left right top bottom)
  simpa only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_hom_app, Functor.associator_inv_app, Category.comp_id,
    Category.id_comp] using h

private theorem inverse_cube_partial {C : Type*} [Category C]
    {a b c d e f : C} (α : a ≅ b) (β : b ≅ c) (γ : c ≅ d)
    (δ : a ≅ e) (ε : e ≅ f) (ζ : f ≅ d)
    (h : α.hom ≫ β.hom ≫ γ.hom = δ.hom ≫ ε.hom ≫ ζ.hom) :
    γ.hom ≫ ζ.inv ≫ ε.inv = β.inv ≫ α.inv ≫ δ.hom := by
  apply (cancel_epi (α.hom ≫ β.hom)).1
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  rw [reassoc_of% h]
  simp only [Iso.hom_inv_id_assoc, Iso.hom_inv_id, Category.comp_id]

private theorem inverse_mate_cube_of_comparison
    {DY DX DY' DX' EY EX EY' EX' : Type*}
    [Category DY] [Category DX] [Category DY'] [Category DX']
    [Category EY] [Category EX] [Category EY'] [Category EX']
    {Lf : DY ⥤ DX} {Rf : DX ⥤ DY} {Lf' : DY' ⥤ DX'} {Rf' : DX' ⥤ DY'}
    {Mf : EY ⥤ EX} {Sf : EX ⥤ EY} {Mf' : EY' ⥤ EX'} {Sf' : EX' ⥤ EY'}
    (af : Lf ⊣ Rf) (af' : Lf' ⊣ Rf') (bf : Mf ⊣ Sf) (bf' : Mf' ⊣ Sf')
    {Gr : DY ⥤ DY'} {Hr : DX ⥤ DX'} {Gs : EY ⥤ EY'} {Hs : EX ⥤ EX'}
    {PY : DY ⥤ EY} {PX : DX ⥤ EX} {PY' : DY' ⥤ EY'} {PX' : DX' ⥤ EX'}
    (θr : Hr ⋙ Rf' ≅ Rf ⋙ Gr) (θs : Hs ⋙ Sf' ≅ Sf ⋙ Gs)
    (θf : PX ⋙ Sf ≅ Rf ⋙ PY) (θf' : PX' ⋙ Sf' ≅ Rf' ⋙ PY')
    (αg : PY ⋙ Gs ≅ Gr ⋙ PY') (αg' : PX ⋙ Hs ≅ Hr ⋙ PX')
    (h : ∀ M, θs.hom.app (PX.obj M) ≫ Gs.map (θf.hom.app M) ≫
      αg.hom.app (Rf.obj M) = Sf'.map (αg'.hom.app M) ≫
        θf'.hom.app (Hr.obj M) ≫ PY'.map (θr.hom.app M)) (K : DY) :
    Mf'.map (αg.hom.app K) ≫
        ((mateEquiv af' bf').symm (TwoSquare.mk _ _ _ _ θf'.inv)).natTrans.app
          (Gr.obj K) ≫
        PX'.map (((mateEquiv af af').symm (TwoSquare.mk _ _ _ _ θr.inv)).natTrans.app K) =
      ((mateEquiv bf bf').symm (TwoSquare.mk _ _ _ _ θs.inv)).natTrans.app (PY.obj K) ≫
        Hs.map (((mateEquiv af bf).symm (TwoSquare.mk _ _ _ _ θf.inv)).natTrans.app K) ≫
        αg'.hom.app (Lf.obj K) := by
  apply mateEquiv_app_cube_converse af af' bf bf'
    ((mateEquiv af af').symm (TwoSquare.mk _ _ _ _ θr.inv)).natTrans
    ((mateEquiv bf bf').symm (TwoSquare.mk _ _ _ _ θs.inv)).natTrans
    ((mateEquiv af bf).symm (TwoSquare.mk _ _ _ _ θf.inv)).natTrans
    ((mateEquiv af' bf').symm (TwoSquare.mk _ _ _ _ θf'.inv)).natTrans αg.hom αg'.hom
  intro M
  simpa only [TwoSquare.mk, Equiv.apply_symm_apply, TwoSquare.natTrans, Functor.mapIso_hom,
    Functor.mapIso_inv,
    Iso.app_inv, Iso.app_hom] using inverse_cube_partial
    (θs.app (PX.obj M)) (Gs.mapIso (θf.app M)) (αg.app (Rf.obj M))
    (Sf'.mapIso (αg'.app M)) (θf'.app (Hr.obj M)) (PY'.mapIso (θr.app M)) (h M)

private theorem inverse_mate_cube_nt
    {DY DX DY' DX' EY EX EY' EX' : Type*}
    [Category DY] [Category DX] [Category DY'] [Category DX']
    [Category EY] [Category EX] [Category EY'] [Category EX']
    {Lf : DY ⥤ DX} {Rf : DX ⥤ DY} {Lf' : DY' ⥤ DX'} {Rf' : DX' ⥤ DY'}
    {Mf : EY ⥤ EX} {Sf : EX ⥤ EY} {Mf' : EY' ⥤ EX'} {Sf' : EX' ⥤ EY'}
    (af : Lf ⊣ Rf) (af' : Lf' ⊣ Rf') (bf : Mf ⊣ Sf) (bf' : Mf' ⊣ Sf')
    {Gr : DY ⥤ DY'} {Hr : DX ⥤ DX'} {Gs : EY ⥤ EY'} {Hs : EX ⥤ EX'}
    {PY : DY ⥤ EY} {PX : DX ⥤ EX} {PY' : DY' ⥤ EY'} {PX' : DX' ⥤ EX'}
    (θr : Hr ⋙ Rf' ≅ Rf ⋙ Gr) (θs : Hs ⋙ Sf' ≅ Sf ⋙ Gs)
    (θf : PX ⋙ Sf ≅ Rf ⋙ PY) (θf' : PX' ⋙ Sf' ≅ Rf' ⋙ PY')
    (αg : PY ⋙ Gs ≅ Gr ⋙ PY') (αg' : PX ⋙ Hs ≅ Hr ⋙ PX')
    (h : ∀ M, θs.hom.app (PX.obj M) ≫ Gs.map (θf.hom.app M) ≫
      αg.hom.app (Rf.obj M) = Sf'.map (αg'.hom.app M) ≫
        θf'.hom.app (Hr.obj M) ≫ PY'.map (θr.hom.app M)) :
    Functor.whiskerRight αg.hom Mf' ≫ (Functor.associator Gr PY' Mf').hom ≫
      Functor.whiskerLeft Gr
        ((mateEquiv af' bf').symm (TwoSquare.mk _ _ _ _ θf'.inv)).natTrans ≫
      (Functor.associator Gr Lf' PX').inv ≫
      Functor.whiskerRight
        ((mateEquiv af af').symm (TwoSquare.mk _ _ _ _ θr.inv)).natTrans PX' ≫
      (Functor.associator Lf Hr PX').hom =
    (Functor.associator PY Gs Mf').hom ≫
      Functor.whiskerLeft PY
        ((mateEquiv bf bf').symm (TwoSquare.mk _ _ _ _ θs.inv)).natTrans ≫
      (Functor.associator PY Mf Hs).inv ≫
      Functor.whiskerRight
        ((mateEquiv af bf).symm (TwoSquare.mk _ _ _ _ θf.inv)).natTrans Hs ≫
      (Functor.associator Lf PX Hs).hom ≫ Functor.whiskerLeft Lf αg'.hom := by
  refine NatTrans.ext (funext fun K ↦ ?_)
  simpa only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_hom_app, Functor.associator_inv_app, Category.comp_id,
    Category.id_comp] using inverse_mate_cube_of_comparison af af' bf bf'
      θr θs θf θf' αg αg' h K

private theorem inverse_mate_cube_nt_from_nt
    {DY DX DY' DX' EY EX EY' EX' : Type*}
    [Category DY] [Category DX] [Category DY'] [Category DX']
    [Category EY] [Category EX] [Category EY'] [Category EX']
    {Lf : DY ⥤ DX} {Rf : DX ⥤ DY} {Lf' : DY' ⥤ DX'} {Rf' : DX' ⥤ DY'}
    {Mf : EY ⥤ EX} {Sf : EX ⥤ EY} {Mf' : EY' ⥤ EX'} {Sf' : EX' ⥤ EY'}
    (af : Lf ⊣ Rf) (af' : Lf' ⊣ Rf') (bf : Mf ⊣ Sf) (bf' : Mf' ⊣ Sf')
    {Gr : DY ⥤ DY'} {Hr : DX ⥤ DX'} {Gs : EY ⥤ EY'} {Hs : EX ⥤ EX'}
    {PY : DY ⥤ EY} {PX : DX ⥤ EX} {PY' : DY' ⥤ EY'} {PX' : DX' ⥤ EX'}
    (θr : Hr ⋙ Rf' ≅ Rf ⋙ Gr) (θs : Hs ⋙ Sf' ≅ Sf ⋙ Gs)
    (θf : PX ⋙ Sf ≅ Rf ⋙ PY) (θf' : PX' ⋙ Sf' ≅ Rf' ⋙ PY')
    (αg : PY ⋙ Gs ≅ Gr ⋙ PY') (αg' : PX ⋙ Hs ≅ Hr ⋙ PX')
    (h : Functor.whiskerLeft PX θs.hom ≫ (Functor.associator PX Sf Gs).inv ≫
      Functor.whiskerRight θf.hom Gs ≫ (Functor.associator Rf PY Gs).hom ≫
      Functor.whiskerLeft Rf αg.hom =
    (Functor.associator PX Hs Sf').inv ≫ Functor.whiskerRight αg'.hom Sf' ≫
      (Functor.associator Hr PX' Sf').hom ≫ Functor.whiskerLeft Hr θf'.hom ≫
      (Functor.associator Hr Rf' PY').inv ≫ Functor.whiskerRight θr.hom PY' ≫
      (Functor.associator Rf Gr PY').hom) :
    Functor.whiskerRight αg.hom Mf' ≫ (Functor.associator Gr PY' Mf').hom ≫
      Functor.whiskerLeft Gr
        ((mateEquiv af' bf').symm (TwoSquare.mk _ _ _ _ θf'.inv)).natTrans ≫
      (Functor.associator Gr Lf' PX').inv ≫
      Functor.whiskerRight
        ((mateEquiv af af').symm (TwoSquare.mk _ _ _ _ θr.inv)).natTrans PX' ≫
      (Functor.associator Lf Hr PX').hom =
    (Functor.associator PY Gs Mf').hom ≫
      Functor.whiskerLeft PY
        ((mateEquiv bf bf').symm (TwoSquare.mk _ _ _ _ θs.inv)).natTrans ≫
      (Functor.associator PY Mf Hs).inv ≫
      Functor.whiskerRight
        ((mateEquiv af bf).symm (TwoSquare.mk _ _ _ _ θf.inv)).natTrans Hs ≫
      (Functor.associator Lf PX Hs).hom ≫ Functor.whiskerLeft Lf αg'.hom := by
  apply inverse_mate_cube_nt af af' bf bf' θr θs θf θf' αg αg'
  intro M
  have hm := congrArg (fun α ↦ α.app M) h
  simpa only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_hom_app, Functor.associator_inv_app, Category.comp_id,
    Category.id_comp] using hm

private theorem native_open_cube_nt {X Y X' Y' A B A' B' : Scheme.{u}}
    {j : X ⟶ Y} {j' : X' ⟶ Y'} {w : X' ⟶ X} {v : Y' ⟶ Y}
    {i : A ⟶ B} {i' : A' ⟶ B'} {w₀ : A' ⟶ A} {v₀ : B' ⟶ B}
    {a : A ⟶ X} {b : B ⟶ Y} {a' : A' ⟶ X'} {b' : B' ⟶ Y'}
    [IsOpenImmersion j] [IsOpenImmersion j'] [IsOpenImmersion i] [IsOpenImmersion i']
    [IsIso a] [IsIso b] [IsIso a'] [IsIso b']
    (front : CommSq w j' j v) (back : CommSq w₀ i' i v₀)
    (left : CommSq a i j b) (right : CommSq a' i' j' b')
    (top : CommSq a' w₀ w a) (bottom : CommSq b' v₀ v b) :
    Functor.whiskerRight (pullbackSquareComparison Λ top).hom (J Λ i') ≫
      (Functor.associator (P Λ w) (P Λ a') (J Λ i')).hom ≫
      Functor.whiskerLeft (P Λ w) (openMate Λ right) ≫
      (Functor.associator (P Λ w) (J Λ j') (P Λ b')).inv ≫
      Functor.whiskerRight (openMate Λ front) (P Λ b') ≫
      (Functor.associator (J Λ j) (P Λ v) (P Λ b')).hom =
    (Functor.associator (P Λ a) (P Λ w₀) (J Λ i')).hom ≫
      Functor.whiskerLeft (P Λ a) (openMate Λ back) ≫
      (Functor.associator (P Λ a) (J Λ i) (P Λ v₀)).inv ≫
      Functor.whiskerRight (openMate Λ left) (P Λ v₀) ≫
      (Functor.associator (J Λ j) (P Λ b) (P Λ v₀)).hom ≫
      Functor.whiskerLeft (J Λ j) (pullbackSquareComparison Λ bottom).hom := by
  unfold openMate
  exact inverse_mate_cube_nt_from_nt (oa Λ j) (oa Λ j') (oa Λ i) (oa Λ i')
    (pullbackSquareComparison Λ front) (pullbackSquareComparison Λ back)
    (pullbackSquareComparison Λ left) (pullbackSquareComparison Λ right)
    (pullbackSquareComparison Λ top) (pullbackSquareComparison Λ bottom)
    (native_pullback_cube_nt Λ front back left right top bottom)

/-- The same cube equation for inverse open mates; on Cartesian faces this is
precisely transport of beta after inversion of the open comparisons.
Source: the source proof, paragraphs 1 and 3
(blueprint: lem-fix-condensed-compactification-reindexing).
Proof: apply the two open-adjunction mate bijections to the pullback cube identity.
Their injectivity and naturality give the displayed equation. Cartesian face mates
are invertible by arbitrary-open base change, so inversion gives transport of beta. -/
theorem open_cube {X Y X' Y' A B A' B' : Scheme.{u}}
    {j : X ⟶ Y} {j' : X' ⟶ Y'} {w : X' ⟶ X} {v : Y' ⟶ Y}
    {i : A ⟶ B} {i' : A' ⟶ B'} {w₀ : A' ⟶ A} {v₀ : B' ⟶ B}
    {a : A ⟶ X} {b : B ⟶ Y} {a' : A' ⟶ X'} {b' : B' ⟶ Y'}
    [IsOpenImmersion j] [IsOpenImmersion j'] [IsOpenImmersion i] [IsOpenImmersion i']
    [IsIso a] [IsIso b] [IsIso a'] [IsIso b']
    (front : CommSq w j' j v) (back : CommSq w₀ i' i v₀)
    (left : CommSq a i j b) (right : CommSq a' i' j' b')
    (top : CommSq a' w₀ w a) (bottom : CommSq b' v₀ v b) (K : D Λ X) :
    (J Λ i').map ((pullbackSquareComparison Λ top).hom.app K) ≫
        (openMate Λ right).app ((P Λ w).obj K) ≫
        (P Λ b').map ((openMate Λ front).app K) =
      (openMate Λ back).app ((P Λ a).obj K) ≫
        (P Λ v₀).map ((openMate Λ left).app K) ≫
        (pullbackSquareComparison Λ bottom).hom.app ((J Λ j).obj K) := by
  have h := congrArg (fun α : (P Λ a ⋙ P Λ w₀) ⋙ J Λ i' ⟶
      J Λ j ⋙ (P Λ v ⋙ P Λ b') ↦ α.app K)
    (native_open_cube_nt Λ front back left right top bottom)
  simpa only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_hom_app, Functor.associator_inv_app, Category.comp_id,
    Category.id_comp] using h

private theorem transport_exchange_cube_aux
    {A B A' B' E F E' F' : Type*}
    [Category A] [Category B] [Category A'] [Category B']
    [Category E] [Category F] [Category E'] [Category F']
    {F₀ T₀ : A ⥤ B} {F₁ T₁ : A' ⥤ B'} {F₂ T₂ : E ⥤ F} {F₃ T₃ : E' ⥤ F'}
    (χ₀ : F₀ ≅ T₀) (χ₁ : F₁ ≅ T₁) (χ₂ : F₂ ≅ T₂) (χ₃ : F₃ ≅ T₃)
    {Gr : B ⥤ B'} {Hr : A ⥤ A'} {Gs : F ⥤ F'} {Hs : E ⥤ E'}
    {PY : B ⥤ F} {PX : A ⥤ E} {PY' : B' ⥤ F'} {PX' : A' ⥤ E'}
    (top : PX ⋙ Hs ≅ Hr ⋙ PX') (bottom : PY ⋙ Gs ≅ Gr ⋙ PY')
    (δr : T₀ ⋙ Gr ⟶ Hr ⋙ T₁) (δs : T₂ ⋙ Gs ⟶ Hs ⋙ T₃)
    (δf : T₀ ⋙ PY ⟶ PX ⋙ T₂) (δf' : T₁ ⋙ PY' ⟶ PX' ⋙ T₃)
    (σr : F₀ ⋙ Gr ⟶ Hr ⋙ F₁) (σs : F₂ ⋙ Gs ⟶ Hs ⋙ F₃)
    (σf : F₀ ⋙ PY ⟶ PX ⋙ F₂) (σf' : F₁ ⋙ PY' ⟶ PX' ⋙ F₃)
    (hr : σr = Functor.whiskerRight χ₀.hom Gr ≫ δr ≫ Functor.whiskerLeft Hr χ₁.inv)
    (hs : σs = Functor.whiskerRight χ₂.hom Gs ≫ δs ≫ Functor.whiskerLeft Hs χ₃.inv)
    (hf : σf = Functor.whiskerRight χ₀.hom PY ≫ δf ≫ Functor.whiskerLeft PX χ₂.inv)
    (hf' : σf' = Functor.whiskerRight χ₁.hom PY' ≫ δf' ≫ Functor.whiskerLeft PX' χ₃.inv)
    (hp : ∀ K, PY'.map (δr.app K) ≫ δf'.app (Hr.obj K) ≫ T₃.map (top.inv.app K) =
      bottom.inv.app (T₀.obj K) ≫ Gs.map (δf.app K) ≫ δs.app (PX.obj K)) (K : A) :
    PY'.map (σr.app K) ≫ σf'.app (Hr.obj K) ≫ F₃.map (top.inv.app K) =
      bottom.inv.app (F₀.obj K) ≫ Gs.map (σf.app K) ≫ σs.app (PX.obj K) := by
  have ht := χ₃.hom.naturality (top.inv.app K)
  have hb := bottom.inv.naturality (χ₀.hom.app K)
  dsimp only [Functor.comp_obj] at ht
  dsimp only [Functor.comp_map] at hb
  rw [hr, hs, hf, hf']
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.map_comp]
  apply (cancel_mono (χ₃.hom.app (Hs.obj (PX.obj K)))).1
  simp only [Category.assoc]
  rw [ht]
  simp only [Iso.inv_hom_id_app_assoc, Iso.inv_hom_id_app]
  rw [← PY'.map_comp_assoc (χ₁.inv.app (Hr.obj K)) (χ₁.hom.app (Hr.obj K)),
    Iso.inv_hom_id_app, CategoryTheory.Functor.map_id, Category.id_comp]
  rw [← Gs.map_comp_assoc (χ₂.inv.app (PX.obj K)) (χ₂.hom.app (PX.obj K)),
    Iso.inv_hom_id_app, CategoryTheory.Functor.map_id, Category.id_comp]
  rw [hp K, reassoc_of% hb]
  simp

private theorem transport_exchange_cube_nt
    {A B A' B' E F E' F' : Type*}
    [Category A] [Category B] [Category A'] [Category B']
    [Category E] [Category F] [Category E'] [Category F']
    {F₀ T₀ : A ⥤ B} {F₁ T₁ : A' ⥤ B'} {F₂ T₂ : E ⥤ F} {F₃ T₃ : E' ⥤ F'}
    (χ₀ : F₀ ≅ T₀) (χ₁ : F₁ ≅ T₁) (χ₂ : F₂ ≅ T₂) (χ₃ : F₃ ≅ T₃)
    {Gr : B ⥤ B'} {Hr : A ⥤ A'} {Gs : F ⥤ F'} {Hs : E ⥤ E'}
    {PY : B ⥤ F} {PX : A ⥤ E} {PY' : B' ⥤ F'} {PX' : A' ⥤ E'}
    (top : PX ⋙ Hs ≅ Hr ⋙ PX') (bottom : PY ⋙ Gs ≅ Gr ⋙ PY')
    (δr : T₀ ⋙ Gr ⟶ Hr ⋙ T₁) (δs : T₂ ⋙ Gs ⟶ Hs ⋙ T₃)
    (δf : T₀ ⋙ PY ⟶ PX ⋙ T₂) (δf' : T₁ ⋙ PY' ⟶ PX' ⋙ T₃)
    (σr : F₀ ⋙ Gr ⟶ Hr ⋙ F₁) (σs : F₂ ⋙ Gs ⟶ Hs ⋙ F₃)
    (σf : F₀ ⋙ PY ⟶ PX ⋙ F₂) (σf' : F₁ ⋙ PY' ⟶ PX' ⋙ F₃)
    (hr : σr = Functor.whiskerRight χ₀.hom Gr ≫ δr ≫ Functor.whiskerLeft Hr χ₁.inv)
    (hs : σs = Functor.whiskerRight χ₂.hom Gs ≫ δs ≫ Functor.whiskerLeft Hs χ₃.inv)
    (hf : σf = Functor.whiskerRight χ₀.hom PY ≫ δf ≫ Functor.whiskerLeft PX χ₂.inv)
    (hf' : σf' = Functor.whiskerRight χ₁.hom PY' ≫ δf' ≫ Functor.whiskerLeft PX' χ₃.inv)
    (hp : ∀ K, PY'.map (δr.app K) ≫ δf'.app (Hr.obj K) ≫ T₃.map (top.inv.app K) =
      bottom.inv.app (T₀.obj K) ≫ Gs.map (δf.app K) ≫ δs.app (PX.obj K)) :
    Functor.whiskerRight σr PY' ≫ (Functor.associator Hr F₁ PY').hom ≫
      Functor.whiskerLeft Hr σf' ≫ (Functor.associator Hr PX' F₃).inv ≫
      Functor.whiskerRight top.inv F₃ ≫ (Functor.associator PX Hs F₃).hom =
    (Functor.associator F₀ Gr PY').hom ≫ Functor.whiskerLeft F₀ bottom.inv ≫
      (Functor.associator F₀ PY Gs).inv ≫ Functor.whiskerRight σf Gs ≫
      (Functor.associator PX F₂ Gs).hom ≫ Functor.whiskerLeft PX σs := by
  refine NatTrans.ext (funext fun K ↦ ?_)
  simpa only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_hom_app, Functor.associator_inv_app, Category.comp_id,
    Category.id_comp] using transport_exchange_cube_aux χ₀ χ₁ χ₂ χ₃ top bottom
      δr δs δf δf' σr σs σf σf' hr hs hf hf' hp K

private theorem composite_exchange_cube_aux
    {A B C A' B' C' E F G E' F' G' : Type*}
    [Category A] [Category B] [Category C] [Category A'] [Category B'] [Category C']
    [Category E] [Category F] [Category G] [Category E'] [Category F'] [Category G']
    (J₀ : A ⥤ B) (R₀ : B ⥤ C) (J₁ : A' ⥤ B') (R₁ : B' ⥤ C')
    (J₂ : E ⥤ F) (R₂ : F ⥤ G) (J₃ : E' ⥤ F') (R₃ : F' ⥤ G')
    (Gr : C ⥤ C') (Hr : A ⥤ A') (Mr : B ⥤ B')
    (Gs : G ⥤ G') (Hs : E ⥤ E') (Ms : F ⥤ F')
    (PY : C ⥤ G) (PX : A ⥤ E) (PM : B ⥤ F)
    (PY' : C' ⥤ G') (PX' : A' ⥤ E') (PM' : B' ⥤ F')
    (r : R₀ ⋙ Gr ⟶ Mr ⋙ R₁) (s : R₂ ⋙ Gs ⟶ Ms ⋙ R₃)
    (f : R₀ ⋙ PY ⟶ PM ⋙ R₂) (f' : R₁ ⋙ PY' ⟶ PM' ⋙ R₃)
    (βr : J₀ ⋙ Mr ≅ Hr ⋙ J₁) (βs : J₂ ⋙ Ms ≅ Hs ⋙ J₃)
    (βf : J₀ ⋙ PM ≅ PX ⋙ J₂) (βf' : J₁ ⋙ PM' ≅ PX' ⋙ J₃)
    (top : PX ⋙ Hs ≅ Hr ⋙ PX') (middle : PM ⋙ Ms ≅ Mr ⋙ PM')
    (bottom : PY ⋙ Gs ≅ Gr ⋙ PY')
    (hp : ∀ N, PY'.map (r.app N) ≫ f'.app (Mr.obj N) ≫ R₃.map (middle.inv.app N) =
      bottom.inv.app (R₀.obj N) ≫ Gs.map (f.app N) ≫ s.app (PM.obj N))
    (hb : ∀ K, PM'.map (βr.hom.app K) ≫ βf'.hom.app (Hr.obj K) ≫
        J₃.map (top.inv.app K) =
      middle.inv.app (J₀.obj K) ≫ Ms.map (βf.hom.app K) ≫ βs.hom.app (PX.obj K))
    (K : A) :
    PY'.map ((compositeExchange J₀ R₀ J₁ R₁ Gr Hr Mr r βr).app K) ≫
      (compositeExchange J₁ R₁ J₃ R₃ PY' PX' PM' f' βf').app (Hr.obj K) ≫
      (J₃ ⋙ R₃).map (top.inv.app K) =
    bottom.inv.app ((J₀ ⋙ R₀).obj K) ≫
      Gs.map ((compositeExchange J₀ R₀ J₂ R₂ PY PX PM f βf).app K) ≫
      (compositeExchange J₂ R₂ J₃ R₃ Gs Hs Ms s βs).app (PX.obj K) := by
  simp only [compositeExchange_app, Functor.map_comp, Functor.comp_map, Category.assoc]
  dsimp only [Functor.comp_obj]
  have hn₁ := f'.naturality (βr.hom.app K)
  have hn₂ := s.naturality (βf.hom.app K)
  dsimp only [Functor.comp_map] at hn₁ hn₂
  rw [reassoc_of% hn₁]
  simp only [← Functor.map_comp]
  rw [hb K]
  simp only [Functor.map_comp]
  rw [reassoc_of% (hp (J₀.obj K))]
  rw [← reassoc_of% hn₂]

private theorem compact_cube_of_model
    {A B C A' B' C' E F G E' F' G' : Type*}
    [Category A] [Category B] [Category C] [Category A'] [Category B'] [Category C']
    [Category E] [Category F] [Category G] [Category E'] [Category F'] [Category G']
    (J₀ : A ⥤ B) (R₀ : B ⥤ C) (J₁ : A' ⥤ B') (R₁ : B' ⥤ C')
    (J₂ : E ⥤ F) (R₂ : F ⥤ G) (J₃ : E' ⥤ F') (R₃ : F' ⥤ G')
    (Gr : C ⥤ C') (Hr : A ⥤ A') (Mr : B ⥤ B')
    (Gs : G ⥤ G') (Hs : E ⥤ E') (Ms : F ⥤ F')
    (PY : C ⥤ G) (PX : A ⥤ E) (PM : B ⥤ F)
    (PY' : C' ⥤ G') (PX' : A' ⥤ E') (PM' : B' ⥤ F')
    (r : R₀ ⋙ Gr ⟶ Mr ⋙ R₁) (s : R₂ ⋙ Gs ⟶ Ms ⋙ R₃)
    (f : R₀ ⋙ PY ⟶ PM ⋙ R₂) (f' : R₁ ⋙ PY' ⟶ PM' ⋙ R₃)
    (βr : J₀ ⋙ Mr ≅ Hr ⋙ J₁) (βs : J₂ ⋙ Ms ≅ Hs ⋙ J₃)
    (βf : J₀ ⋙ PM ≅ PX ⋙ J₂) (βf' : J₁ ⋙ PM' ≅ PX' ⋙ J₃)
    (top : PX ⋙ Hs ≅ Hr ⋙ PX') (middle : PM ⋙ Ms ≅ Mr ⋙ PM')
    (bottom : PY ⋙ Gs ≅ Gr ⋙ PY')
    (hp : ∀ N, PY'.map (r.app N) ≫ f'.app (Mr.obj N) ≫ R₃.map (middle.inv.app N) =
      bottom.inv.app (R₀.obj N) ≫ Gs.map (f.app N) ≫ s.app (PM.obj N))
    (hb : ∀ K, PM'.map (βr.hom.app K) ≫ βf'.hom.app (Hr.obj K) ≫
        J₃.map (top.inv.app K) =
      middle.inv.app (J₀.obj K) ≫ Ms.map (βf.hom.app K) ≫ βs.hom.app (PX.obj K))

    (F₀ : A ⥤ C) (F₁ : A' ⥤ C') (F₂ : E ⥤ G) (F₃ : E' ⥤ G')
    (χ₀ : F₀ ≅ J₀ ⋙ R₀) (χ₁ : F₁ ≅ J₁ ⋙ R₁)
    (χ₂ : F₂ ≅ J₂ ⋙ R₂) (χ₃ : F₃ ≅ J₃ ⋙ R₃)
    (σr : F₀ ⋙ Gr ⟶ Hr ⋙ F₁) (σs : F₂ ⋙ Gs ⟶ Hs ⋙ F₃)
    (σf : F₀ ⋙ PY ⟶ PX ⋙ F₂) (σf' : F₁ ⋙ PY' ⟶ PX' ⋙ F₃)
    (hr : σr = Functor.whiskerRight χ₀.hom Gr ≫
      compositeExchange J₀ R₀ J₁ R₁ Gr Hr Mr r βr ≫ Functor.whiskerLeft Hr χ₁.inv)
    (hs : σs = Functor.whiskerRight χ₂.hom Gs ≫
      compositeExchange J₂ R₂ J₃ R₃ Gs Hs Ms s βs ≫ Functor.whiskerLeft Hs χ₃.inv)
    (hf : σf = Functor.whiskerRight χ₀.hom PY ≫
      compositeExchange J₀ R₀ J₂ R₂ PY PX PM f βf ≫ Functor.whiskerLeft PX χ₂.inv)
    (hf' : σf' = Functor.whiskerRight χ₁.hom PY' ≫
      compositeExchange J₁ R₁ J₃ R₃ PY' PX' PM' f' βf' ≫ Functor.whiskerLeft PX' χ₃.inv) :
    Functor.whiskerRight σr PY' ≫ (Functor.associator Hr F₁ PY').hom ≫
      Functor.whiskerLeft Hr σf' ≫ (Functor.associator Hr PX' F₃).inv ≫
      Functor.whiskerRight top.inv F₃ ≫ (Functor.associator PX Hs F₃).hom =
    (Functor.associator F₀ Gr PY').hom ≫ Functor.whiskerLeft F₀ bottom.inv ≫
      (Functor.associator F₀ PY Gs).inv ≫ Functor.whiskerRight σf Gs ≫
      (Functor.associator PX F₂ Gs).hom ≫ Functor.whiskerLeft PX σs := by
  refine transport_exchange_cube_nt χ₀ χ₁ χ₂ χ₃ top bottom _ _ _ _
    σr σs σf σf' hr hs hf hf' ?_
  intro K
  exact composite_exchange_cube_aux J₀ R₀ J₁ R₁ J₂ R₂ J₃ R₃ Gr Hr Mr Gs Hs Ms
    PY PX PM PY' PX' PM' r s f f' βr βs βf βf' top middle bottom hp hb K

private theorem inverse_cube_eq {C : Type*} [Category C]
    {a b c d e f : C} (α : a ≅ b) (β : b ≅ c) (γ : c ≅ d)
    (δ : a ≅ e) (ε : e ≅ f) (ζ : f ≅ d)
    (h : α.hom ≫ β.hom ≫ γ.hom = δ.hom ≫ ε.hom ≫ ζ.hom) :
    γ.inv ≫ β.inv ≫ α.inv = ζ.inv ≫ ε.inv ≫ δ.inv := by
  have he : α ≪≫ β ≪≫ γ = δ ≪≫ ε ≪≫ ζ := Iso.ext h
  simpa only [Iso.trans_inv, Category.assoc] using
    congrArg (fun e : a ≅ d ↦ e.inv) he

private theorem beta_cube {X Y X' Y' A B A' B' : Scheme.{u}}
    {f : X ⟶ Y} {f' : X' ⟶ Y'} {g : A ⟶ B} {g' : A' ⟶ B'}
    {c : Compactification f} {c' : Compactification f'}
    {d : Compactification g} {d' : Compactification g'}
    {w : X' ⟶ X} {v : Y' ⟶ Y} {w₀ : A' ⟶ A} {v₀ : B' ⟶ B}
    {a : A ⟶ X} {b : B ⟶ Y} {a' : A' ⟶ X'} {b' : B' ⟶ Y'}
    [IsIso a] [IsIso b] [IsIso a'] [IsIso b']
    (front : Square c c' w v) (back : Square d d' w₀ v₀)
    (left : Square c d a b) (right : Square c' d' a' b')
    [IsIso left.middle] [IsIso right.middle]
    (top : CommSq a' w₀ w a)
    (middle : CommSq right.middle back.middle front.middle left.middle)
    (K : D Λ X) :
    (P Λ right.middle).map ((beta Λ front.openSquare).hom.app K) ≫
        (beta Λ right.openSquare).hom.app ((P Λ w).obj K) ≫
        (J Λ d'.i).map ((pullbackSquareComparison Λ top).inv.app K) =
      (pullbackSquareComparison Λ middle).inv.app ((J Λ c.i).obj K) ≫
        (P Λ back.middle).map ((beta Λ left.openSquare).hom.app K) ≫
        (beta Λ back.openSquare).hom.app ((P Λ a).obj K) := by
  simpa only [beta, Iso.app_hom, Iso.app_inv, Iso.symm_hom, Iso.symm_inv,
    Functor.mapIso_hom, Functor.mapIso_inv, asIso_hom] using inverse_cube_eq
    ((J Λ d'.i).mapIso ((pullbackSquareComparison Λ top).app K))
    ((beta Λ right.openSquare).symm.app ((P Λ w).obj K))
    ((P Λ right.middle).mapIso ((beta Λ front.openSquare).symm.app K))
    ((beta Λ back.openSquare).symm.app ((P Λ a).obj K))
    ((P Λ back.middle).mapIso ((beta Λ left.openSquare).symm.app K))
    ((pullbackSquareComparison Λ middle).app ((J Λ c.i).obj K))
    (by simpa only [beta, Iso.app_hom, Iso.app_inv, Iso.symm_hom, Iso.symm_inv,
      Functor.mapIso_hom, Functor.mapIso_inv, asIso_hom] using
        (open_cube Λ front.openSquare.toCommSq back.openSquare.toCommSq
          left.openSquare.toCommSq right.openSquare.toCommSq top middle K))

private theorem native_compact_cube_nt {X Y X' Y' A B A' B' : Scheme.{u}}
    {f : X ⟶ Y} {f' : X' ⟶ Y'} {g : A ⟶ B} {g' : A' ⟶ B'}
    {c : Compactification f} {c' : Compactification f'}
    {d : Compactification g} {d' : Compactification g'}
    {w : X' ⟶ X} {v : Y' ⟶ Y} {w₀ : A' ⟶ A} {v₀ : B' ⟶ B}
    {a : A ⟶ X} {b : B ⟶ Y} {a' : A' ⟶ X'} {b' : B' ⟶ Y'}
    [IsIso a] [IsIso b] [IsIso a'] [IsIso b']
    (front : Square c c' w v) (back : Square d d' w₀ v₀)
    (left : Square c d a b) (right : Square c' d' a' b')
    [IsIso left.middle] [IsIso right.middle]
    (top : CommSq a' w₀ w a) (bottom : CommSq b' v₀ v b)
    (middle : CommSq right.middle back.middle front.middle left.middle) :
    Functor.whiskerRight (squareExchange Λ front) (P Λ b') ≫
      (Functor.associator (P Λ w) (F Λ c') (P Λ b')).hom ≫
      Functor.whiskerLeft (P Λ w) (squareExchange Λ right) ≫
      (Functor.associator (P Λ w) (P Λ a') (F Λ d')).inv ≫
      Functor.whiskerRight (pullbackSquareComparison Λ top).inv (F Λ d') ≫
      (Functor.associator (P Λ a) (P Λ w₀) (F Λ d')).hom =
    (Functor.associator (F Λ c) (P Λ v) (P Λ b')).hom ≫
      Functor.whiskerLeft (F Λ c) (pullbackSquareComparison Λ bottom).inv ≫
      (Functor.associator (F Λ c) (P Λ b) (P Λ v₀)).inv ≫
      Functor.whiskerRight (squareExchange Λ left) (P Λ v₀) ≫
      (Functor.associator (P Λ a) (F Λ d) (P Λ v₀)).hom ≫
      Functor.whiskerLeft (P Λ a) (squareExchange Λ back) := by
  exact compact_cube_of_model
    (J Λ c.i) (R Λ c.g) (J Λ c'.i) (R Λ c'.g)
    (J Λ d.i) (R Λ d.g) (J Λ d'.i) (R Λ d'.g)
    (P Λ v) (P Λ w) (P Λ front.middle) (P Λ v₀) (P Λ w₀) (P Λ back.middle)
    (P Λ b) (P Λ a) (P Λ left.middle) (P Λ b') (P Λ a') (P Λ right.middle)
    (baseChangeMap Λ front.properSquare) (baseChangeMap Λ back.properSquare)
    (baseChangeMap Λ left.properSquare) (baseChangeMap Λ right.properSquare)
    (beta Λ front.openSquare) (beta Λ back.openSquare)
    (beta Λ left.openSquare) (beta Λ right.openSquare)
    (pullbackSquareComparison Λ top) (pullbackSquareComparison Λ middle)
    (pullbackSquareComparison Λ bottom)
    (fun N ↦ direct_cube Λ front.properSquare back.properSquare left.properSquare
      right.properSquare middle bottom N)
    (fun M ↦ beta_cube Λ front back left right top middle M)
    (F Λ c) (F Λ c') (F Λ d) (F Λ d')
    (modelIso Λ c) (modelIso Λ c') (modelIso Λ d) (modelIso Λ d')
    (squareExchange Λ front) (squareExchange Λ back)
    (squareExchange Λ left) (squareExchange Λ right)
    (square_exchange_model_comp Λ front) (square_exchange_model_comp Λ back)
    (square_exchange_model_comp Λ left) (square_exchange_model_comp Λ right)

/-- Compact-support exchanges in an isomorphism cube, even for a non-isomorphic face base.
Source: the source proof, paragraph 3
(blueprint: lem-fix-condensed-compactification-reindexing).
Proof: expand each compact exchange into its direct and open factors. Apply the
direct cube identity to the proper factors and the inverse open cube identity to
the open factors. Naturality moves the intermediate comparisons through proper
pushforward. The middle comparisons cancel, leaving exactly the two displayed routes. -/
theorem compact_cube {X Y X' Y' A B A' B' : Scheme.{u}}
    {f : X ⟶ Y} {f' : X' ⟶ Y'} {g : A ⟶ B} {g' : A' ⟶ B'}
    {c : Compactification f} {c' : Compactification f'}
    {d : Compactification g} {d' : Compactification g'}
    {w : X' ⟶ X} {v : Y' ⟶ Y} {w₀ : A' ⟶ A} {v₀ : B' ⟶ B}
    {a : A ⟶ X} {b : B ⟶ Y} {a' : A' ⟶ X'} {b' : B' ⟶ Y'}
    [IsIso a] [IsIso b] [IsIso a'] [IsIso b']
    (front : Square c c' w v) (back : Square d d' w₀ v₀)
    (left : Square c d a b) (right : Square c' d' a' b')
    [IsIso left.middle] [IsIso right.middle]
    (top : CommSq a' w₀ w a) (bottom : CommSq b' v₀ v b)
    (middle : CommSq right.middle back.middle front.middle left.middle)
    (K : D Λ X) :
    (P Λ b').map ((squareExchange Λ front).app K) ≫
        (squareExchange Λ right).app ((P Λ w).obj K) ≫
        (F Λ d').map ((pullbackSquareComparison Λ top).inv.app K) =
      (pullbackSquareComparison Λ bottom).inv.app ((F Λ c).obj K) ≫
        (P Λ v₀).map ((squareExchange Λ left).app K) ≫
        (squareExchange Λ back).app ((P Λ a).obj K) := by
  have h := congrArg (fun α : (F Λ c ⋙ P Λ v) ⋙ P Λ b' ⟶
      P Λ a ⋙ (P Λ w₀ ⋙ F Λ d') ↦ α.app K)
    (native_compact_cube_nt Λ front back left right top bottom middle)
  simpa only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_hom_app, Functor.associator_inv_app, Category.comp_id,
    Category.id_comp] using h

private theorem inverse_boundary_paste {C : Type*} [Category C]
    {a b c d e : C} (f : a ⟶ b) (g : b ⟶ c) (h : c ⟶ d) (i : e ≅ d)
    (j : a ⟶ e) (w : j = f ≫ g ≫ h ≫ i.inv) :
    f ≫ g ≫ h = j ≫ i.hom := by
  rw [w]
  simp (config := { dsimp := false }) only [Category.assoc, Iso.inv_hom_id, Category.comp_id]

private theorem exchangeRight_paste_of_comparison
    {A B A' B' A'' B'' : Type*}
    [Category A] [Category B] [Category A'] [Category B'] [Category A''] [Category B'']
    {Lf : B ⥤ A} {Rf : A ⥤ B} {Lf' : B' ⥤ A'} {Rf' : A' ⥤ B'}
    {Lf'' : B'' ⥤ A''} {Rf'' : A'' ⥤ B''}
    {G₁ : B ⥤ B'} {G₁' : A ⥤ A'} {G₂ : B' ⥤ B''} {G₂' : A' ⥤ A''}
    {G : B ⥤ B''} {G' : A ⥤ A''}
    (af : Lf ⊣ Rf) (af' : Lf' ⊣ Rf') (af'' : Lf'' ⊣ Rf'')
    (θ₁ : G₁ ⋙ Lf' ≅ Lf ⋙ G₁') (θ₂ : G₂ ⋙ Lf'' ≅ Lf' ⋙ G₂')
    (θ : G ⋙ Lf'' ≅ Lf ⋙ G') (c : G ≅ G₁ ⋙ G₂) (c' : G' ≅ G₁' ⋙ G₂')
    (h : ∀ N, θ.hom.app N = Lf''.map (c.hom.app N) ≫ θ₂.hom.app (G₁.obj N) ≫
      G₂'.map (θ₁.hom.app N) ≫ c'.inv.app (Lf.obj N)) (K : A) :
    c.hom.app (Rf.obj K) ≫ G₂.map ((af.exchangeRight af' θ₁).app K) ≫
        (af'.exchangeRight af'' θ₂).app (G₁'.obj K) =
      (af.exchangeRight af'' θ).app K ≫ Rf''.map (c'.hom.app K) := by
  apply Adjunction.exchangeRight_app_paste af af' af'' θ₁ θ₂ θ c c' _ K
  intro N
  have hh := inverse_boundary_paste
    (Lf''.map (c.hom.app N)) (θ₂.hom.app (G₁.obj N)) (G₂'.map (θ₁.hom.app N))
    (c'.app (Lf.obj N)) (θ.hom.app N) (h N)
  exact hh

private theorem exchangeRight_paste_nt
    {A B A' B' A'' B'' : Type*}
    [Category A] [Category B] [Category A'] [Category B'] [Category A''] [Category B'']
    {Lf : B ⥤ A} {Rf : A ⥤ B} {Lf' : B' ⥤ A'} {Rf' : A' ⥤ B'}
    {Lf'' : B'' ⥤ A''} {Rf'' : A'' ⥤ B''}
    {G₁ : B ⥤ B'} {G₁' : A ⥤ A'} {G₂ : B' ⥤ B''} {G₂' : A' ⥤ A''}
    {G : B ⥤ B''} {G' : A ⥤ A''}
    (af : Lf ⊣ Rf) (af' : Lf' ⊣ Rf') (af'' : Lf'' ⊣ Rf'')
    (θ₁ : G₁ ⋙ Lf' ≅ Lf ⋙ G₁') (θ₂ : G₂ ⋙ Lf'' ≅ Lf' ⋙ G₂')
    (θ : G ⋙ Lf'' ≅ Lf ⋙ G') (c : G ≅ G₁ ⋙ G₂) (c' : G' ≅ G₁' ⋙ G₂')
    (h : ∀ N, θ.hom.app N = Lf''.map (c.hom.app N) ≫ θ₂.hom.app (G₁.obj N) ≫
      G₂'.map (θ₁.hom.app N) ≫ c'.inv.app (Lf.obj N)) :
    Functor.whiskerLeft Rf c.hom ≫ (Functor.associator Rf G₁ G₂).inv ≫
      Functor.whiskerRight (af.exchangeRight af' θ₁) G₂ ≫
      (Functor.associator G₁' Rf' G₂).hom ≫
      Functor.whiskerLeft G₁' (af'.exchangeRight af'' θ₂) =
    (af.exchangeRight af'' θ) ≫ Functor.whiskerRight c'.hom Rf'' ≫
      (Functor.associator G₁' G₂' Rf'').hom := by
  refine NatTrans.ext (funext fun K ↦ ?_)
  simpa only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_hom_app, Functor.associator_inv_app, Category.comp_id,
    Category.id_comp] using exchangeRight_paste_of_comparison af af' af'' θ₁ θ₂ θ c c' h K

private theorem native_direct_paste_nt {X Y X' Y' X'' Y'' : Scheme.{u}}
    {f : X ⟶ Y} {f' : X' ⟶ Y'} {f'' : X'' ⟶ Y''}
    {w : X' ⟶ X} {v : Y' ⟶ Y} {w' : X'' ⟶ X'} {v' : Y'' ⟶ Y'}
    (s : CommSq w f' f v) (t : CommSq w' f'' f' v')
    (outer : CommSq (w' ≫ w) f'' f (v' ≫ v)) :
    Functor.whiskerLeft (R Λ f) (leftDerivedUpperStarComp Λ v' v).hom ≫
      (Functor.associator (R Λ f) (P Λ v) (P Λ v')).inv ≫
      Functor.whiskerRight (baseChangeMap Λ s) (P Λ v') ≫
      (Functor.associator (P Λ w) (R Λ f') (P Λ v')).hom ≫
      Functor.whiskerLeft (P Λ w) (baseChangeMap Λ t) =
    baseChangeMap Λ outer ≫
      Functor.whiskerRight (leftDerivedUpperStarComp Λ w' w).hom (R Λ f'') ≫
      (Functor.associator (P Λ w) (P Λ w') (R Λ f'')).hom := by
  have hp := pullbackSquareComparison_paste_vertical Λ s t
  rw [show t.horiz_comp s = outer from Subsingleton.elim _ _] at hp
  unfold baseChangeMap
  exact exchangeRight_paste_nt
    (derivedUpperStarLowerStarAdjunction Λ f)
    (derivedUpperStarLowerStarAdjunction Λ f')
    (derivedUpperStarLowerStarAdjunction Λ f'')
    (pullbackSquareComparison Λ s) (pullbackSquareComparison Λ t)
    (pullbackSquareComparison Λ outer) (leftDerivedUpperStarComp Λ v' v)
    (leftDerivedUpperStarComp Λ w' w) hp

/-- Direct exchange under vertical pasting, including identity and inverse squares.
Source: the source proof, paragraphs 1 and 3
(blueprint: lem-fix-condensed-compactification-reindexing).
Proof: the normalized comparison for the outer square is the paste of the two
pullback comparisons. The vertical mate-pasting law gives this equation, with the
native pullback compositors on the two boundaries. With identity edges these are
the native unit comparisons; pasting an isomorphism and its inverse therefore gives
mutually inverse exchanges. -/
theorem direct_paste {X Y X' Y' X'' Y'' : Scheme.{u}}
    {f : X ⟶ Y} {f' : X' ⟶ Y'} {f'' : X'' ⟶ Y''}
    {w : X' ⟶ X} {v : Y' ⟶ Y} {w' : X'' ⟶ X'} {v' : Y'' ⟶ Y'}
    (s : CommSq w f' f v) (t : CommSq w' f'' f' v')
    (outer : CommSq (w' ≫ w) f'' f (v' ≫ v)) (K : D Λ X) :
    (leftDerivedUpperStarComp Λ v' v).hom.app ((R Λ f).obj K) ≫
        (P Λ v').map ((baseChangeMap Λ s).app K) ≫
        (baseChangeMap Λ t).app ((P Λ w).obj K) =
      (baseChangeMap Λ outer).app K ≫
        (R Λ f'').map ((leftDerivedUpperStarComp Λ w' w).hom.app K) := by
  have h := congrArg (fun α : R Λ f ⋙ P Λ (v' ≫ v) ⟶
      P Λ w ⋙ (P Λ w' ⋙ R Λ f'') ↦ α.app K) (native_direct_paste_nt Λ s t outer)
  simpa only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_hom_app, Functor.associator_inv_app, Category.comp_id,
    Category.id_comp] using h

private theorem exchange_identity_aux {C D : Type*} [Category C] [Category D]
    {L : C ⥤ D} {R : D ⥤ C} (a : L ⊣ R)
    (G : C ⥤ C) (H : D ⥤ D) (e : G ≅ 𝟭 C) (d : H ≅ 𝟭 D)
    (θ : G ⋙ L ≅ L ⋙ H)
    (h : ∀ N, θ.hom.app N ≫ d.hom.app (L.obj N) = L.map (e.hom.app N)) (K : D) :
    (a.exchangeRight a θ).app K ≫ R.map (d.hom.app K) = e.hom.app (R.obj K) := by
  rw [Adjunction.exchangeRight_app, Category.assoc, Category.assoc, ← R.map_comp]
  rw [show H.map (a.counit.app K) ≫ d.hom.app K =
      d.hom.app (L.obj (R.obj K)) ≫ a.counit.app K from d.hom.naturality _]
  rw [← R.map_comp, ← Category.assoc, h, R.map_comp, ← Category.assoc]
  have hu := a.unit.naturality (e.hom.app (R.obj K))
  dsimp only [Functor.id_map, Functor.comp_map] at hu
  rw [← hu]
  simp only [Functor.id_obj, Category.assoc, a.right_triangle_components,
    Category.comp_id]

/-- Direct exchange on an identity square, with its actual identity comparisons.
Source: the source proof, paragraph 1
(blueprint: lem-fix-condensed-compactification-reindexing).
Proof: apply the mate identity law to the native square unit identity. The normalized
identity adjunction compares the remaining identity pullbacks with identity functors. -/
theorem direct_identity {X Y : Scheme.{u}} (f : X ⟶ Y) (K : D Λ X) :
    (baseChangeMap Λ (CommSq.mk
      ((Category.id_comp f).trans (Category.comp_id f).symm))).app K ≫
        (R Λ f).map ((leftDerivedUpperStarId Λ X).hom.app K) =
      (leftDerivedUpperStarId Λ Y).hom.app ((R Λ f).obj K) := by
  exact exchange_identity_aux (derivedUpperStarLowerStarAdjunction Λ f)
    (P Λ (𝟙 Y)) (P Λ (𝟙 X)) (leftDerivedUpperStarId Λ Y)
    (leftDerivedUpperStarId Λ X)
    (pullbackSquareComparison Λ (CommSq.mk
      ((Category.id_comp f).trans (Category.comp_id f).symm)))
    (pullbackSquareComparison_identity Λ f) K

private theorem mate_composition_aux
    {A B C A' B' C' : Type*}
    [Category A] [Category B] [Category C]
    [Category A'] [Category B'] [Category C']
    {L₁ : A ⥤ B} {R₁ : B ⥤ A} {L₂ : B ⥤ C} {R₂ : C ⥤ B}
    {L₁' : A' ⥤ B'} {R₁' : B' ⥤ A'} {L₂' : B' ⥤ C'} {R₂' : C' ⥤ B'}
    {L : A ⥤ C} {R : C ⥤ A} {L' : A' ⥤ C'} {R' : C' ⥤ A'}
    (a₁ : L₁ ⊣ R₁) (a₂ : L₂ ⊣ R₂) (a : L ⊣ R)
    (a₁' : L₁' ⊣ R₁') (a₂' : L₂' ⊣ R₂') (a' : L' ⊣ R')
    {G : A ⥤ A'} {H : B ⥤ B'} {K : C ⥤ C'}
    (θ₁ : TwoSquare G L₁ L₁' H) (θ₂ : TwoSquare H L₂ L₂' K)
    (θ : TwoSquare G L L' K) (c : L ≅ L₁ ⋙ L₂) (c' : L' ≅ L₁' ⋙ L₂')
    (h : θ.whiskerLeft c.hom = (TwoSquare.vComp θ₁ θ₂).whiskerRight c'.hom)
    (N : C) :
    G.map ((conjugateIsoEquiv (a₁.comp a₂) a c).inv.app N) ≫
        (mateEquiv a₁ a₁' θ₁).natTrans.app (R₂.obj N) ≫
        R₁'.map ((mateEquiv a₂ a₂' θ₂).natTrans.app N) ≫
        (conjugateIsoEquiv (a₁'.comp a₂') a' c').hom.app (K.obj N) =
      (mateEquiv a a' θ).natTrans.app N := by
  have hm := mateEquiv_whiskerTop_conjugateEquiv
    (a₁.comp a₂) a (a₁'.comp a₂') a' c.hom c'.hom (TwoSquare.vComp θ₁ θ₂) θ h
  rw [mateEquiv_hcomp a₁ a₁' a₂ a₂'] at hm
  have ht := congrArg (fun s ↦ s.natTrans.app N) hm
  apply (Iso.inv_comp_eq
    (G.mapIso ((conjugateIsoEquiv (a₁.comp a₂) a c).app N))).2
  simpa only [TwoSquare.whiskerTop, TwoSquare.whiskerBottom, TwoSquare.hComp,
    TwoSquare.mk, TwoSquare.natTrans, NatTrans.comp_app, Functor.whiskerRight_app,
    Functor.whiskerLeft_app, Functor.associator_hom_app, Functor.associator_inv_app,
    Category.id_comp, Category.comp_id, Category.assoc,
    Functor.mapIso_hom, Iso.app_hom, conjugateIsoEquiv_apply_hom] using ht.symm

private theorem exchangeRight_composition_of_comparison
    {A B C A' B' C' : Type*}
    [Category A] [Category B] [Category C]
    [Category A'] [Category B'] [Category C']
    {L₁ : A ⥤ B} {R₁ : B ⥤ A} {L₂ : B ⥤ C} {R₂ : C ⥤ B}
    {L₁' : A' ⥤ B'} {R₁' : B' ⥤ A'} {L₂' : B' ⥤ C'} {R₂' : C' ⥤ B'}
    {L : A ⥤ C} {R : C ⥤ A} {L' : A' ⥤ C'} {R' : C' ⥤ A'}
    (a₁ : L₁ ⊣ R₁) (a₂ : L₂ ⊣ R₂) (a : L ⊣ R)
    (a₁' : L₁' ⊣ R₁') (a₂' : L₂' ⊣ R₂') (a' : L' ⊣ R')
    {G : A ⥤ A'} {H : B ⥤ B'} {K : C ⥤ C'}
    (θ₁ : G ⋙ L₁' ≅ L₁ ⋙ H) (θ₂ : H ⋙ L₂' ≅ L₂ ⋙ K)
    (θ : G ⋙ L' ≅ L ⋙ K) (c : L ≅ L₁ ⋙ L₂) (c' : L' ≅ L₁' ⋙ L₂')
    (h : ∀ N, θ.hom.app N = c'.hom.app (G.obj N) ≫ L₂'.map (θ₁.hom.app N) ≫
      θ₂.hom.app (L₁.obj N) ≫ K.map (c.inv.app N)) (N : C) :
    G.map ((conjugateIsoEquiv (a₁.comp a₂) a c).inv.app N) ≫
        (a₁.exchangeRight a₁' θ₁).app (R₂.obj N) ≫
        R₁'.map ((a₂.exchangeRight a₂' θ₂).app N) ≫
        (conjugateIsoEquiv (a₁'.comp a₂') a' c').hom.app (K.obj N) =
      (a.exchangeRight a' θ).app N := by
  simp only [Adjunction.exchangeRight_eq_mateEquiv]
  apply mate_composition_aux a₁ a₂ a a₁' a₂' a'
    (TwoSquare.mk _ _ _ _ θ₁.hom) (TwoSquare.mk _ _ _ _ θ₂.hom)
    (TwoSquare.mk _ _ _ _ θ.hom) c c'
  ext M
  dsimp only [TwoSquare.whiskerLeft, TwoSquare.whiskerRight, TwoSquare.vComp,
    TwoSquare.mk, TwoSquare.natTrans, NatTrans.comp_app, Functor.whiskerRight_app,
    Functor.whiskerLeft_app, Functor.associator_hom_app, Functor.associator_inv_app]
  simp only [Category.id_comp, Category.comp_id]
  exact (inverse_boundary_paste (c'.hom.app (G.obj M)) (L₂'.map (θ₁.hom.app M))
    (θ₂.hom.app (L₁.obj M)) (K.mapIso (c.app M)) (θ.hom.app M) (h M)).symm

private theorem exchangeRight_composition_nt
    {A B C A' B' C' : Type*}
    [Category A] [Category B] [Category C]
    [Category A'] [Category B'] [Category C']
    {L₁ : A ⥤ B} {R₁ : B ⥤ A} {L₂ : B ⥤ C} {R₂ : C ⥤ B}
    {L₁' : A' ⥤ B'} {R₁' : B' ⥤ A'} {L₂' : B' ⥤ C'} {R₂' : C' ⥤ B'}
    {L : A ⥤ C} {R : C ⥤ A} {L' : A' ⥤ C'} {R' : C' ⥤ A'}
    (a₁ : L₁ ⊣ R₁) (a₂ : L₂ ⊣ R₂) (a : L ⊣ R)
    (a₁' : L₁' ⊣ R₁') (a₂' : L₂' ⊣ R₂') (a' : L' ⊣ R')
    {G : A ⥤ A'} {H : B ⥤ B'} {K : C ⥤ C'}
    (θ₁ : G ⋙ L₁' ≅ L₁ ⋙ H) (θ₂ : H ⋙ L₂' ≅ L₂ ⋙ K)
    (θ : G ⋙ L' ≅ L ⋙ K) (c : L ≅ L₁ ⋙ L₂) (c' : L' ≅ L₁' ⋙ L₂')
    (h : ∀ N, θ.hom.app N = c'.hom.app (G.obj N) ≫ L₂'.map (θ₁.hom.app N) ≫
      θ₂.hom.app (L₁.obj N) ≫ K.map (c.inv.app N)) :
    Functor.whiskerRight (conjugateIsoEquiv (a₁.comp a₂) a c).inv G ≫
      (Functor.associator R₂ R₁ G).hom ≫
      Functor.whiskerLeft R₂ (a₁.exchangeRight a₁' θ₁) ≫
      (Functor.associator R₂ H R₁').inv ≫
      Functor.whiskerRight (a₂.exchangeRight a₂' θ₂) R₁' ≫
      (Functor.associator K R₂' R₁').hom ≫
      Functor.whiskerLeft K (conjugateIsoEquiv (a₁'.comp a₂') a' c').hom =
    a.exchangeRight a' θ := by
  refine NatTrans.ext (funext fun N ↦ ?_)
  simpa only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_hom_app, Functor.associator_inv_app, Category.comp_id,
    Category.id_comp] using exchangeRight_composition_of_comparison
      a₁ a₂ a a₁' a₂' a' θ₁ θ₂ θ c c' h N

private theorem horizontal_comparison_nt_of_app
    {A B C A' B' C' : Type*}
    [Category A] [Category B] [Category C]
    [Category A'] [Category B'] [Category C']
    {L₁ : A ⥤ B} {L₂ : B ⥤ C} {L₁' : A' ⥤ B'} {L₂' : B' ⥤ C'}
    {L : A ⥤ C} {L' : A' ⥤ C'}
    {G : A ⥤ A'} {H : B ⥤ B'} {K : C ⥤ C'}
    (θ₁ : G ⋙ L₁' ≅ L₁ ⋙ H) (θ₂ : H ⋙ L₂' ≅ L₂ ⋙ K)
    (θ : G ⋙ L' ≅ L ⋙ K) (c : L ≅ L₁ ⋙ L₂) (c' : L' ≅ L₁' ⋙ L₂')
    (h : ∀ N, θ.hom.app N = c'.hom.app (G.obj N) ≫ L₂'.map (θ₁.hom.app N) ≫
      θ₂.hom.app (L₁.obj N) ≫ K.map (c.inv.app N)) :
    θ.hom = Functor.whiskerLeft G c'.hom ≫
      (Functor.associator G L₁' L₂').inv ≫ Functor.whiskerRight θ₁.hom L₂' ≫
      (Functor.associator L₁ H L₂').hom ≫ Functor.whiskerLeft L₁ θ₂.hom ≫
      (Functor.associator L₁ L₂ K).inv ≫ Functor.whiskerRight c.inv K := by
  refine NatTrans.ext (funext fun N ↦ ?_)
  simpa only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_hom_app, Functor.associator_inv_app, Category.comp_id,
    Category.id_comp] using h N

private theorem exchangeRight_composition_nt_from_nt
    {A B C A' B' C' : Type*}
    [Category A] [Category B] [Category C]
    [Category A'] [Category B'] [Category C']
    {L₁ : A ⥤ B} {R₁ : B ⥤ A} {L₂ : B ⥤ C} {R₂ : C ⥤ B}
    {L₁' : A' ⥤ B'} {R₁' : B' ⥤ A'} {L₂' : B' ⥤ C'} {R₂' : C' ⥤ B'}
    {L : A ⥤ C} {R : C ⥤ A} {L' : A' ⥤ C'} {R' : C' ⥤ A'}
    (a₁ : L₁ ⊣ R₁) (a₂ : L₂ ⊣ R₂) (a : L ⊣ R)
    (a₁' : L₁' ⊣ R₁') (a₂' : L₂' ⊣ R₂') (a' : L' ⊣ R')
    {G : A ⥤ A'} {H : B ⥤ B'} {K : C ⥤ C'}
    (θ₁ : G ⋙ L₁' ≅ L₁ ⋙ H) (θ₂ : H ⋙ L₂' ≅ L₂ ⋙ K)
    (θ : G ⋙ L' ≅ L ⋙ K) (c : L ≅ L₁ ⋙ L₂) (c' : L' ≅ L₁' ⋙ L₂')
    (h : θ.hom = Functor.whiskerLeft G c'.hom ≫
      (Functor.associator G L₁' L₂').inv ≫ Functor.whiskerRight θ₁.hom L₂' ≫
      (Functor.associator L₁ H L₂').hom ≫ Functor.whiskerLeft L₁ θ₂.hom ≫
      (Functor.associator L₁ L₂ K).inv ≫ Functor.whiskerRight c.inv K) :
    Functor.whiskerRight (conjugateIsoEquiv (a₁.comp a₂) a c).inv G ≫
      (Functor.associator R₂ R₁ G).hom ≫
      Functor.whiskerLeft R₂ (a₁.exchangeRight a₁' θ₁) ≫
      (Functor.associator R₂ H R₁').inv ≫
      Functor.whiskerRight (a₂.exchangeRight a₂' θ₂) R₁' ≫
      (Functor.associator K R₂' R₁').hom ≫
      Functor.whiskerLeft K (conjugateIsoEquiv (a₁'.comp a₂') a' c').hom =
    a.exchangeRight a' θ := by
  apply exchangeRight_composition_nt a₁ a₂ a a₁' a₂' a' θ₁ θ₂ θ c c'
  intro N
  have hn := congrArg (fun α ↦ α.app N) h
  simpa only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_hom_app, Functor.associator_inv_app, Category.comp_id,
    Category.id_comp] using hn

private theorem native_horizontal_comparison_nt {X Y Z X' Y' Z' : Scheme.{u}}
    {f : X ⟶ Y} {g : Y ⟶ Z} {f' : X' ⟶ Y'} {g' : Y' ⟶ Z'}
    {a : X' ⟶ X} {b : Y' ⟶ Y} {d : Z' ⟶ Z}
    (s : CommSq a f' f b) (t : CommSq b g' g d)
    (outer : CommSq a (f' ≫ g') (f ≫ g) d) :
    (pullbackSquareComparison Λ outer).hom =
      Functor.whiskerLeft (P Λ d) (leftDerivedUpperStarComp Λ f' g').hom ≫
      (Functor.associator (P Λ d) (P Λ g') (P Λ f')).inv ≫
      Functor.whiskerRight (pullbackSquareComparison Λ t).hom (P Λ f') ≫
      (Functor.associator (P Λ g) (P Λ b) (P Λ f')).hom ≫
      Functor.whiskerLeft (P Λ g) (pullbackSquareComparison Λ s).hom ≫
      (Functor.associator (P Λ g) (P Λ f) (P Λ a)).inv ≫
      Functor.whiskerRight (leftDerivedUpperStarComp Λ f g).inv (P Λ a) := by
  have hp := pullbackSquareComparison_paste_horizontal Λ s t
  rw [show s.vert_comp t = outer from Subsingleton.elim _ _] at hp
  exact horizontal_comparison_nt_of_app
    (pullbackSquareComparison Λ t) (pullbackSquareComparison Λ s)
    (pullbackSquareComparison Λ outer) (leftDerivedUpperStarComp Λ f g)
    (leftDerivedUpperStarComp Λ f' g') hp

private theorem native_direct_composition_nt {X Y Z X' Y' Z' : Scheme.{u}}
    {f : X ⟶ Y} {g : Y ⟶ Z} {f' : X' ⟶ Y'} {g' : Y' ⟶ Z'}
    {a : X' ⟶ X} {b : Y' ⟶ Y} {d : Z' ⟶ Z}
    (s : CommSq a f' f b) (t : CommSq b g' g d)
    (outer : CommSq a (f' ≫ g') (f ≫ g) d) :
    Functor.whiskerRight (rightDerivedLowerStarComp Λ f g).inv (P Λ d) ≫
      (Functor.associator (R Λ f) (R Λ g) (P Λ d)).hom ≫
      Functor.whiskerLeft (R Λ f) (baseChangeMap Λ t) ≫
      (Functor.associator (R Λ f) (P Λ b) (R Λ g')).inv ≫
      Functor.whiskerRight (baseChangeMap Λ s) (R Λ g') ≫
      (Functor.associator (P Λ a) (R Λ f') (R Λ g')).hom ≫
      Functor.whiskerLeft (P Λ a) (rightDerivedLowerStarComp Λ f' g').hom =
    baseChangeMap Λ outer := by
  unfold baseChangeMap rightDerivedLowerStarComp
  exact exchangeRight_composition_nt_from_nt
    (derivedUpperStarLowerStarAdjunction Λ g) (derivedUpperStarLowerStarAdjunction Λ f)
    (derivedUpperStarLowerStarAdjunction Λ (f ≫ g))
    (derivedUpperStarLowerStarAdjunction Λ g') (derivedUpperStarLowerStarAdjunction Λ f')
    (derivedUpperStarLowerStarAdjunction Λ (f' ≫ g'))
    (pullbackSquareComparison Λ t) (pullbackSquareComparison Λ s)
    (pullbackSquareComparison Λ outer) (leftDerivedUpperStarComp Λ f g)
    (leftDerivedUpperStarComp Λ f' g')
    (native_horizontal_comparison_nt Λ s t outer)

/-- Pasting in the direct-image direction uses the canonical inverse-conjugate compositor.
Source: the source proof, paragraph 3
(blueprint: lem-fix-condensed-compactification-reindexing).
Proof: horizontal pullback pasting gives the common left-adjoint comparison. Its
mates under the composite adjunction are equal. The right-adjoint comparison in this
direction is the native `rightDerivedLowerStarComp`, the conjugate of the left
compositor, and not the conjugate of its inverse. -/
theorem direct_composition {X Y Z X' Y' Z' : Scheme.{u}}
    {f : X ⟶ Y} {g : Y ⟶ Z} {f' : X' ⟶ Y'} {g' : Y' ⟶ Z'}
    {a : X' ⟶ X} {b : Y' ⟶ Y} {d : Z' ⟶ Z}
    (s : CommSq a f' f b) (t : CommSq b g' g d)
    (outer : CommSq a (f' ≫ g') (f ≫ g) d) (K : D Λ X) :
    (P Λ d).map ((rightDerivedLowerStarComp Λ f g).inv.app K) ≫
        (baseChangeMap Λ t).app ((R Λ f).obj K) ≫
        (R Λ g').map ((baseChangeMap Λ s).app K) ≫
        (rightDerivedLowerStarComp Λ f' g').hom.app ((P Λ a).obj K) =
      (baseChangeMap Λ outer).app K := by
  have h := congrArg (fun α : R Λ (f ≫ g) ⋙ P Λ d ⟶
      P Λ a ⋙ R Λ (f' ≫ g') ↦ α.app K) (native_direct_composition_nt Λ s t outer)
  simpa only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_hom_app, Functor.associator_inv_app, Category.comp_id,
    Category.id_comp] using h

/-- The literal pullback of the ambient map of a refinement.
Source: the source proof, paragraph 3
(blueprint: lem-fix-condensed-compactification-reindexing). -/
def refinementBaseMap {X Y Y' : Scheme.{u}} {f : X ⟶ Y}
    {c₁ c₂ : Compactification f} (u : c₁.Refinement c₂) (v : Y' ⟶ Y) :
    (c₁.baseChange v).Z ⟶ (c₂.baseChange v).Z :=
  pullback.lift (pullback.fst c₁.g v ≫ u.hom) (pullback.snd c₁.g v)
    (by rw [Category.assoc, u.hom_g, pullback.condition])

/-- The pulled-back ambient map obeys both refinement triangles.
Source: the source proof, paragraph 3
(blueprint: lem-fix-condensed-compactification-reindexing).
Proof: compose each triangle with the two pullback projections. The first projection
uses the original refinement triangle and the second is the identity over the base.
The universal property of the pullback gives the required equality. -/
theorem refinementBaseMap_triangles {X Y Y' : Scheme.{u}} {f : X ⟶ Y}
    {c₁ c₂ : Compactification f} (u : c₁.Refinement c₂) (v : Y' ⟶ Y) :
    (c₁.baseChange v).i ≫ refinementBaseMap u v = (c₂.baseChange v).i ∧
      refinementBaseMap u v ≫ (c₂.baseChange v).g = (c₁.baseChange v).g := by
  constructor
  · apply pullback.hom_ext
    · simp [refinementBaseMap, Category.assoc, u.i_hom]
    · simp [refinementBaseMap, Category.assoc]
  · simp [refinementBaseMap]

/-- Base change of a proper refinement, without a boundary-preservation condition.
Source: the source proof, paragraph 3
(blueprint: lem-fix-condensed-compactification-reindexing). -/
def refinementBaseChange {X Y Y' : Scheme.{u}} {f : X ⟶ Y}
    {c₁ c₂ : Compactification f} (u : c₁.Refinement c₂) (v : Y' ⟶ Y) :
    (c₁.baseChange v).Refinement (c₂.baseChange v) where
  hom := refinementBaseMap u v
  i_hom := (refinementBaseMap_triangles u v).1
  hom_g := (refinementBaseMap_triangles u v).2

/-- Identity and composition of refinements on the entire ambient category.
Source: the source proof, paragraphs 1 and 3
(blueprint: lem-fix-condensed-compactification-reindexing).
Proof: under the open adjunction the defining map restricts to identity. For an
identity refinement its clopen projector is identity. For two successive refinements,
pasting and the adjunction triangles identify the composite transpose with the same
normalized map for their composite. Uniqueness under the open Hom bijection gives
both equations, and direct-image associativity gives the final support equations. -/
theorem refinement_id_comp {X Y : Scheme.{u}} {f : X ⟶ Y}
    (c : Compactification f) {c₀ c₁ c₂ : Compactification f}
    (z : c₀.Refinement c₁) (u : c₁.Refinement c₂) :
    refinement Λ (Compactification.Refinement.id c) = 𝟙 (F Λ c) ∧
      refinement Λ (z.comp u) = refinement Λ u ≫ refinement Λ z := by
  sorry

set_option maxHeartbeats 1600000 in
-- The endpoints of the native derived adjunctions require additional unification time.
/-- A common-refinement comparison, using only inverses of refinement components.
Source: the source proof, paragraph 1
(blueprint: lem-fix-condensed-compactification-reindexing). -/
@[irreducible] def comparison {X Y : Scheme.{u}} {f : X ⟶ Y}
    {c₁ c₂ d : Compactification f} (h₁ : d.Refinement c₁) (h₂ : d.Refinement c₂)
    (K : D Λ X) [h₁iso : IsIso ((refinement Λ h₁).app K)]
    [h₂iso : IsIso ((refinement Λ h₂).app K)] : (F Λ c₁).obj K ≅ (F Λ c₂).obj K :=
  @asIso _ _ _ _ ((refinement Λ h₁).app K) h₁iso ≪≫
    (@asIso _ _ _ _ ((refinement Λ h₂).app K) h₂iso).symm

/-- All rational bounded-constructible refinement components are invertible.
No positive-characteristic or absolute-separatedness hypothesis is present.
Source: the source proof, paragraph 1; the node's rational boundary argument
(blueprint: lem-fix-condensed-compactification-reindexing).
Proof: over the target open the adjoint refinement is identity by clopen counit
cancellation. On its closed complement both sides vanish: proper base change for
the rational coefficients identifies the target restriction with direct image of a
restriction disjoint from the source open. Open and closed restriction detect
isomorphisms. Proper direct image and its compositor preserve this isomorphism.
The finite-subextension-valued algebraic-closure case follows by finite coefficient
field descent; the finite-extension case is the rational proper base-change theorem. -/
theorem rational_refinement_isIso (ℓ : ℕ) [Fact ℓ.Prime]
    (hΛ : Mon.mk Λ = Mon.mk (Profinite.padicAlgClRingObj.{u} ℓ) ∨
      ∃ E : PadicAlgCl.FiniteIntermediateField ℓ,
        Mon.mk Λ = Mon.mk (Profinite.continuousMapRingObj.{u} E.1))
    (k : Type u) [Field k] [Fact (ringChar k ≠ ℓ)]
    {X Y : Scheme.{u}} [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
    {f : X ⟶ Y} [f.IsOver (Spec (.of k))]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    {c₁ c₂ : Compactification f} (u : c₁.Refinement c₂)
    (K : D Λ X) (hK : boundedConstructible (condensedRingObj Λ X) K) :
    IsIso ((refinement Λ u).app K) := by
  sorry

/-- The property comparison with the native coefficient categories fixed.
Source: the source proof, paragraphs 1 and 3
(blueprint: lem-fix-condensed-compactification-reindexing).
Proof: specialize the preceding property comparison to bounded constructible
objects. Keep the functor family arbitrary during this specialization, and supply
its refinement composition and ambient invertibility hypotheses directly. The
optional default fixes the native category parameters while leaving the family
arbitrary. -/
private theorem comparison_native_family {X Y : Scheme.{u}} {f : X ⟶ Y} [QuasiCompact f]
    (G : _ := fun (c : Compactification f) ↦ F (A := X) (B := Y) (f := f) Λ c)
    (ρ : ∀ {a b : Compactification f}, (a ⟶ b) → (G b ⟶ G a))
    (hc : ∀ {a b c : Compactification f} (r : a ⟶ b) (t : b ⟶ c),
      ρ (r ≫ t) = ρ t ≫ ρ r)
    (hi : ∀ {a b : Compactification f} (r : a ⟶ b) (K : D Λ X),
      boundedConstructible (condensedRingObj Λ X) K → IsIso ((ρ r).app K)) :
    ∃ τ : ∀ c₁ c₂ : Compactification f,
        (boundedConstructible (condensedRingObj Λ X)).ι ⋙ G c₁ ≅
          (boundedConstructible (condensedRingObj Λ X)).ι ⋙ G c₂,
      (∀ (c₁ c₂ d : Compactification f) (h₁ : d.Refinement c₁)
          (h₂ : d.Refinement c₂) (K : BoundedConstructible (condensedRingObj Λ X)),
        (τ c₁ c₂).hom.app K ≫ (ρ h₂).app K.obj =
          (ρ h₁).app K.obj) ∧
      (∀ c : Compactification f, τ c c = Iso.refl _) ∧
      (∀ c₁ c₂ c₃ : Compactification f, τ c₁ c₂ ≪≫ τ c₂ c₃ = τ c₁ c₃) ∧
      (∀ σ : ∀ c₁ c₂ : Compactification f,
          (boundedConstructible (condensedRingObj Λ X)).ι ⋙ G c₁ ≅
            (boundedConstructible (condensedRingObj Λ X)).ι ⋙ G c₂,
        (∀ (c₁ c₂ d : Compactification f) (h₁ : d.Refinement c₁)
            (h₂ : d.Refinement c₂) (K : BoundedConstructible (condensedRingObj Λ X)),
          (σ c₁ c₂).hom.app K ≫ (ρ h₂).app K.obj =
            (ρ h₁).app K.obj) → σ = τ) := by
  exact comparison_on_property f (boundedConstructible (condensedRingObj Λ X))
    G (@ρ) (@hc) (@hi)

/-- Independence, identity and cocycle of common-refinement comparisons, including
naturality in the original bounded constructible full subcategory.
Source: the source proof, paragraphs 1 and 3
(blueprint: lem-fix-condensed-compactification-reindexing).
Proof: the category of compactifications has common refinements and equalizers of
parallel refinement maps. Apply the ambient composition law and cancel invertible
rational refinement components on bounded constructible inputs. This proves
independence of the common refinement. Identity, cocycle and naturality follow by
doing all comparisons over one further common refinement. This uses no density
condition on any supplied compactification or refinement. -/
theorem condensed_compactification_reindexing (ℓ : ℕ) [Fact ℓ.Prime]
    (hΛ : Mon.mk Λ = Mon.mk (Profinite.padicAlgClRingObj.{u} ℓ) ∨
      ∃ E : PadicAlgCl.FiniteIntermediateField ℓ,
        Mon.mk Λ = Mon.mk (Profinite.continuousMapRingObj.{u} E.1))
    (k : Type u) [Field k] [Fact (ringChar k ≠ ℓ)]
    {X Y : Scheme.{u}} [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of k))]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f] :
    ∃ τ : ∀ c₁ c₂ : Compactification f,
        (boundedConstructible (condensedRingObj Λ X)).ι ⋙ F Λ c₁ ≅
          (boundedConstructible (condensedRingObj Λ X)).ι ⋙ F Λ c₂,
      (∀ (c₁ c₂ d : Compactification f) (h₁ : d.Refinement c₁)
          (h₂ : d.Refinement c₂) (K : BoundedConstructible (condensedRingObj Λ X)),
        (τ c₁ c₂).hom.app K ≫ (refinement Λ h₂).app K.obj =
          (refinement Λ h₁).app K.obj) ∧
      (∀ c : Compactification f, τ c c = Iso.refl _) ∧
      (∀ c₁ c₂ c₃ : Compactification f, τ c₁ c₂ ≪≫ τ c₂ c₃ = τ c₁ c₃) ∧
      (∀ σ : ∀ c₁ c₂ : Compactification f,
          (boundedConstructible (condensedRingObj Λ X)).ι ⋙ F Λ c₁ ≅
            (boundedConstructible (condensedRingObj Λ X)).ι ⋙ F Λ c₂,
        (∀ (c₁ c₂ d : Compactification f) (h₁ : d.Refinement c₁)
            (h₂ : d.Refinement c₂) (K : BoundedConstructible (condensedRingObj Λ X)),
          (σ c₁ c₂).hom.app K ≫ (refinement Λ h₂).app K.obj =
            (refinement Λ h₁).app K.obj) → σ = τ) := by
  let G := fun (c : Compactification f) ↦ F (A := X) (B := Y) (f := f) Λ c
  let ρ := fun {a b : Compactification f} (r : a ⟶ b) ↦
    refinement (X := X) (Y := Y) (f := f) (c₁ := a) (c₂ := b) Λ r
  have hc {a b c : Compactification f} (r : a ⟶ b) (s : b ⟶ c) :
      @ρ a c (r ≫ s) = @ρ b c s ≫ @ρ a b r :=
    (refinement_id_comp Λ (f := f) a (c₀ := a) (c₁ := b) (c₂ := c) r s).2
  have hi {a b : Compactification f} (r : a ⟶ b) (K : D Λ X)
      (hK : boundedConstructible (condensedRingObj Λ X) K) :
      IsIso ((@ρ a b r).app K) :=
    rational_refinement_isIso Λ ℓ hΛ k (X := X) (Y := Y) (f := f)
      (c₁ := a) (c₂ := b) r K hK
  exact comparison_native_family Λ (f := f) G (@ρ) (@hc) (@hi)

private theorem inverse_mate_paste_aux
    {A B C D E F : Type*} [Category A] [Category B] [Category C]
    [Category D] [Category E] [Category F]
    {L₁ : A ⥤ B} {R₁ : B ⥤ A} {L₂ : C ⥤ D} {R₂ : D ⥤ C}
    {L₃ : E ⥤ F} {R₃ : F ⥤ E}
    (a₁ : L₁ ⊣ R₁) (a₂ : L₂ ⊣ R₂) (a₃ : L₃ ⊣ R₃)
    {G₁ : A ⥤ C} {G₂ : C ⥤ E} {H₁ : B ⥤ D} {H₂ : D ⥤ F}
    {G : A ⥤ E} {H : B ⥤ F}
    (b₁ : R₁ ⋙ G₁ ⟶ H₁ ⋙ R₂) (b₂ : R₂ ⋙ G₂ ⟶ H₂ ⋙ R₃)
    (b : R₁ ⋙ G ⟶ H ⋙ R₃) (c : G ≅ G₁ ⋙ G₂) (d : H ≅ H₁ ⋙ H₂)
    (h : ∀ N, c.hom.app (R₁.obj N) ≫ G₂.map (b₁.app N) ≫ b₂.app (H₁.obj N) =
      b.app N ≫ R₃.map (d.hom.app N)) (K : A) :
    ((mateEquiv a₂ a₃).symm (TwoSquare.mk _ _ _ _ b₂)).natTrans.app (G₁.obj K) ≫
        H₂.map (((mateEquiv a₁ a₂).symm (TwoSquare.mk _ _ _ _ b₁)).natTrans.app K) =
      L₃.map (c.inv.app K) ≫ ((mateEquiv a₁ a₃).symm (TwoSquare.mk _ _ _ _ b)).natTrans.app K ≫
        d.hom.app (L₁.obj K) := by
  let α := (mateEquiv a₁ a₂).symm (TwoSquare.mk _ _ _ _ b₁)
  let β := (mateEquiv a₂ a₃).symm (TwoSquare.mk _ _ _ _ b₂)
  let γ := (mateEquiv a₁ a₃).symm (TwoSquare.mk _ _ _ _ b)
  have he : TwoSquare.hComp α β = (γ.whiskerTop c.inv).whiskerBottom d.hom := by
    apply (mateEquiv a₁ a₃).injective
    rw [mateEquiv_vcomp a₁ a₂ a₃, mateEquiv_whiskerTop_whiskerBottom]
    simp only [α, β, γ, Equiv.apply_symm_apply]
    ext N
    dsimp only [TwoSquare.vComp, TwoSquare.whiskerRight, TwoSquare.whiskerLeft,
      TwoSquare.mk, TwoSquare.natTrans, NatTrans.comp_app, Functor.whiskerRight_app,
      Functor.whiskerLeft_app, Functor.associator_hom_app, Functor.associator_inv_app]
    simp only [Category.id_comp, Category.comp_id]
    apply (cancel_epi (c.hom.app (R₁.obj N))).1
    simpa only [Category.assoc, Iso.hom_inv_id_app_assoc] using h N
  have := congrArg (fun s ↦ s.natTrans.app K) he
  simpa only [α, β, γ, TwoSquare.hComp, TwoSquare.whiskerTop, TwoSquare.whiskerBottom,
    TwoSquare.mk, TwoSquare.natTrans, NatTrans.comp_app, Functor.whiskerRight_app,
    Functor.whiskerLeft_app, Functor.associator_hom_app, Functor.associator_inv_app,
    Category.id_comp, Category.comp_id, Category.assoc] using this

private theorem inverse_mate_paste_of_comparison
    {A B C D E F : Type*} [Category A] [Category B] [Category C]
    [Category D] [Category E] [Category F]
    {L₁ : A ⥤ B} {R₁ : B ⥤ A} {L₂ : C ⥤ D} {R₂ : D ⥤ C}
    {L₃ : E ⥤ F} {R₃ : F ⥤ E}
    (a₁ : L₁ ⊣ R₁) (a₂ : L₂ ⊣ R₂) (a₃ : L₃ ⊣ R₃)
    {G₁ : A ⥤ C} {G₂ : C ⥤ E} {H₁ : B ⥤ D} {H₂ : D ⥤ F}
    {G : A ⥤ E} {H : B ⥤ F}
    (θ₁ : R₁ ⋙ G₁ ≅ H₁ ⋙ R₂) (θ₂ : R₂ ⋙ G₂ ≅ H₂ ⋙ R₃)
    (θ : R₁ ⋙ G ≅ H ⋙ R₃) (c : G ≅ G₁ ⋙ G₂) (d : H ≅ H₁ ⋙ H₂)
    (h : ∀ N, θ.hom.app N = c.hom.app (R₁.obj N) ≫ G₂.map (θ₁.hom.app N) ≫
      θ₂.hom.app (H₁.obj N) ≫ R₃.map (d.inv.app N)) (K : A) :
    ((mateEquiv a₂ a₃).symm (TwoSquare.mk _ _ _ _ θ₂.hom)).natTrans.app (G₁.obj K) ≫
        H₂.map (((mateEquiv a₁ a₂).symm
          (TwoSquare.mk _ _ _ _ θ₁.hom)).natTrans.app K) =
      L₃.map (c.inv.app K) ≫
        ((mateEquiv a₁ a₃).symm (TwoSquare.mk _ _ _ _ θ.hom)).natTrans.app K ≫
        d.hom.app (L₁.obj K) := by
  apply inverse_mate_paste_aux a₁ a₂ a₃ θ₁.hom θ₂.hom θ.hom c d _ K
  intro N
  have hh := inverse_boundary_paste (c.hom.app (R₁.obj N))
    (G₂.map (θ₁.hom.app N)) (θ₂.hom.app (H₁.obj N))
    (R₃.mapIso (d.app N)) (θ.hom.app N) (h N)
  exact hh

private theorem inverse_mate_paste_nt
    {A B C D E F : Type*} [Category A] [Category B] [Category C]
    [Category D] [Category E] [Category F]
    {L₁ : A ⥤ B} {R₁ : B ⥤ A} {L₂ : C ⥤ D} {R₂ : D ⥤ C}
    {L₃ : E ⥤ F} {R₃ : F ⥤ E}
    (a₁ : L₁ ⊣ R₁) (a₂ : L₂ ⊣ R₂) (a₃ : L₃ ⊣ R₃)
    {G₁ : A ⥤ C} {G₂ : C ⥤ E} {H₁ : B ⥤ D} {H₂ : D ⥤ F}
    {G : A ⥤ E} {H : B ⥤ F}
    (θ₁ : R₁ ⋙ G₁ ≅ H₁ ⋙ R₂) (θ₂ : R₂ ⋙ G₂ ≅ H₂ ⋙ R₃)
    (θ : R₁ ⋙ G ≅ H ⋙ R₃) (c : G ≅ G₁ ⋙ G₂) (d : H ≅ H₁ ⋙ H₂)
    (h : ∀ N, θ.hom.app N = c.hom.app (R₁.obj N) ≫ G₂.map (θ₁.hom.app N) ≫
      θ₂.hom.app (H₁.obj N) ≫ R₃.map (d.inv.app N)) :
    Functor.whiskerLeft G₁
        ((mateEquiv a₂ a₃).symm (TwoSquare.mk _ _ _ _ θ₂.hom)).natTrans ≫
      (Functor.associator G₁ L₂ H₂).inv ≫
      Functor.whiskerRight
        ((mateEquiv a₁ a₂).symm (TwoSquare.mk _ _ _ _ θ₁.hom)).natTrans H₂ ≫
      (Functor.associator L₁ H₁ H₂).hom =
    (Functor.associator G₁ G₂ L₃).inv ≫ Functor.whiskerRight c.inv L₃ ≫
      ((mateEquiv a₁ a₃).symm (TwoSquare.mk _ _ _ _ θ.hom)).natTrans ≫
      Functor.whiskerLeft L₁ d.hom := by
  refine NatTrans.ext (funext fun K ↦ ?_)
  simpa only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_hom_app, Functor.associator_inv_app, Category.comp_id,
    Category.id_comp] using inverse_mate_paste_of_comparison a₁ a₂ a₃ θ₁ θ₂ θ c d h K

private theorem inverse_mate_paste_nt_from_nt
    {A B C D E F : Type*} [Category A] [Category B] [Category C]
    [Category D] [Category E] [Category F]
    {L₁ : A ⥤ B} {R₁ : B ⥤ A} {L₂ : C ⥤ D} {R₂ : D ⥤ C}
    {L₃ : E ⥤ F} {R₃ : F ⥤ E}
    (a₁ : L₁ ⊣ R₁) (a₂ : L₂ ⊣ R₂) (a₃ : L₃ ⊣ R₃)
    {G₁ : A ⥤ C} {G₂ : C ⥤ E} {H₁ : B ⥤ D} {H₂ : D ⥤ F}
    {G : A ⥤ E} {H : B ⥤ F}
    (θ₁ : R₁ ⋙ G₁ ≅ H₁ ⋙ R₂) (θ₂ : R₂ ⋙ G₂ ≅ H₂ ⋙ R₃)
    (θ : R₁ ⋙ G ≅ H ⋙ R₃) (c : G ≅ G₁ ⋙ G₂) (d : H ≅ H₁ ⋙ H₂)
    (h : θ.hom = Functor.whiskerLeft R₁ c.hom ≫
      (Functor.associator R₁ G₁ G₂).inv ≫ Functor.whiskerRight θ₁.hom G₂ ≫
      (Functor.associator H₁ R₂ G₂).hom ≫ Functor.whiskerLeft H₁ θ₂.hom ≫
      (Functor.associator H₁ H₂ R₃).inv ≫ Functor.whiskerRight d.inv R₃) :
    Functor.whiskerLeft G₁
        ((mateEquiv a₂ a₃).symm (TwoSquare.mk _ _ _ _ θ₂.hom)).natTrans ≫
      (Functor.associator G₁ L₂ H₂).inv ≫
      Functor.whiskerRight
        ((mateEquiv a₁ a₂).symm (TwoSquare.mk _ _ _ _ θ₁.hom)).natTrans H₂ ≫
      (Functor.associator L₁ H₁ H₂).hom =
    (Functor.associator G₁ G₂ L₃).inv ≫ Functor.whiskerRight c.inv L₃ ≫
      ((mateEquiv a₁ a₃).symm (TwoSquare.mk _ _ _ _ θ.hom)).natTrans ≫
      Functor.whiskerLeft L₁ d.hom := by
  apply inverse_mate_paste_nt a₁ a₂ a₃ θ₁ θ₂ θ c d
  intro N
  have hn := congrArg (fun α ↦ α.app N) h
  simpa only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_hom_app, Functor.associator_inv_app, Category.comp_id,
    Category.id_comp] using hn

/-- The open inverse mate respects vertical pasting, with native boundary compositors.
Source: the source proof, paragraphs 1 and 3
(blueprint: lem-fix-condensed-compactification-reindexing).
Proof: apply open-adjunction mate pasting to native pullback square pasting. The two
boundary comparisons are precisely the pullback compositors displayed here. This
also determines pasting for beta by inversion on Cartesian squares. -/
private theorem native_open_paste_nt {X Y X' Y' X'' Y'' : Scheme.{u}}
    {j : X ⟶ Y} {j' : X' ⟶ Y'} {j'' : X'' ⟶ Y''}
    [IsOpenImmersion j] [IsOpenImmersion j'] [IsOpenImmersion j'']
    {w : X' ⟶ X} {v : Y' ⟶ Y} {w' : X'' ⟶ X'} {v' : Y'' ⟶ Y'}
    (s : CommSq w j' j v) (t : CommSq w' j'' j' v')
    (outer : CommSq (w' ≫ w) j'' j (v' ≫ v)) :
    Functor.whiskerLeft (P Λ w) (openMate Λ t) ≫
      (Functor.associator (P Λ w) (J Λ j') (P Λ v')).inv ≫
      Functor.whiskerRight (openMate Λ s) (P Λ v') ≫
      (Functor.associator (J Λ j) (P Λ v) (P Λ v')).hom =
    (Functor.associator (P Λ w) (P Λ w') (J Λ j'')).inv ≫
      Functor.whiskerRight (leftDerivedUpperStarComp Λ w' w).inv (J Λ j'') ≫
      openMate Λ outer ≫
      Functor.whiskerLeft (J Λ j) (leftDerivedUpperStarComp Λ v' v).hom := by
  have hp := native_horizontal_comparison_nt Λ t.flip s.flip outer.flip
  rw [pullbackSquareComparison_flip Λ s, pullbackSquareComparison_flip Λ t,
    pullbackSquareComparison_flip Λ outer] at hp
  unfold openMate
  exact inverse_mate_paste_nt_from_nt (oa Λ j) (oa Λ j') (oa Λ j'')
    (pullbackSquareComparison Λ s).symm (pullbackSquareComparison Λ t).symm
    (pullbackSquareComparison Λ outer).symm
    (leftDerivedUpperStarComp Λ w' w) (leftDerivedUpperStarComp Λ v' v) hp

/-- The open inverse mate respects vertical pasting, with native boundary compositors.
Source: the source proof, paragraphs 1 and 3
(blueprint: lem-fix-condensed-compactification-reindexing).
Proof: apply open-adjunction mate pasting to native pullback square pasting. The two
boundary comparisons are precisely the pullback compositors displayed here. This
also determines pasting for beta by inversion on Cartesian squares. -/
theorem open_paste {X Y X' Y' X'' Y'' : Scheme.{u}}
    {j : X ⟶ Y} {j' : X' ⟶ Y'} {j'' : X'' ⟶ Y''}
    [IsOpenImmersion j] [IsOpenImmersion j'] [IsOpenImmersion j'']
    {w : X' ⟶ X} {v : Y' ⟶ Y} {w' : X'' ⟶ X'} {v' : Y'' ⟶ Y'}
    (s : CommSq w j' j v) (t : CommSq w' j'' j' v')
    (outer : CommSq (w' ≫ w) j'' j (v' ≫ v)) (K : D Λ X) :
    (openMate Λ t).app ((P Λ w).obj K) ≫ (P Λ v').map ((openMate Λ s).app K) =
      (J Λ j'').map ((leftDerivedUpperStarComp Λ w' w).inv.app K) ≫
        (openMate Λ outer).app K ≫
        (leftDerivedUpperStarComp Λ v' v).hom.app ((J Λ j).obj K) := by
  have h := congrArg (fun α : P Λ w ⋙ (P Λ w' ⋙ J Λ j'') ⟶
      J Λ j ⋙ (P Λ v ⋙ P Λ v') ↦ α.app K) (native_open_paste_nt Λ s t outer)
  simpa only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_hom_app, Functor.associator_inv_app, Category.comp_id,
    Category.id_comp] using h

private theorem open_identity_aux {C D : Type*} [Category C] [Category D]
    {L : C ⥤ D} {R : D ⥤ C} (a : L ⊣ R)
    (G : C ⥤ C) (H : D ⥤ D) (e : G ≅ 𝟭 C) (d : H ≅ 𝟭 D)
    (θ : R ⋙ G ≅ H ⋙ R)
    (h : ∀ N, θ.hom.app N ≫ R.map (d.hom.app N) = e.hom.app (R.obj N)) (K : C) :
    (((mateEquiv a a).symm (TwoSquare.mk _ _ _ _ θ.hom)).natTrans).app K ≫ d.hom.app (L.obj K) =
      L.map (e.hom.app K) := by
  let α := ((mateEquiv a a).symm (TwoSquare.mk _ _ _ _ θ.hom)).natTrans
  have hu : G.map (a.unit.app K) ≫ θ.hom.app (L.obj K) =
      a.unit.app (G.obj K) ≫ R.map (α.app K) :=
    unit_mateEquiv_symm a a (TwoSquare.mk _ _ _ _ θ.hom) K
  change α.app K ≫ d.hom.app (L.obj K) = _
  apply (a.homEquiv (G.obj K) (L.obj K)).injective
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit, R.map_comp,
    ← Category.assoc, ← hu, Category.assoc, h]
  have he := e.hom.naturality (a.unit.app K)
  have hn := a.unit.naturality (e.hom.app K)
  dsimp only [Functor.id_map, Functor.comp_map, Functor.id_obj] at he hn
  exact he.trans hn

/-- The open identity mate, with its native unit normalization.
Source: the source proof, paragraph 1
(blueprint: lem-fix-condensed-compactification-reindexing).
Proof: apply the open-adjunction mate bijection to the normalized pullback square
identity. Its triangle identities contract the unit and counit to identity. -/
theorem open_identity {X Y : Scheme.{u}} (j : X ⟶ Y) [IsOpenImmersion j]
    (K : D Λ X) :
    (openMate Λ (CommSq.mk
      ((Category.id_comp j).trans (Category.comp_id j).symm))).app K ≫
        (leftDerivedUpperStarId Λ Y).hom.app ((J Λ j).obj K) =
      (J Λ j).map ((leftDerivedUpperStarId Λ X).hom.app K) := by
  unfold openMate
  refine open_identity_aux (oa Λ j) (P Λ (𝟙 X)) (P Λ (𝟙 Y))
    (leftDerivedUpperStarId Λ X) (leftDerivedUpperStarId Λ Y)
    (pullbackSquareComparison Λ (CommSq.mk
      ((Category.id_comp j).trans (Category.comp_id j).symm))).symm ?_ K
  intro N
  apply (cancel_epi ((pullbackSquareComparison Λ (CommSq.mk
    ((Category.id_comp j).trans (Category.comp_id j).symm))).hom.app N)).1
  rw [Iso.symm_hom, ← Category.assoc, Iso.hom_inv_id_app, Category.id_comp]
  exact (pullbackSquareComparison_identity Λ j N).symm

private theorem native_delta {X Y : Scheme.{u}} (f : X ⟶ Y)
    (K L : D Λ Y) :
    Functor.OplaxMonoidal.δ (P Λ f) K L = ((leftDerivedUpperStarTensor Λ f).app K).app L := by
  rfl

private theorem proper_projection_eq {X Y : Scheme.{u}} (f : X ⟶ Y) (K : D Λ X) (L : D Λ Y) :
    properProjectionMorphism Λ f K L = moduleObjectProjectionMap Λ f K L := by
  unfold properProjectionMorphism moduleObjectProjectionMap moduleObjectProjectionData
  rw [Adjunction.rightAdjointProjectionMap_app_app]
  unfold Adjunction.projectionMorphism
  rw [native_delta]
  rfl

/-- The native compact projection has exactly the specified proper/open factorization.
This records the connection to the dependency's explicit projection-mate interface.
Source: the source proof, paragraph 3
(blueprint: lem-fix-condensed-compactification-reindexing).
Proof: the native monoidal pullback has tensorator the inverse K-flat comparison.
Consequently its adjunction projection morphism is the same counit transpose as
`moduleObjectProjectionMap`. The remaining two factors are, by definition, the
inverse open projection and the inverse compactification pullback compositor. -/
theorem pf_factorization {X Y : Scheme.{u}} {f : X ⟶ Y}
    (c : Compactification f) (K : D Λ X) (L : D Λ Y) :
    pf Λ c K L = moduleObjectProjectionMap Λ c.g ((J Λ c.i).obj K) L ≫
      (R Λ c.g).map
        (inv (openImmersionProjectionComparison Λ c.i K ((P Λ c.g).obj L)) ≫
          (J Λ c.i).map (𝟙 K ⊗ₘ (leftDerivedUpperStarCompactificationIso Λ c).inv.app L)) := by
  have hpf : pf Λ c K L = properProjectionMorphism Λ c.g ((J Λ c.i).obj K) L ≫
      (R Λ c.g).map
        (inv (openImmersionProjectionComparison Λ c.i K ((P Λ c.g).obj L)) ≫
          (J Λ c.i).map (𝟙 K ⊗ₘ (leftDerivedUpperStarCompactificationIso Λ c).inv.app L)) := by
    unfold pf exceptionalProjectionMorphismOfCompactification
    simp only [CategoryTheory.MonoidalCategory.id_tensorHom]
  exact hpf.trans (congrArg (fun m ↦ m ≫ _) (proper_projection_eq Λ c.g _ L))

private theorem transport_exchange_paste_aux
    {A B A' B' A'' B'' : Type*}
    [Category A] [Category B] [Category A'] [Category B'] [Category A''] [Category B'']
    {F : A ⥤ B} {F' : A' ⥤ B'} {F'' : A'' ⥤ B''}
    {T : A ⥤ B} {T' : A' ⥤ B'} {T'' : A'' ⥤ B''}
    (χ : F ≅ T) (χ' : F' ≅ T') (χ'' : F'' ≅ T'')
    {G₁ : B ⥤ B'} {G₂ : B' ⥤ B''} {G : B ⥤ B''}
    {H₁ : A ⥤ A'} {H₂ : A' ⥤ A''} {H : A ⥤ A''}
    (c : G ≅ G₁ ⋙ G₂) (d : H ≅ H₁ ⋙ H₂)
    (δ₁ : T ⋙ G₁ ⟶ H₁ ⋙ T') (δ₂ : T' ⋙ G₂ ⟶ H₂ ⋙ T'') (δ : T ⋙ G ⟶ H ⋙ T'')
    (σ₁ : F ⋙ G₁ ⟶ H₁ ⋙ F') (σ₂ : F' ⋙ G₂ ⟶ H₂ ⋙ F'') (σ : F ⋙ G ⟶ H ⋙ F'')
    (h₁ : σ₁ = Functor.whiskerRight χ.hom G₁ ≫ δ₁ ≫ Functor.whiskerLeft H₁ χ'.inv)
    (h₂ : σ₂ = Functor.whiskerRight χ'.hom G₂ ≫ δ₂ ≫ Functor.whiskerLeft H₂ χ''.inv)
    (h₀ : σ = Functor.whiskerRight χ.hom G ≫ δ ≫ Functor.whiskerLeft H χ''.inv)
    (hp : ∀ K, c.hom.app (T.obj K) ≫ G₂.map (δ₁.app K) ≫ δ₂.app (H₁.obj K) =
      δ.app K ≫ T''.map (d.hom.app K)) (K : A) :
    c.hom.app (F.obj K) ≫ G₂.map (σ₁.app K) ≫ σ₂.app (H₁.obj K) =
      σ.app K ≫ F''.map (d.hom.app K) := by
  have hd := χ''.hom.naturality (d.hom.app K)
  have hc := c.hom.naturality (χ.hom.app K)
  dsimp only [Functor.comp_obj] at hd
  dsimp only [Functor.comp_map] at hc
  rw [h₁, h₂, h₀]
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.map_comp]
  apply (cancel_mono (χ''.hom.app (H₂.obj (H₁.obj K)))).1
  simp only [Category.assoc]
  rw [hd]
  simp only [Iso.inv_hom_id_app_assoc, Iso.inv_hom_id_app]
  rw [← G₂.map_comp_assoc (χ'.inv.app (H₁.obj K)) (χ'.hom.app (H₁.obj K)),
    Iso.inv_hom_id_app, CategoryTheory.Functor.map_id, Category.id_comp]
  rw [← reassoc_of% hc]
  simpa using
    congrArg (fun a ↦ G.map (χ.hom.app K) ≫ a) (hp K)

private theorem transport_exchange_paste_nt
    {A B A' B' A'' B'' : Type*}
    [Category A] [Category B] [Category A'] [Category B'] [Category A''] [Category B'']
    {F : A ⥤ B} {F' : A' ⥤ B'} {F'' : A'' ⥤ B''}
    {T : A ⥤ B} {T' : A' ⥤ B'} {T'' : A'' ⥤ B''}
    (χ : F ≅ T) (χ' : F' ≅ T') (χ'' : F'' ≅ T'')
    {G₁ : B ⥤ B'} {G₂ : B' ⥤ B''} {G : B ⥤ B''}
    {H₁ : A ⥤ A'} {H₂ : A' ⥤ A''} {H : A ⥤ A''}
    (c : G ≅ G₁ ⋙ G₂) (d : H ≅ H₁ ⋙ H₂)
    (δ₁ : T ⋙ G₁ ⟶ H₁ ⋙ T') (δ₂ : T' ⋙ G₂ ⟶ H₂ ⋙ T'') (δ : T ⋙ G ⟶ H ⋙ T'')
    (σ₁ : F ⋙ G₁ ⟶ H₁ ⋙ F') (σ₂ : F' ⋙ G₂ ⟶ H₂ ⋙ F'') (σ : F ⋙ G ⟶ H ⋙ F'')
    (h₁ : σ₁ = Functor.whiskerRight χ.hom G₁ ≫ δ₁ ≫ Functor.whiskerLeft H₁ χ'.inv)
    (h₂ : σ₂ = Functor.whiskerRight χ'.hom G₂ ≫ δ₂ ≫ Functor.whiskerLeft H₂ χ''.inv)
    (h₀ : σ = Functor.whiskerRight χ.hom G ≫ δ ≫ Functor.whiskerLeft H χ''.inv)
    (hp : ∀ K, c.hom.app (T.obj K) ≫ G₂.map (δ₁.app K) ≫ δ₂.app (H₁.obj K) =
      δ.app K ≫ T''.map (d.hom.app K)) :
    Functor.whiskerLeft F c.hom ≫ (Functor.associator F G₁ G₂).inv ≫
      Functor.whiskerRight σ₁ G₂ ≫ (Functor.associator H₁ F' G₂).hom ≫
      Functor.whiskerLeft H₁ σ₂ =
    σ ≫ Functor.whiskerRight d.hom F'' ≫ (Functor.associator H₁ H₂ F'').hom := by
  refine NatTrans.ext (funext fun K ↦ ?_)
  simpa only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_hom_app, Functor.associator_inv_app, Category.comp_id,
    Category.id_comp] using transport_exchange_paste_aux χ χ' χ'' c d
      δ₁ δ₂ δ σ₁ σ₂ σ h₁ h₂ h₀ hp K

private theorem composite_exchange_paste_aux
    {A B C A' B' C' A'' B'' C'' : Type*}
    [Category A] [Category B] [Category C] [Category A'] [Category B'] [Category C']
    [Category A''] [Category B''] [Category C'']
    (J : A ⥤ B) (R : B ⥤ C) (J' : A' ⥤ B') (R' : B' ⥤ C')
    (J'' : A'' ⥤ B'') (R'' : B'' ⥤ C'')
    (G₁ : C ⥤ C') (G₂ : C' ⥤ C'') (G : C ⥤ C'')
    (H₁ : A ⥤ A') (H₂ : A' ⥤ A'') (H : A ⥤ A'')
    (M₁ : B ⥤ B') (M₂ : B' ⥤ B'') (M : B ⥤ B'')
    (r₁ : R ⋙ G₁ ⟶ M₁ ⋙ R') (r₂ : R' ⋙ G₂ ⟶ M₂ ⋙ R'')
    (r : R ⋙ G ⟶ M ⋙ R'')
    (β₁ : J ⋙ M₁ ≅ H₁ ⋙ J') (β₂ : J' ⋙ M₂ ≅ H₂ ⋙ J'')
    (β : J ⋙ M ≅ H ⋙ J'') (c : G ≅ G₁ ⋙ G₂) (d : H ≅ H₁ ⋙ H₂)
    (m : M ≅ M₁ ⋙ M₂)
    (hp : ∀ N, c.hom.app (R.obj N) ≫ G₂.map (r₁.app N) ≫ r₂.app (M₁.obj N) =
      r.app N ≫ R''.map (m.hom.app N))
    (hb : ∀ K, m.hom.app (J.obj K) ≫ M₂.map (β₁.hom.app K) ≫
      β₂.hom.app (H₁.obj K) = β.hom.app K ≫ J''.map (d.hom.app K)) (K : A) :
    c.hom.app ((J ⋙ R).obj K) ≫
        G₂.map ((compositeExchange J R J' R' G₁ H₁ M₁ r₁ β₁).app K) ≫
        (compositeExchange J' R' J'' R'' G₂ H₂ M₂ r₂ β₂).app (H₁.obj K) =
      (compositeExchange J R J'' R'' G H M r β).app K ≫
        (J'' ⋙ R'').map (d.hom.app K) := by
  simp only [compositeExchange_app, Functor.map_comp, Functor.comp_map, Category.assoc]
  dsimp only [Functor.comp_obj]
  have hn := r₂.naturality (β₁.hom.app K)
  dsimp only [Functor.comp_map] at hn
  rw [reassoc_of% hn, reassoc_of% (hp (J.obj K))]
  simp only [← R''.map_comp]
  rw [hb]

private theorem compact_paste_of_model
    {A B C A' B' C' A'' B'' C'' : Type*}
    [Category A] [Category B] [Category C] [Category A'] [Category B'] [Category C']
    [Category A''] [Category B''] [Category C'']
    (J : A ⥤ B) (R : B ⥤ C) (J' : A' ⥤ B') (R' : B' ⥤ C')
    (J'' : A'' ⥤ B'') (R'' : B'' ⥤ C'')
    (G₁ : C ⥤ C') (G₂ : C' ⥤ C'') (G : C ⥤ C'')
    (H₁ : A ⥤ A') (H₂ : A' ⥤ A'') (H : A ⥤ A'')
    (M₁ : B ⥤ B') (M₂ : B' ⥤ B'') (M : B ⥤ B'')
    (r₁ : R ⋙ G₁ ⟶ M₁ ⋙ R') (r₂ : R' ⋙ G₂ ⟶ M₂ ⋙ R'')
    (r : R ⋙ G ⟶ M ⋙ R'')
    (β₁ : J ⋙ M₁ ≅ H₁ ⋙ J') (β₂ : J' ⋙ M₂ ≅ H₂ ⋙ J'')
    (β : J ⋙ M ≅ H ⋙ J'') (c : G ≅ G₁ ⋙ G₂) (d : H ≅ H₁ ⋙ H₂)
    (m : M ≅ M₁ ⋙ M₂)
    (hp : ∀ N, c.hom.app (R.obj N) ≫ G₂.map (r₁.app N) ≫ r₂.app (M₁.obj N) =
      r.app N ≫ R''.map (m.hom.app N))
    (hb : ∀ K, m.hom.app (J.obj K) ≫ M₂.map (β₁.hom.app K) ≫
      β₂.hom.app (H₁.obj K) = β.hom.app K ≫ J''.map (d.hom.app K))
    (F : A ⥤ C) (F' : A' ⥤ C') (F'' : A'' ⥤ C'')
    (χ : F ≅ J ⋙ R) (χ' : F' ≅ J' ⋙ R') (χ'' : F'' ≅ J'' ⋙ R'')
    (σ₁ : F ⋙ G₁ ⟶ H₁ ⋙ F') (σ₂ : F' ⋙ G₂ ⟶ H₂ ⋙ F'') (σ : F ⋙ G ⟶ H ⋙ F'')
    (h₁ : σ₁ = Functor.whiskerRight χ.hom G₁ ≫
      compositeExchange J R J' R' G₁ H₁ M₁ r₁ β₁ ≫ Functor.whiskerLeft H₁ χ'.inv)
    (h₂ : σ₂ = Functor.whiskerRight χ'.hom G₂ ≫
      compositeExchange J' R' J'' R'' G₂ H₂ M₂ r₂ β₂ ≫ Functor.whiskerLeft H₂ χ''.inv)
    (h₀ : σ = Functor.whiskerRight χ.hom G ≫
      compositeExchange J R J'' R'' G H M r β ≫ Functor.whiskerLeft H χ''.inv) :
    Functor.whiskerLeft F c.hom ≫ (Functor.associator F G₁ G₂).inv ≫
      Functor.whiskerRight σ₁ G₂ ≫ (Functor.associator H₁ F' G₂).hom ≫
      Functor.whiskerLeft H₁ σ₂ =
    σ ≫ Functor.whiskerRight d.hom F'' ≫ (Functor.associator H₁ H₂ F'').hom := by
  refine transport_exchange_paste_nt χ χ' χ'' c d _ _ _ σ₁ σ₂ σ h₁ h₂ h₀ ?_
  intro K
  exact composite_exchange_paste_aux J R J' R' J'' R'' G₁ G₂ G H₁ H₂ H M₁ M₂ M
    r₁ r₂ r β₁ β₂ β c d m hp hb K

private theorem inverse_paste_eq {C : Type*} [Category C]
    {a b c d e : C} (α : a ≅ b) (β : b ≅ c) (γ : d ≅ a)
    (δ : d ≅ e) (ε : e ≅ c)
    (h : α.hom ≫ β.hom = γ.inv ≫ δ.hom ≫ ε.hom) :
    ε.hom ≫ β.inv ≫ α.inv = δ.inv ≫ γ.hom := by
  apply (cancel_epi δ.hom).1
  apply (cancel_epi γ.inv).1
  calc
    γ.inv ≫ δ.hom ≫ ε.hom ≫ β.inv ≫ α.inv =
        α.hom ≫ β.hom ≫ β.inv ≫ α.inv := by
      simpa only [Category.assoc] using
        congrArg (fun k ↦ k ≫ β.inv ≫ α.inv) h.symm
    _ = γ.inv ≫ δ.hom ≫ δ.inv ≫ γ.hom := by simp

private theorem beta_paste {X Y X' Y' X'' Y'' : Scheme.{u}}
    {j : X ⟶ Y} {j' : X' ⟶ Y'} {j'' : X'' ⟶ Y''}
    [IsOpenImmersion j] [IsOpenImmersion j'] [IsOpenImmersion j'']
    {w : X' ⟶ X} {v : Y' ⟶ Y} {w' : X'' ⟶ X'} {v' : Y'' ⟶ Y'}
    (s : IsPullback w j' j v) (t : IsPullback w' j'' j' v')
    (outer : IsPullback (w' ≫ w) j'' j (v' ≫ v)) (K : D Λ X) :
    (leftDerivedUpperStarComp Λ v' v).hom.app ((J Λ j).obj K) ≫
        (P Λ v').map ((beta Λ s).hom.app K) ≫
        (beta Λ t).hom.app ((P Λ w).obj K) =
      (beta Λ outer).hom.app K ≫
        (J Λ j'').map ((leftDerivedUpperStarComp Λ w' w).hom.app K) := by
  simpa only [beta, Iso.app_hom, Iso.app_inv, Iso.symm_hom, Iso.symm_inv,
    Functor.mapIso_hom, Functor.mapIso_inv, asIso_hom] using
    inverse_paste_eq ((beta Λ t).symm.app ((P Λ w).obj K))
    ((P Λ v').mapIso ((beta Λ s).symm.app K))
    ((J Λ j'').mapIso ((leftDerivedUpperStarComp Λ w' w).app K))
    ((beta Λ outer).symm.app K)
    ((leftDerivedUpperStarComp Λ v' v).app ((J Λ j).obj K))
    (by simpa only [beta, Iso.app_hom, Iso.app_inv, Iso.symm_hom, Iso.symm_inv,
        Functor.mapIso_hom, Functor.mapIso_inv, asIso_hom] using
      open_paste Λ s.toCommSq t.toCommSq outer.toCommSq K)

private theorem native_compact_paste_nt {X Y X' Y' X'' Y'' : Scheme.{u}}
    {f : X ⟶ Y} {f' : X' ⟶ Y'} {f'' : X'' ⟶ Y''}
    {c : Compactification f} {c' : Compactification f'} {c'' : Compactification f''}
    {w : X' ⟶ X} {v : Y' ⟶ Y} {w' : X'' ⟶ X'} {v' : Y'' ⟶ Y'}
    (s : Square c c' w v) (t : Square c' c'' w' v')
    (outer : Square c c'' (w' ≫ w) (v' ≫ v))
    (h : outer.middle = t.middle ≫ s.middle) :
    Functor.whiskerLeft (F Λ c) (leftDerivedUpperStarComp Λ v' v).hom ≫
      (Functor.associator (F Λ c) (P Λ v) (P Λ v')).inv ≫
      Functor.whiskerRight (squareExchange Λ s) (P Λ v') ≫
      (Functor.associator (P Λ w) (F Λ c') (P Λ v')).hom ≫
      Functor.whiskerLeft (P Λ w) (squareExchange Λ t) =
    squareExchange Λ outer ≫
      Functor.whiskerRight (leftDerivedUpperStarComp Λ w' w).hom (F Λ c'') ≫
      (Functor.associator (P Λ w) (P Λ w') (F Λ c'')).hom := by
  obtain ⟨m, so, sp⟩ := outer
  dsimp only at h
  subst m
  exact compact_paste_of_model (J Λ c.i) (R Λ c.g) (J Λ c'.i) (R Λ c'.g)
    (J Λ c''.i) (R Λ c''.g) (P Λ v) (P Λ v') (P Λ (v' ≫ v))
    (P Λ w) (P Λ w') (P Λ (w' ≫ w)) (P Λ s.middle) (P Λ t.middle)
    (P Λ (t.middle ≫ s.middle)) (baseChangeMap Λ s.properSquare)
    (baseChangeMap Λ t.properSquare) (baseChangeMap Λ sp)
    (beta Λ s.openSquare) (beta Λ t.openSquare) (beta Λ so)
    (leftDerivedUpperStarComp Λ v' v) (leftDerivedUpperStarComp Λ w' w)
    (leftDerivedUpperStarComp Λ t.middle s.middle)
    (fun N ↦ direct_paste Λ s.properSquare t.properSquare sp N)
    (fun M ↦ beta_paste Λ s.openSquare t.openSquare so M)
    (F Λ c) (F Λ c') (F Λ c'') (modelIso Λ c) (modelIso Λ c') (modelIso Λ c'')
    (squareExchange Λ s) (squareExchange Λ t) (squareExchange Λ ⟨_, so, sp⟩)
    (square_exchange_model_comp Λ s) (square_exchange_model_comp Λ t)
    (square_exchange_model_comp Λ ⟨_, so, sp⟩)

/-- Pasting of compact-support exchanges uses the same boundary compositors.
Source: the source proof, paragraphs 1 and 3
(blueprint: lem-fix-condensed-compactification-reindexing).
Proof: expand into the proper and open factors. Apply direct mate pasting and open
mate pasting to the two factors. Native associativity cancels their middle
comparisons. This yields the displayed equation for the outer square. -/
theorem compact_paste {X Y X' Y' X'' Y'' : Scheme.{u}}
    {f : X ⟶ Y} {f' : X' ⟶ Y'} {f'' : X'' ⟶ Y''}
    {c : Compactification f} {c' : Compactification f'} {c'' : Compactification f''}
    {w : X' ⟶ X} {v : Y' ⟶ Y} {w' : X'' ⟶ X'} {v' : Y'' ⟶ Y'}
    (s : Square c c' w v) (t : Square c' c'' w' v')
    (outer : Square c c'' (w' ≫ w) (v' ≫ v))
    (h : outer.middle = t.middle ≫ s.middle) (K : D Λ X) :
    (leftDerivedUpperStarComp Λ v' v).hom.app ((F Λ c).obj K) ≫
        (P Λ v').map ((squareExchange Λ s).app K) ≫
        (squareExchange Λ t).app ((P Λ w).obj K) =
      (squareExchange Λ outer).app K ≫
        (F Λ c'').map ((leftDerivedUpperStarComp Λ w' w).hom.app K) := by
  have hnt := native_compact_paste_nt Λ s t outer h
  have hh := congrArg (fun α : F Λ c ⋙ P Λ (v' ≫ v) ⟶
      P Λ w ⋙ (P Λ w' ⋙ F Λ c'') ↦ α.app K) hnt
  simpa only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_hom_app, Functor.associator_inv_app, Category.comp_id,
    Category.id_comp] using hh

/-- Identity compactification square, with the native unit comparisons.
Source: the source proof, paragraph 1
(blueprint: lem-fix-condensed-compactification-reindexing).
Proof: direct identity mates give identity, and open identity mates give identity
under the normalized open unit. Their product is identity under the same pullback
unit comparisons. -/
theorem compact_identity {X Y : Scheme.{u}} {f : X ⟶ Y}
    (c : Compactification f) (s : Square c c (𝟙 X) (𝟙 Y))
    (h : s.middle = 𝟙 c.Z) (K : D Λ X) :
    (squareExchange Λ s).app K ≫
        (F Λ c).map ((leftDerivedUpperStarId Λ X).hom.app K) =
      (leftDerivedUpperStarId Λ Y).hom.app ((F Λ c).obj K) := by
  rcases s with ⟨m, ho, hp⟩
  change m = 𝟙 c.Z at h
  subst m
  refine compact_identity_of_model (F Λ c) (J Λ c.i) (P Λ c.g) (R Λ c.g)
    (derivedUpperStarLowerStarAdjunction Λ c.g) (P Λ (𝟙 Y)) (P Λ (𝟙 X))
    (P Λ (𝟙 c.Z)) (pullbackSquareComparison Λ hp) (beta Λ ho) (modelIso Λ c)
    (squareExchange Λ ⟨𝟙 c.Z, ho, hp⟩) (square_exchange_model Λ ⟨𝟙 c.Z, ho, hp⟩)
    (leftDerivedUpperStarId Λ X) (leftDerivedUpperStarId Λ c.Z)
    (leftDerivedUpperStarId Λ Y) ?_ ?_ K
  · intro L
    simpa only [beta, Iso.symm_inv, asIso_hom] using open_identity Λ c.i L
  · intro N
    simpa only [baseChangeMap] using direct_identity Λ c.g N

/-- Projection descends through the actual common-refinement comparison.
The four invertibilities here specify exactly the displayed comparison domain;
the rational bounded-constructible theorem supplies them on the node's domain.
Source: the source proof, paragraph 3
(blueprint: lem-fix-condensed-compactification-reindexing).
Proof: apply refinement projection compatibility for the two arrows to the common
refinement. Cancel the second refinement at the tensor input and the first at the
original input. The remaining inverses are exactly those in `comparison`. -/
theorem comparison_projection {X Y : Scheme.{u}} {f : X ⟶ Y}
    {c₁ c₂ d : Compactification f} (h₁ : d.Refinement c₁) (h₂ : d.Refinement c₂)
    (K : D Λ X) (L : D Λ Y)
    [a₁ : IsIso ((refinement Λ h₁).app K)] [a₂ : IsIso ((refinement Λ h₂).app K)]
    [b₁ : IsIso ((refinement Λ h₁).app (K ⊗ (P Λ f).obj L))]
    [b₂ : IsIso ((refinement Λ h₂).app (K ⊗ (P Λ f).obj L))] :
    pf Λ c₁ K L ≫ (comparison Λ h₁ h₂ (K ⊗ (P Λ f).obj L) (h₁iso := b₁) (h₂iso := b₂)).hom =
      ((comparison Λ h₁ h₂ K (h₁iso := a₁) (h₂iso := a₂)).hom ⊗ₘ 𝟙 L) ≫ pf Λ c₂ K L := by
  apply (cancel_mono ((refinement Λ h₂).app (K ⊗ (P Λ f).obj L))).1
  simp only [comparison, Iso.trans_hom, Iso.symm_hom, asIso_hom, asIso_inv]
  simp only [Category.assoc, IsIso.inv_hom_id, Category.comp_id]
  rw [refinement_projection Λ h₂ K L, tensorHom_comp_tensorHom_assoc]
  simp only [IsIso.inv_hom_id, Category.assoc, Category.comp_id]
  exact refinement_projection Λ h₁ K L

private theorem inverse_composition_boundary {C : Type*} [Category C]
    {a b c d e : C} (α : a ≅ b) (β : b ≅ c) (γ : c ≅ d) (δ : d ≅ e)
    (ε : a ≅ e) (h : ε.hom = α.hom ≫ β.hom ≫ γ.hom ≫ δ.hom) :
    δ.hom ≫ ε.inv ≫ α.hom = γ.inv ≫ β.inv := by
  have he : ε = α ≪≫ β ≪≫ γ ≪≫ δ := Iso.ext h
  rw [he]
  simp

private theorem inverse_mate_composition_aux
    {A B C A' B' C' : Type*}
    [Category A] [Category B] [Category C] [Category A'] [Category B'] [Category C']
    {L₁ : A ⥤ B} {R₁ : B ⥤ A} {L₂ : B ⥤ C} {R₂ : C ⥤ B}
    {L₁' : A' ⥤ B'} {R₁' : B' ⥤ A'} {L₂' : B' ⥤ C'} {R₂' : C' ⥤ B'}
    {L : A ⥤ C} {R : C ⥤ A} {L' : A' ⥤ C'} {R' : C' ⥤ A'}
    (a₁ : L₁ ⊣ R₁) (a₂ : L₂ ⊣ R₂) (a : L ⊣ R)
    (a₁' : L₁' ⊣ R₁') (a₂' : L₂' ⊣ R₂') (a' : L' ⊣ R')
    {G : A ⥤ A'} {H : B ⥤ B'} {K : C ⥤ C'}
    (θ₁ : H ⋙ R₁' ≅ R₁ ⋙ G) (θ₂ : K ⋙ R₂' ≅ R₂ ⋙ H)
    (θ : K ⋙ R' ≅ R ⋙ G) (c : R ≅ R₂ ⋙ R₁) (c' : R' ≅ R₂' ⋙ R₁')
    (h : ∀ N, θ.hom.app N = c'.hom.app (K.obj N) ≫ R₁'.map (θ₂.hom.app N) ≫
      θ₁.hom.app (R₂.obj N) ≫ G.map (c.inv.app N)) :
    let e := ((conjugateIsoEquiv (a₁.comp a₂) a).symm c.symm).symm
    let e' := ((conjugateIsoEquiv (a₁'.comp a₂') a').symm c'.symm).symm
    ∀ N,
      L₂'.map (((mateEquiv a₁ a₁').symm (TwoSquare.mk _ _ _ _ θ₁.inv)).natTrans.app N) ≫
        ((mateEquiv a₂ a₂').symm (TwoSquare.mk _ _ _ _ θ₂.inv)).natTrans.app (L₁.obj N) =
      e'.hom.app (G.obj N) ≫
        ((mateEquiv a a').symm (TwoSquare.mk _ _ _ _ θ.inv)).natTrans.app N ≫
        K.map (e.inv.app N) := by
  intro e e' N
  let α := (mateEquiv a₁ a₁').symm (TwoSquare.mk _ _ _ _ θ₁.inv)
  let β := (mateEquiv a₂ a₂').symm (TwoSquare.mk _ _ _ _ θ₂.inv)
  let γ := (mateEquiv a a').symm (TwoSquare.mk _ _ _ _ θ.inv)
  have hc : conjugateEquiv (a₁.comp a₂) a e.inv = c.inv := by
    change (conjugateIsoEquiv (a₁.comp a₂) a
      ((conjugateIsoEquiv (a₁.comp a₂) a).symm c.symm)).hom = c.inv
    rw [Equiv.apply_symm_apply]
    rfl
  have hc' : conjugateEquiv a' (a₁'.comp a₂') e'.hom = c'.hom := by
    have hh := congrArg (fun i : R₂' ⋙ R₁' ≅ R' ↦ i.inv)
      ((conjugateIsoEquiv (a₁'.comp a₂') a').apply_symm_apply c'.symm)
    change conjugateEquiv a' (a₁'.comp a₂')
      ((conjugateIsoEquiv (a₁'.comp a₂') a').symm c'.symm).inv = c'.hom
    simpa only [conjugateIsoEquiv_apply_inv, Iso.symm_inv] using hh
  have he : TwoSquare.vComp α β = (γ.whiskerRight e'.hom).whiskerLeft e.inv := by
    apply (mateEquiv (a₁.comp a₂) (a₁'.comp a₂')).injective
    rw [mateEquiv_hcomp a₁ a₁' a₂ a₂',
      conjugateEquiv_mateEquiv_vcomp (a₁.comp a₂) a (a₁'.comp a₂'),
      mateEquiv_conjugateEquiv_vcomp a a' (a₁'.comp a₂'), hc, hc']
    simp only [α, β, γ, Equiv.apply_symm_apply]
    ext M
    dsimp only [TwoSquare.hComp, TwoSquare.whiskerTop, TwoSquare.whiskerBottom,
      TwoSquare.mk, TwoSquare.natTrans, NatTrans.comp_app, Functor.whiskerRight_app,
      Functor.whiskerLeft_app, Functor.associator_hom_app, Functor.associator_inv_app]
    simp only [Category.id_comp, Category.comp_id]
    symm
    simpa only [Functor.mapIso_hom, Functor.mapIso_inv, Iso.app_hom, Iso.app_inv,
      Iso.symm_hom, Iso.symm_inv] using inverse_composition_boundary
      (c'.app (K.obj M)) (R₁'.mapIso (θ₂.app M)) (θ₁.app (R₂.obj M))
      (G.mapIso (c.symm.app M)) (θ.app M) (h M)
  have hn := congrArg (fun s ↦ s.natTrans.app N) he
  simpa only [α, β, γ, TwoSquare.vComp, TwoSquare.whiskerRight, TwoSquare.whiskerLeft,
    TwoSquare.mk, TwoSquare.natTrans, NatTrans.comp_app, Functor.whiskerRight_app,
    Functor.whiskerLeft_app, Functor.associator_hom_app, Functor.associator_inv_app,
    Category.id_comp, Category.comp_id, Category.assoc] using hn

private theorem inverse_mate_composition_nt
    {A B C A' B' C' : Type*}
    [Category A] [Category B] [Category C] [Category A'] [Category B'] [Category C']
    {L₁ : A ⥤ B} {R₁ : B ⥤ A} {L₂ : B ⥤ C} {R₂ : C ⥤ B}
    {L₁' : A' ⥤ B'} {R₁' : B' ⥤ A'} {L₂' : B' ⥤ C'} {R₂' : C' ⥤ B'}
    {L : A ⥤ C} {R : C ⥤ A} {L' : A' ⥤ C'} {R' : C' ⥤ A'}
    (a₁ : L₁ ⊣ R₁) (a₂ : L₂ ⊣ R₂) (a : L ⊣ R)
    (a₁' : L₁' ⊣ R₁') (a₂' : L₂' ⊣ R₂') (a' : L' ⊣ R')
    {G : A ⥤ A'} {H : B ⥤ B'} {K : C ⥤ C'}
    (θ₁ : H ⋙ R₁' ≅ R₁ ⋙ G) (θ₂ : K ⋙ R₂' ≅ R₂ ⋙ H)
    (θ : K ⋙ R' ≅ R ⋙ G) (c : R ≅ R₂ ⋙ R₁) (c' : R' ≅ R₂' ⋙ R₁')
    (h : ∀ N, θ.hom.app N = c'.hom.app (K.obj N) ≫ R₁'.map (θ₂.hom.app N) ≫
      θ₁.hom.app (R₂.obj N) ≫ G.map (c.inv.app N)) :
    let e := ((conjugateIsoEquiv (a₁.comp a₂) a).symm c.symm).symm
    let e' := ((conjugateIsoEquiv (a₁'.comp a₂') a').symm c'.symm).symm
    Functor.whiskerRight
        ((mateEquiv a₁ a₁').symm (TwoSquare.mk _ _ _ _ θ₁.inv)).natTrans L₂' ≫
      (Functor.associator L₁ H L₂').hom ≫
      Functor.whiskerLeft L₁
        ((mateEquiv a₂ a₂').symm (TwoSquare.mk _ _ _ _ θ₂.inv)).natTrans =
    (Functor.associator G L₁' L₂').hom ≫ Functor.whiskerLeft G e'.hom ≫
      ((mateEquiv a a').symm (TwoSquare.mk _ _ _ _ θ.inv)).natTrans ≫
      Functor.whiskerRight e.inv K ≫ (Functor.associator L₁ L₂ K).hom := by
  intro e e'
  refine NatTrans.ext (funext fun N ↦ ?_)
  simpa only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_hom_app, Functor.associator_inv_app, Category.comp_id,
    Category.id_comp] using inverse_mate_composition_aux
      a₁ a₂ a a₁' a₂' a' θ₁ θ₂ θ c c' h N

private theorem inverse_mate_composition_nt_from_nt
    {A B C A' B' C' : Type*}
    [Category A] [Category B] [Category C] [Category A'] [Category B'] [Category C']
    {L₁ : A ⥤ B} {R₁ : B ⥤ A} {L₂ : B ⥤ C} {R₂ : C ⥤ B}
    {L₁' : A' ⥤ B'} {R₁' : B' ⥤ A'} {L₂' : B' ⥤ C'} {R₂' : C' ⥤ B'}
    {L : A ⥤ C} {R : C ⥤ A} {L' : A' ⥤ C'} {R' : C' ⥤ A'}
    (a₁ : L₁ ⊣ R₁) (a₂ : L₂ ⊣ R₂) (a : L ⊣ R)
    (a₁' : L₁' ⊣ R₁') (a₂' : L₂' ⊣ R₂') (a' : L' ⊣ R')
    {G : A ⥤ A'} {H : B ⥤ B'} {K : C ⥤ C'}
    (θ₁ : H ⋙ R₁' ≅ R₁ ⋙ G) (θ₂ : K ⋙ R₂' ≅ R₂ ⋙ H)
    (θ : K ⋙ R' ≅ R ⋙ G) (c : R ≅ R₂ ⋙ R₁) (c' : R' ≅ R₂' ⋙ R₁')
    (h : θ.hom = Functor.whiskerLeft K c'.hom ≫
      (Functor.associator K R₂' R₁').inv ≫ Functor.whiskerRight θ₂.hom R₁' ≫
      (Functor.associator R₂ H R₁').hom ≫ Functor.whiskerLeft R₂ θ₁.hom ≫
      (Functor.associator R₂ R₁ G).inv ≫ Functor.whiskerRight c.inv G) :
    let e := ((conjugateIsoEquiv (a₁.comp a₂) a).symm c.symm).symm
    let e' := ((conjugateIsoEquiv (a₁'.comp a₂') a').symm c'.symm).symm
    Functor.whiskerRight
        ((mateEquiv a₁ a₁').symm (TwoSquare.mk _ _ _ _ θ₁.inv)).natTrans L₂' ≫
      (Functor.associator L₁ H L₂').hom ≫
      Functor.whiskerLeft L₁
        ((mateEquiv a₂ a₂').symm (TwoSquare.mk _ _ _ _ θ₂.inv)).natTrans =
    (Functor.associator G L₁' L₂').hom ≫ Functor.whiskerLeft G e'.hom ≫
      ((mateEquiv a a').symm (TwoSquare.mk _ _ _ _ θ.inv)).natTrans ≫
      Functor.whiskerRight e.inv K ≫ (Functor.associator L₁ L₂ K).hom := by
  apply inverse_mate_composition_nt a₁ a₂ a a₁' a₂' a' θ₁ θ₂ θ c c'
  intro N
  have hn := congrArg (fun α ↦ α.app N) h
  simpa only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_hom_app, Functor.associator_inv_app, Category.comp_id,
    Category.id_comp] using hn

private theorem native_open_composition_nt {X Y Z X' Y' Z' : Scheme.{u}}
    {j : X ⟶ Y} {i : Y ⟶ Z} {j' : X' ⟶ Y'} {i' : Y' ⟶ Z'}
    [IsOpenImmersion j] [IsOpenImmersion i] [IsOpenImmersion j'] [IsOpenImmersion i']
    {a : X' ⟶ X} {b : Y' ⟶ Y} {d : Z' ⟶ Z}
    (s : CommSq a j' j b) (t : CommSq b i' i d)
    (outer : CommSq a (j' ≫ i') (j ≫ i) d) :
    Functor.whiskerRight (openMate Λ s) (J Λ i') ≫
      (Functor.associator (J Λ j) (P Λ b) (J Λ i')).hom ≫
      Functor.whiskerLeft (J Λ j) (openMate Λ t) =
    (Functor.associator (P Λ a) (J Λ j') (J Λ i')).hom ≫
      Functor.whiskerLeft (P Λ a) (jComp Λ j' i').hom ≫
      openMate Λ outer ≫ Functor.whiskerRight (jComp Λ j i).inv (P Λ d) ≫
      (Functor.associator (J Λ j) (J Λ i) (P Λ d)).hom := by
  unfold openMate jComp
  exact inverse_mate_composition_nt_from_nt (oa Λ j) (oa Λ i) (oa Λ (j ≫ i))
    (oa Λ j') (oa Λ i') (oa Λ (j' ≫ i'))
    (pullbackSquareComparison Λ s) (pullbackSquareComparison Λ t)
    (pullbackSquareComparison Λ outer) (leftDerivedUpperStarComp Λ j i)
    (leftDerivedUpperStarComp Λ j' i')
    (native_horizontal_comparison_nt Λ s t outer)

/-- Transport of composition of open extensions uses the adjoint-normalized compositor.
Source: the source proof, paragraph 3
(blueprint: lem-fix-condensed-compactification-reindexing).
Proof: both routes are the open mates of the horizontal pullback-pasting equation.
The composite open adjunction fixes `jComp`, and mate pasting identifies its two
transposes. Injectivity of the mate bijection gives the equation. -/
theorem open_composition {X Y Z X' Y' Z' : Scheme.{u}}
    {j : X ⟶ Y} {i : Y ⟶ Z} {j' : X' ⟶ Y'} {i' : Y' ⟶ Z'}
    [IsOpenImmersion j] [IsOpenImmersion i] [IsOpenImmersion j'] [IsOpenImmersion i']
    {a : X' ⟶ X} {b : Y' ⟶ Y} {d : Z' ⟶ Z}
    (s : CommSq a j' j b) (t : CommSq b i' i d)
    (outer : CommSq a (j' ≫ i') (j ≫ i) d) (K : D Λ X) :
    (J Λ i').map ((openMate Λ s).app K) ≫ (openMate Λ t).app ((J Λ j).obj K) =
      (jComp Λ j' i').hom.app ((P Λ a).obj K) ≫ (openMate Λ outer).app K ≫
        (P Λ d).map ((jComp Λ j i).inv.app K) := by
  have h := congrArg (fun α : (P Λ a ⋙ J Λ j') ⋙ J Λ i' ⟶
      J Λ j ⋙ (J Λ i ⋙ P Λ d) ↦ α.app K) (native_open_composition_nt Λ s t outer)
  simpa only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_hom_app, Functor.associator_inv_app, Category.comp_id,
    Category.id_comp] using h

set_option maxHeartbeats 1600000 in
-- Functor-category comparisons retain the native derived endpoints.
set_option maxHeartbeats 1600000 in
-- Native derived functor endpoint comparisons exceed the default heartbeat allowance.
set_option maxHeartbeats 1600000 in
-- Native derived functor endpoint comparisons exceed the default heartbeat allowance.
set_option maxHeartbeats 1600000 in
-- Native derived functor endpoint comparisons exceed the default heartbeat allowance.
set_option maxHeartbeats 1600000 in
-- Compute only the tensorator field of the native monoidal structure.
set_option maxHeartbeats 1600000 in
-- Match the two adjoint transposes after identifying their tensorator fields.
set_option maxHeartbeats 1600000 in
-- Native derived functor endpoint comparisons exceed the default heartbeat allowance.
set_option maxHeartbeats 1600000 in
-- Native derived functor endpoint comparisons exceed the default heartbeat allowance.
/-- Native pullback comparison for an isomorphism followed by its inverse.
Source: the source proof, paragraph 1
(blueprint: lem-fix-condensed-compactification-reindexing). -/
def pInverse {A B : Scheme.{u}} (a : A ⟶ B) [IsIso a] :
    P Λ a ⋙ P Λ (inv a) ≅ 𝟭 (D Λ B) :=
  (leftDerivedUpperStarComp Λ (inv a) a).symm ≪≫
    eqToIso (congrArg (P Λ) (IsIso.inv_hom_id a)) ≪≫ leftDerivedUpperStarId Λ B

private theorem identity_exchange_nt
    {A B : Type*} [Category A] [Category B] (F : A ⥤ B)
    {G : B ⥤ B} {H : A ⥤ A} (e : G ≅ 𝟭 B) (d : H ≅ 𝟭 A)
    (δ : F ⋙ G ⟶ H ⋙ F)
    (h : ∀ K, δ.app K ≫ F.map (d.hom.app K) = e.hom.app (F.obj K)) :
    δ ≫ Functor.whiskerRight d.hom F ≫ (Functor.leftUnitor F).hom =
      Functor.whiskerLeft F e.hom ≫ (Functor.rightUnitor F).hom := by
  refine NatTrans.ext (funext fun K ↦ ?_)
  simpa using h K

private theorem native_direct_identity_eq_nt {X Y : Scheme.{u}} (f : X ⟶ Y)
    {w : X ⟶ X} {v : Y ⟶ Y} (hw : w = 𝟙 X) (hv : v = 𝟙 Y)
    (s : CommSq w f f v) :
    baseChangeMap Λ s ≫ Functor.whiskerRight
      (eqToIso (congrArg (P Λ) hw) ≪≫ leftDerivedUpperStarId Λ X).hom (R Λ f) ≫
      (Functor.leftUnitor (R Λ f)).hom =
    Functor.whiskerLeft (R Λ f)
      (eqToIso (congrArg (P Λ) hv) ≪≫ leftDerivedUpperStarId Λ Y).hom ≫
      (Functor.rightUnitor (R Λ f)).hom := by
  subst w
  subst v
  simpa only [eqToIso_refl, Iso.refl_trans] using
    identity_exchange_nt (R Λ f) (leftDerivedUpperStarId Λ Y)
      (leftDerivedUpperStarId Λ X) (baseChangeMap Λ s) (fun K ↦ direct_identity Λ f K)

private theorem inverse_exchange_aux
    {A B A' B' : Type*} [Category A] [Category B] [Category A'] [Category B']
    (F : A ⥤ B) (F' : A' ⥤ B')
    {G : B ⥤ B'} {G' : B' ⥤ B} {G₀ : B ⥤ B}
    {H : A ⥤ A'} {H' : A' ⥤ A} {H₀ : A ⥤ A}
    (c : G₀ ≅ G ⋙ G') (d : H₀ ≅ H ⋙ H')
    (e : G₀ ≅ 𝟭 B) (q : H₀ ≅ 𝟭 A)
    (δ : F ⋙ G ⟶ H ⋙ F') (δ' : F' ⋙ G' ⟶ H' ⋙ F)
    (δ₀ : F ⋙ G₀ ⟶ H₀ ⋙ F)
    (hp : ∀ K, c.hom.app (F.obj K) ≫ G'.map (δ.app K) ≫ δ'.app (H.obj K) =
      δ₀.app K ≫ F.map (d.hom.app K))
    (hi : ∀ K, δ₀.app K ≫ F.map (q.hom.app K) = e.hom.app (F.obj K)) (K : A) :
    G'.map (δ.app K) ≫ δ'.app (H.obj K) ≫
      F.map ((d.symm ≪≫ q).hom.app K) = (c.symm ≪≫ e).hom.app (F.obj K) := by
  simp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, Functor.map_comp]
  apply (cancel_epi (c.hom.app (F.obj K))).1
  simp only [Iso.hom_inv_id_app_assoc]
  rw [reassoc_of% (hp K)]
  simp only [← F.map_comp]
  simpa using hi K

private theorem inverse_exchange_app_nt
    {A B A' B' : Type*} [Category A] [Category B] [Category A'] [Category B']
    (F : A ⥤ B) (F' : A' ⥤ B')
    {G : B ⥤ B'} {G' : B' ⥤ B} {G₀ : B ⥤ B}
    {H : A ⥤ A'} {H' : A' ⥤ A} {H₀ : A ⥤ A}
    (c : G₀ ≅ G ⋙ G') (d : H₀ ≅ H ⋙ H')
    (e : G₀ ≅ 𝟭 B) (q : H₀ ≅ 𝟭 A)
    (δ : F ⋙ G ⟶ H ⋙ F') (δ' : F' ⋙ G' ⟶ H' ⋙ F)
    (δ₀ : F ⋙ G₀ ⟶ H₀ ⋙ F)
    (hp : Functor.whiskerLeft F c.hom ≫ (Functor.associator F G G').inv ≫
      Functor.whiskerRight δ G' ≫ (Functor.associator H F' G').hom ≫
      Functor.whiskerLeft H δ' =
      δ₀ ≫ Functor.whiskerRight d.hom F ≫ (Functor.associator H H' F).hom)
    (hi : δ₀ ≫ Functor.whiskerRight q.hom F ≫ (Functor.leftUnitor F).hom =
      Functor.whiskerLeft F e.hom ≫ (Functor.rightUnitor F).hom) :
    ∀ K, G'.map (δ.app K) ≫ δ'.app (H.obj K) ≫
      F.map ((d.symm ≪≫ q).hom.app K) = (c.symm ≪≫ e).hom.app (F.obj K) := by
  have hu (K : A) : δ₀.app K ≫ F.map (q.hom.app K) = e.hom.app (F.obj K) := by
    have hh := congrArg (fun α ↦ α.app K) hi
    simpa using hh
  have hpa (K : A) : c.hom.app (F.obj K) ≫ G'.map (δ.app K) ≫
      δ'.app (H.obj K) = δ₀.app K ≫ F.map (d.hom.app K) := by
    have hh := congrArg (fun a ↦ a.app K) hp
    simpa using hh
  exact inverse_exchange_aux F F' c d e q δ δ' δ₀ hpa hu

private theorem inverse_exchange_whole
    {A B A' B' : Type*} [Category A] [Category B] [Category A'] [Category B']
    (F : A ⥤ B) (F' : A' ⥤ B')
    {G : B ⥤ B'} {G' : B' ⥤ B} {G₀ : B ⥤ B}
    {H : A ⥤ A'} {H' : A' ⥤ A} {H₀ : A ⥤ A}
    (c : G₀ ≅ G ⋙ G') (d : H₀ ≅ H ⋙ H')
    (e : G₀ ≅ 𝟭 B) (q : H₀ ≅ 𝟭 A)
    (δ : F ⋙ G ⟶ H ⋙ F') (δ' : F' ⋙ G' ⟶ H' ⋙ F)
    (δ₀ : F ⋙ G₀ ⟶ H₀ ⋙ F)
    (hp : Functor.whiskerLeft F c.hom ≫ (Functor.associator F G G').inv ≫
      Functor.whiskerRight δ G' ≫ (Functor.associator H F' G').hom ≫
      Functor.whiskerLeft H δ' =
      δ₀ ≫ Functor.whiskerRight d.hom F ≫ (Functor.associator H H' F).hom)
    (hi : δ₀ ≫ Functor.whiskerRight q.hom F ≫ (Functor.leftUnitor F).hom =
      Functor.whiskerLeft F e.hom ≫ (Functor.rightUnitor F).hom) :
    (Functor.associator F G G').inv ≫ Functor.whiskerRight δ G' ≫
      (Functor.associator H F' G').hom ≫ Functor.whiskerLeft H δ' ≫
      (Functor.associator H H' F).inv ≫
      Functor.whiskerRight (d.symm ≪≫ q).hom F ≫ (Functor.leftUnitor F).hom =
    Functor.whiskerLeft F (c.symm ≪≫ e).hom ≫ (Functor.rightUnitor F).hom := by
  refine NatTrans.ext (funext fun K ↦ ?_)
  simpa using inverse_exchange_app_nt F F' c d e q δ δ' δ₀ hp hi K

private theorem inverse_exchange_app_of_whole
    {A B A' B' : Type*} [Category A] [Category B] [Category A'] [Category B']
    (F : A ⥤ B) (F' : A' ⥤ B')
    {G : B ⥤ B'} {G' : B' ⥤ B} {H : A ⥤ A'} {H' : A' ⥤ A}
    (e : G ⋙ G' ≅ 𝟭 B) (q : H ⋙ H' ≅ 𝟭 A)
    (δ : F ⋙ G ⟶ H ⋙ F') (δ' : F' ⋙ G' ⟶ H' ⋙ F)
    (h : (Functor.associator F G G').inv ≫ Functor.whiskerRight δ G' ≫
      (Functor.associator H F' G').hom ≫ Functor.whiskerLeft H δ' ≫
      (Functor.associator H H' F).inv ≫
      Functor.whiskerRight q.hom F ≫ (Functor.leftUnitor F).hom =
      Functor.whiskerLeft F e.hom ≫ (Functor.rightUnitor F).hom) (K : A) :
    G'.map (δ.app K) ≫ δ'.app (H.obj K) ≫ F.map (q.hom.app K) =
      e.hom.app (F.obj K) := by
  have hh := congrArg (fun a ↦ a.app K) h
  simpa using hh

private theorem native_direct_inverse_whole {X Y X' Y' : Scheme.{u}}
    {f : X ⟶ Y} {f' : X' ⟶ Y'} {w : X' ⟶ X} {v : Y' ⟶ Y}
    [IsIso w] [IsIso v] (s : CommSq w f' f v)
    (s' : CommSq (inv w) f f' (inv v)) :
    (Functor.associator (R Λ f) (P Λ v) (P Λ (inv v))).inv ≫
      Functor.whiskerRight (baseChangeMap Λ s) (P Λ (inv v)) ≫
      (Functor.associator (P Λ w) (R Λ f') (P Λ (inv v))).hom ≫
      Functor.whiskerLeft (P Λ w) (baseChangeMap Λ s') ≫
      (Functor.associator (P Λ w) (P Λ (inv w)) (R Λ f)).inv ≫
      Functor.whiskerRight (pInverse Λ w).hom (R Λ f) ≫
      (Functor.leftUnitor (R Λ f)).hom =
    Functor.whiskerLeft (R Λ f) (pInverse Λ v).hom ≫
      (Functor.rightUnitor (R Λ f)).hom := by
  exact inverse_exchange_whole (R Λ f) (R Λ f')
    (leftDerivedUpperStarComp Λ (inv v) v) (leftDerivedUpperStarComp Λ (inv w) w)
    (eqToIso (congrArg (P Λ) (IsIso.inv_hom_id v)) ≪≫ leftDerivedUpperStarId Λ Y)
    (eqToIso (congrArg (P Λ) (IsIso.inv_hom_id w)) ≪≫ leftDerivedUpperStarId Λ X)
    (baseChangeMap Λ s) (baseChangeMap Λ s') (baseChangeMap Λ (s'.horiz_comp s))
    (native_direct_paste_nt Λ s s' (s'.horiz_comp s))
    (native_direct_identity_eq_nt Λ f (IsIso.inv_hom_id w) (IsIso.inv_hom_id v)
      (s'.horiz_comp s))

/-- The specified inverse-square direct exchange is the inverse, under native identifications.
Source: the source proof, paragraph 1
(blueprint: lem-fix-condensed-compactification-reindexing).
Proof: paste the square and its inverse. Pullback pasting contracts the two outside
compositors to `pInverse`. Direct identity exchange contracts the middle paste to
identity. Swapping the two squares gives the other inverse equation. -/
theorem direct_inverse {X Y X' Y' : Scheme.{u}}
    {f : X ⟶ Y} {f' : X' ⟶ Y'} {w : X' ⟶ X} {v : Y' ⟶ Y}
    [IsIso w] [IsIso v] (s : CommSq w f' f v)
    (s' : CommSq (inv w) f f' (inv v)) (K : D Λ X) :
    (P Λ (inv v)).map ((baseChangeMap Λ s).app K) ≫
        (baseChangeMap Λ s').app ((P Λ w).obj K) ≫
        (R Λ f).map ((pInverse Λ w).hom.app K) =
      (pInverse Λ v).hom.app ((R Λ f).obj K) := by
  exact inverse_exchange_app_of_whole (R Λ f) (R Λ f')
    (pInverse Λ v) (pInverse Λ w) (baseChangeMap Λ s) (baseChangeMap Λ s')
    (native_direct_inverse_whole Λ s s') K

private def inverseSquare {X Y X' Y' : Scheme.{u}}
    {f : X ⟶ Y} {f' : X' ⟶ Y'} {c : Compactification f} {c' : Compactification f'}
    {w : X' ⟶ X} {v : Y' ⟶ Y} [IsIso w] [IsIso v]
    (s : Square c c' w v) (s' : Square c' c (inv w) (inv v)) :
    Square c c (inv w ≫ w) (inv v ≫ v) where
  middle := s'.middle ≫ s.middle
  openSquare := s'.openSquare.paste_horiz s.openSquare
  properSquare := s'.properSquare.horiz_comp s.properSquare

private theorem native_compact_identity_eq_nt {X Y : Scheme.{u}} {f : X ⟶ Y}
    (c : Compactification f) {w : X ⟶ X} {v : Y ⟶ Y}
    (hw : w = 𝟙 X) (hv : v = 𝟙 Y) (s : Square c c w v) (hm : s.middle = 𝟙 c.Z) :
    squareExchange Λ s ≫ Functor.whiskerRight
      (eqToIso (congrArg (P Λ) hw) ≪≫ leftDerivedUpperStarId Λ X).hom (F Λ c) ≫
      (Functor.leftUnitor (F Λ c)).hom =
    Functor.whiskerLeft (F Λ c)
      (eqToIso (congrArg (P Λ) hv) ≪≫ leftDerivedUpperStarId Λ Y).hom ≫
      (Functor.rightUnitor (F Λ c)).hom := by
  subst w
  subst v
  simpa only [eqToIso_refl, Iso.refl_trans] using
    identity_exchange_nt (F Λ c) (leftDerivedUpperStarId Λ Y)
      (leftDerivedUpperStarId Λ X) (squareExchange Λ s)
      (fun K ↦ compact_identity Λ c s hm K)

private theorem native_compact_inverse_whole {X Y X' Y' : Scheme.{u}}
    {f : X ⟶ Y} {f' : X' ⟶ Y'} {c : Compactification f} {c' : Compactification f'}
    {w : X' ⟶ X} {v : Y' ⟶ Y} [IsIso w] [IsIso v]
    (s : Square c c' w v) [IsIso s.middle]
    (s' : Square c' c (inv w) (inv v)) (h : s'.middle = inv s.middle) :
    (Functor.associator (F Λ c) (P Λ v) (P Λ (inv v))).inv ≫
      Functor.whiskerRight (squareExchange Λ s) (P Λ (inv v)) ≫
      (Functor.associator (P Λ w) (F Λ c') (P Λ (inv v))).hom ≫
      Functor.whiskerLeft (P Λ w) (squareExchange Λ s') ≫
      (Functor.associator (P Λ w) (P Λ (inv w)) (F Λ c)).inv ≫
      Functor.whiskerRight (pInverse Λ w).hom (F Λ c) ≫
      (Functor.leftUnitor (F Λ c)).hom =
    Functor.whiskerLeft (F Λ c) (pInverse Λ v).hom ≫
      (Functor.rightUnitor (F Λ c)).hom := by
  have hm : (inverseSquare s s').middle = 𝟙 c.Z := by
    dsimp only [inverseSquare]
    rw [h, IsIso.inv_hom_id]
  exact inverse_exchange_whole (F Λ c) (F Λ c')
    (leftDerivedUpperStarComp Λ (inv v) v) (leftDerivedUpperStarComp Λ (inv w) w)
    (eqToIso (congrArg (P Λ) (IsIso.inv_hom_id v)) ≪≫ leftDerivedUpperStarId Λ Y)
    (eqToIso (congrArg (P Λ) (IsIso.inv_hom_id w)) ≪≫ leftDerivedUpperStarId Λ X)
    (squareExchange Λ s) (squareExchange Λ s') (squareExchange Λ (inverseSquare s s'))
    (native_compact_paste_nt Λ s s' (inverseSquare s s') rfl)
    (native_compact_identity_eq_nt Λ c (IsIso.inv_hom_id w) (IsIso.inv_hom_id v)
      (inverseSquare s s') hm)

set_option maxHeartbeats 1600000 in
-- Native derived functor endpoint comparisons exceed the default heartbeat allowance.
set_option maxHeartbeats 1600000 in
-- Native derived functor endpoint comparisons exceed the default heartbeat allowance.
/-- The actual inverse-diagram compact exchange, without choosing another inverse.
Source: the source proof, paragraph 1
(blueprint: lem-fix-condensed-compactification-reindexing).
Proof: apply compact pasting to the square and its inverse. The middle ambient
isomorphisms cancel, and compact identity gives the displayed equation. Swapping
the diagrams proves the reverse inverse equation. Only vertex exchanges are inverted. -/
theorem compact_inverse {X Y X' Y' : Scheme.{u}}
    {f : X ⟶ Y} {f' : X' ⟶ Y'} {c : Compactification f} {c' : Compactification f'}
    {w : X' ⟶ X} {v : Y' ⟶ Y} [IsIso w] [IsIso v]
    (s : Square c c' w v) [IsIso s.middle]
    (s' : Square c' c (inv w) (inv v)) (h : s'.middle = inv s.middle) (K : D Λ X) :
    (P Λ (inv v)).map ((squareExchange Λ s).app K) ≫
        (squareExchange Λ s').app ((P Λ w).obj K) ≫
        (F Λ c).map ((pInverse Λ w).hom.app K) =
      (pInverse Λ v).hom.app ((F Λ c).obj K) := by
  exact inverse_exchange_app_of_whole (F Λ c) (F Λ c')
    (pInverse Λ v) (pInverse Λ w) (squareExchange Λ s) (squareExchange Λ s')
    (native_compact_inverse_whole Λ s s' h) K

/-- A general isomorphism of refinement diagrams preserves the specified refinement map.
Source: the source proof, paragraph 3
(blueprint: lem-fix-condensed-compactification-reindexing).
Proof: the vertex isomorphisms identify the two pulled-back target opens, the
clopen sections, and their complementary opens. Both coordinates of the projector
are preserved. Open mate coherence identifies the adjuncts, and proper mate pasting
with the native direct compositor identifies their compact-support transposes.
This is the displayed equality; no field-linearity hypothesis enters. -/
theorem refinement_cube {X Y A B : Scheme.{u}} {f : X ⟶ Y} {g : A ⟶ B}
    {c₁ c₂ : Compactification f} {d₁ d₂ : Compactification g}
    (u : c₁.Refinement c₂) (z : d₁.Refinement d₂)
    {a : A ⟶ X} {b : B ⟶ Y} [IsIso a] [IsIso b]
    (s₁ : Square c₁ d₁ a b) (s₂ : Square c₂ d₂ a b)
    [IsIso s₁.middle] [IsIso s₂.middle]
    (h : z.hom ≫ s₂.middle = s₁.middle ≫ u.hom) (K : D Λ X) :
    (P Λ b).map ((refinement Λ u).app K) ≫ (squareExchange Λ s₁).app K =
      (squareExchange Λ s₂).app K ≫ (refinement Λ z).app ((P Λ a).obj K) := by
  sorry

/-- The specified open/proper diagram of the literal pullback model. -/
private def literalSquare {X Y Y' : Scheme.{u}} {f : X ⟶ Y}
    (c : Compactification f) (v : Y' ⟶ Y) :
    Square c (c.baseChange v) (pullback.fst f v) v where
  middle := pullback.fst c.g v
  openSquare := c.isPullback_i_ofIsPullback (IsPullback.of_hasPullback f v)
  properSquare := (IsPullback.of_hasPullback c.g v).toCommSq

/-- The literal exchange uses precisely the named pullback diagram. -/
private theorem exchange_literalSquare {X Y Y' : Scheme.{u}} {f : X ⟶ Y}
    (c : Compactification f) (v : Y' ⟶ Y) :
    exchange Λ c v = squareExchange Λ (literalSquare c v) := by
  delta exchange literalSquare
  rfl

/-- Isomorphism transport of the specified refinement, with its direction fixed.
Source: the source proof, paragraph 3
(blueprint: lem-fix-condensed-compactification-reindexing).
Proof: an isomorphism preserves the pulled-back open, its distinguished section and
the clopen projector on both coordinates. Thus it preserves the adjunct defining
refinement. Apply mate pasting to the proper adjunction and direct-image compositor;
this is exactly the displayed equation. No refinement map is inverted. -/
theorem refinement_exchange {X Y Y' : Scheme.{u}} {f : X ⟶ Y}
    {c₁ c₂ : Compactification f} (u : c₁.Refinement c₂) (v : Y' ⟶ Y) [IsIso v]
    (K : D Λ X) :
    (P Λ v).map ((refinement Λ u).app K) ≫ (exchange Λ c₁ v).app K =
      (exchange Λ c₂ v).app K ≫
        (refinement Λ (refinementBaseChange u v)).app ((P Λ (pullback.fst f v)).obj K) := by
  rw [exchange_literalSquare Λ c₁ v, exchange_literalSquare Λ c₂ v]
  have : IsIso (literalSquare c₁ v).middle := by
    dsimp only [literalSquare]
    infer_instance
  have : IsIso (literalSquare c₂ v).middle := by
    dsimp only [literalSquare]
    infer_instance
  exact refinement_cube Λ u (refinementBaseChange u v)
    (literalSquare c₁ v) (literalSquare c₂ v)
    (by simp only [literalSquare, refinementBaseChange, refinementBaseMap,
      pullback.lift_fst]) K

set_option maxHeartbeats 1600000 in
-- Native derived functor endpoint comparisons exceed the default heartbeat allowance.
end AlgebraicGeometry.ProEtale.CondensedRing.CompactificationReindexing
