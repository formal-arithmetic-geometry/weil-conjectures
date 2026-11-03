/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Diagonal.DiagonalTowerSystem
public import WeilConjectures.AlgebraicGeometry.Diagonal.DiagonalTowerLimitInterface
public import WeilConjectures.AlgebraicGeometry.Diagonal.DiagonalLimitAssembly
public import WeilConjectures.AlgebraicGeometry.Completed.CompletedCondensedCoefficients
public import WeilConjectures.AlgebraicGeometry.Internal.InternalSignedTateTwist
public import WeilConjectures.AlgebraicGeometry.AdicCompletion.DerivedCompletionSupplement
public import WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
public import Mathlib.CategoryTheory.Triangulated.Functor
import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleSurjectiveTowerDerivedLimitSupplement
import WeilConjectures.ProperBaseChange.RingedStrictTowerHomotopyLimitIndependentCoefficients
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.ClosedImmersion
import WeilConjectures.AlgebraicGeometry.ProEtaleInverseImage
import WeilConjectures.CategoryTheory.Ringed.RingedTowerPushforwardLimitComparison
import WeilConjectures.Algebra.Homology.LineUnbounded.LineUnboundedDerivedTensor
import WeilConjectures.ProperBaseChange.ConstantCompletionCore
import WeilConjectures.NumberTheory.Padics.ExtensionIntegersDvr
import WeilConjectures.AlgebraicGeometry.Completed.CompletedCoefficientFiniteUnit
import WeilConjectures.CategoryTheory.AdicSites.CompletionUnitFiniteProjection
import WeilConjectures.Algebra.Homology.SixFunctors.OrdinaryDerivedChangeOfRings
public import WeilConjectures.Algebra.Homology.FlatSingleDerivedNormalization.FlatSingleDerivedNormalization
public import WeilConjectures.Algebra.Homology.LineEvaluation.LineEvaluationInversePair
public import WeilConjectures.AlgebraicGeometry.Diagonal.DiagonalAdicEvaluationComparison
public import WeilConjectures.AlgebraicGeometry.Diagonal.DiagonalCompletedDataAssembly
public import WeilConjectures.AlgebraicGeometry.Diagonal.DiagonalCompletedReductionRestriction
public import WeilConjectures.AlgebraicGeometry.Diagonal.DiagonalLimitSpecificationAPI
public import WeilConjectures.AlgebraicGeometry.Diagonal.DiagonalStrictLimitData
public import WeilConjectures.AlgebraicGeometry.Diagonal.DiagonalSupportedOrdinaryLimit
public import WeilConjectures.AlgebraicGeometry.DiagonalEndpointsProof.DiagonalLimitEndpointsAux
public import WeilConjectures.AlgebraicGeometry.DiagonalTrace.DiagonalCompleteScalarRestrictionCore
public import WeilConjectures.AlgebraicGeometry.Pur.PurTwistRootLocalModels
public import WeilConjectures.CategoryTheory.SmoothPurity.CanonicalRightDerivedAdjunctionShift
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import WeilConjectures.ProEtaleCoefficients.RingedStrictTowerHomotopyLimit

/-! # The completed diagonal class on an arbitrary base

Source: latest blueprint, sec-six-functors-basics/sk-prop-diagonal-tower/
sk-prop-diagonal-tower-limit.md, clauses 1--3; Stacks Tags 099L and 099I
(blueprint: det-prop-diagonal-tower-limit).

The strict towers have constant discrete Z_l coefficients. Their completed endpoints
use the limit ring sheaf, canonically identified with the pulled-back condensed ring.
The existing sectionwise module presentation retains the coefficient action and is
canonically equivalent to internal modules. Positive level n+1 is indexed by n.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe u

open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.ProEtale

private theorem mapTransition
    {C : Type u} {D : Type v} [Category.{w} C] [Category.{x} D]
    [Preadditive C] [Preadditive D] (F : C ⥤ D) [F.Additive]
    {K : ℕ → C} [HasProduct K]
    [HasProduct (fun n => F.obj (K n))] (f : ∀ n, K (n + 1) ⟶ K n)
    (e : F.obj (∏ᶜ K) ≅ ∏ᶜ (fun n => F.obj (K n)))
    (he : ∀ n, e.hom ≫ Pi.π _ n = F.map (Pi.π K n)) :
    F.map (towerTransitionEndomorphism f) ≫ e.hom =
      e.hom ≫ towerTransitionEndomorphism (fun n => F.map (f n)) := by
  apply Pi.hom_ext
  intro n
  simp only [towerTransitionEndomorphism, towerProductShift, Functor.map_sub,
    Preadditive.sub_comp, Preadditive.comp_sub, Category.assoc,
    Pi.lift_π, Category.id_comp, he]
  simp only [← F.map_comp, Pi.lift_π, Category.id_comp]
  rw [← Category.assoc, he, ← F.map_comp]

private theorem mapRoos
    {C : Type u} {D : Type v} [Category.{w} C] [Category.{x} D]
    [HasZeroObject C] [HasShift C ℤ] [Preadditive C]
    [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
    [HasZeroObject D] [HasShift D ℤ] [Preadditive D]
    [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]
    (F : C ⥤ D) [F.CommShift ℤ] [F.Additive] [F.IsTriangulated]
    {K : ℕ → C} [HasProduct K]
    [HasProduct (fun n => F.obj (K n))] (f : ∀ n, K (n + 1) ⟶ K n)
    (L : C) (p : L ⟶ ∏ᶜ K) (δ : ∏ᶜ K ⟶ L⟦(1 : ℤ)⟧)
    (h : IsDerivedLimitTriangle f L p δ)
    (e : F.obj (∏ᶜ K) ≅ ∏ᶜ (fun n => F.obj (K n)))
    (he : ∀ n, e.hom ≫ Pi.π _ n = F.map (Pi.π K n)) :
    IsDerivedLimitTriangle (fun n => F.map (f n)) (F.obj L) (F.map p ≫ e.hom)
      (e.inv ≫ F.map δ ≫ (F.commShiftIso (1 : ℤ)).hom.app L) := by
  let T := Triangle.mk p (towerTransitionEndomorphism f) δ
  let T' := Triangle.mk (F.map p ≫ e.hom)
    (towerTransitionEndomorphism (fun n => F.map (f n)))
    (e.inv ≫ F.map δ ≫ (F.commShiftIso (1 : ℤ)).hom.app L)
  let q : F.mapTriangle.obj T ≅ T' :=
    Triangle.isoMk _ _ (Iso.refl _) e e (by
      change F.map p ≫ e.hom = 𝟙 _ ≫ (F.map p ≫ e.hom)
      simp)
      (mapTransition F f e he) (by
        change (F.map δ ≫ (F.commShiftIso (1 : ℤ)).hom.app L) ≫
          (shiftFunctor D (1 : ℤ)).map (𝟙 _) =
            e.hom ≫ (e.inv ≫ F.map δ ≫ (F.commShiftIso (1 : ℤ)).hom.app L)
        simp)
  exact isomorphic_distinguished _ (F.map_distinguished T h) _ q.symm

/-- The generic direct-image assertion, sharing its categorical structures.
Source: blueprint clause 1 (blueprint: det-prop-diagonal-tower-limit). -/
private def diagonalDirectImageAssertion
    {A : Type a} [Category.{v} A] [Abelian A]
    {B : Type b} [Category.{u} B] [Abelian B]
    [HasDerivedCategory.{w} A] [HasDerivedCategory.{w} B]
    [HasDerivedCategory.{w} (ℕᵒᵖ ⥤ A)] [HasDerivedCategory.{w} (ℕᵒᵖ ⥤ B)]
    [HasLimitsOfShape ℕᵒᵖ A] [HasLimitsOfShape ℕᵒᵖ B]
    (F : A ⥤ B) [F.Additive] : Prop :=
    ∃ (LX : DiagonalRlim A) (LY : DiagonalRlim B)
      (Rf : DiagonalRightDerived (F))
      (Rt : DiagonalRightDerived ((Functor.whiskeringRight ℕᵒᵖ
        A B).obj
          (F)))
      (e : ∀ n : ℕ, Rt.R ⋙
        ((evaluation ℕᵒᵖ B).obj (op n)).mapDerivedCategory ≅
        ((evaluation ℕᵒᵖ A).obj (op n)).mapDerivedCategory ⋙ Rf.R)
      (c : LX.R ⋙ Rf.R ≅ Rt.R ⋙ LY.R)
      (c₀ : (lim : (ℕᵒᵖ ⥤ A) ⥤ A) ⋙
          F ≅
        (Functor.whiskeringRight ℕᵒᵖ A B).obj
          (F) ⋙ lim),
      (∀ H : (ℕᵒᵖ ⥤ A),
        c₀.hom.app H = limit.post H
          (F)) ∧
      (∀ P : CochainComplex ((ℕᵒᵖ ⥤ A)) ℤ,
        Rf.η.app (((lim : (ℕᵒᵖ ⥤ A) ⥤ A).mapHomologicalComplex
          (.up ℤ)).obj P) ≫ Rf.R.map (LX.η.app P) ≫ c.hom.app (DerivedCategory.Q.obj P) =
        DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex c₀.hom (.up ℤ)).app P) ≫
          LY.η.app ((((Functor.whiskeringRight ℕᵒᵖ
            A B).obj
              (F)).mapHomologicalComplex
                (.up ℤ)).obj P) ≫ LY.R.map (Rt.η.app P)) ∧
      (∀ (P : CochainComplex ((ℕᵒᵖ ⥤ A)) ℤ), P.IsKInjective → ∀ n : ℕ,
        ((evaluation ℕᵒᵖ B).obj (op n)).mapDerivedCategory.map (Rt.η.app P) ≫
          (e n).hom.app (DerivedCategory.Q.obj P) ≫
          Rf.R.map (((evaluation ℕᵒᵖ A).obj
            (op n)).mapDerivedCategoryFactors.hom.app P) =
        ((evaluation ℕᵒᵖ B).obj (op n)).mapDerivedCategoryFactors.hom.app
          ((((Functor.whiskeringRight ℕᵒᵖ A B).obj
            (F)).mapHomologicalComplex
              (.up ℤ)).obj P) ≫ Rf.η.app (P.asFunctor.obj (op n))) ∧
      ∀ (M : DerivedCategory ((ℕᵒᵖ ⥤ A))) (n : ℕ),
        c.hom.app M ≫ (LY.projection n).app (Rt.R.obj M) ≫ (e n).hom.app M =
          Rf.R.map ((LX.projection n).app M)

private theorem diagonal_limit_endpoints (ℓ : ℕ) [Fact ℓ.Prime]
    (Y : Scheme.{u}) (hY : IsUnit (ℓ : Γ(Y, ⊤)))
    [HasDerivedCategory.{u + 1} (DiagonalAb (diagonalSurface Y))]
    [HasDerivedCategory.{u + 1} (DiagonalMod ℓ (diagonalSurface Y))]
    [HasDerivedCategory.{u + 1} (DiagonalSystems ℓ (diagonalSurface Y))]
    [HasDerivedCategory.{u + 1} (ℕᵒᵖ ⥤ DiagonalAb (diagonalSurface Y))]
    [HasDerivedCategory.{u + 1} (DiagonalCompleted ℓ (diagonalSurface Y))]
    [HasDerivedCategory.{u + 1} (ℕᵒᵖ ⥤ DiagonalCompleted ℓ (diagonalSurface Y))]
    [HasExt.{u + 1} (DiagonalSystems ℓ (diagonalSurface Y))]
    (D : DiagonalDerivedReduction ℓ (diagonalScalarExtension ℓ (diagonalSurface Y)))
    (hcompletion : DiagonalCompletionSpec ℓ (diagonalSurface Y) D)
    (H : DiagonalSystems ℓ (diagonalSurface Y))
    (roots : H ⋙ diagonalForget ℓ (diagonalSurface Y) ≅
      Scheme.proEtaleRootsOfUnityTower (diagonalSurface Y) ℓ (Fact.out : ℓ.Prime))
    (a : D.T.obj ((DerivedCategory.singleFunctor _ 0).obj (diagonalIntegralSource Y)) ≅
      (DerivedCategory.singleFunctor _ 0).obj (D.ordinary.E.obj (diagonalIntegralSource Y)))
    (b : D.T.obj (((DerivedCategory.singleFunctor _ 0).obj
      (diagonalComparisonUnits Y))⟦(1 : ℤ)⟧) ≅
      ((DerivedCategory.singleFunctor _ 0).obj H)⟦(2 : ℤ)⟧) :
    ∃ (L : DiagonalRlim (DiagonalMod ℓ (diagonalSurface Y)))
      (s : (diagonalCompletedRestriction ℓ (diagonalSurface Y)).obj
        (diagonalCompletedSource ℓ Y) ≅ limit (D.ordinary.E.obj (diagonalIntegralSource Y)))
      (t : (diagonalCompletedRestriction ℓ (diagonalSurface Y)).obj
        (Scheme.purTwistZlModule (diagonalSurface Y) ℓ) ≅ limit H),
      (∀ n : ℕ,
        diagonalCompletedGenerator ℓ Y ≫ (diagonalForget ℓ (diagonalSurface Y)).map
          (s.hom ≫ limit.π (D.ordinary.E.obj (diagonalIntegralSource Y)) (op n)) =
        (diagonalScalarAdjunction ℓ (diagonalSurface Y)).unit.app (diagonalIntegralSource Y) ≫
          (diagonalForget ℓ (diagonalSurface Y)).map
            ((D.ordinary.π n).app (diagonalIntegralSource Y))) ∧
      HEq ((diagonalForget ℓ (diagonalSurface Y)).map t.hom)
        (diagonalRootLimitComparison ℓ (diagonalSurface Y) H roots).inv ∧
      IsIso (diagonalSourceLimitMap ℓ Y D a L s) ∧
      IsIso (diagonalTargetLimitMap ℓ Y D H b L t) ∧
      (∀ V : DerivedCategory (DiagonalCompleted ℓ (diagonalSurface Y)),
        IsIso (ℓ • 𝟙 V) → Subsingleton (V ⟶ diagonalCompletedDomain ℓ Y)) ∧
      (∀ V : DerivedCategory (DiagonalCompleted ℓ (diagonalSurface Y)),
        IsIso (ℓ • 𝟙 V) → Subsingleton (V ⟶ diagonalCompletedCodomain ℓ Y)) ∧
      (∀ V : DerivedCategory (DiagonalMod ℓ (diagonalSurface Y)),
        IsIso (ℓ • 𝟙 V) → Subsingleton (V ⟶
          (diagonalCompletedUnderlying ℓ (diagonalSurface Y)).obj
            (diagonalCompletedDomain ℓ Y))) ∧
      (∀ V : DerivedCategory (DiagonalMod ℓ (diagonalSurface Y)),
        IsIso (ℓ • 𝟙 V) → Subsingleton (V ⟶
          (diagonalCompletedUnderlying ℓ (diagonalSurface Y)).obj
            (diagonalCompletedCodomain ℓ Y))) := by
  have _ := hcompletion
  clear hcompletion
  classical
  let X := diagonalSurface Y
  let S := D.ordinary.E.obj (diagonalIntegralSource Y)
  let s := (diagonal_supported_ordinary_limit ℓ Y D.ordinary).choose
  have hs := (diagonal_supported_ordinary_limit ℓ Y D.ordinary).choose_spec
  let t := (root_limit_iso ℓ X H roots).choose
  have ht := (root_limit_iso ℓ X H roots).choose_spec
  let L := Classical.choice (moduleRlim_exists ℓ X)
  have hS : IsIso (diagonalOrdinaryRlim L S) :=
    ordinaryRlim_isIso_of_epi ℓ X L S
      (ordinary_tower_epi ℓ (diagonalScalarExtension ℓ X) D.ordinary _)
  have hX : IsUnit (ℓ : Γ(X, ⊤)) := by
    simpa only [Nat.zero_add, pow_one] using diagonalSurface_power_unit ℓ Y hY 0
  have hHepi (n : ℕ) : Epi (H.map (homOfLE (Nat.le_succ n)).op) :=
    root_system_epi ℓ X hX H roots n
  have hH : IsIso (diagonalOrdinaryRlim L H) :=
    ordinaryRlim_isIso_of_epi ℓ X L H hHepi
  have hsource : IsIso (diagonalSourceLimitMap ℓ Y D a L s) :=
    sourceLimitMap_isIso ℓ Y D a L s hS
  have htarget : IsIso (diagonalTargetLimitMap ℓ Y D H b L t) :=
    targetLimitMap_isIso ℓ Y D H b L t hH
  have hSkill (n : ℕ) : ℓ ^ (n + 1) • 𝟙 (S.obj (op n)) = 0 :=
    ordinary_tower_killed ℓ (diagonalScalarExtension ℓ X) D.ordinary _ n
  have hHkill (n : ℕ) : ℓ ^ (n + 1) • 𝟙 (H.obj (op n)) = 0 :=
    root_system_killed ℓ X H roots n
  -- Finite torsion and exact products give completeness in both coefficient categories.
  exact ⟨L, s, t, hs, ht, hsource, htarget,
    completedEndpoints_orthogonal ℓ X (2 : ℤ)
      (diagonalCompletedSource ℓ Y) (Scheme.purTwistZlModule X ℓ) S H s t hSkill hHkill⟩

private theorem diagonal_limit_finite_reduction (ℓ : ℕ) [Fact ℓ.Prime]
    (Y : Scheme.{u}) (hY : IsUnit (ℓ : Γ(Y, ⊤)))
    [HasDerivedCategory.{u + 1} (DiagonalAb (diagonalSurface Y))]
    [HasDerivedCategory.{u + 1} (DiagonalMod ℓ (diagonalSurface Y))]
    [HasDerivedCategory.{u + 1} (DiagonalSystems ℓ (diagonalSurface Y))]
    [HasDerivedCategory.{u + 1} (ℕᵒᵖ ⥤ DiagonalAb (diagonalSurface Y))]
    [HasDerivedCategory.{u + 1} (DiagonalCompleted ℓ (diagonalSurface Y))]
    [HasDerivedCategory.{u + 1} (ℕᵒᵖ ⥤ DiagonalCompleted ℓ (diagonalSurface Y))]
    [HasExt.{u + 1} (DiagonalSystems ℓ (diagonalSurface Y))]
    (D : DiagonalDerivedReduction ℓ (diagonalScalarExtension ℓ (diagonalSurface Y)))
    (hcompletion : DiagonalCompletionSpec ℓ (diagonalSurface Y) D)
    (H : DiagonalSystems ℓ (diagonalSurface Y))
    (a : D.T.obj ((DerivedCategory.singleFunctor _ 0).obj (diagonalIntegralSource Y)) ≅
      (DerivedCategory.singleFunctor _ 0).obj (D.ordinary.E.obj (diagonalIntegralSource Y)))
    (b : D.T.obj (((DerivedCategory.singleFunctor _ 0).obj
      (diagonalComparisonUnits Y))⟦(1 : ℤ)⟧) ≅
      ((DerivedCategory.singleFunctor _ 0).obj H)⟦(2 : ℤ)⟧)
    (L : DiagonalRlim (DiagonalMod ℓ (diagonalSurface Y)))
    (s : (diagonalCompletedRestriction ℓ (diagonalSurface Y)).obj
      (diagonalCompletedSource ℓ Y) ≅ limit (D.ordinary.E.obj (diagonalIntegralSource Y)))
    (t : (diagonalCompletedRestriction ℓ (diagonalSurface Y)).obj
      (Scheme.purTwistZlModule (diagonalSurface Y) ℓ) ≅ limit H)
    (hs : IsIso (diagonalSourceLimitMap ℓ Y D a L s))
    (ht : IsIso (diagonalTargetLimitMap ℓ Y D H b L t)) :
    let F := diagonalCompletedUnderlying ℓ (diagonalSurface Y)
    let E := fun n : ℕ ↦
      ((evaluation ℕᵒᵖ (DiagonalMod ℓ (diagonalSurface Y))).obj (op n)).mapDerivedCategory
    let C := fun n : ℕ ↦
      ((evaluation ℕᵒᵖ (DiagonalCompleted ℓ (diagonalSurface Y))).obj (op n)).mapDerivedCategory
    ∃ M : DiagonalCompletedReduction ℓ (diagonalSurface Y),
      ∀ (f : (DerivedCategory.singleFunctor _ 0).obj (diagonalIntegralSource Y) ⟶
        ((DerivedCategory.singleFunctor _ 0).obj
          (diagonalComparisonUnits Y))⟦(1 : ℤ)⟧)
        (δ : diagonalCompletedDomain ℓ Y ⟶ diagonalCompletedCodomain ℓ Y),
        F.map δ ≫ diagonalTargetLimitMap ℓ Y D H b L t =
          diagonalSourceLimitMap ℓ Y D a L s ≫ L.R.map (D.T.map f) → ∀ n : ℕ,
        ∃ (e : F.obj ((C n).obj (M.derived.T.obj (diagonalCompletedDomain ℓ Y))) ≅
            (E n).obj (D.T.obj
              ((DerivedCategory.singleFunctor _ 0).obj (diagonalIntegralSource Y))))
          (g : F.obj ((C n).obj (M.derived.T.obj (diagonalCompletedCodomain ℓ Y))) ≅
            (E n).obj (D.T.obj
              (((DerivedCategory.singleFunctor _ 0).obj
                (diagonalComparisonUnits Y))⟦(1 : ℤ)⟧))),
          F.map ((M.unit n).app (diagonalCompletedDomain ℓ Y)) ≫ e.hom =
            diagonalSourceLimitMap ℓ Y D a L s ≫ (L.projection n).app _ ∧
          F.map ((M.unit n).app (diagonalCompletedCodomain ℓ Y)) ≫ g.hom =
            diagonalTargetLimitMap ℓ Y D H b L t ≫ (L.projection n).app _ ∧
          F.map ((C n).map (M.derived.T.map δ)) =
            e.hom ≫ (E n).map (D.T.map f) ≫ g.inv := by
  classical
  have _ := hY
  let F := diagonalCompletedUnderlying ℓ (diagonalSurface Y)
  let E := fun n : ℕ ↦
    ((evaluation ℕᵒᵖ (DiagonalMod ℓ (diagonalSurface Y))).obj (op n)).mapDerivedCategory
  let C := fun n : ℕ ↦
    ((evaluation ℕᵒᵖ (DiagonalCompleted ℓ (diagonalSurface Y))).obj (op n)).mapDerivedCategory
  obtain ⟨M, N, hα⟩ := diagonal_completed_reduction_restriction ℓ (diagonalSurface Y)
  refine ⟨M, ?_⟩
  intro f δ hδ n
  obtain ⟨α, hαunit⟩ := hα n
  obtain ⟨β, hβunit⟩ := diagonal_adic_evaluation_comparison ℓ (diagonalSurface Y)
    D hcompletion L N n
  let B := N.derived.T ⋙ E n
  let source := diagonalSourceLimitMap ℓ Y D a L s
  let target := diagonalTargetLimitMap ℓ Y D H b L t
  let : IsIso source := hs
  let : IsIso target := ht
  let e := α.app (diagonalCompletedDomain ℓ Y) ≪≫
    B.mapIso (asIso source) ≪≫ β.app _
  let g := α.app (diagonalCompletedCodomain ℓ Y) ≪≫
    B.mapIso (asIso target) ≪≫ β.app _
  refine ⟨e, g, ?_, ?_, ?_⟩
  · change F.map ((M.unit n).app _) ≫
      (α.hom.app _ ≫ B.map source ≫ β.hom.app _) = _
    rw [← Category.assoc, hαunit]
    rw [← (N.unit n).naturality_assoc source]
    rw [hβunit]
    rfl
  · change F.map ((M.unit n).app _) ≫
      (α.hom.app _ ≫ B.map target ≫ β.hom.app _) = _
    rw [← Category.assoc, hαunit]
    rw [← (N.unit n).naturality_assoc target]
    rw [hβunit]
    rfl
  · apply (cancel_mono g.hom).1
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    change F.map ((C n).map (M.derived.T.map δ)) ≫
      (α.hom.app _ ≫ B.map target ≫ β.hom.app _) =
      (α.hom.app _ ≫ B.map source ≫ β.hom.app _) ≫ (E n).map (D.T.map f)
    have hαδ := α.hom.naturality δ
    change F.map ((C n).map (M.derived.T.map δ)) ≫ α.hom.app _ =
      α.hom.app _ ≫ B.map (F.map δ) at hαδ
    rw [reassoc_of% hαδ]
    change α.hom.app _ ≫ B.map (F.map δ) ≫ B.map target ≫ β.hom.app _ = _
    rw [← B.map_comp_assoc, hδ, B.map_comp_assoc]
    change α.hom.app _ ≫ B.map source ≫
      B.map (L.R.map (D.T.map f)) ≫ β.hom.app _ = _
    have hβf := β.hom.naturality f
    change B.map (L.R.map (D.T.map f)) ≫ β.hom.app _ =
      β.hom.app _ ≫ (E n).map (D.T.map f) at hβf
    rw [hβf]
    simp only [Category.assoc]

private theorem diagonal_limit_completed_data (ℓ : ℕ) [Fact ℓ.Prime]
    (Y : Scheme.{u}) (hY : IsUnit (ℓ : Γ(Y, ⊤)))
    [HasDerivedCategory.{u + 1} (DiagonalAb (diagonalSurface Y))]
    [HasDerivedCategory.{u + 1} (DiagonalMod ℓ (diagonalSurface Y))]
    [HasDerivedCategory.{u + 1} (DiagonalSystems ℓ (diagonalSurface Y))]
    [HasDerivedCategory.{u + 1} (ℕᵒᵖ ⥤ DiagonalAb (diagonalSurface Y))]
    [HasDerivedCategory.{u + 1} (DiagonalCompleted ℓ (diagonalSurface Y))]
    [HasDerivedCategory.{u + 1} (ℕᵒᵖ ⥤ DiagonalCompleted ℓ (diagonalSurface Y))]
    [HasExt.{u + 1} (DiagonalSystems ℓ (diagonalSurface Y))]
    (D : DiagonalDerivedReduction ℓ (diagonalScalarExtension ℓ (diagonalSurface Y)))
    (hcompletion : DiagonalCompletionSpec ℓ (diagonalSurface Y) D)
    (H : DiagonalSystems ℓ (diagonalSurface Y))
    (roots : H ⋙ diagonalForget ℓ (diagonalSurface Y) ≅
      Scheme.proEtaleRootsOfUnityTower (diagonalSurface Y) ℓ (Fact.out : ℓ.Prime))
    (a : D.T.obj ((DerivedCategory.singleFunctor _ 0).obj (diagonalIntegralSource Y)) ≅
      (DerivedCategory.singleFunctor _ 0).obj (D.ordinary.E.obj (diagonalIntegralSource Y)))
    (b : D.T.obj (((DerivedCategory.singleFunctor _ 0).obj
      (diagonalComparisonUnits Y))⟦(1 : ℤ)⟧) ≅
      ((DerivedCategory.singleFunctor _ 0).obj H)⟦(2 : ℤ)⟧) :
    diagonalCompleteDataAssertion ℓ (diagonalCompletedRestriction ℓ (diagonalSurface Y))
      (diagonalCompletedSource ℓ Y) (Scheme.purTwistZlModule (diagonalSurface Y) ℓ)
      (D.ordinary.E.obj (diagonalIntegralSource Y)) H _ _
      (D.T.map (diagonalIntegralBoundary Y).hom) a b
      (fun s ↦ ∀ n : ℕ,
        diagonalCompletedGenerator ℓ Y ≫ (diagonalForget ℓ (diagonalSurface Y)).map
          (s.hom ≫ limit.π (D.ordinary.E.obj (diagonalIntegralSource Y)) (op n)) =
        (diagonalScalarAdjunction ℓ (diagonalSurface Y)).unit.app (diagonalIntegralSource Y) ≫
          (diagonalForget ℓ (diagonalSurface Y)).map
            ((D.ordinary.π n).app (diagonalIntegralSource Y)))
      (fun t ↦ HEq ((diagonalForget ℓ (diagonalSurface Y)).map t.hom)
        (diagonalRootLimitComparison ℓ (diagonalSurface Y) H roots).inv) := by
  classical
  refine Exists.elim
    (diagonal_limit_endpoints ℓ Y hY D hcompletion H roots a b) (fun L hL ↦ ?_)
  refine Exists.elim hL (fun s hsrest ↦ ?_)
  refine Exists.elim hsrest (fun t hparts ↦ ?_)
  obtain ⟨hs, ht, hsource, htarget, hP, hQ, hPC, hQC⟩ := hparts
  refine Exists.elim (diagonal_limit_finite_reduction ℓ Y hY D hcompletion
    H a b L s t hsource htarget) (fun M hM ↦ ?_)
  let F := diagonalCompletedUnderlying ℓ (diagonalSurface Y)
  have hF : Function.Bijective (fun δ : diagonalCompletedDomain ℓ Y ⟶
      diagonalCompletedCodomain ℓ Y ↦ F.map δ) := by
    as_aux_lemma =>
      let complete : ObjectProperty
          (DerivedCategory (DiagonalCompleted ℓ (diagonalSurface Y))) :=
        fun P ↦ ∀ V : DerivedCategory (DiagonalMod ℓ (diagonalSurface Y)),
          IsIso (ℓ • 𝟙 V) → Subsingleton (V ⟶ F.obj P)
      obtain ⟨ff⟩ := DiagonalTrace.diagonalCompleteScalarRestrictionCore ℓ (diagonalSurface Y)
      let P : complete.FullSubcategory := ⟨diagonalCompletedDomain ℓ Y, hPC⟩
      let Q : complete.FullSubcategory := ⟨diagonalCompletedCodomain ℓ Y, hQC⟩
      constructor
      · intro x y h
        have hxy : (ObjectProperty.homMk x : P ⟶ Q) = ObjectProperty.homMk y :=
          ff.map_injective h
        exact congrArg (fun f : P ⟶ Q ↦ f.hom) hxy
      · intro f
        obtain ⟨g, hg⟩ := ff.map_surjective (X := P) (Y := Q) f
        exact ⟨g.hom, hg⟩
  apply diagonalCompleteData_of_bijective
    ℓ (diagonalCompletedRestriction ℓ (diagonalSurface Y)) _ _ _ _ _ _
    (D.T.map (diagonalIntegralBoundary Y).hom) a b _ _ L M s t hs ht
    hsource htarget hP hQ hF
  intro δ hδ n
  obtain ⟨e, g, he, hg, hmap⟩ := hM (diagonalIntegralBoundary Y).hom δ hδ n
  exact ⟨e, g, he, hg, hmap⟩

private theorem diagonal_limit_typed_data (ℓ : ℕ) [Fact ℓ.Prime]
    (Y : Scheme.{u}) (hY : IsUnit (ℓ : Γ(Y, ⊤)))
    [HasDerivedCategory.{u + 1} (DiagonalAb (diagonalSurface Y))]
    [HasDerivedCategory.{u + 1} (DiagonalMod ℓ (diagonalSurface Y))]
    [HasExt.{u + 1} (DiagonalMod ℓ (diagonalSurface Y))]
    [HasDerivedCategory.{u + 1} (DiagonalSystems ℓ (diagonalSurface Y))]
    [HasDerivedCategory.{u + 1} (ℕᵒᵖ ⥤ DiagonalAb (diagonalSurface Y))]
    [HasDerivedCategory.{u + 1} (DiagonalCompleted ℓ (diagonalSurface Y))]
    [HasDerivedCategory.{u + 1} (ℕᵒᵖ ⥤ DiagonalCompleted ℓ (diagonalSurface Y))]
    [HasExt.{u + 1} (DiagonalSystems ℓ (diagonalSurface Y))]
    (D : DiagonalDerivedReduction ℓ (diagonalScalarExtension ℓ (diagonalSurface Y)))
    (hcompletion : DiagonalCompletionSpec ℓ (diagonalSurface Y) D)
    (hsystem : DiagonalCycleSystemSpec ℓ Y hY D) :
  DiagonalTypedLimitSpec ℓ Y hY D := by
  unfold DiagonalTypedLimitSpec
  -- Keep the normalizers and implicit instances exactly as stored in the specification.
  run_tac withMainContext do
    let source := (← getMainTarget).consumeMData
    unless source.isAppOf ``DiagonalLimitDataSpec do
      throwError "Unexpected diagonal limit specification"
    let names : Array Name := #[`ℓ, `Y, `hY, `D, `hsystem]
    let args ← names.mapM fun name => do
      let some decl := (← getLCtx).findFromUserName? name | throwError "Missing {name}"
      pure decl.toExpr
    let strict ← mkAppM ``diagonal_strict_limit_data args
    let proof ← mkAppOptM ``diagonalLimitData_of_strict
      ((source.getAppArgs.map some) ++ #[some strict])
    replaceMainGoal (← (← getMainGoal).apply proof)
  intro H roots a b
  run_tac withMainContext do
    let names : Array Name := #[`ℓ, `Y, `hY, `D, `hcompletion,
      `H, `roots, `a, `b]
    let args ← names.mapM fun name => do
      let some decl := (← getLCtx).findFromUserName? name | throwError "Missing {name}"
      pure decl.toExpr
    let proof ← mkAppM ``diagonal_limit_completed_data args
    (← getMainGoal).assign proof
    replaceMainGoal []

/-- The supported coefficient tower and the root tower have the completed endpoints,
and the limit of the strict diagonal class has a unique completed-coefficient lift.
Its finite reductions are the normalized torsion Cartier classes.

Source: latest blueprint, clauses 1 and 3; Stacks Tags 099L and 099I
(blueprint: det-prop-diagonal-tower-limit).

Proof:
1. On the compatible-root cover the root tower is the quotient tower. Its power
   transitions and the quotient transitions are epimorphisms. Repleteness and exact
   products identify their derived limits with their ordinary limits. The normalized
   coefficient limit comparison gives Z_l and the coordinatewise root limit gives Z_l(1).
2. The diagonal complement is quasi-compact, as checked on the four affine product
   charts by D(x-y) and D(xy-1). Thus diagonal direct image is exact and preserves
   limits. The same surjective-tower comparison gives the supported completed source.
3. The strict-system theorem identifies c with simultaneous derived reduction of the
   positive Cartier boundary. Its completion specification identifies Rlim(c) with
   completion of that boundary, including the completion unit. Both endpoints are
   derived ell-complete, equivalently right orthogonal to ell-invertible complexes.
4. For the constant Z_l ring, completion along (ell) is the completed coefficient
   sheaf just identified. Constant/completed scalar restriction is an equivalence on
   complete objects. Full faithfulness gives exactly one lift of the entire underlying
   limit arrow, with the source generator and root-limit comparisons fixed.
5. Reduction of the completion unit is invertible. Its inverse is adjoint to the
   finite tower projection. Naturality and the finite change-of-rings comparison
   identify each reduction of the lifted arrow with c_n, the positive torsion Cartier
   cycle class. This uses the unit/projection comparison, not uniqueness from levels. -/
theorem diagonalTower_limit_general (ℓ : ℕ) [Fact ℓ.Prime] (Y : Scheme.{u})
    (hY : IsUnit (ℓ : Γ(Y, ⊤)))
    [HasDerivedCategory.{u + 1} (DiagonalAb (diagonalSurface Y))]
    [HasDerivedCategory.{u + 1} (DiagonalMod ℓ (diagonalSurface Y))]
    [HasDerivedCategory.{u + 1} (DiagonalSystems ℓ (diagonalSurface Y))]
    [HasDerivedCategory.{u + 1} (ℕᵒᵖ ⥤ DiagonalAb (diagonalSurface Y))]
    [HasDerivedCategory.{u + 1} (DiagonalCompleted ℓ (diagonalSurface Y))]
    [HasDerivedCategory.{u + 1} (ℕᵒᵖ ⥤ DiagonalCompleted ℓ (diagonalSurface Y))]
    [HasExt.{u + 1} (DiagonalSystems ℓ (diagonalSurface Y))]
    (D : DiagonalDerivedReduction ℓ (diagonalScalarExtension ℓ (diagonalSurface Y)))
    (hcompletion : DiagonalCompletionSpec ℓ (diagonalSurface Y) D)
    (hsystem : DiagonalCycleSystemSpec ℓ Y hY D) :
    DiagonalCompletedLimitSpec ℓ Y hY D := by
  sorry

/-- Derived direct image on strict constant-coefficient towers commutes with Rlim
and is computed levelwise. Both comparisons are normalized by their full derived
units and by the canonical projections.

Source: latest blueprint, clause 1; Stacks Tag 099L
(blueprint: det-prop-diagonal-tower-limit).

Proof: inverse image is exact and left adjoint to direct image, both on sheaves
and on strict systems. The constant-system functor is exact and left adjoint to
limit. Evaluation also has an exact left adjoint. These right adjoints preserve
K-injective complexes, so their total right derived functors have the stated
composite and evaluation comparisons. Ordinary direct image commutes with limits;
its comparison is limit.post. Uniqueness in the right-derived universal properties
fixes the two comparison maps by their cochain units. Naturality of the limit
projections gives the final compatibility equation on all derived systems. -/
theorem diagonalTower_directImage_general (ℓ : ℕ) [Fact ℓ.Prime]
    {X Y : Scheme.{u}} (hX : IsUnit (ℓ : Γ(X, ⊤))) (hY : IsUnit (ℓ : Γ(Y, ⊤)))
    (f : X ⟶ Y)
    [HasDerivedCategory.{u + 1} (DiagonalMod ℓ X)]
    [HasDerivedCategory.{u + 1} (DiagonalMod ℓ Y)]
    [HasDerivedCategory.{u + 1} (DiagonalSystems ℓ X)]
    [HasDerivedCategory.{u + 1} (DiagonalSystems ℓ Y)] :
    ∃ (LX : DiagonalRlim (DiagonalMod ℓ X)) (LY : DiagonalRlim (DiagonalMod ℓ Y))
      (Rf : DiagonalRightDerived ((lowerStar (ModuleCat.{u + 1} (ULift.{u + 1} ℤ_[ℓ])) f)))
      (Rt : DiagonalRightDerived ((Functor.whiskeringRight ℕᵒᵖ
        (DiagonalMod ℓ X) (DiagonalMod ℓ Y)).obj
          ((lowerStar (ModuleCat.{u + 1} (ULift.{u + 1} ℤ_[ℓ])) f))))
      (e : ∀ n : ℕ, Rt.R ⋙
        ((evaluation ℕᵒᵖ (DiagonalMod ℓ Y)).obj (op n)).mapDerivedCategory ≅
        ((evaluation ℕᵒᵖ (DiagonalMod ℓ X)).obj (op n)).mapDerivedCategory ⋙ Rf.R)
      (c : LX.R ⋙ Rf.R ≅ Rt.R ⋙ LY.R)
      (c₀ : (lim : (ℕᵒᵖ ⥤ (DiagonalMod ℓ X)) ⥤ (DiagonalMod ℓ X)) ⋙
          (lowerStar (ModuleCat.{u + 1} (ULift.{u + 1} ℤ_[ℓ])) f) ≅
        (Functor.whiskeringRight ℕᵒᵖ (DiagonalMod ℓ X) (DiagonalMod ℓ Y)).obj
          ((lowerStar (ModuleCat.{u + 1} (ULift.{u + 1} ℤ_[ℓ])) f)) ⋙ lim),
      (∀ H : (ℕᵒᵖ ⥤ (DiagonalMod ℓ X)),
        c₀.hom.app H = limit.post H
          ((lowerStar (ModuleCat.{u + 1} (ULift.{u + 1} ℤ_[ℓ])) f))) ∧
      (∀ P : CochainComplex ((ℕᵒᵖ ⥤ (DiagonalMod ℓ X))) ℤ,
        Rf.η.app (((lim : (ℕᵒᵖ ⥤ (DiagonalMod ℓ X)) ⥤ (DiagonalMod ℓ X)).mapHomologicalComplex
          (.up ℤ)).obj P) ≫ Rf.R.map (LX.η.app P) ≫ c.hom.app (DerivedCategory.Q.obj P) =
        DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex c₀.hom (.up ℤ)).app P) ≫
          LY.η.app ((((Functor.whiskeringRight ℕᵒᵖ
            (DiagonalMod ℓ X) (DiagonalMod ℓ Y)).obj
              ((lowerStar (ModuleCat.{u + 1} (ULift.{u + 1} ℤ_[ℓ])) f))).mapHomologicalComplex
                (.up ℤ)).obj P) ≫ LY.R.map (Rt.η.app P)) ∧
      (∀ (P : CochainComplex ((ℕᵒᵖ ⥤ (DiagonalMod ℓ X))) ℤ), P.IsKInjective → ∀ n : ℕ,
        ((evaluation ℕᵒᵖ (DiagonalMod ℓ Y)).obj (op n)).mapDerivedCategory.map (Rt.η.app P) ≫
          (e n).hom.app (DerivedCategory.Q.obj P) ≫
          Rf.R.map (((evaluation ℕᵒᵖ (DiagonalMod ℓ X)).obj
            (op n)).mapDerivedCategoryFactors.hom.app P) =
        ((evaluation ℕᵒᵖ (DiagonalMod ℓ Y)).obj (op n)).mapDerivedCategoryFactors.hom.app
          ((((Functor.whiskeringRight ℕᵒᵖ (DiagonalMod ℓ X) (DiagonalMod ℓ Y)).obj
            ((lowerStar (ModuleCat.{u + 1} (ULift.{u + 1} ℤ_[ℓ])) f))).mapHomologicalComplex
              (.up ℤ)).obj P) ≫ Rf.η.app (P.asFunctor.obj (op n))) ∧
      ∀ (M : DerivedCategory ((ℕᵒᵖ ⥤ (DiagonalMod ℓ X)))) (n : ℕ),
        c.hom.app M ≫ (LY.projection n).app (Rt.R.obj M) ≫ (e n).hom.app M =
          Rf.R.map ((LX.projection n).app M) := by
  sorry

end AlgebraicGeometry.ProEtale
