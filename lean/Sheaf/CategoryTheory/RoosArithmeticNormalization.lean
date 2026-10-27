/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group B2
-/
module

public import Sheaf.CategoryTheory.StrictRoosModel
public import Sheaf.CategoryTheory.StrictRoosDerivedLimitComparison
public import Sheaf.CategoryTheory.StrictTowerArithmeticRestrictionDefs
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.ShortExactPullback
import all Sheaf.CategoryTheory.CompactSupportRoosCofinality
import all Sheaf.CategoryTheory.StrictRoosDerivedLimitComparison

/-! # Arithmetic normalization of a unit-normalized Roos comparison

The selection/block coordinate formula fixes the derived restriction map and
its value on every strict augmentation. Source: Stacks 0941
(blueprint: lem-pur-roos-arithmetic-normalization).
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 4096

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory

attribute [local implicit_reducible] CategoryTheory.roosF CategoryTheory.roosConeFunctor
  CategoryTheory.strictRoosComplex CategoryTheory.strictRoosEndomorphism
  CategoryTheory.strictRoosProduct HomologicalComplex.asFunctor HomologicalComplex.eval
  HomologicalComplex.complexOfFunctorsToFunctorToComplex
  CategoryTheory.Functor.mapHomologicalComplex CategoryTheory.NatTrans.mapHomologicalComplex
  HomologicalComplex.coneOfHasLimitEval CategoryTheory.strictTowerLimitIso

universe v w d
variable {A : Type v} [Category.{w} A] [Abelian A] [HasCountableProducts A]
  [HasLimitsOfShape ℕᵒᵖ A]

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
omit [HasCountableProducts A] in
private theorem scalarLimitRestriction_cochain (e : ℕ)
    (α : (lim : (ℕᵒᵖ ⥤ A) ⥤ A) ⟶
      CategoryTheory.StrictTowerArithmetic.restriction A e ⋙ lim)
    (hα : ∀ T, α.app T = limit.pre T (CategoryTheory.StrictTowerArithmetic.index e))
    (K : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) :
    limit.pre K.asFunctor (CategoryTheory.StrictTowerArithmetic.index e) ≫
        (CategoryTheory.strictTowerLimitIso).hom.app
          ((CategoryTheory.StrictTowerArithmetic.complexRestriction A e).obj K) =
      (CategoryTheory.strictTowerLimitIso).hom.app K ≫
        (NatTrans.mapHomologicalComplex α (.up ℤ)).app K := by
  let R := CategoryTheory.StrictTowerArithmetic.complexRestriction A e
  have hp (L : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) (n : ℕᵒᵖ) (p : ℤ) :
      ((CategoryTheory.strictTowerLimitIso).hom.app L).f p ≫ limit.π (L.X p) n =
        (limit.π L.asFunctor n).f p := by
    dsimp only [CategoryTheory.strictTowerLimitIso, NatIso.ofComponents]
    have h := congrArg (fun z ↦ z.f p)
      (limit.isoLimitCone_hom_π
        ⟨HomologicalComplex.coneOfHasLimitEval L.asFunctor,
          HomologicalComplex.isLimitConeOfHasLimitEval L.asFunctor⟩ n)
    dsimp only [HomologicalComplex.comp_f, HomologicalComplex.coneOfHasLimitEval] at h
    exact h
  apply (HomologicalComplex.isLimitConeOfHasLimitEval (R.obj K).asFunctor).hom_ext
  intro n
  apply HomologicalComplex.Hom.ext
  funext p
  simp only [HomologicalComplex.comp_f, Category.assoc]
  change (limit.pre K.asFunctor (CategoryTheory.StrictTowerArithmetic.index e)).f p ≫
    ((CategoryTheory.strictTowerLimitIso).hom.app (R.obj K)).f p ≫
      limit.π ((R.obj K).X p) n =
    ((CategoryTheory.strictTowerLimitIso).hom.app K).f p ≫
      (α.app (K.X p)) ≫ limit.π ((R.obj K).X p) n
  rw [hp, hα]
  change (limit.pre K.asFunctor (CategoryTheory.StrictTowerArithmetic.index e) ≫
    limit.π (CategoryTheory.StrictTowerArithmetic.index e ⋙ K.asFunctor) n).f p =
    ((CategoryTheory.strictTowerLimitIso).hom.app K).f p ≫
      limit.pre (K.X p) (CategoryTheory.StrictTowerArithmetic.index e) ≫
        limit.π (CategoryTheory.StrictTowerArithmetic.index e ⋙ K.X p) n
  rw [limit.pre_π, limit.pre_π, hp]

section DerivedComparison

variable [HasDerivedCategory.{d} A] [HasDerivedCategory.{d} (ℕᵒᵖ ⥤ A)]
  [Abelian.HasKInjectiveResolutions (ℕᵒᵖ ⥤ A)]
  [(lim : (ℕᵒᵖ ⥤ A) ⥤ A).Additive]

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
private theorem scalarRoosRestriction_derived (e : ℕ) (he : 1 ≤ e)
    (α : (lim : (ℕᵒᵖ ⥤ A) ⥤ A) ⟶
      CategoryTheory.StrictTowerArithmetic.restriction A e ⋙ lim)
    (hα : ∀ T, α.app T = limit.pre T (CategoryTheory.StrictTowerArithmetic.index e))
    (κ : roosF (A := A) ⋙ DerivedCategory.Q ≅ DerivedCategory.Q ⋙
      (lim : (ℕᵒᵖ ⥤ A) ⥤ A).rightDerivedFunctor)
    (hk : ∀ L, DerivedCategory.Q.map (roosι L) ≫ κ.hom.app L =
      DerivedCategory.Q.map ((CategoryTheory.strictTowerLimitIso).hom.app L) ≫
        (lim : (ℕᵒᵖ ⥤ A) ⥤ A).rightDerivedFunctorUnitQ L)
    (K : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) :
    DerivedCategory.Q.map (CategoryTheory.rho K e he) ≫
        κ.hom.app ((CategoryTheory.StrictTowerArithmetic.complexRestriction A e).obj K) ≫
        (lim : (ℕᵒᵖ ⥤ A) ⥤ A).rightDerivedFunctor.map
          ((CategoryTheory.StrictTowerArithmetic.restriction A e).mapDerivedCategoryFactors.inv.app
            K)
        = κ.hom.app K ≫
          (Functor.rightDerivedPullback
            (CategoryTheory.StrictTowerArithmetic.restriction A e) α).app
            (DerivedCategory.Q.obj K) := by
  let R := CategoryTheory.StrictTowerArithmetic.complexRestriction A e
  let H : (ℕᵒᵖ ⥤ A) ⥤ A := lim
  let P := CategoryTheory.StrictTowerArithmetic.restriction A e
  let Q := DerivedCategory.Q (C := ℕᵒᵖ ⥤ A)
  have hmu {L N : CochainComplex (ℕᵒᵖ ⥤ A) ℤ} (j : L ⟶ N) :
      CategoryTheory.mu j = roosF.map j := by
    apply CategoryTheory.coord_ext
    intro p
    exact (CategoryTheory.mu_coord j p).trans (roosF_map_χ j p).symm
  let ρ : roosF (A := A) ⟶ R ⋙ roosF :=
    { app := fun L ↦ CategoryTheory.rho L e he
      naturality := by
        intro L N j
        simpa only [hmu, Functor.comp_map] using CategoryTheory.rho_nat j e he }
  let T := Q ⋙ P.mapDerivedCategory ⋙ H.rightDerivedFunctor
  let δ : roosF ⋙ DerivedCategory.Q ⟶ T :=
    Functor.whiskerRight ρ DerivedCategory.Q ≫
      Functor.whiskerLeft R κ.hom ≫
      Functor.whiskerRight P.mapDerivedCategoryFactors.inv H.rightDerivedFunctor
  let δ' : roosF ⋙ DerivedCategory.Q ⟶ T :=
    κ.hom ≫ Functor.whiskerLeft Q (Functor.rightDerivedPullback P α)
  have hδ (I : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) [I.IsKInjective] :
      δ.app I = δ'.app I := by
    have : IsIso (H.rightDerivedFunctorUnitQ I) := by
      rw [Functor.rightDerivedFunctorUnitQ_eq]
      infer_instance
    have : IsIso (DerivedCategory.Q.map ((CategoryTheory.strictTowerLimitIso).hom.app I)) :=
      inferInstanceAs (IsIso (DerivedCategory.Q.mapIso
        ((CategoryTheory.strictTowerLimitIso (A := A)).app I)).hom)
    have : IsIso (DerivedCategory.Q.map (roosι I) ≫ κ.hom.app I) := by
      rw [hk]
      infer_instance
    have : IsIso (DerivedCategory.Q.map (roosι I)) :=
      IsIso.of_isIso_comp_right _ (κ.hom.app I)
    apply (cancel_epi (DerivedCategory.Q.map (roosι I))).mp
    have hι : roosι I ≫ ρ.app I =
        limit.pre I.asFunctor (CategoryTheory.StrictTowerArithmetic.index e) ≫
          roosι (R.obj I) :=
      CategoryTheory.rho_limit_coordinates I e he (roosι I) (roosι (R.obj I))
        (roosι_χ I) (roosι_χ (R.obj I))
    dsimp only [δ, δ', NatTrans.comp_app, Functor.whiskerRight_app,
      Functor.whiskerLeft_app]
    change DerivedCategory.Q.map (roosι I) ≫
        DerivedCategory.Q.map (ρ.app I) ≫ κ.hom.app (R.obj I) ≫
          H.rightDerivedFunctor.map (P.mapDerivedCategoryFactors.inv.app I) =
      DerivedCategory.Q.map (roosι I) ≫ κ.hom.app I ≫
        (Functor.rightDerivedPullback P α).app (Q.obj I)
    rw [← DerivedCategory.Q.map_comp_assoc, hι, DerivedCategory.Q.map_comp,
      Category.assoc, reassoc_of% hk (R.obj I)]
    rw [← Category.assoc, ← DerivedCategory.Q.map_comp,
      scalarLimitRestriction_cochain e α hα I, DerivedCategory.Q.map_comp]
    rw [Category.assoc, reassoc_of% hk I]
    congr 1
    exact (Functor.rightDerivedFunctorUnitQ_rightDerivedPullback_app' P
      α I).symm
  obtain ⟨I, hI, j, _, hj⟩ := Abelian.HasKInjectiveResolutions.exists_isKInjective K
  have := hI
  have := hj
  have : IsIso ((T).map j) := by
    change IsIso (H.rightDerivedFunctor.map
      ((CategoryTheory.StrictTowerArithmetic.derivedRestriction A e).map (DerivedCategory.Q.map j)))
    infer_instance
  have h : δ.app K = δ'.app K := by
    apply (cancel_mono ((T).map j)).mp
    rw [← δ.naturality j, ← δ'.naturality j, hδ I]
  simpa only [δ, δ', NatTrans.comp_app, Functor.whiskerRight_app,
    Functor.whiskerLeft_app, ρ, R, P, Q, H, Category.assoc] using h

end DerivedComparison

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
omit [HasLimitsOfShape ℕᵒᵖ A] in
private theorem scalarRoosRestriction_augment
    (K : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) (e : ℕ) (he : 1 ≤ e)
    (P : CochainComplex A ℤ) (a : ∀ n : ℕ, P ⟶ K.asFunctor.obj (op n))
    (ha : ∀ n : ℕ, a (n + 1) ≫
      K.asFunctor.map (homOfLE (Nat.le_succ n)).op = a n)
    (h : ∀ n : ℕ, a (e * (n + 2) - 1) ≫
      K.asFunctor.map ((CategoryTheory.StrictTowerArithmetic.index e).map
        (homOfLE (Nat.le_succ n)).op) = a (e * (n + 1) - 1)) :
    roosAugment a ha ≫ CategoryTheory.rho K e he =
      roosAugment (fun n : ℕ ↦ a (e * (n + 1) - 1)) h := by
  obtain ⟨b, hb, b', hb', hbb⟩ := CategoryTheory.rho_augment K e he P a ha
  have hba : b = roosAugment a ha := by
    apply CategoryTheory.coord_ext
    intro p
    exact (hb p).trans (roosAugment_χ a ha p).symm
  have hba' : b' = roosAugment (fun n : ℕ ↦ a (e * (n + 1) - 1)) h := by
    apply CategoryTheory.coord_ext
    intro p
    exact (hb' p).trans (roosAugment_χ
      (X := (CategoryTheory.StrictTowerArithmetic.complexRestriction A e).obj K)
      (fun n : ℕ ↦ a (e * (n + 1) - 1)) h p).symm
  simpa only [hba, hba'] using hbb

variable [HasDerivedCategory.{d} A] [HasDerivedCategory.{d} (ℕᵒᵖ ⥤ A)]
  [Abelian.HasKInjectiveResolutions (ℕᵒᵖ ⥤ A)]
  [(lim : (ℕᵒᵖ ⥤ A) ⥤ A).Additive]

/-- The coordinate-normalized arithmetic cone map realizes derived restriction
and sends each strict augmentation to its selected augmentation.
Source: Stacks 0941 (blueprint: lem-pur-roos-arithmetic-normalization).
Proof: coordinate extensionality identifies the given family with the
selection/block cone map. The limit comparison commutes with restriction by
its projections. On a K-injective complex the unit-normalized comparison makes
the Roos inclusion invertible; cancel it and apply the cochain formula for
rightDerivedPullback. Naturality along a K-injective resolution extends the
equality to every complex. The augmentation has coordinates (0,a), so selection
of the second coordinate and the zero first coordinate give its formula. -/
theorem roosArithmeticNormalization (e : ℕ) (he : 1 ≤ e)
    (α : (lim : (ℕᵒᵖ ⥤ A) ⥤ A) ⟶
      StrictTowerArithmetic.restriction A e ⋙ lim)
    (hα : ∀ T, α.app T = limit.pre T (StrictTowerArithmetic.index e))
    (κ : roosF (A := A) ⋙ DerivedCategory.Q ≅ DerivedCategory.Q ⋙
      (lim : (ℕᵒᵖ ⥤ A) ⥤ A).rightDerivedFunctor)
    (hk : ∀ L, DerivedCategory.Q.map (roosι L) ≫ κ.hom.app L =
      DerivedCategory.Q.map
        (limit.isoLimitCone ⟨HomologicalComplex.coneOfHasLimitEval L.asFunctor,
          HomologicalComplex.isLimitConeOfHasLimitEval L.asFunctor⟩).hom ≫
        (lim : (ℕᵒᵖ ⥤ A) ⥤ A).rightDerivedFunctorUnitQ L)
    (r : ∀ L : CochainComplex (ℕᵒᵖ ⥤ A) ℤ,
      strictRoosComplex L ⟶
        strictRoosComplex ((StrictTowerArithmetic.complexRestriction A e).obj L))
    (hr : ∀ L p, (r L).f (p + 1) ≫
      (strictRoosCoordinates ((StrictTowerArithmetic.complexRestriction A e).obj L) p).hom =
        (strictRoosCoordinates L p).hom ≫
          biprod.map ((StrictTowerArithmetic.block e L.asFunctor).f p)
            ((StrictTowerArithmetic.selection e L.asFunctor).f (p + 1)))
    (K : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) :
    (DerivedCategory.Q.map (r K) ≫
        κ.hom.app ((StrictTowerArithmetic.complexRestriction A e).obj K) ≫
        (lim : (ℕᵒᵖ ⥤ A) ⥤ A).rightDerivedFunctor.map
          ((StrictTowerArithmetic.restriction A e).mapDerivedCategoryFactors.inv.app K) =
      κ.hom.app K ≫
        (Functor.rightDerivedPullback (StrictTowerArithmetic.restriction A e) α).app
          (DerivedCategory.Q.obj K)) ∧
      ∀ (P : CochainComplex A ℤ) (a : ∀ n : ℕ, P ⟶ K.asFunctor.obj (op n))
        (ha : ∀ n : ℕ, a (n + 1) ≫
          K.asFunctor.map (homOfLE (Nat.le_succ n)).op = a n)
        (h : ∀ n : ℕ, a (e * (n + 2) - 1) ≫
          K.asFunctor.map ((StrictTowerArithmetic.index e).map
            (homOfLE (Nat.le_succ n)).op) = a (e * (n + 1) - 1)),
        roosAugment a ha ≫ r K = roosAugment (fun n : ℕ ↦ a (e * (n + 1) - 1)) h := by
  have hρ (L : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) : r L = rho L e he := by
    apply coord_ext
    intro p
    exact (hr L p).trans (rho_coord L e he p).symm
  rw [hρ]
  refine ⟨scalarRoosRestriction_derived e he α hα κ hk K, ?_⟩
  intro P a ha h
  exact scalarRoosRestriction_augment K e he P a ha h

end CategoryTheory
