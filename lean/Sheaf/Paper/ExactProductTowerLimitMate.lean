/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Adjunction
public import Mathlib.CategoryTheory.Adjunction.Mates
public import Mathlib.CategoryTheory.Sites.Abelian
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
import all Sheaf.CategoryTheory.UnboundedExactAdjunctionSquare
import all Sheaf.CategoryTheory.CoefficientSequenceSectionsLimit
import all Sheaf.Paper.ExactProductFunctorStrictLimit
import all Sheaf.CategoryTheory.ExactEquivalenceDerivedSquares
import all Sheaf.Algebra.Homology.ExactProductsRoosComparison
import all Sheaf.CategoryTheory.RingedStrictTowerHomotopyLimitIndependentCoefficients
import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolutionInjective

/-! # The normalized total-limit mate for an exact product-preserving functor

The statement isolates invertibility of the actual counit mate, rather than a choice
of isomorphism of underlying functors. Source: Stacks Tags 0940, 0941 and 07KC;
the normalized Roos argument of `lem-cbc-exact-product-functor-strict-limit`.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe a av b bv da db dat dbt
open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory

private def canonicalUnit
    {A : Type a} [Category.{av} A] [Abelian A] [HasDerivedCategory.{da} A]
    {B : Type b} [Category.{bv} B] [Abelian B] [HasDerivedCategory.{db} B]
    [Abelian.HasKInjectiveResolutions A] (G : A ⥤ B) [G.Additive] :=
  derivedCochainRightUnit G G.rightDerivedFunctor G.rightDerivedFunctorUnit

private theorem canonicalUnit_app
    {A : Type a} [Category.{av} A] [Abelian A] [HasDerivedCategory.{da} A]
    {B : Type b} [Category.{bv} B] [Abelian B] [HasDerivedCategory.{db} B]
    [Abelian.HasKInjectiveResolutions A] (G : A ⥤ B) [G.Additive]
    (I : CochainComplex A ℤ) :
    (canonicalUnit G).app I = UnboundedExactTower.cochainUnit G I := by
  simp only [canonicalUnit, derivedCochainRightUnit, derivedCochainComparisonFactors,
    NatTrans.comp_app, Iso.trans_hom, Iso.symm_hom, Functor.isoWhiskerRight_hom,
    Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_hom_app, Functor.associator_inv_app, Category.id_comp,
    Category.assoc, UnboundedExactTower.cochainUnit]

private theorem splitComparison
    {B : Type b} [Category.{bv} B] [Abelian B]
    [HasCountableProducts B] [HasLimitsOfShape ℕᵒᵖ B]
    [HasDerivedCategory.{db} B]
    (I : CochainComplex (ℕᵒᵖ ⥤ B) ℤ)
    [∀ (p : ℤ) (n : ℕ), IsSplitEpi ((I.X p).map (homOfLE (Nat.le_succ n)).op)] :
    QuasiIso (ExactProductsRoos.comparison.app I) := by
  obtain ⟨h, hs⟩ := SheafOfModules.sectionsSplitRoos I
  let S := ShortComplex.mk (ExactProductsRoos.inclusion.app I)
    (-ExactProductsRoos.difference.app I)
    (by rw [Preadditive.comp_neg, ExactProductsRoos.inclusion_difference, neg_zero])
  have hS : S.ShortExact := by
    apply ShortComplex.shortExact_of_iso (S₁ := ShortComplex.mk _ _ h) _ hs
    exact ShortComplex.isoMk (Iso.refl _) (Iso.refl _)
      { hom := -𝟙 _
        inv := -𝟙 _
        hom_inv_id := by simp
        inv_hom_id := by simp } (by simp [S]) (by
          change 𝟙 _ ≫ (-ExactProductsRoos.difference.app I) = _ ≫ (-𝟙 _)
          simp)
  exact AlgebraicGeometry.ProEtale.cocone_lift_quasiIso S hS
    (ExactProductsRoos.comparison_condition I)

private theorem ordinaryMate
    {A : Type a} [Category.{av} A] {B : Type b} [Category.{bv} B]
    [HasLimitsOfShape ℕᵒᵖ A] [HasLimitsOfShape ℕᵒᵖ B]
    (F : A ⥤ B) [PreservesLimitsOfShape ℕᵒᵖ F] :
    (mateEquiv (constLimAdj : (Functor.const ℕᵒᵖ : A ⥤ _) ⊣ lim)
      (constLimAdj : (Functor.const ℕᵒᵖ : B ⥤ _) ⊣ lim)
      (Functor.compConstIso ℕᵒᵖ F).hom).natTrans =
        (preservesLimitNatIso F (J := ℕᵒᵖ)).hom := by
  let aa := (constLimAdj : (Functor.const ℕᵒᵖ : A ⥤ _) ⊣ lim)
  let bb := (constLimAdj : (Functor.const ℕᵒᵖ : B ⥤ _) ⊣ lim)
  apply NatTrans.ext
  funext M
  apply limit.hom_ext
  intro n
  have h := congrArg (fun z ↦ z.app n)
    (mateEquiv_counit aa bb (Functor.compConstIso ℕᵒᵖ F).hom M)
  change (mateEquiv aa bb (Functor.compConstIso ℕᵒᵖ F).hom).natTrans.app M ≫
    limit.π _ n = 𝟙 _ ≫ F.map (limit.π M n) at h
  rw [Category.id_comp] at h
  exact h.trans (preservesLimitIso_hom_π F M n).symm

-- The proved normalized Roos construction, with separate universes for both localizations.
open ExactProductsRoos in
private theorem normalizedFibre
    {B : Type b} [Category.{bv} B] [Abelian B]
    [HasCountableProducts B] [HasLimitsOfShape ℕᵒᵖ B]
    [HasExactLimitsOfShape (Discrete ℕ) B]
    [HasDerivedCategory.{db} B] [HasDerivedCategory.{dbt} (ℕᵒᵖ ⥤ B)]
    [IsGrothendieckAbelian.{bv} (ℕᵒᵖ ⥤ B)]
    (RF : DerivedCategory (ℕᵒᵖ ⥤ B) ⥤ DerivedCategory B)
    (η : ordinary ⋙ DerivedCategory.Q ⟶ DerivedCategory.Q ⋙ RF)
    (hI : ∀ I : CochainComplex (ℕᵒᵖ ⥤ B) ℤ, I.IsKInjective → IsIso (η.app I)) :
    ∃ e : fibre ⋙ DerivedCategory.Q ≅ DerivedCategory.Q ⋙ RF,
      Functor.whiskerRight comparison DerivedCategory.Q ≫ e.hom = η := by
  let F := CochainComplex.kInjectiveResolutionFunctor.{bv} (ℕᵒᵖ ⥤ B)
  let q := CochainComplex.toKInjectiveResolution.{bv} (ℕᵒᵖ ⥤ B)
  let α := Functor.whiskerRight q (fibre ⋙ DerivedCategory.Q)
  have hi (X : CochainComplex (ℕᵒᵖ ⥤ B) ℤ) : IsIso (α.app X) := by
    have : QuasiIso (q.app X) :=
      (CochainComplex.monoQuasiIso_toKInjectiveResolution_app.{bv} (ℕᵒᵖ ⥤ B) X).2
    have : QuasiIso (fibre.map (q.app X)) := fibreMap_quasiIso (q.app X)
    exact (DerivedCategory.isIso_Q_map_iff_quasiIso B _).2 inferInstance
  have : IsIso α := NatIso.isIso_of_isIso_app _
  let β := Functor.whiskerLeft F (Functor.whiskerRight comparison DerivedCategory.Q)
  have (X : CochainComplex (ℕᵒᵖ ⥤ B) ℤ) : IsIso (β.app X) := by
    have : QuasiIso (comparison.app (F.obj X)) := comparison_quasiIso _
    exact (DerivedCategory.isIso_Q_map_iff_quasiIso B _).2 inferInstance
  have : IsIso β := NatIso.isIso_of_isIso_app _
  let δ := Functor.whiskerRight q DerivedCategory.Q
  have (X : CochainComplex (ℕᵒᵖ ⥤ B) ℤ) : IsIso (δ.app X) := by
    have : QuasiIso (q.app X) :=
      (CochainComplex.monoQuasiIso_toKInjectiveResolution_app.{bv} (ℕᵒᵖ ⥤ B) X).2
    exact (DerivedCategory.isIso_Q_map_iff_quasiIso (ℕᵒᵖ ⥤ B) _).2 inferInstance
  have : IsIso δ := NatIso.isIso_of_isIso_app _
  let ε := Functor.whiskerLeft F η
  have (X : CochainComplex (ℕᵒᵖ ⥤ B) ℤ) : IsIso (ε.app X) := hI _ inferInstance
  have : IsIso ε := NatIso.isIso_of_isIso_app _
  let γ : F ⋙ ordinary ⋙ DerivedCategory.Q ≅ DerivedCategory.Q ⋙ RF :=
    asIso ε ≪≫ (Functor.associator F DerivedCategory.Q RF).symm ≪≫
      Functor.isoWhiskerRight (asIso δ).symm RF
  let e : fibre ⋙ DerivedCategory.Q ≅ DerivedCategory.Q ⋙ RF :=
    asIso α ≪≫ (Functor.associator F fibre DerivedCategory.Q) ≪≫
      (asIso β).symm ≪≫ γ
  refine ⟨e, ?_⟩
  apply NatTrans.ext
  funext X
  change DerivedCategory.Q.map (comparison.app X) ≫ e.hom.app X = η.app X
  have hq : IsIso (DerivedCategory.Q.map (q.app X)) := inferInstanceAs (IsIso (δ.app X))
  have hc : IsIso (DerivedCategory.Q.map (comparison.app (F.obj X))) :=
    inferInstanceAs (IsIso (β.app X))
  dsimp only [e, γ, α, β, δ, ε, Iso.trans_hom, Iso.symm_hom, asIso_hom,
    asIso_inv, NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.associator_hom_app, Functor.associator_inv_app, Functor.isoWhiskerRight_hom]
  simp only [Functor.comp_map, NatIso.isIso_inv_app, Functor.whiskerLeft_app,
    Functor.whiskerRight_app, Category.id_comp]
  erw [Category.id_comp]
  change DerivedCategory.Q.map (comparison.app X) ≫
    DerivedCategory.Q.map (fibre.map (q.app X)) ≫
      inv (DerivedCategory.Q.map (comparison.app (F.obj X))) ≫
        η.app (F.obj X) ≫ RF.map (inv (DerivedCategory.Q.map (q.app X))) = _
  rw [← DerivedCategory.Q.map_comp_assoc, ← comparison.naturality,
    DerivedCategory.Q.map_comp, Category.assoc, IsIso.hom_inv_id_assoc]
  have hn := η.naturality (q.app X)
  dsimp only [Functor.comp_map] at hn
  rw [← Category.assoc, hn, Category.assoc]
  rw [← RF.map_comp, IsIso.hom_inv_id, RF.map_id]
  exact Category.comp_id _


/-- An exact functor preserving countable products commutes with total derived tower
limits through the mate of its termwise constant-tower identity.

Source: Stacks Tags 0940, 0941 and 07KC; blueprint proof step 5 of the point-system
transport prerequisite and `lem-cbc-exact-product-functor-strict-limit`.
(blueprint: lem-trf-exact-product-tower-limit-mate)

Proof: products and finite limits compute ordinary tower limits, so F preserves
these limits. The ordinary mate is their canonical comparison, as follows by
composing its counit equation with each projection. Choose a K-injective tower
resolution with injective terms. Its transitions split, and their images under F
still split. The split-transition Roos short exact sequence makes the comparison
from the ordinary limit to the target Roos fibre a quasi-isomorphism. The normalized
Roos model identifies this comparison with the target derived-limit cochain unit.
The cochain normalization of the derived mate expresses it, up to invertible
localization factors and the source cochain unit, as the ordinary mate followed
by that target cochain unit. All these factors are invertible on the resolution.
Finally naturality transports invertibility to any derived object. This uses the
entire derived counit and no faithfulness of separate derived evaluations. No
boundedness or constructibility hypothesis is imposed. -/
theorem exactProductTowerLimitMate_isIso
    {A : Type a} [Category.{av} A] [Abelian A]
    {B : Type b} [Category.{bv} B] [Abelian B]
    [IsGrothendieckAbelian.{av} A] [IsGrothendieckAbelian.{bv} B]
    [HasDerivedCategory.{da} A] [HasDerivedCategory.{db} B]
    [HasDerivedCategory.{dat} (ℕᵒᵖ ⥤ A)] [HasDerivedCategory.{dbt} (ℕᵒᵖ ⥤ B)]
    [Abelian.HasKInjectiveResolutions (ℕᵒᵖ ⥤ A)]
    [Abelian.HasKInjectiveResolutions (ℕᵒᵖ ⥤ B)]
    [HasLimitsOfShape ℕᵒᵖ A] [HasLimitsOfShape ℕᵒᵖ B]
    [HasCountableProducts A] [HasCountableProducts B]
    [HasExactLimitsOfShape (Discrete ℕ) B]
    [(lim : (ℕᵒᵖ ⥤ A) ⥤ A).Additive]
    [(lim : (ℕᵒᵖ ⥤ B) ⥤ B).Additive]
    (F : A ⥤ B) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesLimitsOfShape (Discrete ℕ) F]
    [PreservesFiniteLimits ((Functor.whiskeringRight ℕᵒᵖ A B).obj F)]
    [PreservesFiniteColimits ((Functor.whiskeringRight ℕᵒᵖ A B).obj F)] :
    IsIso (mateEquiv
      ((constLimAdj : (Functor.const ℕᵒᵖ : A ⥤ _) ⊣ lim).mapDerivedCategoryRightDerivedAdjunction)
      ((constLimAdj : (Functor.const ℕᵒᵖ : B ⥤ _) ⊣ lim).mapDerivedCategoryRightDerivedAdjunction)
      ((Functor.mapDerivedCategoryCompIso F (Functor.const ℕᵒᵖ)).symm ≪≫
        Functor.mapDerivedCategoryNatIso (Functor.compConstIso ℕᵒᵖ F) ≪≫
        Functor.mapDerivedCategoryCompIso (Functor.const ℕᵒᵖ)
          ((Functor.whiskeringRight ℕᵒᵖ A B).obj F)).hom).natTrans := by
  let : IsGrothendieckAbelian.{av} (ℕᵒᵖ ⥤ A) := tower_grothendieck A
  let : IsGrothendieckAbelian.{bv} (ℕᵒᵖ ⥤ B) := tower_grothendieck B
  have : PreservesLimitsOfShape ℕᵒᵖ F := natProducts_preservesTowers F
  let W := (Functor.whiskeringRight ℕᵒᵖ A B).obj F
  let aa := (constLimAdj : (Functor.const ℕᵒᵖ : A ⥤ _) ⊣ lim)
  let bb := (constLimAdj : (Functor.const ℕᵒᵖ : B ⥤ _) ⊣ lim)
  let α := (mateEquiv aa.mapDerivedCategoryRightDerivedAdjunction
    bb.mapDerivedCategoryRightDerivedAdjunction
    ((Functor.mapDerivedCategoryCompIso F (Functor.const ℕᵒᵖ)).symm ≪≫
      Functor.mapDerivedCategoryNatIso (Functor.compConstIso ℕᵒᵖ F) ≪≫
      Functor.mapDerivedCategoryCompIso (Functor.const ℕᵒᵖ) W).hom).natTrans
  have hJ (J : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) [J.IsKInjective]
      [∀ p : ℤ, Injective (J.X p)] : IsIso (α.app (DerivedCategory.Q.obj J)) := by
    let K := (W.mapHomologicalComplex (.up ℤ)).obj J
    have (p : ℤ) (n : ℕ) : IsSplitEpi ((K.X p).map
        (homOfLE (Nat.le_succ n)).op) := by
      have := injective_tower_transition_split (J.X p) n
      change IsSplitEpi (F.map ((J.X p).map (homOfLE (Nat.le_succ n)).op))
      infer_instance
    have : QuasiIso (ExactProductsRoos.comparison.app K) := splitComparison K
    let η := canonicalUnit (lim : (ℕᵒᵖ ⥤ B) ⥤ B)
    have hη (I : CochainComplex (ℕᵒᵖ ⥤ B) ℤ) (hI : I.IsKInjective) :
        IsIso (η.app I) := by
      have := hI
      rw [canonicalUnit_app]
      exact UnboundedExactTower.cochainUnit_isIso (G := lim) I
    obtain ⟨e, he⟩ := normalizedFibre (B := B)
      (lim : (ℕᵒᵖ ⥤ B) ⥤ B).rightDerivedFunctor η hη
    have hηK : IsIso (UnboundedExactTower.cochainUnit (lim : (ℕᵒᵖ ⥤ B) ⥤ B) K) := by
      rw [← canonicalUnit_app]
      have hk := congrArg (fun z ↦ z.app K) he
      dsimp only [NatTrans.comp_app, Functor.whiskerRight_app] at hk
      rw [← hk]
      infer_instance
    have hm : IsIso (mateEquiv aa bb (Functor.compConstIso ℕᵒᵖ F).hom).natTrans := by
      rw [ordinaryMate F]
      infer_instance
    have hc : IsIso ((NatTrans.mapHomologicalComplex
        (mateEquiv aa bb (Functor.compConstIso ℕᵒᵖ F).hom).natTrans (.up ℤ)).app J) := by
      change IsIso ((NatIso.mapHomologicalComplex
        (asIso (mateEquiv aa bb (Functor.compConstIso ℕᵒᵖ F).hom).natTrans)
        (.up ℤ)).hom.app J)
      infer_instance
    have hs : IsIso (DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex
        (mateEquiv aa bb (Functor.compConstIso ℕᵒᵖ F).hom).natTrans (.up ℤ)).app J) ≫
        UnboundedExactTower.cochainUnit (lim : (ℕᵒᵖ ⥤ B) ⥤ B) K) := inferInstance
    have hn := UnboundedExactTower.localized_mate_cochain_normalization aa bb
      (Functor.compConstIso ℕᵒᵖ F) J
    rw [← hn] at hs
    have := UnboundedExactTower.cochainUnit_isIso (G := (lim : (ℕᵒᵖ ⥤ A) ⥤ A)) J
    simpa only [α, W, UnboundedExactTower.localizedSquare,
      isIso_comp_left_iff, isIso_comp_right_iff] using hs
  have : ∀ X, IsIso (α.app X) := by
    intro X
    let I := DerivedCategory.Q.objPreimage X
    let J := (CochainComplex.kInjectiveResolutionFunctor.{av} (ℕᵒᵖ ⥤ A)).obj I
    let q : I ⟶ J := (CochainComplex.toKInjectiveResolution.{av} (ℕᵒᵖ ⥤ A)).app I
    have : QuasiIso q := (CochainComplex.monoQuasiIso_toKInjectiveResolution_app _ I).2
    have := hJ J
    let e : X ≅ DerivedCategory.Q.obj J :=
      (DerivedCategory.Q.objObjPreimageIso X).symm ≪≫ asIso (DerivedCategory.Q.map q)
    have ht : IsIso (((lim : (ℕᵒᵖ ⥤ A) ⥤ A).rightDerivedFunctor ⋙
        F.mapDerivedCategory).map e.hom ≫ α.app (DerivedCategory.Q.obj J)) := inferInstance
    rw [α.naturality] at ht
    exact (isIso_comp_right_iff _ _).mp ht
  exact NatIso.isIso_of_isIso_app α

end CategoryTheory
