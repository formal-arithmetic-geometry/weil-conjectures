/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.CategoryTheory.Functor.OfSequence
public import Mathlib.Algebra.Homology.BifunctorShift
public import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
public import WeilConjectures.CategoryTheory.PrincipalQuotientCompletion.PrincipalQuotientCompletionModel
public import WeilConjectures.Algebra.Homology.RegularQuotientCone.RegularQuotientConeBasic
public import WeilConjectures.Algebra.Homology.SixFunctors.OrdinaryDerivedChangeOfRings
public import WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
import Mathlib.Algebra.Homology.HomologicalComplexLimits
import all WeilConjectures.CategoryTheory.RoosConeCalculus.RoosConeCalculus
import all WeilConjectures.CategoryTheory.PrincipalQuotientCompletion.PrincipalQuotientCompletionExists
import all WeilConjectures.CategoryTheory.RingedPowerTorsion.SignedDoubleRoosChainIso

/-! Augmentations for the signed double Roos interchange.

Source: Bhatt--Scholze, Lemma 3.4.13; Stacks Tag 0941.
(blueprint: lem-sp-signed-double-roos-augmentation)

The Koszul inclusions `theta`, the row augmentations `gamma` and their
naturality are proved below (private); the coordinate calculus of the double
Roos complex (`doubleCoordinate_ext`, `limit_map_coordinate`) comes from
`import all Sheaf.CategoryTheory.SignedDoubleRoosChainIso`. A Roos augmentation
has coordinates `(γ, 0)` (`roosAugment_coordinate_false`/`_true`); comparing
the four signed coordinates proves `etaL ≫ T = Roos γ`.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open CochainComplex

namespace CategoryTheory.RingedPowerTorsion

universe u v r a b

private theorem roosAugment_natural {B : Type a} [Category.{b} B] [Abelian B]
    [HasCountableProducts B] {X Y : CochainComplex (ℕᵒᵖ ⥤ B) ℤ} (f : X ⟶ Y)
    {P P' : CochainComplex B ℤ} (a : P ⟶ P')
    (γ : ∀ n : ℕ, P ⟶ X.asFunctor.obj (op n))
    (hγ : ∀ n, γ (n + 1) ≫ X.asFunctor.map (homOfLE (Nat.le_succ n)).op = γ n)
    (δ : ∀ n : ℕ, P' ⟶ Y.asFunctor.obj (op n))
    (hδ : ∀ n, δ (n + 1) ≫ Y.asFunctor.map (homOfLE (Nat.le_succ n)).op = δ n)
    (h : ∀ n, a ≫ δ n = γ n ≫
      (HomologicalComplex.complexOfFunctorsToFunctorToComplex.map f).app (op n)) :
    a ≫ roosAugment δ hδ = roosAugment γ hγ ≫ roosF.map f := by
  have hp : a ≫ Pi.lift δ = Pi.lift γ ≫ roosPmap f := by
    apply Pi.hom_ext
    intro n
    simp only [roosPmap, Category.assoc, Pi.map_π, Pi.lift_π_assoc, Pi.lift_π]
    exact h n
  ext k : 1
  obtain ⟨p, hp'⟩ := (Equiv.addRight (1 : ℤ)).surjective k
  change p + 1 = k at hp'
  subst k
  apply (cancel_mono (roosχ Y p).hom).mp
  simp only [HomologicalComplex.comp_f, Category.assoc]
  rw [roosF_map_χ, roosAugment_χ]
  rw [← Category.assoc, roosAugment_χ]
  apply biprod.hom_ext
  · simp
  · simp only [Category.assoc, biprod.map_snd, biprod.lift_snd_assoc, biprod.lift_snd]
    exact congrArg (fun z ↦ z.f (p + 1)) hp

variable {C : Type u} [Category.{v} C] [EssentiallySmall.{r} C]
  {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
  [HasSheafify J AddCommGrpCat.{r}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{r}]
  (R : Sheaf J CommRingCat.{r})

/- Notation for the coefficient category and its global sections. -/
set_option hygiene false in
local notation "A" => ringedSiteModules.{r}
  (SheafOfModules.derivedChangeRingIndependentCoefficients J R)
set_option hygiene false in
local notation "Section" => (SheafOfModules.unit
  (SheafOfModules.derivedChangeRingIndependentCoefficients J R)).sections

attribute [local instance] SheafOfModules.isMonoidal_W_independentCoefficients
attribute [local instance] SheafOfModules.monoidalCategory
attribute [local instance]
  SheafOfModules.preservesZeroMorphisms_curriedTensor_independentCoefficients
attribute [local instance]
  SheafOfModules.preservesZeroMorphisms_curriedTensor_obj_independentCoefficients

private theorem koszulInclusion_natural (t : Section) {P P' : CochainComplex A ℤ}
    (f : P ⟶ P') (j : ℕ) :
    f ≫ koszulRepresentativeAugmentation R P' t j =
      koszulRepresentativeAugmentation R P t j ≫ ((koszulRows R t).map f).app (op j) := by
  let B := (curriedTensor A).map₂CochainComplex
  let q := CochainComplex.mappingCone.inr
    ((CochainComplex.singleFunctor A 0).map
      (endoPow (globalSectionMultiplication R t) (j + 1)))
  change f ≫ (koszulTensorUnitInclusion R P' ≫ (B.map q).app P') =
    (koszulTensorUnitInclusion R P ≫ (B.map q).app P) ≫
      (B.obj (principalKoszul R t j)).map f
  rw [← Category.assoc, PrincipalQuotientCompletion.tensorUnitInclusion_natural,
    Category.assoc, (B.map q).naturality, Category.assoc]
  rfl

private theorem roosAugment_coordinate_false (W : ℕᵒᵖ ⥤ CochainComplex A ℤ)
    {P : CochainComplex A ℤ}
    (γ : ∀ n : ℕ, P ⟶ (koszulTowerComplex R W).asFunctor.obj (op n))
    (hγ : ∀ n, γ (n + 1) ≫
      (koszulTowerComplex R W).asFunctor.map (homOfLE (Nat.le_succ n)).op = γ n)
    (k : ℤ) (n : ℕ) :
    (roosAugment γ hγ).f k ≫ coordinate R (koszulTowerComplex R W) k false ≫
      (Pi.π (fun n : ℕ ↦ W.obj (op n)) n).f (degree k false) = (γ n).f k := by
  have h : (roosAugment γ hγ).f k ≫
      (CochainComplex.mappingCocone.fst (roosU (koszulTowerComplex R W))).f k =
        (Pi.lift γ).f k := by
    unfold roosAugment roosLift
    exact CochainComplex.mappingCocone.lift_f_fst_f _ _ _ _ k
  have h₂ := congrArg (fun z ↦ z.f k) (Pi.lift_π γ n)
  simp only [HomologicalComplex.comp_f] at h₂
  exact ((reassoc_of% h) _).trans h₂

private theorem roosAugment_coordinate_true (W : ℕᵒᵖ ⥤ CochainComplex A ℤ)
    {P : CochainComplex A ℤ}
    (γ : ∀ n : ℕ, P ⟶ (koszulTowerComplex R W).asFunctor.obj (op n))
    (hγ : ∀ n, γ (n + 1) ≫
      (koszulTowerComplex R W).asFunctor.map (homOfLE (Nat.le_succ n)).op = γ n)
    (k : ℤ) :
    (roosAugment γ hγ).f k ≫ coordinate R (koszulTowerComplex R W) k true = 0 := by
  have h : (roosAugment γ hγ).f k ≫
      (CochainComplex.mappingCocone.snd (roosU (koszulTowerComplex R W))).v k (k - 1)
        (by omega) = 0 := by
    unfold roosAugment roosLift
    exact (CochainComplex.mappingCocone.lift_f_snd_v _ _ _ _ k (k - 1) (by omega)).trans
      (CochainComplex.HomComplex.Cochain.zero_v _ _ _)
  exact h

private def theta (t : Section) (U : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) (j : ℕ) :
    U.asFunctor ⟶ (koszulDouble R t U).flip.obj (op j) where
  app n := koszulRepresentativeAugmentation R (U.asFunctor.obj n) t j
  naturality _ _ f := koszulInclusion_natural R t (U.asFunctor.map f) j

set_option maxHeartbeats 1600000 in
-- Converting the chosen total tensor representatives needs a larger heartbeat budget.
private theorem rowUnit_natural (t : Section) {P P' : CochainComplex A ℤ}
    (f : P ⟶ P') :
    f ≫ rowUnit R t P' = rowUnit R t P ≫
      (limitComplex R).map ((koszulRows R t).map f) := by
  exact roosAugment_natural (koszulTowerComplexMap R ((koszulRows R t).map f)) f
    (koszulRepresentativeAugmentation R P t)
    (fun n ↦ (koszulRepresentativeAugmentation_naturality R P t n).symm)
    (koszulRepresentativeAugmentation R P' t)
    (fun n ↦ (koszulRepresentativeAugmentation_naturality R P' t n).symm)
    (koszulInclusion_natural R t f)

set_option maxHeartbeats 1600000 in
-- The naturality field converts the same chosen total tensor representatives.
private def gamma (t : Section) (U : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) :
    U.asFunctor ⟶ koszulDouble R t U ⋙ limitComplex R where
  app n := rowUnit R t (U.asFunctor.obj n)
  naturality _ _ f := rowUnit_natural R t (U.asFunctor.map f)

set_option maxHeartbeats 1600000 in
-- The coordinate comparison unfolds the chosen Koszul and Roos representatives.
/-- The strict Koszul augmentation comparison for a supplied signed transposition.

Proof source: Bhatt--Scholze, Lemma 3.4.13. Define each `θ j` by the actual
Koszul representative inclusion, define `γ` by the rowwise Roos augmentation,
and define `etaL` by augmenting the family of Roos maps. The shifted coordinate
is zero and the unshifted coordinate is the product of the Roos maps. Projection
onto all four signed coordinates then proves the comparison with `Roos γ`; the
second Roos degree of the augmentation is zero, so its transposition sign is one.
-/
theorem signed_double_roos_augmentation
    (T : ∀ V : ℕᵒᵖ ⥤ ℕᵒᵖ ⥤ CochainComplex (ringedSiteModules.{r}
        (SheafOfModules.derivedChangeRingIndependentCoefficients J R)) ℤ,
        doubleLimit R V.flip ≅ doubleLimit R V)
    (hT : ∀ V (k : ℤ) (n j : ℕ),
        (T V).hom.f k ≫ doubleCoordinate R V k false false n j =
          doubleCoordinate R V.flip k false false j n ∧
        (T V).hom.f k ≫ doubleCoordinate R V k true false n j =
          doubleCoordinate R V.flip k false true j n ∧
        (T V).hom.f k ≫ doubleCoordinate R V k false true n j =
          doubleCoordinate R V.flip k true false j n ∧
        (T V).hom.f k ≫ doubleCoordinate R V k true true n j =
          -doubleCoordinate R V.flip k true true j n) :
      ∀ t : (SheafOfModules.unit
          (SheafOfModules.derivedChangeRingIndependentCoefficients J R)).sections,
        ∀ U : CochainComplex (ℕᵒᵖ ⥤ ringedSiteModules.{r}
          (SheafOfModules.derivedChangeRingIndependentCoefficients J R)) ℤ,
          ∃ (γ : U.asFunctor ⟶ koszulDouble R t U ⋙ limitComplex R)
            (θ : ∀ j : ℕ, U.asFunctor ⟶ (koszulDouble R t U).flip.obj (op j))
            (etaL : roosF.obj U ⟶ doubleLimit R (koszulDouble R t U).flip),
            (∀ n, γ.app (op n) = rowUnit R t (U.asFunctor.obj (op n))) ∧
            (∀ (j n : ℕ), (θ j).app (op n) =
              koszulRepresentativeAugmentation R (U.asFunctor.obj (op n)) t j) ∧
            (∀ k : ℤ, etaL.f (k + 1) ≫
              (roosχ (koszulTowerComplex R
                ((koszulDouble R t U).flip ⋙ limitComplex R)) k).hom =
              biprod.lift 0 ((Pi.lift (fun j : ℕ ↦
                roosF.map (koszulTowerComplexMap R (θ j)))).f (k + 1))) ∧
            etaL ≫ (T (koszulDouble R t U)).hom =
              roosF.map (koszulTowerComplexMap R γ) := by
  classical
  intro t U
  let θ := theta R t U
  let γ := gamma R t U
  have hθ (j : ℕ) : θ (j + 1) ≫
      (koszulDouble R t U).flip.map (homOfLE (Nat.le_succ j)).op = θ j := by
    ext n : 2
    dsimp [θ, koszulDouble, koszulRows]
    change koszulRepresentativeAugmentation R (U.asFunctor.obj n) t (j + 1) ≫
      (koszulTensorTower R (U.asFunctor.obj n) t).map
        (homOfLE (Nat.le_succ j)).op =
      koszulRepresentativeAugmentation R (U.asFunctor.obj n) t j
    exact (koszulRepresentativeAugmentation_naturality R
      (U.asFunctor.obj n) t j).symm
  have hθ' (j : ℕ) :
      koszulTowerComplexMap R (θ (j + 1)) ≫
        koszulTowerComplexMap R
          ((koszulDouble R t U).flip.map (homOfLE (Nat.le_succ j)).op) =
      koszulTowerComplexMap R (θ j) := by
    apply HomologicalComplex.Hom.ext
    funext i
    apply NatTrans.ext
    funext n
    simpa [koszulTowerComplexMap] using
      congrArg (fun z => z.f i) (congrArg (fun z => z.app n) (hθ j))
  have hγ (j : ℕ) :
      (roosF.map (koszulTowerComplexMap R (θ (j + 1)))) ≫
        (roosF.map (koszulTowerComplexMap R
          ((koszulDouble R t U).flip.map (homOfLE (Nat.le_succ j)).op))) =
      roosF.map (koszulTowerComplexMap R (θ j)) := by
    rw [← Functor.map_comp, hθ']
  let etaL := roosAugment
    (X := koszulTowerComplex R ((koszulDouble R t U).flip ⋙ limitComplex R))

    (fun j : ℕ => roosF.map (koszulTowerComplexMap R (θ j))) hγ
  refine ⟨γ, θ, etaL, ?_, ?_, ?_, ?_⟩
  · intro n
    rfl
  · intro j n
    rfl
  · intro k
    exact roosAugment_χ _ _ k
  · -- Compare the four signed coordinates `(p, q, n, j)` of both sides.
    ext k : 1
    apply doubleCoordinate_ext R (koszulDouble R t U) k
    intro p q n j
    rw [HomologicalComplex.comp_f, Category.assoc]
    -- `Roos γ` in the coordinates `(p, q, n, j)`.
    have hR : ∀ p q : Bool, (roosF.map (koszulTowerComplexMap R γ)).f k ≫
          doubleCoordinate R (koszulDouble R t U) k p q n j =
        coordinate R (koszulTowerComplex R U.asFunctor) k p ≫
          (Pi.π (fun n : ℕ ↦ U.asFunctor.obj (op n)) n).f (degree k p) ≫
          (γ.app (op n)).f (degree k p) ≫
          coordinate R (koszulTowerComplex R ((koszulDouble R t U).obj (op n)))
            (degree k p) q ≫
          (Pi.π (fun j : ℕ ↦ ((koszulDouble R t U).obj (op n)).obj (op j)) j).f
            (degree (degree k p) q) :=
      fun p q ↦ limit_map_coordinate_assoc R γ k p n _
    -- The row augmentation `γ` has coordinates `(θ, 0)`.
    have hI0 : ∀ d : ℤ, (γ.app (op n)).f d ≫
        coordinate R (koszulTowerComplex R ((koszulDouble R t U).obj (op n))) d false ≫
        (Pi.π (fun j : ℕ ↦ ((koszulDouble R t U).obj (op n)).obj (op j)) j).f
          (degree d false) = ((θ j).app (op n)).f d :=
      fun d ↦ roosAugment_coordinate_false R
        (koszulTensorTower R (U.asFunctor.obj (op n)) t)
        (koszulRepresentativeAugmentation R (U.asFunctor.obj (op n)) t)
        (fun j ↦ (koszulRepresentativeAugmentation_naturality R _ t j).symm) d j
    have hI1 : ∀ d : ℤ, (γ.app (op n)).f d ≫
        coordinate R (koszulTowerComplex R ((koszulDouble R t U).obj (op n))) d true = 0 :=
      fun d ↦ roosAugment_coordinate_true R
        (koszulTensorTower R (U.asFunctor.obj (op n)) t)
        (koszulRepresentativeAugmentation R (U.asFunctor.obj (op n)) t)
        (fun j ↦ (koszulRepresentativeAugmentation_naturality R _ t j).symm) d
    -- The outer augmentation `etaL` has coordinates `(Roos θ, 0)`.
    have hL : ∀ q' : Bool,
        etaL.f k ≫ doubleCoordinate R (koszulDouble R t U).flip k false q' j n =
          coordinate R (koszulTowerComplex R U.asFunctor) k q' ≫
            (Pi.π (fun n : ℕ ↦ U.asFunctor.obj (op n)) n).f (degree k q') ≫
            ((θ j).app (op n)).f (degree k q') := by
      intro q'
      have h₁ := roosAugment_coordinate_false R
        ((koszulDouble R t U).flip ⋙ limitComplex R)
        (fun j : ℕ => roosF.map (koszulTowerComplexMap R (θ j))) hγ k j
      have h₂ := limit_map_coordinate R (θ j) k q' n
      have h₃ := h₁ =≫
        (coordinate R (koszulTowerComplex R ((koszulDouble R t U).flip.obj (op j))) k q' ≫
          (Pi.π (fun n : ℕ ↦ ((koszulDouble R t U).flip.obj (op j)).obj (op n)) n).f
            (degree k q'))
      simp only [Category.assoc] at h₃
      exact h₃.trans h₂
    have hL1 : ∀ q' : Bool,
        etaL.f k ≫ doubleCoordinate R (koszulDouble R t U).flip k true q' j n = 0 := by
      intro q'
      have h₁ := roosAugment_coordinate_true R
        ((koszulDouble R t U).flip ⋙ limitComplex R)
        (fun j : ℕ => roosF.map (koszulTowerComplexMap R (θ j))) hγ k
      have h₃ := h₁ =≫
        ((Pi.π (fun n : ℕ ↦ (limitComplex R).obj ((koszulDouble R t U).flip.obj (op n)))
            j).f (degree k true) ≫
          coordinate R (koszulTowerComplex R ((koszulDouble R t U).flip.obj (op j)))
            (degree k true) q' ≫
          (Pi.π (fun n : ℕ ↦ ((koszulDouble R t U).flip.obj (op j)).obj (op n)) n).f
            (degree (degree k true) q'))
      simp only [Category.assoc, Limits.zero_comp] at h₃
      exact h₃
    cases p <;> cases q
    · rw [(hT _ k n j).1, hL false, hR false false, hI0]
    · rw [(hT _ k n j).2.2.1, hL1 false, hR false true, ← Category.assoc
        ((γ.app (op n)).f _), hI1, Limits.zero_comp, Limits.comp_zero, Limits.comp_zero]
    · rw [(hT _ k n j).2.1, hL true, hR true false, hI0]
    · rw [(hT _ k n j).2.2.2, Preadditive.comp_neg, hL1 true, neg_zero, hR true true,
        ← Category.assoc ((γ.app (op n)).f _), hI1, Limits.zero_comp, Limits.comp_zero,
        Limits.comp_zero]

end CategoryTheory.RingedPowerTorsion
