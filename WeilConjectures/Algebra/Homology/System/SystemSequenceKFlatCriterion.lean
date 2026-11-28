/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Algebra.Homology.System.SystemEvaluationTopos
import WeilConjectures.CategoryTheory.RingedCocontinuousMonoidal
import WeilConjectures.Mathlib.Algebra.Homology.Bifunctor
import WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor

/-! # Levelwise criterion for K-flatness on the ringed sequence site

## Implementation details

Exactness on the sequence site is detected by the vertical evaluations through the strict
system equivalence. Each evaluation is strong monoidal (`ringed_cocontinuous_monoidal`) and
preserves coproducts, so it commutes with total tensor complexes and with `- ⊗ M`.

## References

* Stacks Project, Tags 06YN, 0941
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u v w
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite WeilConjectures
namespace SheafOfModules
variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [EssentiallySmall.{w} C]
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasSheafify J AddCommGrpCat.{w}]
  (B : ℕᵒᵖ ⥤ Sheaf J CommRingCat.{w})

private local instance addCommGrpSmallestColimits : HasColimitsOfSize.{0, 0} AddCommGrpCat.{w} :=
  hasColimitsOfSizeShrink.{0, 0, w, w} _

private local instance systemSequenceCoproducts (I : Type) :
    HasColimitsOfShape (Discrete I) (systemSequenceModules B) :=
  have : HasColimitsOfShape (Discrete I) (PresheafOfModules.{w}
      (derivedChangeRingIndependentCoefficients.{w} (coefficientSequenceTopology J)
        (systemSequenceRing B)).obj) :=
    PresheafOfModules.hasColimitsOfShape _ _
  SheafOfModules.instHasColimitsOfShapeOfPresheafOfModulesObjFunctorOppositeRingCatIsSheaf _ _

private local instance systemLevelCoproducts (n : ℕ) (I : Type) :
    HasColimitsOfShape (Discrete I) (systemLevel B n) :=
  have : HasColimitsOfShape (Discrete I) (PresheafOfModules.{w}
      (derivedChangeRingIndependentCoefficients J (B.obj (op n))).obj) :=
    PresheafOfModules.hasColimitsOfShape _ _
  SheafOfModules.instHasColimitsOfShapeOfPresheafOfModulesObjFunctorOppositeRingCatIsSheaf _ _

/-- The vertical coefficient map of a slice is invertible. -/
instance systemSequenceVerticalRingMap_isIso (n : ℕ) :
    IsIso (systemSequenceVerticalRingMap B n) := by
  rw [← isIso_iff_of_reflects_iso _ (sheafToPresheaf _ _), NatTrans.isIso_iff_isIso_app]
  intro U
  exact inferInstanceAs (IsIso (𝟙 _))

/-- Vertical evaluation is strong monoidal for the sheafified tensor products. -/
theorem systemSequenceEvaluation_monoidal (n : ℕ) :
    letI := isMonoidal_W_independentCoefficients (systemSequenceRing B)
    letI := monoidalCategory (systemSequenceRing B)
    letI := isMonoidal_W_independentCoefficients (B.obj (op n))
    letI := monoidalCategory (B.obj (op n))
    Nonempty (systemSequenceEvaluation B n).Monoidal :=
  ringed_cocontinuous_monoidal (Prod.sectR n C) (B.obj (op n)) (systemSequenceRing B)
    (asIso (systemSequenceVerticalRingMap B n))

/-- Vertical evaluation preserves the coproducts defining total complexes. -/
instance systemSequenceEvaluation_preservesCoproducts (n : ℕ) (I : Type) :
    PreservesColimitsOfShape (Discrete I) (systemSequenceEvaluation B n) := by
  have := systemEvaluation_colimitsOfShape B (Discrete I) n
  exact inferInstanceAs (PreservesColimitsOfShape (Discrete I)
    ((strictSystemSequenceEquivalence B).inverse ⋙ systemEvaluation B n))

/-- Exactness of a short complex on the ringed sequence site is detected by the
vertical evaluations. -/
theorem systemSequence_exact_of_evaluations (S : ShortComplex (systemSequenceModules B))
    (h : ∀ n : ℕ, (S.map (systemSequenceEvaluation B n)).Exact) : S.Exact := by
  rw [← S.exact_map_iff_of_faithful (strictSystemSequenceEquivalence B).inverse,
    ShortComplex.exact_iff_isZero_homology, strictRingSystem_isZero_iff]
  intro n
  exact ((S.map (systemSequenceEvaluation B n)).exact_iff_isZero_homology.1 (h n)).of_iso
    ((S.map (strictSystemSequenceEquivalence B).inverse).mapHomologyIso
      (systemEvaluation B n)).symm

/-- A complex on the ringed sequence site is K-flat once all its vertical evaluations are. -/
theorem systemSequence_isKFlat_of_evaluations (P : CochainComplex (systemSequenceModules B) ℤ)
    (hP : ∀ n : ℕ, CochainComplex.IsKFlatIndependentCoefficients (R := B.obj (op n))
      (((systemSequenceEvaluation B n).mapHomologicalComplex (.up ℤ)).obj P)) :
    CochainComplex.IsKFlatIndependentCoefficients (R := systemSequenceRing B) P := by
  let := isMonoidal_W_independentCoefficients (systemSequenceRing B)
  let := monoidalCategory (systemSequenceRing B)
  let := preservesZeroMorphisms_curriedTensor_independentCoefficients (systemSequenceRing B)
  let := preservesZeroMorphisms_curriedTensor_obj_independentCoefficients
    (systemSequenceRing B)
  intro K hK i
  apply systemSequence_exact_of_evaluations B
  intro n
  let := isMonoidal_W_independentCoefficients (B.obj (op n))
  let := monoidalCategory (B.obj (op n))
  let := preservesZeroMorphisms_curriedTensor_independentCoefficients (B.obj (op n))
  let := preservesZeroMorphisms_curriedTensor_obj_independentCoefficients (B.obj (op n))
  obtain ⟨hL⟩ := systemSequenceEvaluation_monoidal B n
  let F := systemSequenceEvaluation B n
  let τ : (Functor.postcompose₂.obj F).obj (curriedTensor _) ⟶
      (((Functor.whiskeringLeft₂ _).obj F).obj F).obj (curriedTensor _) :=
    { app := fun X ↦
        { app := fun Y ↦ Functor.OplaxMonoidal.δ F X Y
          naturality := fun _ _ g ↦ (Functor.OplaxMonoidal.δ_natural_right F X g).symm }
      naturality := fun _ _ f ↦ NatTrans.ext (funext fun Y ↦
        (Functor.OplaxMonoidal.δ_natural_left F f Y).symm) }
  have (X Y : systemSequenceModules B) : IsIso ((τ.app X).app Y) :=
    inferInstanceAs (IsIso (Functor.OplaxMonoidal.δ F X Y))
  have hKn : ((F.mapHomologicalComplex (.up ℤ)).obj K).Acyclic := fun j ↦ (hK j).map F
  exact ((hP n _ hKn) i).of_iso
    (asIso (HomologicalComplex.mapBifunctorComparison τ (.up ℤ) K P)).symm

/-- A module on the ringed sequence site is flat once all its vertical evaluations are. -/
theorem systemSequence_flatOnSite_of_evaluations (X : systemSequenceModules B)
    (hX : ∀ n : ℕ, IsFlatOnSite (R := B.obj (op n)) ((systemSequenceEvaluation B n).obj X)) :
    IsFlatOnSite (R := systemSequenceRing B) X := by
  let := isMonoidal_W_independentCoefficients (systemSequenceRing B)
  let := monoidalCategory (systemSequenceRing B)
  let := symmetricCategory (systemSequenceRing B)
  let := tensorLeft_additive_independent (systemSequenceRing B) X
  have h (S : ShortComplex (systemSequenceModules B)) (hS : S.Exact) :
      (S.map (tensorLeft X)).Exact := by
    apply systemSequence_exact_of_evaluations B
    intro n
    let := isMonoidal_W_independentCoefficients (B.obj (op n))
    let := monoidalCategory (B.obj (op n))
    let := symmetricCategory (B.obj (op n))
    obtain ⟨hL⟩ := systemSequenceEvaluation_monoidal B n
    let F := systemSequenceEvaluation B n
    obtain ⟨_, _⟩ := (exactFunctor_iff _).1 ((exactFunctor _ _).prop_of_iso
      (siteSheafTensorRightIso (B.obj (op n)) (F.obj X) ≪≫
        (BraidedCategory.tensorLeftIsoTensorRight (F.obj X)).symm) (hX n))
    let e : (S.map F).map (tensorLeft (F.obj X)) ≅ (S.map (tensorLeft X)).map F :=
      ShortComplex.isoMk (asIso (Functor.LaxMonoidal.μ F X S.X₁))
        (asIso (Functor.LaxMonoidal.μ F X S.X₂)) (asIso (Functor.LaxMonoidal.μ F X S.X₃))
        (Functor.LaxMonoidal.μ_natural_right F X S.f).symm
        (Functor.LaxMonoidal.μ_natural_right F X S.g).symm
    exact (ShortComplex.exact_iff_of_iso e).1 ((hS.map F).map (tensorLeft (F.obj X)))
  exact (exactFunctor _ _).prop_of_iso (BraidedCategory.tensorLeftIsoTensorRight X ≪≫
    (siteSheafTensorRightIso (systemSequenceRing B) X).symm)
    (((Functor.exact_tfae (tensorLeft X)).out 2 4).1 h)

/-- A complex on the ringed sequence site whose evaluations are flat-term K-flat at every
level is flat-term K-flat. -/
theorem systemSequence_kFlat_of_evaluations (P : CochainComplex (systemSequenceModules B) ℤ)
    (hP : ∀ n : ℕ, systemLevelKFlat B n
      (((systemSequenceEvaluation B n).mapHomologicalComplex (.up ℤ)).obj P)) :
    CochainComplex.IsKFlatIndependentCoefficients (R := systemSequenceRing B) P ∧
      ∀ i : ℤ, IsFlatOnSite (R := systemSequenceRing B) (P.X i) :=
  ⟨systemSequence_isKFlat_of_evaluations B P (fun n ↦ (hP n).1),
    fun i ↦ systemSequence_flatOnSite_of_evaluations B (P.X i) (fun n ↦ (hP n).2 i)⟩

end SheafOfModules
