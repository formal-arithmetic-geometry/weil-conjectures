/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.CompletedUnitPullback.CompletedUnitPullbackData
import Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful

/-! # Uniqueness of the normalized regular coefficient reduction -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory AlgebraicGeometry Opposite
namespace WeilConjectures.CompletedUnitPullback

/-- The finite section normalization determines the whole regular reduction.
Source: Stacks 0941; the normalization in `Reduction`.
(blueprint: lem-pur-completed-unit-reduction-unique).
Proof: the ratio of the two comparisons is an endomorphism of the regular system
in degree zero. Full faithfulness of the single-complex functor makes it an ordinary
endomorphism of the sheaf of systems. The reduction equations identify every finite
component with the identity, since both finite section identifications agree.
Ordinary sectionwise extensionality identifies that endomorphism with the identity.
Cancel the first comparison. This uses no faithfulness for general derived maps. -/
theorem Reduction.comparison_eq
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (X : Scheme.{u}) (S : CoefficientDerivedSystemCalculus l E X)
    (r s : Reduction l E X S) : r.comparison.hom = s.comparison.hom := by
  let F := DerivedCategory.singleFunctor (coefficientSequenceModules l E X) 0
  let g := F.preimage (r.comparison.inv ≫ s.comparison.hom)
  have hg : F.map g = r.comparison.inv ≫ s.comparison.hom := F.map_preimage _
  have hf (n : ℕ) : (r.finite n).hom = (s.finite n).hom := by
    apply SheafOfModules.hom_ext
    apply PresheafOfModules.hom_ext
    intro V
    apply ModuleCat.hom_ext
    ext x
    exact eq_of_heq ((r.finite_sections n V x).trans (s.finite_sections n V x).symm)
  have he (n : ℕ) :
      (coefficientSequenceDerivedEvaluation l E X n).map
        (r.comparison.inv ≫ s.comparison.hom) = 𝟙 _ := by
    apply (cancel_epi ((coefficientSequenceDerivedEvaluation l E X n).map
      r.comparison.hom)).1
    apply (cancel_mono ((evaluationSingle l E X n).hom ≫
      (DerivedCategory.singleFunctor (normalizedDVRModules l E X n) 0).map
        (r.finite n).hom)).1
    simp only [Functor.map_comp, Category.assoc]
    rw [← Functor.map_comp_assoc, Iso.hom_inv_id, CategoryTheory.Functor.map_id,
      Category.id_comp]
    simpa only [hf n, Category.assoc, Category.comp_id, Category.id_comp] using
      (s.reduction n).trans (r.reduction n).symm
  have hge (n : ℕ) : (coefficientSequenceEvaluation l E X n).map g = 𝟙 _ := by
    apply (DerivedCategory.singleFunctor (normalizedDVRModules l E X n) 0).map_injective
    have hnat := ((coefficientSequenceEvaluation l E X n).mapDerivedCategorySingleFunctor
      0).hom.naturality g
    change (coefficientSequenceDerivedEvaluation l E X n).map (F.map g) ≫
      (evaluationSingle l E X n).hom = (evaluationSingle l E X n).hom ≫
        (DerivedCategory.singleFunctor (normalizedDVRModules l E X n) 0).map
          ((coefficientSequenceEvaluation l E X n).map g) at hnat
    rw [hg, he n] at hnat
    simp only [CategoryTheory.Functor.map_id]
    apply (cancel_epi (evaluationSingle l E X n).hom).1
    calc
      _ = 𝟙 _ ≫ (evaluationSingle l E X n).hom := hnat.symm
      _ = _ := by simp only [CategoryTheory.Category.id_comp, CategoryTheory.Category.comp_id]
  have hgid : g = 𝟙 _ := by
    apply SheafOfModules.hom_ext
    apply PresheafOfModules.hom_ext
    intro V
    obtain ⟨⟨n, V⟩⟩ := V
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    have h := congrArg (fun k ↦ k.val.app (op V) x) (hge n)
    exact h
  apply (cancel_epi r.comparison.inv).1
  calc
    _ = 𝟙 _ := r.comparison.inv_hom_id
    _ = F.map (𝟙 _) := (F.map_id _).symm
    _ = _ := by rw [← hgid, hg]

end WeilConjectures.CompletedUnitPullback
