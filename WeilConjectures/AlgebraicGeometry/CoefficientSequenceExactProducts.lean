/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CoefficientRingedSequenceSiteSupplement
import WeilConjectures.AlgebraicGeometry.CoefficientSequenceCoinduction
import WeilConjectures.AlgebraicGeometry.ProEtaleCountableProductsExact
import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
import Mathlib.AlgebraicGeometry.Sites.Proetale
import Mathlib.CategoryTheory.Sites.ConstantSheaf
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import WeilConjectures.CategoryTheory.RingedSiteModules
import WeilConjectures.AlgebraicGeometry.CompletedIntegralCoefficientsSupplement
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
import Mathlib.CategoryTheory.Limits.Shapes.Countable
import WeilConjectures.AlgebraicGeometry.ProEtaleAffineWeaklyContractibleCover
import WeilConjectures.AlgebraicGeometry.ProEtaleAffineContractibleExtension
import WeilConjectures.AlgebraicGeometry.ProEtale.WeaklyContractible
import WeilConjectures.AlgebraicGeometry.ProEtaleWeaklyContractibleEvaluationColimitsSupplement
import Mathlib.CategoryTheory.Sites.CompatibleSheafification
import Mathlib.CategoryTheory.Limits.Types.Products
import Mathlib.CategoryTheory.Sites.EpiMono
import Mathlib.CategoryTheory.Sites.Abelian
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products

/-! # Exact countable products of coefficient sequences

Source: Stacks Tags 03DB and 0947; Bhatt--Scholze, Propositions 3.1.9 and 3.2.3.
(blueprint: lem-coef-sequence-exact-countable-products).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u v r
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
namespace WeilConjectures.CoefficientCoinduction

private theorem pushforward_countable_limits
    {C D : Type*} [Category C] [Category D]
    {J : GrothendieckTopology C} {T : GrothendieckTopology D}
    {F : C ⥤ D} [F.IsContinuous J T]
    {S : Sheaf J RingCat.{r}} {R : Sheaf T RingCat.{r}}
    (φ : S ⟶ (F.sheafPushforwardContinuous RingCat.{r} J T).obj R) :
    PreservesLimitsOfShape (Discrete ℕ) (SheafOfModules.pushforward.{v} φ) := by
  let V := SheafOfModules.forget.{v} S ⋙ PresheafOfModules.toPresheaf S.obj
  have : PreservesLimitsOfShape (Discrete ℕ) (SheafOfModules.pushforward.{v} φ ⋙ V) := by
    change PreservesLimitsOfShape (Discrete ℕ)
      ((SheafOfModules.forget.{v} R ⋙ PresheafOfModules.toPresheaf R.obj) ⋙
        (Functor.whiskeringLeft Cᵒᵖ Dᵒᵖ AddCommGrpCat.{v}).obj F.op)
    infer_instance
  have : ReflectsLimitsOfShape (Discrete ℕ) V :=
    reflectsLimitsOfShape_of_reflectsIsomorphisms
  exact preservesLimitsOfShape_of_reflects_of_preserves _ V

private theorem exactProducts_of_epi {A : Type*} [Category A] [Abelian A]
    [HasCountableProducts A]
    (he : ∀ (X Y : ℕ → A) (f : ∀ n, X n ⟶ Y n),
      (∀ n, Epi (f n)) → Epi (Limits.Pi.map f)) :
    HasExactLimitsOfShape (Discrete ℕ) A := by
  let : (lim (J := Discrete ℕ) (C := A)).PreservesEpimorphisms := ⟨fun {X Y} f hf ↦ by
    have : ∀ n : ℕ, Epi (f.app ⟨n⟩) := fun n ↦ inferInstance
    have : Epi (Limits.Pi.map (fun n : ℕ ↦ f.app ⟨n⟩)) := he _ _ _ this
    have hmap : lim.map f = (Pi.isoLimit X).inv ≫
        Limits.Pi.map (fun n : ℕ ↦ f.app ⟨n⟩) ≫ (Pi.isoLimit Y).hom := by
      apply limit.hom_ext
      rintro ⟨n⟩
      simp only [Category.assoc, Pi.isoLimit_hom_π, Limits.Pi.map_π,
        Pi.isoLimit_inv_π_assoc]
      exact limMap_π f ⟨n⟩
    rw [hmap]
    infer_instance⟩
  exact hasExactLimitsOfShape_of_preservesEpi A (Discrete ℕ)

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (W : Scheme.{u})

private theorem evaluation_countable_limits (n : ℕ) :
    PreservesLimitsOfShape (Discrete ℕ) (coefficientSequenceEvaluation l E W n) := by
  unfold coefficientSequenceEvaluation
  exact pushforward_countable_limits _

private theorem epi_of_evaluation_epi
    {M N : coefficientSequenceModules l E W} (f : M ⟶ N)
    (hf : ∀ n, Epi ((coefficientSequenceEvaluation l E W n).map f)) : Epi f := by
  apply (equivalence l E W).inverse.epi_of_epi_map
  constructor
  intro Z g h hfg
  apply SheafOfModules.strictRingSystem_hom_ext
  intro n
  have hn : Epi ((SheafOfModules.systemEvaluation (rings l E W) n).map
      ((equivalence l E W).inverse.map f)) := by
    change Epi (((equivalence l E W).inverse ⋙
      SheafOfModules.systemEvaluation (rings l E W) n).map f)
    rw [evaluation_eq]
    exact hf n
  apply (cancel_epi ((SheafOfModules.systemEvaluation (rings l E W) n).map
    ((equivalence l E W).inverse.map f))).1
  simpa only [Functor.map_comp, SheafOfModules.systemEvaluation] using
    congrArg (fun k ↦ (SheafOfModules.systemEvaluation (rings l E W) n).map k) hfg

/-- Countable products in the actual coefficient sequence category are exact.
Source: Stacks Tags 03DB and 0947; Bhatt--Scholze, Propositions 3.1.9 and 3.2.3.
(blueprint: lem-coef-sequence-exact-countable-products).

Proof: coefficient evaluation is continuous module pushforward and preserves countable
products, as can be checked after forgetting to presheaves of abelian groups. The
strict-system equivalence identifies these evaluations with the component functors;
componentwise epimorphisms are epimorphisms by cancellation in every component.
Products of epimorphisms are epimorphisms in each finite-level pro-etale module category.
The product comparison isomorphisms therefore make a sequence product map epic at
every level, hence epic. Since the limit functor is left exact, preservation of
epimorphisms gives its exactness. The argument includes the empty scheme and zero
coefficient modules and makes no flatness assumption on the quotient rings. -/
theorem sequence_exact_products :
    HasExactLimitsOfShape (Discrete ℕ) (coefficientSequenceModules l E W) := by
  apply exactProducts_of_epi
  intro X Y f hf
  apply epi_of_evaluation_epi l E W
  intro n
  let F := coefficientSequenceEvaluation l E W n
  have : PreservesLimitsOfShape (Discrete ℕ) F := evaluation_countable_limits l E W n
  have hfn : ∀ i, Epi (F.map (f i)) := fun i ↦ by
    have := hf i
    infer_instance
  have : Epi (Limits.Pi.map (fun i ↦ F.map (f i))) :=
    (Scheme.ProEt.countableProducts_exact.{u, 0, 0} W
      (integralCoefficientCommRingSheaf l E W n)).2.2
      ℕ (fun i ↦ F.obj (X i)) (fun i ↦ F.obj (Y i)) (fun i ↦ F.map (f i)) hfn
  have he : F.map (Limits.Pi.map f) ≫ piComparison F Y =
      piComparison F X ≫ Limits.Pi.map (fun i ↦ F.map (f i)) := by
    apply Pi.hom_ext
    intro i
    simp [← Functor.map_comp]
  apply (epi_comp_iff_of_isIso (F.map (Limits.Pi.map f)) (piComparison F Y)).1
  rw [he]
  infer_instance

end WeilConjectures.CoefficientCoinduction
