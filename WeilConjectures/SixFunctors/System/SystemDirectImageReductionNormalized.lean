/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Supporting.CoefDerivedSystemEvaluationCalculus
public import WeilConjectures.TraceFormula.Integral.IntegralComparisonSequenceSystems
import WeilConjectures.SixFunctors.System.SystemDirectImageFiniteComparisonTransitions
import WeilConjectures.TraceFormula.Compact.CompactSupportDirectImageEvaluation
import WeilConjectures.AlgebraicGeometry.ProEtale.Coefficient.ProEtaleCoefficientPullbackExact

/-! # Normalization of the direct image of a reduction system

## References

* [Stacks, Tag 0941](https://stacks.math.columbia.edu/tag/0941)
* [Stacks, Tag 099N](https://stacks.math.columbia.edu/tag/099N)
* Zheng, Construction 4.1, Lemma 4.10
* Bhatt--Scholze, Lemma 6.5.11(3)
-/

@[expose] public section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
attribute [local irreducible] CategoryTheory.Functor.rightDerivedFunctor
  CategoryTheory.Functor.mapDerivedCategory HasDerivedCategory.standard
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures

private theorem transition_bijective_of_iso
    {C D : Type*} [Category C] [Category D] (R : D ⥤ C)
    {M M' : C} {N N' : D} (em : M ≅ M') (en : N ≅ N')
    (s : M ⟶ R.obj N) (t : M' ⟶ R.obj N')
    (h : s ≫ R.map en.hom = em.hom ≫ t) (P : D)
    (hs : Function.Bijective (fun a : N ⟶ P ↦ s ≫ R.map a)) :
    Function.Bijective (fun a : N' ⟶ P ↦ t ≫ R.map a) := by
  constructor
  · intro a b hab
    apply (cancel_epi en.hom).1
    apply hs.injective
    simp only [Functor.map_comp, ← Category.assoc, h]
    simpa only [Category.assoc] using congrArg (fun z ↦ em.hom ≫ z) hab
  · intro a
    obtain ⟨b, hb⟩ := hs.surjective (em.hom ≫ a)
    refine ⟨en.inv ≫ b, ?_⟩
    apply (cancel_epi em.hom).1
    rw [← Category.assoc, ← h]
    calc
      (s ≫ R.map en.hom) ≫ R.map (en.inv ≫ b) = s ≫ R.map b := by
        rw [Category.assoc, ← R.map_comp, Iso.hom_inv_id_assoc]
      _ = em.hom ≫ a := hb

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall in
/-- The whole-system direct image of a reduction system is normalized.
This asserts only the universal finite quotient transition property. It does not
choose a limit, a finite evaluation comparison, or a map of Roos triangles. -/
theorem systemDirectImage_reduction_normalized
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    [(integralComparisonSequenceDirectImage l E f).Additive]
    [Abelian.HasKInjectiveResolutions (coefficientSequenceModules l E X)]
    (S : CoefficientDerivedSystemCalculus l E X)
    (K : DerivedCategory (scalarReductionSource l E X)) :
    IsNormalizedCoefficientSequence l E Y
      ((integralComparisonSequenceDirectImage l E f).rightDerivedFunctor.obj
        (S.reduction.obj K)) := by
  let levelAdditive (n : ℕ) : (compactSupportLevelDirectImage l E f n).Additive := by
    constructor
    intro M N a b
    ext V x
    rfl
  let levelKInjective (n : ℕ) :
      Abelian.HasKInjectiveResolutions (normalizedDVRModules l E X n) :=
    proEtaleRingModules_hasKInjectiveResolutions X (integralCoefficientCommRingSheaf l E X n)
  let pullAdditive (n : ℕ) : (compactSupportLevelPullback l E f n).Additive :=
    (Adjunction.ofIsRightAdjoint (compactSupportLevelDirectImage l E f n)).left_adjoint_additive
  let pullLimits (n : ℕ) : PreservesFiniteLimits (compactSupportLevelPullback l E f n) :=
    (Scheme.coefficientProEtaleModulePullback_exact.{u, u} f _).1
  let pullColimits (n : ℕ) : PreservesFiniteColimits (compactSupportLevelPullback l E f n) :=
    (Scheme.coefficientProEtaleModulePullback_exact.{u, u} f _).2
  obtain ⟨_, d, o, ho, hd, _, _⟩ := compactSupportDirectImageEvaluation l E f
  obtain ⟨T, _⟩ := coefficientDerivedSystemEvaluationCalculus l E Y
  let b (n : ℕ) := systemDirectImageFiniteComparison l E f S T d K n
  have hb (n : ℕ) : IsIso (b n) := by
    have := completedDirectImageFiniteProjection_isIso l E f n K
    dsimp only [b, systemDirectImageFiniteComparison]
    infer_instance
  intro m n h P
  exact transition_bijective_of_iso (normalizedDVRRes l E Y h)
    (asIso (b m)) (asIso (b n)) _ _
    (systemDirectImageFiniteComparison_transitions l E f S T o d ho hd K h) P
    (T.reduction_normalized _ h P)

end WeilConjectures
