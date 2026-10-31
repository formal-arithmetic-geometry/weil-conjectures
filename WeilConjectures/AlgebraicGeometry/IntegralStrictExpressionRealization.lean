/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.IntegralExpressionSystemComparison
import WeilConjectures.AlgebraicGeometry.IntegralStructuralSystemComparison

/-! # Strict expression models before derived inverse limit

Source: Stacks 07A4 and 0941; integral coherence, strict-model step.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] WeilConjectures.sfAbSheafify WeilConjectures.sfAbBijective
attribute [local instance 2000] SheafOfModules.cochainModulesMonoidal
attribute [local irreducible] SheafOfModules.monoidalCategory

universe t u s i
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor MonoidalCategory
open Opposite AlgebraicGeometry
namespace WeilConjectures.IntegralCoherence
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
variable {S : Type s} {W : S → Scheme.{t}}

/-- The strict portion of an expression realization, prior to completed operations.
Source: Stacks 07A4 and 0941
(blueprint: stage3-pur-strict-expression-realization). -/
structure StrictRealization (M : CompletedOperations.Models l E W)
    {I : Type i} {location : I → S} (N : ∀ k : I, Complex l E (W (location k))) where
  good : ∀ {a : S} (P : CompletedOperations.Expression W location a),
    Good l E (W := W) a (value l E N P)
  normalized : ∀ {a : S} (P : CompletedOperations.Expression W location a),
    IsNormalizedCoefficientSequence l E (W a) (DerivedCategory.Q.obj (value l E N P))
  system : ∀ {a : S} (P : CompletedOperations.Expression W location a),
    DerivedCategory.Q.obj (value l E N P) ≅
      (CompletedOperations.systemValue l E M P).obj (fun k ↦ DerivedCategory.Q.obj (N k))
  system_input : ∀ k : I, system (.input k) = Iso.refl _
  system_unit : ∀ a : S, system (.unit a) = (by
    exact (show DerivedCategory.Q.obj (value l E N (.unit a)) ≅
      CompletedOperations.unit l E (W := W) a from
      (by with_unfolding_all exact Iso.refl (CompletedOperations.unit l E (W := W) a))))
  system_tensor : ∀ {a : S} (P Q : CompletedOperations.Expression W location a),
    system (.tensor P Q) =
      CoefficientTensorModels.iso
        (coefficientSequenceTopology (Scheme.ProEt.topology (W a)))
        (coefficientSequenceCommRingSheaf l E (W a)) (M.system a).closed (M.system a).models
        (value l E N P) (value l E N Q) (good P).1 (good Q).1 ≪≫
      (CompletedOperations.tensor l E M a).mapIso (Iso.prod (system P) (system Q))
  system_pullback : ∀ {a b : S} (f : W a ⟶ W b)
    (P : CompletedOperations.Expression W location b),
    system (.pullback f P) =
      ((integralComparisonSequencePullback l E f).mapDerivedCategoryFactors.app
        (value l E N P)).symm ≪≫
        (integralComparisonDerivedSequencePullback l E f).mapIso (system P)
  structural : ∀ {a : S} {P Q : CompletedOperations.Expression W location a}
    (α : CompletedOperations.StructuralMap P Q),
    DerivedCategory.Q.map (structuralValue l E N α).hom ≫ (system Q).hom =
      (system P).hom ≫ (CompletedOperations.structuralValue l E M α
        (fun k ↦ DerivedCategory.Q.obj (N k))).hom

/-- Strict tensor/pullback expressions compute their system-derived interpretations.
Source: Stacks sites-cohomology.tex, Tags 07A4 and 0941; integral-coherence
proof steps 1--4 (blueprint: stage3-pur-strict-expression-realization).

Proof: induct on the expression. Inputs use the supplied good and normalized
complexes, with the identity comparison. The coefficient unit is the complex
concentrated in degree zero, hence is K-flat with flat terms. Tensor uses the
K-flat total-tensor theorem and the normalized system tensor comparison. Inverse
image uses exact constant-coefficient pullback and its localization comparison.
Transport normalization through these comparisons, using the primitive normalized
unit, tensor and pullback laws. For structural arrows induct on StructuralMap.
On the associator, unitors and symmetry, the RingedSiteDualityModel equations
identify the localized actual cochain maps with the prescribed system maps:
use tensor-generator extensionality, including the Koszul sign for symmetry.
For composition use localization of the actual adjunction-normalized compositor.
Identity, inverse, composite, tensor context and pullback context follow by
functoriality, naturality of the tensor model and cancellation of isomorphisms.
All constructions take place on the sequence site; no inference from equality
of evaluated derived arrows is needed. Empty families and zero inputs obey the
same recursion, and no flatness of a quotient ring map is assumed. -/
theorem strictExpressionRealization
    (M : CompletedOperations.Models l E W)
    (hM : CompletedOperations.ComparisonLaws.{t, u, s, i} l E M)
    {I : Type i} {location : I → S}
    (N : ∀ k : I, Complex l E (W (location k)))
    (hg : ∀ k : I, Good l E (W := W) (location k) (N k))
    (hn : ∀ k : I, IsNormalizedCoefficientSequence l E (W (location k))
      (DerivedCategory.Q.obj (N k))) :
    Nonempty (StrictRealization l E M N) := by
  exact ⟨{
    good := goodExpression l E M N hg
    normalized := normalizedExpression l E M hM N hg hn
    system := systemComparison l E M N hg
    system_input := fun _ ↦ rfl
    system_unit := fun _ ↦ rfl
    system_tensor := fun _ _ ↦ rfl
    system_pullback := fun _ _ ↦ rfl
    structural := structuralSystemComparison l E M N hg }⟩

end WeilConjectures.IntegralCoherence
