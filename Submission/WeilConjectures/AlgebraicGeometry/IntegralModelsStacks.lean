/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import Submission.WeilConjectures.AlgebraicGeometry.ConstantModelTorAmplitude
public import Submission.WeilConjectures.AlgebraicGeometry.IntegralConstantModelRealization
public import Submission.WeilConjectures.AlgebraicGeometry.IntegralModelsStacksData
import all Submission.WeilConjectures.AlgebraicGeometry.IntegralConstantModelHeartClosure
import Submission.WeilConjectures.AlgebraicGeometry.IntegralConstantModelCriterion
import Submission.WeilConjectures.AlgebraicGeometry.IntegralModelsCompletionTransport
import Submission.WeilConjectures.AlgebraicGeometry.IntegralModelsStacksBasic
import Submission.WeilConjectures.Mathlib.CategoryTheory.ObjectProperty.Equivalence
import Submission.WeilConjectures.SixFunctors.ProEtale.InternalCompletionStacksComparison
import Submission.WeilConjectures.SixFunctors.ProEtale.InternalResidueStacksComparison

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

/-! # Integral models and Stacks adic constructibility

This file proves `det-lem-integral-models-stacks` along the blueprint route: restriction of
scalars along the map from the constant coefficient ring, the integral constructibility
criterion `sk-prop-integral-criterion`, part (2) of
`det-prop-integral-criterion-constant-coefficients` and the pro-étale/étale comparison of
constructible complexes. The criterion is stated in the internal presentation over
`DerivedNakayama.integerRing` (`internal_integral_criterion_forward`,
`internal_integral_criterion_reverse`), where completeness is the Roos condition
`IsDerivedComplete` and the residue is `AdicCompletion.derivedReduction`.

Here `Dᵇc(X, 𝒪_E)` is `constantModelBoundedConstructible`, the finite-constant-model form of
`sk-def-sfb-constructible`. For this form the reverse implication of the criterion needs the
local structure theorem `sk-prop-integral-local-structure`; it is supplied by the adic stratified
perfect models through `integral_models_stacks_criterion`.

## Main statements

* `internal_integral_criterion_forward`, `internal_integral_criterion_reverse`: the two
  directions of `sk-prop-integral-criterion`.
* `integral_models_stacks`: `K ∈ Dᵇc(X, 𝒪_E)` iff `Res K` is Stacks adic constructible
  (`integral_models_stacks_criterion`), and `Res` restricts to an equivalence of the two full
  subcategories.

Source: blueprint det-lem-integral-models-stacks; Stacks Tag 09C1.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] AlgebraicGeometry.ProEtale.upperStarFromPoint
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale.IntegralModelsStacks

/-- Local derived completeness for the first residue map, transported to the small site:
the completeness clause of `stacksConstructible`.
Source: Stacks Tag 09C1 (auxiliary; not a blueprint node). -/
def stacksComplete (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (X : Scheme.{u}) :
    ObjectProperty (DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (discreteObj (Padic.coefficientExtensionIntegers l E)) X))) :=
  fun L ↦ ConstantCompletion.IsComplete (smallMap X (residueMap l E X))
    (smallDerivedObject X _ L)

/-- The complexes over the continuous integers whose restriction to the constant integers is
complete in the sense of `stacksComplete`.
Source: blueprint det-lem-integral-models-stacks
(auxiliary; not a blueprint node). -/
def restrictionComplete (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (X : Scheme.{u}) :
    ObjectProperty (DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (integersObj l E) X))) :=
  fun K ↦ stacksComplete l E X ((restriction l E X).obj K)


/-- Restriction of scalars along the map from the constant integer ring is an equivalence from
the complexes whose restriction is complete onto the complete complexes, with the inclusion
functors identified with restriction. This is part (2) of
`det-prop-integral-criterion-constant-coefficients` (restriction of scalars is an equivalence
on derived complete objects), transported to the small-site presentation of
`stacksConstructible`; completeness of `K` is read on its restriction as in part (3).
Source: Stacks Tags 0999 and 09C1
(blueprint: det-prop-integral-criterion-constant-coefficients).

Proof: this is `completion_transport`, whose first clause identifies its source property
with `restrictionComplete` and whose target property is `stacksComplete`. -/
theorem restriction_complete_equivalence
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (X : Scheme.{u}) [IsNoetherian X] :
    ∃ e : (restrictionComplete l E X).FullSubcategory ≌ (stacksComplete l E X).FullSubcategory,
      Nonempty (e.functor ⋙ (stacksComplete l E X).ι ≅
        (restrictionComplete l E X).ι ⋙ restriction l E X) := by
  obtain ⟨h, e, α⟩ := completion_transport l E X
  have hA : (fun K ↦ Scheme.IsSfbAdicComplete X (IntegralConstantCompletion.ideal l E)
      ((IntegralConstantModel.derived l E X).functor.obj K)) = restrictionComplete l E X :=
    funext fun K ↦ propext (h K)
  exact hA ▸ ⟨e, α⟩

/-- Restriction of scalars identifies the bounded constant-model constructible category
with the Stacks adic constructible category, and reflects membership for every complex.
Source: blueprint det-lem-integral-models-stacks; Stacks Tag 09C1
(blueprint: det-lem-integral-models-stacks).

Proof: the criterion is `integral_models_stacks_criterion`. Restriction is an equivalence
from the complexes with complete restriction onto the complete complexes
(`restriction_complete_equivalence`); bounded constructible complexes have complete
restriction and Stacks adic constructible complexes are complete, so the equivalence
restricts to the selected full subcategories with the same functor. -/
theorem integral_models_stacks (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (X : Scheme.{u}) [IsNoetherian X] :
    (∀ K, constantModelBoundedConstructible (integersObj l E) X K ↔
      stacksConstructible l E X ((restriction l E X).obj K)) ∧
    ∃ e : ConstantModelBoundedConstructible (integersObj l E) X ≌
        (stacksConstructible l E X).FullSubcategory,
      Nonempty (e.functor ⋙ (stacksConstructible l E X).ι ≅
        (constantModelBoundedConstructible (integersObj l E) X).ι ⋙ restriction l E X) := by
  have hm := integral_models_stacks_criterion l E X
  refine ⟨hm, ?_⟩
  obtain ⟨e, ⟨α⟩⟩ := restriction_complete_equivalence l E X
  let : (stacksConstructible l E X).IsClosedUnderIsomorphisms :=
    ⟨fun ε h ↦ stacksConstructible_iso l E X ε h⟩
  exact ObjectProperty.exists_equivalence_of_le
    (constantModelBoundedConstructible (integersObj l E) X)
    (restrictionComplete l E X) (stacksConstructible l E X) (stacksComplete l E X)
    (restriction l E X) e α
    (fun K hK ↦ ((hm K).mp hK).1) (fun _ h ↦ h.1) (fun K _ ↦ hm K)

end AlgebraicGeometry.ProEtale.IntegralModelsStacks
