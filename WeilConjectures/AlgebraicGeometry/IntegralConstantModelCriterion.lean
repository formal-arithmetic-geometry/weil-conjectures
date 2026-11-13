/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.IntegralModelsStacksData
import all WeilConjectures.AlgebraicGeometry.IntegralCohomologicalAdicCriterion
import WeilConjectures.AlgebraicGeometry.IntegralConstantModelConstructibility
import WeilConjectures.AlgebraicGeometry.IntegralModelsCompletionTransport
import WeilConjectures.AlgebraicGeometry.IntegralModelsResidueTransport

/-! # The integral criterion for constant-model constructibility

For the finite-constant-model formulation `constantModelBoundedConstructible`, a complex
over the continuous integers is bounded constructible iff its restriction to the constant
integers is Stacks adic constructible. The proof goes through the adic stratified perfect
models (Bhatt–Scholze, Proposition 6.8.11(3)), which supply the local structure theorem
for finite constant models.

## References

* Bhatt–Scholze, *The pro-étale topology for schemes*, Proposition 6.8.11.
* Stacks Project, Tags 09C1 and 09C7.
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

/-- A complex over the continuous integers is bounded constructible (bounded cohomology
with finite constant stratified models) iff its restriction to the constant integers is
Stacks adic constructible. (Bhatt–Scholze, Proposition 6.8.11; Stacks, Tags 09C1, 09C7.) -/
theorem integral_models_stacks_criterion (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (X : Scheme.{u}) [IsNoetherian X]
    (K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (integersObj l E) X))) :
    constantModelBoundedConstructible (integersObj l E) X K ↔
      stacksConstructible l E X ((restriction l E X).obj K) := by
  let F := IntegralConstantModel.modulesFunctor l E X
  have hc : constantModelBoundedConstructible (integersObj l E) X K ↔
      (DerivedCategory.TStructure.t.bounded
          ((IntegralConstantModel.derived l E X).functor.obj K) ∧
        ∀ q : ℤ, Scheme.IsCompletedConstantStratified X
          (IntegralConstantCompletion.ideal l E)
          ((DerivedCategory.homologyFunctor _ q).obj
            ((IntegralConstantModel.derived l E X).functor.obj K))) := by
    apply and_congr
    · exact ⟨F.bounded_mapDerivedCategory_obj, F.bounded_of_bounded_mapDerivedCategory_obj⟩
    · apply forall_congr'
      intro q
      let e := (F.mapDerivedCategoryHomologyFunctorIso q).app K
      exact (IntegralConstantModel.constructible_iff l E X _).trans
        ⟨fun h ↦ Scheme.completedStratified_of_iso e h,
          fun h ↦ Scheme.completedStratified_of_iso e.symm h⟩
  have hcomplete := (completion_transport l E X).1
  have ha : Scheme.IsSfbAdicConstructible X (IntegralConstantCompletion.ideal l E)
      ((IntegralConstantModel.derived l E X).functor.obj K) ↔
        stacksConstructible l E X ((restriction l E X).obj K) := by
    constructor
    · intro h
      exact ⟨(hcomplete K).mp h.1, (residue_transport l E X K h.1).mpr h⟩
    · intro h
      exact (residue_transport l E X K ((hcomplete K).mpr h.1)).mp h.2
  exact hc.trans ((Scheme.integral_cohomological_adic_criterion l E X _).trans ha)

end AlgebraicGeometry.ProEtale.IntegralModelsStacks
