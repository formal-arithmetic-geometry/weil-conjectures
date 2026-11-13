/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.TopologicalInvariance
public import Mathlib.Algebra.Category.ModuleCat.Sheaf
public import Mathlib.CategoryTheory.Abelian.RightDerived
import WeilConjectures.AlgebraicGeometry.ConstantRingModuleSheafEquivalence
import WeilConjectures.CategoryTheory.Sites.CohomologyDerivedEvaluation

/-!
# Comparison of the two encodings of injective module sheaves

## References

* Stacks Project, Cohomology on Sites, Tag 03FD.
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Etale

/-- An injective module-valued sheaf `J` has an injective constant-ring module representative `I`,
with the same underlying abelian sheaf, whose right-derived abelian evaluation computes the same
cohomology (Stacks, Tag 03FD). -/
theorem moduleValued_injective_cohomology_comparison (X : Scheme.{u}) (r : ℕ)
    (J : Sheaf X.smallEtaleTopology
      (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod r)))) [Injective J] :
    ∃ I : SheafOfModules.{u + 1}
      ((constantSheaf X.smallEtaleTopology RingCat.{u + 1}).obj
        (RingCat.of (ULift.{u + 1, u} (ULift.{u} (ZMod r))))),
      Injective I ∧
      Nonempty ((SheafOfModules.toSheaf _).obj I ≅
        (sheafCompose X.smallEtaleTopology
          (forget₂ (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod r))) AddCommGrpCat.{u + 1})).obj J) ∧
      ∀ q : ℕ, Nonempty
        (Sheaf.H
          ((sheafCompose X.smallEtaleTopology
            (forget₂ (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod r)))
              AddCommGrpCat.{u + 1})).obj J) q ≃+
          (((sheafToPresheaf X.smallEtaleTopology AddCommGrpCat.{u + 1} ⋙
            (CategoryTheory.evaluation X.Etaleᵒᵖ AddCommGrpCat.{u + 1}).obj
              (Opposite.op (Scheme.Etale.mk (𝟙 X)))).rightDerived q).obj
            ((SheafOfModules.toSheaf _).obj I))) := by
  obtain ⟨E, ⟨e⟩⟩ := constantRing_moduleSheaf_equivalence X r
  refine ⟨E.functor.obj J, (E.map_injective_iff J).2 inferInstance, ⟨(e.app J).symm⟩, ?_⟩
  let F := (SheafOfModules.toSheaf _).obj (E.functor.obj J)
  let Γ := sheafToPresheaf X.smallEtaleTopology AddCommGrpCat.{u + 1} ⋙
    (CategoryTheory.evaluation X.Etaleᵒᵖ AddCommGrpCat.{u + 1}).obj
      (Opposite.op (Scheme.Etale.mk (𝟙 X)))
  have hT : Limits.IsTerminal (Scheme.Etale.mk (𝟙 X)) :=
    MorphismProperty.Over.mkIdTerminal _ X
  intro q
  have h : Nonempty (Sheaf.H F q ≃+ (Γ.rightDerived q).obj F) := by
    cases q with
    | zero =>
      exact ⟨(Sheaf.H.equiv₀ F hT).trans
        ((Γ.rightDerivedZeroIsoSelf.app F).addCommGroupIsoToAddEquiv.symm)⟩
    | succ n =>
      exact Sheaf.cohomology_nonempty_addEquiv_rightDerived_evaluation_succ
        X.smallEtaleTopology (Scheme.Etale.mk (𝟙 X)) hT F n
  obtain ⟨a⟩ := h
  let b := (Sheaf.functorH X.smallEtaleTopology q).mapIso (e.app J)
  exact ⟨b.addCommGroupIsoToAddEquiv.trans a⟩

end AlgebraicGeometry.Etale
