/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Bounded.BoundedConstructibleLocalizingClosure
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.EllAdic.EllAdicCondensedCoefficient
import WeilConjectures.AlgebraicGeometry.Constructible.ConstructibleModuleObjectsEssentiallySmall
import WeilConjectures.CategoryTheory.DerivedCategory.Bounded.BoundedHomologyEssentiallySmall
import WeilConjectures.CategoryTheory.SixFunctors.CohomologicalSolutionSetRepresentability
import WeilConjectures.CategoryTheory.SixFunctors.SetGeneratedDerivedSolutionSet

/-! # Cohomological Brown representability on the constructible localizing hull
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits
open CategoryTheory.Pretriangulated.Opposite
open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ] (ℓ : ℕ) [Fact ℓ.Prime]
  {k : Type u} [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
  (X : Over (Spec (.of k)))
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
  (hΛ : IsEllAdicCoefficient ℓ Λ inferInstance)

include ℓ k hΛ

-- The more general argument below retains every binder of the assigned statement.
set_option linter.unusedSectionVars false in

/-- Brown representability on the localizing hull of adic constructible complexes. -/
theorem ellAdic_localizing_cohomological_isRepresentable
    (H : (boundedConstructibleLocalizingClosure Λ X.left).FullSubcategoryᵒᵖ ⥤
      AddCommGrpCat.{u + 1}) [H.IsHomological]
    (hH : ∀ I : Type (u + 1), PreservesLimitsOfShape (Discrete I) H) :
    (H ⋙ forget AddCommGrpCat).IsRepresentable := by
  have : IsLocallyNoetherian X.left := LocallyOfFiniteType.isLocallyNoetherian X.hom
  have : CompactSpace X.left := QuasiCompact.compactSpace_of_compactSpace X.hom
  let R := condensedRingObj Λ X.left
  have hheart : ObjectProperty.EssentiallySmall.{u + 1}
      (IsConstructibleModuleObject R) :=
    constructibleModuleObjects_essentiallySmall X.left R
  let P := ObjectProperty.isoClosure (IsConstructibleModuleObject R)
  have hbounded : ObjectProperty.EssentiallySmall.{u + 1} (boundedConstructible R) := by
    have := DerivedCategory.bounded_homologyProperty_essentiallySmall P
    apply ObjectProperty.EssentiallySmall.of_le
      (Q := DerivedCategory.TStructure.t.bounded ⊓ DerivedCategory.homologyProperty P)
    intro K hK
    exact ⟨hK.1, fun n ↦ ObjectProperty.le_isoClosure _ _ (hK.2 n)⟩
  apply cohomological_isRepresentable_of_solutionSet H hH
  refine setGeneratedDerived_cohomological_solutionSet (boundedConstructible R)
    (boundedConstructibleLocalizingClosure Λ X.left)
    (boundedConstructible_le_localizingClosure Λ X.left) ?_ H hH
  intro Q hQ hi ht hc
  let := hi
  let := ht
  let := hc
  exact boundedConstructibleLocalizingClosure_le Λ X.left Q hQ

end AlgebraicGeometry.ProEtale.CondensedRing
