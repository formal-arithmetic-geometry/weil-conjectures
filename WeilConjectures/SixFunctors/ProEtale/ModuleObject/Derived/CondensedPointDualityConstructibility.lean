/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CondensedPointDualComparisonData
import WeilConjectures.AlgebraicGeometry.Adic.AdicConstructibilityPredicateComparison
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Finite
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible

/-! # Constructibility of the dual on a finite condensed boundary -/

@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
universe u w
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.MonoidalClosed
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale.CondensedRing
variable (ℓ : ℕ) [Fact ℓ.Prime] (k : Type u) [Field k] [IsAlgClosed k]
  (I : Type w) [Finite I]

/-- The finite boundary is finite over its ground field, hence Noetherian. Identify
constant-model constructibility with the internal module constructibility predicate
and use closure of bounded constructible complexes under internal Hom with the unit.
Source: blueprint local boundary duality, Step 5.
(blueprint: lem-a1-condensed-point-dual-constructible) -/
theorem condensed_point_dual_constructible
    [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)] :
    CondensedBoundaryDualConstructibleAssertion ℓ k I := by
  let X : Over (Spec (.of k)) :=
    Over.mk (Sigma.desc fun _ : I ↦ 𝟙 (Spec (.of k)))
  have : IsFinite X.hom := by dsimp [X]; infer_instance
  have : LocallyOfFiniteType X.hom := inferInstance
  have : QuasiCompact X.hom := inferInstance
  have : IsSeparated X.hom := inferInstance
  have : CompactSpace X.left := QuasiCompact.compactSpace_of_compactSpace X.hom
  have : IsLocallyNoetherian X.left := LocallyOfFiniteType.isLocallyNoetherian X.hom
  have h := (adicConstructibilityPredicateComparison ℓ X.left
    (Profinite.padicAlgClRingObj ℓ) .algebraicClosure).2
  have : (boundedConstructible
      (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X.left)).IsMonoidalClosed :=
    isMonoidalClosed_boundedConstructible ℓ X
  have : (boundedConstructible
      (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X.left)).IsMonoidal :=
    isMonoidal_boundedConstructible ℓ X
  intro K hK
  change constantModelBoundedConstructible (Profinite.padicAlgClRingObj ℓ) X.left _
  rw [← h]
  apply ObjectProperty.prop_ihom
  · rw [h]
    exact hK
  · exact ObjectProperty.prop_unit _

end AlgebraicGeometry.ProEtale.CondensedRing
