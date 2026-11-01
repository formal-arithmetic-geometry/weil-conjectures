/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.Algebra.CharP.Algebra
public import WeilConjectures.TraceFormula.Specialization.Trait

/-!
# Instances on the trait `Spec k'⟦t⟧`

The closed point `Spec k' ⟶ Spec k'⟦t⟧` of the trait is a closed immersion, and the field `Ω` of
the geometric generic point of the trait has the characteristic of `k'`
(`AlgebraicGeometry.ProEtale.CondensedRing.NearbyCyclesModel.ringChar_traitGenericField`).

These are split out of `WeilConjectures.TraceFormula.Specialization.NearbyKunnethGlobal` so that
the modules which only need them do not depend on the global-sections step of Gabber's Künneth
formula.

-/

@[expose] public section

universe u

namespace AlgebraicGeometry.ProEtale.CondensedRing

namespace NearbyCyclesModel

section Product

variable {k' : Type u} [Field k']

instance : IsClosedImmersion (traitClosedPoint k') :=
  IsClosedImmersion.spec_of_surjective _ fun a ↦ ⟨PowerSeries.C a, by simp⟩

end Product

section TraitGenericField

variable (ℓ : ℕ) {k' : Type u} [Field k']

/-- The geometric generic point of the trait has the characteristic of `k'`. -/
lemma ringChar_traitGenericField : ringChar (traitGenericField k') = ringChar k' :=
  (Algebra.ringChar_eq k' _).symm

instance [Fact (ringChar k').Prime] : Fact (ringChar (traitGenericField k')).Prime :=
  ⟨by rw [ringChar_traitGenericField]; exact Fact.out⟩

instance [Fact (ringChar k' ≠ ℓ)] : Fact (ringChar (traitGenericField k') ≠ ℓ) :=
  ⟨by rw [ringChar_traitGenericField]; exact Fact.out⟩

end TraitGenericField

end NearbyCyclesModel

end AlgebraicGeometry.ProEtale.CondensedRing
