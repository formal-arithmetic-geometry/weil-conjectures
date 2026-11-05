/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperStarUnitCoherence
public import WeilConjectures.TraceFormula.Specialization.Integral

/-!

# Unit classes along proper morphisms

For a proper morphism `f : X ⟶ Y` the *relative unit class* `[f] : ℚ̄_ℓ ⟶ Rf_! ℚ̄_ℓ` is the unit
of `Lf^* ⊣ Rf_*` at `ℚ̄_ℓ`, read through `Lf^* ℚ̄_ℓ ≅ ℚ̄_ℓ` and `Rf_! ≅ Rf_*`
(`ProEtale.CondensedRing.properUnitClass`). For the structure map of a proper scheme it is the
unit class `BorelMooreSection.unitClass`. Relative unit classes compose:
`[f ≫ g] = Rg_!([f]) ∘ [g]` read through `R(f ≫ g)_! ≅ Rg_! Rf_!`
(`ProEtale.CondensedRing.properUnitClass_comp`), by the composition of the units of the
adjunctions `L(·)^* ⊣ R(·)_*`. In particular, for a proper morphism `r : B ⟶ F` of proper
`k`-schemes, `[B] = Ra_{F!}([r]) ∘ [F]` read through `Ra_{B!} ≅ Ra_{F!} Rr_!`
(`ProEtale.CondensedRing.unitClass_comp_map_properUnitClass`). This is the compatibility of unit
classes needed in fact (III) of `ComponentClassReduction`, for `r` the closed immersion
`componentSpecialLift : B'' ⟶ F'`.

-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

section Abstract

variable {C₁ C₂ C₃ : Type*} [Category C₁] [Category C₂] [Category C₃]

end Abstract

open Scheme

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)]

section Relative

variable {X Y Z : Over (Spec (.of k))} [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
  [IsSeparated X.hom] [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
  [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom] [IsSeparated Z.hom]

end Relative

end AlgebraicGeometry.ProEtale.CondensedRing
