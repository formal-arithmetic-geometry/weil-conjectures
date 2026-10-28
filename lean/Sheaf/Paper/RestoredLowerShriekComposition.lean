/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license.
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ShriekComposition

/-! The bounded-constructible lower-shriek composition isomorphism used by the condensed
compositor.

The upstream source `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ShriekComposition`
is back in the library (rework cluster restore, 2026-10-28), so this module re-exports it and
names its composition isomorphism `boundedConstructibleLowerShriekComp_padicAlgCl` as
`condensedLowerShriekComp_padicAlgCl` for the condensed compositor, instead of declaring a
second copy under the same name.
(blueprint: def-pur-restored-lower-shriek-composition). -/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory
namespace AlgebraicGeometry.ProEtale.CondensedRing

variable (ℓ : ℕ) [Fact ℓ.Prime]
variable {k : Type u} [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
variable {X Y S : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
  [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
  [LocallyOfFiniteType S.hom] [QuasiCompact S.hom] [IsSeparated S.hom]
variable (f : X ⟶ Y) (g : Y ⟶ S)

/-- The composition isomorphism `R(f ≫ g)_! ≅ Rf_! ⋙ Rg_!` of the bounded constructible
`ℚ̄_ℓ` lower shrieks used by the condensed compositor: the library composition
`boundedConstructibleLowerShriekComp_padicAlgCl` (chosen compactifications, common proper/open
refinement, open and proper compositors, proper/open exchange).
Source: ShriekComposition (blueprint: def-pur-restored-lower-shriek-composition). -/
abbrev condensedLowerShriekComp_padicAlgCl :
    boundedConstructibleLowerShriek (Profinite.padicAlgClRingObj ℓ) ℓ (f ≫ g) ≅
      boundedConstructibleLowerShriek (Profinite.padicAlgClRingObj ℓ) ℓ f ⋙
        boundedConstructibleLowerShriek (Profinite.padicAlgClRingObj ℓ) ℓ g :=
  boundedConstructibleLowerShriekComp_padicAlgCl ℓ f g

end AlgebraicGeometry.ProEtale.CondensedRing
