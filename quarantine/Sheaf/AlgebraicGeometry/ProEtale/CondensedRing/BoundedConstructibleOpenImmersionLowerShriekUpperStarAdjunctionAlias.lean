module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible

@[expose] public section

/-!
# Short alias for the bounded-constructible open-immersion adjunction

Source: `literature/blueprint/main-20261015/blueprint/sec-six-functors-basics/`
`sk-def-sfb-dc-restricted-functors/def-sfb-dc-open-lower-shriek-adjunction.md`
(blueprint: def-sfb-dc-open-lower-shriek-adjunction)

This transparent abbreviation names the exact published declaration while keeping the
stage-2 existing-declaration probe below the style linter's line limit.
-/

universe u

open CategoryTheory
open AlgebraicGeometry
open AlgebraicGeometry.ProEtale
open AlgebraicGeometry.ProEtale.CondensedRing

namespace AlgebraicGeometry.ProEtale.CondensedRing

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]
  (ℓ : ℕ) [Fact ℓ.Prime]
  {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)]

section

include ℓ k

variable {U X : Over (Spec (.of k))}
  [LocallyOfFiniteType U.hom] [QuasiCompact U.hom] [IsSeparated U.hom]
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
  (j : U ⟶ X) [IsOpenImmersion j.left]

/-- Transparent short name for the exact existing adjunction declaration.

Source: `literature/blueprint/main-20261015/blueprint/sec-six-functors-basics/`
`sk-def-sfb-dc-restricted-functors/def-sfb-dc-open-lower-shriek-adjunction.md`
(blueprint: def-sfb-dc-open-lower-shriek-adjunction)
-/
noncomputable abbrev bcoOpenAdjunction :
    boundedConstructibleOpenImmersionLowerShriek Λ ℓ j ⊣ boundedConstructibleUpperStar Λ ℓ j :=
  boundedConstructibleOpenImmersionLowerShriekUpperStarAdjunction Λ ℓ j

end
end AlgebraicGeometry.ProEtale.CondensedRing
