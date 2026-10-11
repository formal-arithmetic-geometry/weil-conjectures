module

public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.RingTheory.Ideal.AssociatedPrime.Basic

@[expose] public section

universe w

open AlgebraicGeometry

namespace AlgebraicGeometry

/-!
# Associated points of a scheme

Source: Stacks Project, Divisors, Tag 02OZ (blueprint: def-sc-associated-points).
-/

/-- The associated points of a scheme, defined stalkwise by the associated-prime
condition for the maximal ideal of the local ring.
Source: Stacks Project, Divisors, Tag 02OZ (blueprint: def-sc-associated-points). -/
def associatedPoints (X : Scheme.{w}) : Set X :=
  {x | IsAssociatedPrime (IsLocalRing.maximalIdeal (X.presheaf.stalk x))
    (X.presheaf.stalk x)}

end AlgebraicGeometry
