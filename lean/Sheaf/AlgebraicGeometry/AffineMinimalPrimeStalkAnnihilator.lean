module

public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.RingTheory.Noetherian.Defs
public import Sheaf.AlgebraicGeometry.AssociatedPoints

import Mathlib.RingTheory.Ideal.AssociatedPrime.Localization
import Mathlib.RingTheory.Localization.AtPrime.Basic

/-!
# Stalk annihilators at minimal primes of Noetherian affine charts

Source: Stacks Project, Divisors, Tag 02OK(1), and Algebra, Tag 05BV, specialized to the
structure sheaf (blueprint: lem-trf-affine-minimal-prime-stalk-annihilator).
-/

@[expose] public section

universe u

namespace AlgebraicGeometry

/-- A minimal prime on a Noetherian affine chart gives a stalk element whose annihilator
is the maximal ideal, and hence an associated point of the structure sheaf.
The colon ideal of zero by `{w}` is precisely the ideal of elements `r` with `r * w = 0`.

Source: Stacks Project, Divisors, Tag 02OK(1), Algebra, Tags 05BV and 0310(1), and Schemes,
Tag 01HV(6) (blueprint: lem-trf-affine-minimal-prime-stalk-annihilator).

Proof:
1. Apply `lem-weil-pbc-noetherian-minimal-prime-associated` to the Noetherian section
   ring and its minimal prime to obtain `z` whose annihilator is that prime (Tag 05BV).
2. By `lem-weil-pbc-affine-open-stalk-localization`, the germ map identifies the stalk
   with localization at `hU.primeIdealOf y`. By `def-weil-pbc-localization-at-prime`,
   its maximal ideal is the extension of this prime. A ring isomorphism preserves units,
   hence also these maximal ideals of nonunits.
3. The annihilator of `z/1` is the extended prime: if `(a/s) * (z/1) = 0`, some
   `t` outside the prime satisfies `t*a*z = 0`. Thus `t*a` lies in the prime and `a`
   lies in it by primality. Conversely, the prime kills `z`, so its extension kills `z/1`.
4. Transport `z/1` and its annihilator across the stalk isomorphism. The resulting
   maximal-ideal annihilator witness gives membership in `associatedPoints T` by
   `def-sc-associated-points` (Tag 02OJ).
-/
theorem exists_stalk_annihilator_of_minimal_prime
    {T : Scheme.{u}} {U : T.Opens} (hU : IsAffineOpen U) (y : U)
    [IsNoetherianRing (T.presheaf.obj (Opposite.op U))]
    (hy : (hU.primeIdealOf y).asIdeal ∈
      minimalPrimes (T.presheaf.obj (Opposite.op U))) :
    (∃ w : T.presheaf.stalk (y : T),
      (⊥ : Ideal (T.presheaf.stalk (y : T))).colon {w} =
        IsLocalRing.maximalIdeal (T.presheaf.stalk (y : T))) ∧
      (y : T) ∈ associatedPoints T := by
  sorry

end AlgebraicGeometry
