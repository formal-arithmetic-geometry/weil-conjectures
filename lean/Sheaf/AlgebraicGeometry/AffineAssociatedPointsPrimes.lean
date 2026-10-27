/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q66
-/
module

public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.RingTheory.Noetherian.Defs
public import WeilConjectures.RingTheory.AnnihilatorAssociatedPrimes
public import Sheaf.AlgebraicGeometry.CoherentFiniteType
public import Sheaf.AlgebraicGeometry.RelativeAssassin
import WeilConjectures.AlgebraicGeometry.Morphisms.AffineModuleGermLocalization
import Sheaf.RingTheory.AssociatedPrimeLocalizeAtPrime

/-! # Associated points on an affine open and associated primes of sections

Source: Stacks Project, Divisors, Tag 02OK (`lemma-associated-affine-open`),
both implications and the Noetherian consequence
(blueprint: lem-sfb-affine-associated-points-primes).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory Opposite

namespace AlgebraicGeometry.Scheme.Modules

/-- On an affine open, annihilator-associated primes of sections give associated points.
The converse holds when the corresponding prime is finitely generated, and hence the
conditions are equivalent when the section ring is Noetherian. The section module need
not be finitely generated.

Source: Stacks Project, Divisors, Tag 02OK (`lemma-associated-affine-open`), with the
finite-generator argument of Algebra, Tag 0310 (`lemma-associated-primes-localize`).
(blueprint: lem-sfb-affine-associated-points-primes)

Proof:
1. Identify the ring germ with localization at the corresponding prime using
   `IsAffineOpen.isLocalization_stalk` (lem-weil-pbc-affine-open-stalk-localization).
   Identify the module germ with localization of sections using
   `Scheme.isLocalizedModule_affine_germ` (lem-sbc-affine-module-germ-localization).
   These identifications respect the localized scalar action, and the maximal ideal
   of the local ring is the extended prime (def-weil-pbc-localization-at-prime).
   Thus `associatedPoints` (def-trf-relative-assassin) says that the extended prime
   is the annihilator of an element of the localized section module.
2. If the prime is an element annihilator before localization, it remains one after
   localization by `Module.associated_prime_localize_at_prime`
   (lem-weil-pbc-associated-prime-localize-at-prime). Step 1 gives the forward direction.
3. Conversely, write a localized witness as m/f. The denominator is a unit, so m/1
   has the same annihilator. For generators a_i of the prime, choose s_i outside the
   prime killing a_i m using the localization kernel criterion
   (def-weil-pbc-module-localization). Their product s lies outside the prime and
   z = s m is killed by the whole prime. For no generators, take the empty product 1.
4. If a z = 0, localize and cancel the unit s/1. Then a/1 belongs to the extended
   prime. Writing a/1 = b/t with b in the prime and t outside it, the fraction
   equality gives u(ta-b) = 0 for u outside the prime. Primality implies a is in the
   prime. Hence the annihilator of z is exactly that prime, as required by
   def-weil-pbc-annihilator-associated-primes.
5. In a Noetherian ring every ideal is finitely generated
   (def-weil-pbc-noetherian-ring), so the two directions give the equivalence.
   None of these steps uses finite generation of the section module. -/
theorem affine_associated_points_primes
    {X : Scheme.{u}} (F : X.Modules) (hqc : F.IsQuasicoherent)
    (W : X.Opens) (hW : IsAffineOpen W) (x : W) :
    ((hW.primeIdealOf x).asIdeal ∈
        RingTheory.annihilatorAssociatedPrimes (X.presheaf.obj (op W)) (F.val.obj (op W)) →
      (x : X) ∈ associatedPoints F) ∧
    ((x : X) ∈ associatedPoints F → (hW.primeIdealOf x).asIdeal.FG →
      (hW.primeIdealOf x).asIdeal ∈
        RingTheory.annihilatorAssociatedPrimes (X.presheaf.obj (op W)) (F.val.obj (op W))) ∧
    (IsNoetherianRing (X.presheaf.obj (op W)) →
      ((x : X) ∈ associatedPoints F ↔
        (hW.primeIdealOf x).asIdeal ∈
          RingTheory.annihilatorAssociatedPrimes (X.presheaf.obj (op W))
            (F.val.obj (op W)))) := by
  sorry

end AlgebraicGeometry.Scheme.Modules
