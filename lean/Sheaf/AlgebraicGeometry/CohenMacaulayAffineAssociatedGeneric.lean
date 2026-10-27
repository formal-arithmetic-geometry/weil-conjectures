/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import WeilConjectures.RingTheory.Depth
public import Mathlib.RingTheory.KrullDimension.Basic
public import Mathlib.AlgebraicGeometry.Scheme
public import Sheaf.AlgebraicGeometry.RelativeAssassin
public import WeilConjectures.RingTheory.AnnihilatorAssociatedPrimes
public import WeilConjectures.Topology.PresheafModuleStalkFunctor
public import Mathlib.Topology.Sober
public import Mathlib.Topology.Irreducible
import Mathlib.AlgebraicGeometry.StructureSheaf
import Mathlib.AlgebraicGeometry.FunctionField
import Mathlib.RingTheory.Localization.Submodule
import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
import WeilConjectures.RingTheory.AssociatedPrimeMinimalOfDepth
import Mathlib.RingTheory.Localization.Ideal
import Mathlib.RingTheory.Ideal.AssociatedPrime.Localization
import Mathlib.RingTheory.Spectrum.Prime.Topology

/-! # Associated points of a Cohen–Macaulay affine scheme

Source: Stacks Project, Divisors, Tag 05DC (lemma-base-change-relative-assassin),
final sentence of the proof, expanded by Algebra Tags 0BUS, 05BV and 05BZ
(blueprint: lem-trf-cm-affine-associated-generic).
-/

@[expose] public section

set_option autoImplicit false

universe u

namespace AlgebraicGeometry.Scheme.Modules

/-- On the spectrum of a Noetherian ring with Cohen–Macaulay prime localizations,
association for the structure sheaf, minimality of the prime, and being generic
for an irreducible component are equivalent.

Source: Stacks Project, Divisors, Tag 05DC, final sentence of the proof;
Algebra Tags 0BUS, 05BV, 05BZ, 00E3 and 00ES, and Schemes Tag 01HV
(blueprint: lem-trf-cm-affine-associated-generic).

Proof, following the node's four steps:
1. Identify the affine structure-sheaf stalk at q with A = T_q using
   lem-weil-pbc-spec-domain-stalks-function-field. By
   lem-weil-pbc-localization-noetherian and
   lem-weil-pbc-noetherian-local-finite-krull-dimension, A is Noetherian local of
   finite dimension e. The hypothesis gives depth A = e. The unit module sheaf
   has stalk A as its self-module. The stalk isomorphism preserves maximal ideals
   and element annihilators, so association is association of the maximal ideal of A.
2. If q is associated, lem-weil-pbc-cm-local-associated-prime-minimal makes the
   maximal ideal of A minimal. A prime strictly below q would give a prime strictly
   below that maximal ideal by lem-weil-pbc-primes-of-localization, a contradiction.
3. If q is minimal, lem-weil-pbc-noetherian-minimal-prime-associated supplies
   an element with annihilator q. The localization statement
   lem-weil-pbc-associated-prime-localization-depth-zero gives an element of A
   with annihilator its maximal ideal. This element is nonzero since that ideal
   is proper. Transport across the stalk isomorphism proves association.
4. The closure of a prime p is V(p). By
   lem-weil-pbc-spec-irreducible-components-minimal-primes, minimal q makes V(q)
   a component, with generic point q. Conversely a component with generic point q
   equals both V(q) and V(p) for some minimal prime p. Membership in these two
   equal zero loci gives p ≤ q and q ≤ p, hence p = q and q is minimal. -/
theorem associatedPoints_unit_spec_iff_minimalPrime_and_generic
    {T : Type u} [CommRing T] [IsNoetherianRing T]
    (hcm : ∀ p : PrimeSpectrum T,
      (IsLocalRing.depth (R := Localization.AtPrime p.asIdeal)
        (Localization.AtPrime p.asIdeal) : WithBot ℕ∞) =
          ringKrullDim (Localization.AtPrime p.asIdeal))
    (q : PrimeSpectrum T) :
    (q ∈ associatedPoints (SheafOfModules.unit (Spec (CommRingCat.of T)).ringCatSheaf) ↔
      q.asIdeal ∈ minimalPrimes T) ∧
    (q.asIdeal ∈ minimalPrimes T ↔
      ∃ Z ∈ irreducibleComponents (Spec (CommRingCat.of T)), IsGenericPoint q Z) := by
  sorry

end AlgebraicGeometry.Scheme.Modules
