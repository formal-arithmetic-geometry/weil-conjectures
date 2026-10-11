/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group M1
-/
import Sheaf.RingTheory.QuasiFiniteAtPrime
import Mathlib.RingTheory.Localization.Away.Basic

/-!
# Quasi-finiteness at a prime and principal localization

Source: Stacks Project, Algebra, Lemma 10.122.6 (Tag 077H)
(blueprint: lem-weil-pbc-quasi-finite-at-prime-principal-localization).
-/

universe u v

namespace Algebra

/-- (blueprint: lem-weil-pbc-quasi-finite-at-prime-principal-localization)
Stacks Project, Algebra, Lemma 10.122.6 (Tag 077H): quasi-finiteness at a prime is
unchanged by principal localization of the base and target away from that prime.
The commuting square characterizes the unique induced map `φ'`. Its finite type
and the primality of the extended ideal are included in the conclusion.

Proof, following the nine steps of the node:
1. The localization universal property constructs the induced map. If `s₁, …, sₙ`
generate `S` over `R`, their images together with `1 / (φ(f)g)` generate the target
localization over `R_f` (localization-away-universal-property and finite-type-algebra).
2. Since `φ(f)g` avoids `q`, localization-prime-residue-field-iso gives the extended
prime, its contraction `q`, the contracted base prime `pR_f`, and the compatible
residue-field isomorphism `κ(p) ≅ κ(pR_f)`.
3. Fibre-ring-primes-bijection gives the two corresponding fibre primes. In the
original fibre, the image of `φ(f)` is a unit and the image of `φ(f)g` avoids its prime.
4. Algebra-tensor-pushout-universal-property and localization-away-universal-property
construct a map from the original fibre localized at that image to the new fibre.
5. The same universal properties construct the inverse map: localize the target
map and use the inverse residue-field isomorphism on the other tensor factor.
6. Check both composites on the tensor factors and localization generators;
uniqueness in these universal properties makes both composites the identity.
7. Contracting the transported fibre prime to `S` gives `q`, so uniqueness in
localization-prime-residue-field-iso and fibre-ring-primes-bijection identifies it
with the new fibre prime.
8. Principal-localization-open-immersion identifies the new fibre spectrum with
the principal open of the original fibre, carrying its distinguished prime to the
original distinguished prime (affine-spectrum and open-immersion).
9. A singleton in an open subspace is open there iff it is open in the whole space.
Apply ring-map-quasi-finite-at-prime to obtain the asserted equivalence. -/
theorem isQuasiFiniteAtPrime_iff_principalLocalization
    (R : Type u) (S : Type v) [CommRing R] [CommRing S]
    [Algebra R S] [Algebra.FiniteType R S] (q : PrimeSpectrum S)
    (f : R) (hf : f ∉ q.asIdeal.comap (algebraMap R S))
    (g : S) (hg : g ∉ q.asIdeal)
    (φ' : Localization.Away f →+* Localization.Away (algebraMap R S f * g))
    (hφ' : φ'.comp (algebraMap R (Localization.Away f)) =
      (algebraMap S (Localization.Away (algebraMap R S f * g))).comp (algebraMap R S)) :
    ∃ hft : @Algebra.FiniteType (Localization.Away f)
      (Localization.Away (algebraMap R S f * g)) _ _ φ'.toAlgebra,
    ∃ hq' : (q.asIdeal.map
      (algebraMap S (Localization.Away (algebraMap R S f * g)))).IsPrime,
      (IsQuasiFiniteAtPrime R S q ↔
        @IsQuasiFiniteAtPrime (Localization.Away f)
          (Localization.Away (algebraMap R S f * g)) _ _ φ'.toAlgebra hft
          ⟨q.asIdeal.map (algebraMap S (Localization.Away (algebraMap R S f * g))), hq'⟩) := by
  sorry

end Algebra
