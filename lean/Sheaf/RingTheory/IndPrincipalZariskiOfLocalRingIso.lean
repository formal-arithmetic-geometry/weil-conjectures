/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NO
-/
module

public import WeilConjectures.RingTheory.ProEtale.WLocal
public import Sheaf.RingTheory.IndPrincipalZariski
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.GroupTheory.MonoidLocalization.Away
import Mathlib.RingTheory.FinitePresentation
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.RingTheory.Spectrum.Prime.Topology
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.RingTheory.Etale.Basic
import Mathlib.RingTheory.Etale.Pi
import Sheaf.RingTheory.FilteredColimitOfFactorization

/-! # Local-ring identifications with w-local target

Source: blueprint, proper base change, `sk-thm-properbasechange`, lemma
`lem-weil-pbc-local-rings-ind-zariski`
(blueprint: lem-weil-pbc-local-rings-ind-zariski).
-/

@[expose] public section

universe u

namespace Algebra

/-- A ring map identifying all prime localizations and having w-local target presents that
 target as a filtered colimit of finite products of principal localizations of the source.
 No w-locality of the source or of the map is assumed.

Source: blueprint, proper base change, `sk-thm-properbasechange`, lemma
`lem-weil-pbc-local-rings-ind-zariski`
(blueprint: lem-weil-pbc-local-rings-ind-zariski).

Proof:
1. For a finitely presented `A`-algebra `P` mapping to `B`, choose finitely many generators
   and relations. At each maximal ideal `q` of `B`, invert the local-ring isomorphism and
   express the images of the generators as fractions in `A` at the contracted prime.
   Their denominators have product `d` outside that prime, including `d = 1` if empty.
2. Clear the finitely many relations using the fraction equality criterion. Multiplying
   `d` by the resulting annihilators gives `f` outside the contracted prime and a map
   `P → A_f` inducing the selected map to the local ring.
3. Clear the finitely many equalities between this map and `P → B` at `q`. Their
   annihilators and the image of `f` give `g` outside `q`. The localization universal
   property gives `A_f → B_g`, through which the localized original map factors.
4. By lem-weil-pbc-w-local-partition, the closed points are profinite. Choose a finite
   clopen partition subordinate to these neighbourhoods, and extend it to a clopen
   partition of `Spec B`, still subordinate to them. For the empty spectrum use the
   empty partition.
5. By lem-weil-pbc-spec-clopen-idempotent the partition gives orthogonal idempotents
   `e_j` with sum one. The maps `b ↦ (e_j b)` and `(b_j) ↦ ∑ b_j` give the decomposition
   `B ≅ ∏ B_j`. In the empty case the same idempotent uniqueness gives `0 = 1` in `B`.
6. Each selected `g_j` is a unit in `B_j`, since it lies in no prime ideal there, by
   lem-weil-pbc-spec-basic-opens-unit-ideal-quasi-compact. The localization universal
   property then gives a factorization `P → ∏ A_{f_j} → B`.
7. Each principal localization is etale, by lem-weil-pbc-open-immersion-etale and
   lem-weil-pbc-etale-algebra-finite-presentation-localization. The finite product is
   etale by lem-weil-pbc-etale-algebra-finite-product, including the empty product,
   and hence finitely presented.
8. Apply lem-weil-pbc-factorization-criterion-filtered-colimit to the set of these finite
   products, using steps 6 and 7. This gives a small filtered diagram with colimit `B`.
9. Its terms are precisely the finite products of principal localizations required by
   def-weil-pbc-ind-etale-algebra, so it witnesses `IsIndPrincipalZariski A B`. -/
theorem isIndPrincipalZariski_of_bijective_localRingHom
    (A B : Type u) [CommRing A] [CommRing B] [Algebra A B] [IsWLocalRing B]
    (hlocal : ∀ (q : Ideal B) [q.IsPrime],
      Function.Bijective
        (Localization.localRingHom (q.comap (algebraMap A B)) q (algebraMap A B) rfl)) :
    IsIndPrincipalZariski A B := by
  sorry

end Algebra
