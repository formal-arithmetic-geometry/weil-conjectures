/-
Copyright (c) 2026 The SHEAF contributors.
-/
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic

/-!
# Regularity descends along faithfully flat ring maps

Source: literature/stacks-project/algebra.tex, Algebra, Lemma Tag 07NG
(blueprint: lem-weil-pbc-regular-ring-faithfully-flat-descent).
-/

universe u v

namespace IsRegularRing

/--
If a homomorphism of commutative rings `R → S` (the structure map of `[Algebra R S]`) is
faithfully flat and its target is regular, then its source is regular, hence Noetherian.
Source: Stacks Project, Algebra, Lemma Tag 07NG
(blueprint: lem-weil-pbc-regular-ring-faithfully-flat-descent).

Proof, following the five steps of the blueprint node: (1) `S` is Noetherian by
`def-weil-regular-scheme`, and faithful-flat Noetherian descent is
`lem-weil-pbc-faithfully-flat-descent-noetherian`, so `R` is Noetherian. (2) For a
prime `p` of `R`, surjectivity of the spectrum map from faithful flatness gives a
prime `q` of `S` over `p`, by `lem-weil-pbc-faithfully-flat-surjective-spectrum`.
(3) The induced map `R_p → S_q` is a flat local map of Noetherian local rings by
`lem-weil-pbc-flat-local-ring-maps`, using `def-weil-pbc-localization-at-prime`.
(4) Since `S_q` is regular by `def-weil-regular-scheme`,
`lem-weil-pbc-flat-under-regular` gives that `R_p` is regular. (5) Since `p` was
arbitrary, `R` is regular by `def-weil-regular-scheme`; its Noetherianity is the
parent field of `IsRegularRing`.
-/
theorem of_faithfullyFlat
    (R : Type u) (S : Type v) [CommRing R] [CommRing S] [Algebra R S]
    [Module.FaithfullyFlat R S] [IsRegularRing S] :
    IsRegularRing R := by
  sorry

end IsRegularRing
