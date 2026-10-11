## Worker report

The node is exactly Mathlib's existing `isRegularRing_iff` in
`Mathlib.RingTheory.RegularLocalRing.Defs`; no module is added. Mathlib's outer
context supplies `{R : Type u}` and `[CommRing R]`, while the declaration adds
`[IsNoetherianRing R]`. Its conclusion is
`IsRegularRing R ↔ ∀ (p : Ideal R) [p.IsPrime],
IsRegularLocalRing (Localization.AtPrime p)`. The left side is the regular-ring
notion in [def-weil-regular-scheme], and the right side is the prime
localization notion in [def-weil-pbc-localization-at-prime]. Thus the Noetherian
hypothesis, universal prime-ideal quantifier, localization, and regular-local
conclusion each match the node clause by clause.

Dependency declarations used: `Mathlib.RingTheory.RegularLocalRing.Defs.isRegularRing_iff`
(and its `IsRegularRing` and `IsRegularLocalRing` declarations), matching the
recorded Mathlib declaration for [def-weil-regular-scheme];
`Mathlib.RingTheory.Localization.AtPrime.Basic.Localization.AtPrime`, matching
the recorded declaration for [def-weil-pbc-localization-at-prime]; and
`Mathlib.RingTheory.Noetherian.Defs.IsNoetherianRing`, matching the recorded
Mathlib declaration for [def-weil-pbc-noetherian-ring].

Edge cases checked: the quantifier ranges over all prime ideals, including the
empty-prime case when there are no primes; `Localization.AtPrime` is the
canonical localization at the complement of each prime; and the existing
criterion retains the Noetherian assumption exactly. No universe restriction is
introduced beyond Mathlib's implicit universe for `R`.

Searches made: `msearch.py ... leanfinder "Noetherian ring regular iff localization at every prime regular local"`
returned no exact criterion (only unrelated regular-sequence declarations);
`msearch.py ... loogle "isRegularRing_iff IsRegularRing localization"` returned no search hits because the query was not a valid Loogle pattern, but
its diagnostic displayed Mathlib's `isRegularRing_iff` type; and
`msearch.py ... grep "isRegularRing_iff" RingTheory/RegularLocalRing` found
`Mathlib/RingTheory/RegularLocalRing/Defs.lean:101` and its uses. Direct `rg`
searches of Mathlib and WeilConjectures found the same declaration and no
project duplicate. Therefore the node records `existing: true` rather than
introducing a second definition or theorem.

No `STATEMENT-DISPUTED` or node faults.

LeanSearch query "A Noetherian ring is regular iff every localization at a prime
is a regular local ring" was unavailable (Internal Server Error); no verdict
is inferred from that failure. A valid Loogle name query `"isRegularRing_iff"`
returned one exact hit with `{R : Type u_1} [CommRing R] [IsNoetherianRing R]`.
The declaration has no separate docstring; its enclosing regular-ring section
and `IsRegularRing` docstring explain precisely this definition.

## Second reading by C1

The node introduces a commutative ring (A), assumes that it is Noetherian,
and concludes an iff.  The left clause is that (A) is regular in the sense
of `def-weil-regular-scheme`; for a ring this is Mathlib's `IsRegularRing A`.
The right clause quantifies over every prime ideal \\(\\mathfrak q : Ideal A\\),
uses the localization (A_{\\mathfrak q}), and requires that localization to
be a regular local ring.  The Lean rendering is exactly
`lemma isRegularRing_iff [IsNoetherianRing R] : IsRegularRing R ↔
    ∀ (p : Ideal R) [p.IsPrime], IsRegularLocalRing (Localization.AtPrime p)`.
The surrounding Mathlib declaration supplies `{R : Type u} [CommRing R]`.
Thus the Noetherian hypothesis, prime-ideal binder (including its typeclass
prime hypothesis), localization, and regular-local conclusion all match the
node, in the same quantifier order.  No extra hypothesis or stronger clause
is present.

The edge cases are covered: the prime quantifier is over all prime ideals,
including the vacuous case when there are none; `Localization.AtPrime` is the
canonical localization at each prime; no nonzero, domain, finite type, or
characteristic assumption is introduced; and the universe is Mathlib's
implicit universe for the ring.  The criterion also retains the explicit
Noetherian assumption even though `IsRegularRing` itself extends it.

I rechecked the three searches in the worker report: LeanSearch found no
separate project statement, Loogle's valid name query found the exact
Mathlib theorem, and grep found only
`Mathlib.RingTheory.RegularLocalRing.Defs.isRegularRing_iff` (plus its uses).
Searches of `WeilConjectures/` and `lean/Sheaf` found no duplicate.

No mismatch was found and no source or Lean text was changed.  The existing
declaration record is retained because the Mathlib theorem is exactly the
ring specialization of the node after unfolding `def-weil-regular-scheme`;
there is no module to compile or dependency module to add.
