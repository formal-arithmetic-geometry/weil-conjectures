## Worker report

The module `Sheaf.RingTheory.UniversallyCatenaryQuotient` states
`IsUniversallyCatenary.quotient`, with its sole proof `sorry`. It introduces no definitions,
changes no mathematical statement, and needs no new nodes or dependency repairs.
The source is Stacks Project, Algebra, Tag 00NK, lemma-quotient-catenary, second assertion,
read in `literature/stacks-project/algebra.tex`, together with Tag 00NL.

Clause-by-clause correspondence:

- The arbitrary commutative ring A is `(A : Type u) [CommRing A]`, with explicit universe `u`.
- “Noetherian universally catenary” is `(hA : IsUniversallyCatenary A)`. The recorded
  predicate already includes `IsNoetherianRing A` as its first conjunct, so a separate
  Noetherian binder would only repeat that hypothesis. Its second conjunct says every
  finite type A-algebra is catenary, including both the finite bound on finite prime-chain
  lengths and equality of saturated-chain lengths in each prime interval.
- “Any ideal I” is `(I : Ideal A)`, with no primality or properness restriction.
- “A/I is universally catenary” is `IsUniversallyCatenary (A ⧸ I)`. This retains
  Noetherianity of the quotient as part of the conclusion, using the identical predicate.

Dependencies read and used:

- `def-weil-pbc-noetherian-ring`: `IsNoetherianRing` in
  `Mathlib.RingTheory.Noetherian.Defs`, whose docstring and definition identify it with
  Noetherianity as a module over itself, equivalently finite generation of all ideals.
- `def-exc-excellent-ring`: `Sheaf.RingTheory.ExcellentRing`, specifically
  `IsUniversallyCatenary`, `IsCatenaryRing`, `IsPrimeChain`, and `IsSaturatedPrimeChain`.
  I read their entire signatures and docstrings. Only universal catenarity is assumed;
  excellence, the G-ring condition, and J-2 are not assumed.
- Proof dependency `def-weil-pbc-finite-type-algebra`: `RingHom.FiniteType` and
  `Algebra.FiniteType` in `Mathlib.RingTheory.FiniteType`. The recorded ring-map predicate
  is the algebra predicate for `f.toAlgebra`. The proof-only module is imported without
  `public`, as required. Both definitions and docstrings were read.
- The quotient uses Mathlib's actual `Ideal` quotient and its commutative ring instance
  from `Mathlib.RingTheory.Ideal.Quotient.Defs`, not a newly defined carrier or map.

The declaration docstring carries all three node proof steps: finite generation of
quotient ideals by lifting; finite type over the quotient implying finite type over A
by coefficient lifting; and applying universal catenarity to the unchanged algebra B.

Edge cases checked before writing: I = bottom gives the original ring; I = top gives
its zero quotient, whose finite type unital algebras are zero and whose prime conditions
are vacuous. The zero ring A is allowed. Nonprime ideals such as (x²) or (xy) are allowed;
neither reducedness nor domain, locality, or finite dimension is assumed. Length-zero
prime intervals remain included by the dependency predicate. The universe of A and A/I
is the same `u`, and the recorded predicate quantifies finite type test algebras in that
same universe; no independent smaller testing universe was introduced.

Searches made through `msearch.py Q82 lem-per-universal-catenarity-quotient`:

- LeanFinder: “A quotient of a Noetherian universally catenary ring is universally catenary”.
  Eight hits concern quotient Noetherianity and finite type, including
  `Ideal.Quotient.isNoetherianRing`; none asserts catenarity.
- Loogle: `"Catenary"`. Zero hits.
- Mathlib grep: `catenary|catenarity|IsUniversallyCatenary`, subdirectory `RingTheory`.
  Zero hits.
- LeanSearch: “Universal catenarity is preserved by quotient rings”. Eight hits concern
  integrality, Noetherianity, Artinian quotients, or quotient domains; none is this theorem.
- Direct `rg` of Mathlib and upstream `WeilConjectures` for `IsUniversallyCatenary|Catenary`
  found no declaration. Direct upstream item-id search also found none.
- Direct `rg` of `lean/Sheaf` for catenary/catenarity found the recorded excellent-ring
  definitions and other catenarity results. I inspected the quotient mentions: they are
  arguments in docstrings for other statements, not an existing quotient theorem.
- `dag/lean_names_upstream.json` has no item-id binding. The existing minimal-quotient
  criterion is a different statement and is not restated here.

No STATEMENT-DISPUTED flag, statement correction, or dependency fault was found.

## Second reading by Q82

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
