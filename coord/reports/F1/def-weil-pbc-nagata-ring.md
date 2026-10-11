## Worker report

`Sheaf.RingTheory.NagataRing` defines `IsUniversallyJapanese` and `IsNagataRing`.
Both follow Stacks Project, Algebra, Definition 10.162.1 (Tag 032R).

- The common hypothesis that `R` is a commutative ring is `(R : Type u) [CommRing R]`.
- Clause (1) quantifies over every finite type ring map `R -> S` using
  `forall (S : Type u) [CommRing S] [Algebra R S] [Algebra.FiniteType R S]`.
  Its requirement that `S` is a domain is `[IsDomain S]`. Its conclusion that
  `S` is N-2 is `IsN2 S (FractionRing S)`.
- Clause (2) requires `IsNoetherianRing R` and, for every prime ideal, uses
  `forall (p : Ideal R) [p.IsPrime], IsN2 (R ⧸ p) (FractionRing (R ⧸ p))`.
  The `IsPrime` instance gives the quotient its domain structure. The `And`
  preserves the conjunction of Noetherianity and the prime quotient condition.

Dependencies: `Algebra.FiniteType` in `Mathlib.RingTheory.FiniteType`, `IsN2`
in `Sheaf.RingTheory.JapaneseDomain`, and `IsNoetherianRing` in
`Mathlib.RingTheory.Noetherian.Defs`. `Ideal.Quotient.isDomain` is supplied by
`Mathlib.RingTheory.Ideal.Quotient.Basic`.

Edge cases: the zero ring has no prime ideal, so clause (2)'s universal
quantification is vacuous after Noetherianity; the zero finite type algebra is
excluded from clause (1) by `IsDomain`. The identity algebra `S = R` is included
when `R` is a domain. The zero prime is included whenever it is prime. The
`S : Type u` binder is sufficient up to equivalence for finite type algebras of
`R : Type u`, whose generators and polynomial presentations have the same
universe size. No separability is imposed in `IsN2`.

Searches: `msearch.py leanfinder` queried "universally Japanese ring Nagata ring
every finite type domain algebra Japanese every prime quotient N-2" and returned
only related quasi-finite/Jacobson results. `msearch.py loogle` queried
`IsNagata, IsUniversallyJapanese, IsN2` and found no Nagata predicate.
`msearch.py grep` queried `IsNagata|UniversallyJapanese|Japanese|NagataRing`
under Mathlib `RingTheory` and found no match. `rg` in the source
`WeilConjectures` found no relevant declaration; `grep -rn` for the node ID
found none. `rg` in the project `lean/Sheaf` found `IsN2` only, in the recorded
dependency module.

The repository's fetched `literature/stacks-project/algebra.tex` is absent on
this machine. The same source place was read at the Stacks Project Tag 032R
web page, which states the two clauses exactly as the node does.

## Second reading by F1

Independently checked the node against Stacks, Algebra, Definition 10.162.1
(Tag 032R), and read the recorded dependency declarations and their source.
The source has no further standing hypotheses beyond a commutative ring.

- Object: an arbitrary commutative ring `R` is `(R : Type u) [CommRing R]` in
  both definitions. Verdict: exact.
- Clause (1), every finite type ring map `R -> S`: the quantifiers
  `∀ (S : Type u) [CommRing S] [Algebra R S] [Algebra.FiniteType R S]`
  range over the map through its algebra structure. `Algebra.FiniteType` is
  the recorded Mathlib match for `def-weil-pbc-finite-type-algebra` and has
  no injectivity condition. Verdict: exact up to transport of a finitely
  generated algebra to a same-universe representative.
- Clause (1), `S` an integral domain: `[IsDomain S]`; together with
  `[CommRing S]` this is the domain in the node. Verdict: exact.
- Clause (1), `S` is N-2: `IsN2 S (FractionRing S)` uses the recorded
  `def-weil-pbc-japanese-domain` declaration with the canonical fraction
  field. Verdict: exact; no Noetherian or separability premise is added.
- Clause (2), `R` Noetherian: `IsNoetherianRing R`, the recorded Mathlib match
  for `def-weil-pbc-noetherian-ring`. Verdict: exact.
- Clause (2), each prime ideal `p` of `R`: `∀ (p : Ideal R) [p.IsPrime]`.
  The instance selects precisely the prime ideals, without a maximality
  condition. Verdict: exact.
- Clause (2), `R/p` is N-2: `IsN2 (R ⧸ p) (FractionRing (R ⧸ p))`.
  Primality makes the quotient a domain and `FractionRing` supplies its
  fraction field. The `∧` joins this to Noetherianity. Verdict: exact.

Edge cases: the zero ring is covered by `CommRing R`; its prime-ideal
quantifier is empty. Zero finite type algebras are excluded by `IsDomain S`,
as the source requires. The identity algebra is included for a domain `R`;
the zero ideal is included when prime. There is no `n > 0`, characteristic,
nonempty-index, or scheme restriction. The `Type u` quantifier covers every
finite type `R`-algebra up to isomorphism: finite generation bounds its
cardinality by `max(|R|, aleph0)`, so it has a representative in `Type u`.
This is the same universe convention as the recorded `IsN2` dependency.

Independent searches: `msearch.py leanfinder` for "universally Japanese
commutative ring finite type integral domain N-2 Japanese" returned only
Jacobson/quasi-finite results; `msearch.py loogle` for "Nagata ring Japanese
domain" returned no declaration; `msearch.py grep` for "universally
Japanese|Nagata ring|Japanese domain|IsN2" found no existing predicate.
An independent case-insensitive `rg` of Mathlib, the source repository's
`WeilConjectures`, and `lean/Sheaf` found only the recorded `IsN2`
dependency. No duplicate notion exists there.

Mismatches found: none. Changes: replaced this pending handoff note with the
completed second reading; the Lean definitions and node record were retained.
`scompile.py F1 def-weil-pbc-nagata-ring` compiled the module with exit 0
and no warnings. Both definitions are non-hollow; no theorem is proved here.
