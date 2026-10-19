## Worker report

The module `lean/Sheaf/RingTheory/QuasiExcellentNagata.lean` states
`isNagataRing_of_isQuasiExcellent`, with `sorry` as its entire proof. The node's
statement is unchanged. No new nodes and no statement correction were needed.

Clause-by-clause correspondence for lem-exc-quasi-excellent-nagata:

- “Let R be a commutative ring” is `(R : Type u) [CommRing R]`, with the universe
  `u` explicitly bound and auto-implicit variables disabled.
- “quasi-excellent” is `(hR : IsQuasiExcellent R)`, from the dependency module
  `Sheaf.RingTheory.ExcellentRing`. This is precisely Noetherianity, the existing
  `IsGRing R`, and openness of the regular locus in every finite type algebra.
- “Then R is a Nagata ring” is `: IsNagataRing R`, from the recorded dependency
  `Sheaf.RingTheory.NagataRing`. Its full definition was read: Noetherianity and
  `IsN2 (R ⧸ p) (FractionRing (R ⧸ p))` for every prime ideal p. It does not assert
  merely the N-1 condition, nor assume that R is a domain.

Source read: [Stacks 07QV](https://stacks.math.columbia.edu/tag/07QV),
`lemma-quasi-excellent-nagata`. It states exactly that every quasi-excellent ring
is Nagata. The theorem docstring carries all eight DAG proof steps, including
construction of a normal principal open, reduced completion at each maximal
localization, the local N-1 criterion, and the universally Japanese criterion.
The local literature checkout is absent; the Stacks tag pages were opened.

Dependency declarations used for the statement are `IsQuasiExcellent` in
`Sheaf.RingTheory.ExcellentRing` and `IsNagataRing` in
`Sheaf.RingTheory.NagataRing`. The latter uses `IsN2` from
`Sheaf.RingTheory.JapaneseDomain`, whose full signature and docstring were read.
The excellent-ring definition uses the recorded `IsGRing` in
`Sheaf.RingTheory.GRing`; its geometric regularity, regular map, and completion
map definitions were read in full. Its Mathlib building blocks are
`IsNoetherianRing` (`Mathlib.RingTheory.Noetherian.Defs`), `Algebra.FiniteType`
(`Mathlib.RingTheory.FiniteType`), `Localization.AtPrime`
(`Mathlib.RingTheory.Localization.AtPrime.Basic`), `IsRegularLocalRing` and
`IsRegularRing` (`Mathlib.RingTheory.RegularLocalRing.Defs`), and the Zariski
`PrimeSpectrum` topology (`Mathlib.RingTheory.Spectrum.Prime.Topology`). Their
recorded signatures and docstrings were opened. `AlgebraicGeometry.Spec` in
`Mathlib.AlgebraicGeometry.Scheme` was also read; the J-2 condition uses its
underlying prime spectrum, not a different topology.

Recorded proof-dependency imports are retained: `Sheaf.RingTheory.FiniteTypeGRing`,
`Mathlib.AlgebraicGeometry.Scheme`, `Mathlib.RingTheory.Localization.Away.Basic`,
`Mathlib.RingTheory.Localization.Submodule`, `Sheaf.RingTheory.RegularRingNormal`,
`Sheaf.RingTheory.AdicCompletionNoetherian`,
`Sheaf.RingTheory.IsN1OfIsAnalyticallyUnramified`, and
`Sheaf.RingTheory.IsN1OfLocalCharacterization`. The existing non-Mathlib
signatures/docstrings were read. The regular-locus topology and regular-local-ring
Mathlib proof dependencies arrive through the public statement imports.
`lem-exc-regular-map-reduced-target` and
`lem-exc-universally-japanese-n1-criterion` have no recorded Lean module at the
read base, so no import can yet be named for them; they remain in the proof plan.
They are not prerequisites for typing this theorem's statement.

Edge cases checked: R is allowed to be the zero ring (no nontriviality binder),
nonlocal, reducible, or positive characteristic. For the zero ring there are no
prime ideals, so the Nagata prime-quotient clause is vacuous as intended. No
`IsDomain R`, `IsLocalRing R`, excellence/universal catenarity, finite-dimensionality,
or characteristic hypothesis was added. Quantifying test finite type algebras in
`Type u` in the reused definition loses no isomorphism classes: every finite type
algebra is a quotient of a finite-variable polynomial algebra over R, which lies
in the same universe. The G-ring definition independently uses `max u v` for its
field-extension tests. There is no independent smaller test universe.

Searches made with the prescribed search wrapper (group NU, this item):

- LeanFinder: `A quasi excellent ring is a Nagata ring`: eight hits, including
  `Algebra.QuasiFiniteAt`, `Algebra.quasiFinite_iff`, and Noetherian-localization
  results; none states the theorem or defines excellence.
- Loogle: `Nagata, Excellent, QuasiExcellent`: zero hits, unknown identifier
  `Nagata`; followed by the valid substring query `"Excellent"`, zero hits.
- Mathlib grep: `IsExcellent|QuasiExcellent|ExcellentRing|IsNagataRing` in
  `RingTheory`: zero hits.
- LeanFinder: `A commutative ring is quasi excellent if Noetherian G ring and
  every finite type algebra has open regular locus, excellent if universally
  catenary`: eight hits, all on Noetherianity, smoothness or quasi-finiteness,
  with no definition match.
- Mathlib grep: `IsCatenary|IsExcellent|IsQuasiExcellent|IsJTwo`: zero hits.
- Direct `rg` for excellence, quasi-excellence, catenarity and the proposed
  theorem name in the upstream project and `lean/Sheaf`: only incidental comments,
  not declarations. Direct search for this node id in the upstream project:
  no result. Search of `dag/lean_names_upstream.json`: no match.
- Exact declaration-name grep for `IsPrimeChain`, `IsSaturatedPrimeChain`,
  `IsCatenaryRing`, `IsUniversallyCatenary`, `IsQuasiExcellent`, and
  `isNagataRing_of_isQuasiExcellent` across Mathlib, upstream project and
  published side source: no result at the time of reading.
- `scompile.py --source Sheaf.RingTheory.ExcellentRing`: module source unavailable.
  The read-only server delivery-branch listing found
  `deliver/Q21/def-exc-excellent-ring`; its node record and entire module were read.
  This existing delivered definition is reused verbatim in this sandbox rather
  than replaced by another notion.

No STATEMENT-DISPUTED issue was found. The definition and theorem use real ring
notions; the only postponed proof is the main theorem.

## Dependency modules

`def-exc-excellent-ring`: the read base has no Lean record or Mathlib match.
The human's 2026-10-16 unstated-dependency instruction authorizes supplying this
existing node in the same delivery. `lean/Sheaf/RingTheory/ExcellentRing.lean`
reuses Q21's already delivered module verbatim, including its authorship. The
node copy changes only `lean`, with a note explaining its absence and provenance.
This is the complete dependency definition, not just the quasi-excellent part.
Its definitions were checked against [07QT](https://stacks.math.columbia.edu/tag/07QT),
[07P7](https://stacks.math.columbia.edu/tag/07P7),
[00NI](https://stacks.math.columbia.edu/tag/00NI), and
[00NL](https://stacks.math.columbia.edu/tag/00NL).

For each clause of that dependency: `IsPrimeChain` uses a family on `Fin (n+1)`,
primality of every member, the named endpoints, and strict consecutive
inclusions; n is exactly the number of inclusions. `IsSaturatedPrimeChain` adds
nonexistence of a prime strictly between each consecutive pair.
`IsCatenaryRing` quantifies every prime pair p ≤ q, requires a natural bound N on
all such finite chain lengths, and equality n = m for all saturated chains with
these endpoints. When p = q the length-zero chain is allowed and saturated;
strictness prevents positive-length return chains. For the zero ring all prime
pair tests are vacuous. `IsUniversallyCatenary` includes Noetherianity and the
catenary predicate for every finite type algebra. `IsQuasiExcellent` includes
Noetherianity, `IsGRing`, and openness of exactly the prime set with regular local
localization in every finite type algebra. Empty regular loci are allowed to be
open, as required. `IsExcellent` is the conjunction of that quasi-excellent
predicate and universal catenarity. The finite-type quantifiers do not demand a
nonempty spectrum, positive number of generators, or any separability condition.
Every definition has real data and no proof is postponed in this module.

## Second reading by NU

I reread Stacks Project Tag 07QV (Lemma 15.53.5, `lemma-quasi-excellent-nagata`).
Its statement is the single implication “a quasi-excellent ring is Nagata”; the
source proof has no extra locality, domain, characteristic, or finiteness hypothesis
on the ring itself.

The statement inventory and Lean correspondence are:

1. The object is a commutative ring `R`, rendered by
   `(R : Type u) [CommRing R]`; the explicit universe is unrestricted.
2. The hypothesis is that `R` is quasi-excellent, rendered by
   `(hR : IsQuasiExcellent R)`, using the recorded dependency
   `IsQuasiExcellent` from `Sheaf.RingTheory.ExcellentRing`. That definition is the
   conjunction of Noetherianity, the G-ring condition, and J-2 (open regular locus
   for every finite type `R`-algebra), exactly as in Tags 07QT and 07P7.
3. The conclusion is that `R` is Nagata, rendered by
   `: IsNagataRing R`, using `IsNagataRing` from `Sheaf.RingTheory.NagataRing`.
   Its clauses are Noetherianity and `IsN2 (R ⧸ p) (FractionRing (R ⧸ p))` for
   every prime ideal `p`, exactly Definition 032R.

Thus the file signature is verbatim the node statement, with no added or dropped
hypotheses and no altered quantifier order. The dependency module supplied in this
delivery was also read declaration by declaration; it contains the complete
quasi-excellent predicate rather than a special-case or stronger predicate. The
Nagata dependency was read in the shared library and has the stated N-2
prime-quotient form.

Edge cases checked: the zero ring is admitted (its prime-ideal quantification is
vacuous), as are nonlocal, reducible, and positive-characteristic rings. No domain,
local, nontriviality, finite-dimensionality, universal-catenary, or characteristic
hypothesis is present. The finite-type algebra universe in `IsQuasiExcellent` is
the ring universe, so it does not introduce an independent smaller universe. Empty
regular loci remain open, and no index set or natural-number parameter occurs.

Independent searches were repeated with `msearch.py`: LeanFinder `IsQuasiExcellent`,
Loogle `"catenary"`, and grep `\b(Excellent|Nagata|Japanese|Catenary|IsQuasiExcellent)\b`.
LeanSearch for geometrically regular formal fibers and J2 implying integral-closure
finiteness was unavailable (Internal Server Error), so it supplies no verdict.
Direct `rg` searched the upstream source, project `lean/Sheaf`, and upstream names
for `quasi.?excellent`, `universally.?catenary`, `IsPrimeChain`, `IsCatenaryRing`, and
the theorem name. They found no existing declaration of either the theorem or the
excellent/quasi-excellent predicates; the hits were unrelated Noetherian,
quasi-finite, smoothness, or integral-closure results. The source project and
`dag/lean_names_upstream.json` likewise contain no duplicate declaration. The
online source page and upstream `more-algebra.tex` and `algebra.tex` were read
directly because the local literature checkout is absent. In TeX I read
`lemma-quasi-excellent-nagata`, `definition-excellent`, `definition-J`,
`definition-catenary`, `definition-universally-catenary`, and `definition-nagata`.

The dependency's chain encoding also matches its node: `Fin (n+1)` has `n` strict
inclusions, each endpoint is fixed, and saturation excludes an intermediate prime.
The catenary predicate bounds all finite lengths and equates saturated lengths.
For `p = q`, the length-zero chain is admitted and saturated; no positive-length
chain returns to its initial ideal. `IsUniversallyCatenary` includes Noetherianity
as the source assumes. Its finite-type quantification, like J-2, covers every
isomorphism class because a finite type algebra is a quotient of a polynomial
algebra on finitely many variables over `R`.

I opened the G-ring and Japanese-domain dependencies themselves: `IsGRing` uses
the actual localization-to-maximal-adic-completion map, `RingHom.IsRegular` is
flatness with geometrically regular fibres, and `IsN2` quantifies all finite field
extensions with the composite `R` action specified by `IsScalarTower`. These are
the source objects, with no separability restriction. I checked all eight proof
steps against the theorem docstring: the regular principal open, normal
localization, reduced completions, local and global N-1 criteria, and universal
Japanese reduction are all retained.

No mismatch was found and no statement correction was needed. I made no edits to
the theorem or its dependencies. The dependency module is a real-data definition,
and the theorem is statement-only with `sorry`; all declarations carry the source
place and `(blueprint: ...)` documentation. `scompile.py` compiled both delivered
modules cleanly with no errors or warnings.
