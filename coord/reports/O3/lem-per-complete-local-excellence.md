## Worker report

The new module `Sheaf.RingTheory.CompleteLocalExcellent` states
`isExcellent_of_isNoetherianRing_of_isAdicComplete`, with proof `sorry`.
It is exactly Stacks Project More on Algebra, Tag 07QW,
`proposition-ubiquity-excellent`, clause (2), read in
`literature/stacks-project/more-algebra.tex:13385` and its proof.
No definitions, new nodes, dependency repairs, or statement corrections are needed.
The item node changes only in `lean`.

Hypothesis and conclusion correspondence:

- “Every commutative ring A”: `(A : Type u) [CommRing A]`, with explicit arbitrary
  universe `u`; no characteristic, dimension, or cardinality restriction.
- “Noetherian”: `[IsNoetherianRing A]`, the recorded Mathlib predicate that every
  ideal is finitely generated, not merely a Noetherianity assumption on a localization.
- “local”: `[IsLocalRing A]`, Mathlib's nontrivial ring with a unique maximal ideal.
  The ideal used for completeness is exactly `IsLocalRing.maximalIdeal A`.
- “complete for its maximal-ideal-adic topology”:
  `[IsAdicComplete (IsLocalRing.maximalIdeal A) A]`. This includes separatedness,
  as the class extends `IsHausdorff` and `IsPrecomplete`. The recorded
  `AdicCompletion.of_bijective_iff` identifies it with bijectivity of the canonical
  map to the inverse limit, including the intersection-of-powers condition.
- “is excellent”: `IsExcellent A`, the recorded definition, not a replacement.
  Reading its full body gives `IsQuasiExcellent A ∧ IsUniversallyCatenary A`;
  quasi-excellence includes Noetherianity, the G-ring condition, and the open
  regular locus for every finite type algebra. Universal catenarity includes
  the finite bound on chain lengths in every prime interval and equality of
  saturated-chain lengths. No conclusion clause is dropped or separately assumed.

Statement dependencies read and used:

- `def-weil-pbc-noetherian-ring`: `Mathlib.RingTheory.Noetherian.Defs`,
  `IsNoetherianRing` and `isNoetherianRing_iff_ideal_fg`.
- `def-weil-pbc-adically-complete-ring`: `Mathlib.RingTheory.AdicCompletion.Basic`,
  `IsAdicComplete`, with `AdicCompletion.of_bijective_iff` validating the convention.
- `def-exc-excellent-ring`: `Sheaf.RingTheory.ExcellentRing`, `IsExcellent`.
  Its six declarations and `Sheaf.RingTheory.GRing` were read to check the conclusion.

The proof docstring carries all eight node steps, with their named inputs:
G-ringness; finite-algebra prime quotients and their nonempty regular opens;
regular-locus openness; the finite-algebra J-2 criterion; the Cohen power-series
presentation; regular localizations and universal catenarity of its source;
quotient descent of universal catenarity by lifting polynomial coefficients;
and combining the definition of excellence.
All currently recorded proof-dependency modules are imported without `public`:
`RegularLocusOpenFromPrimeQuotients`, `RegularRingUniversallyCatenary`,
`CohenStructurePowerSeriesSurjection`, `CompleteLocalGRing`,
`FiniteOverCompleteLocalProduct`, `PowerSeriesFieldCohenRegularComplete`,
and `RegularLocalLocalization` in `Sheaf.RingTheory`, plus the Mathlib
finiteness and finite-type modules. The statement-dependency modules are public.
`lem-per-complete-local-domain-regular-open` and
`lem-per-j2-finite-algebra-criterion` have no recorded Lean declaration yet;
these proof-only dependencies do not obstruct this statement, and their full
node IDs are retained in the proof docstring for stage 3. There is no import cycle.

Edge cases checked before writing:

- A field has maximal ideal zero, and the hypothesis allows its zero-adic
  completeness; the conclusion agrees with the field case of Tag 07QW.
- Nonreduced complete Artinian local rings are allowed: there is no domain,
  reducedness, normality, regularity, or integrally closed hypothesis.
- Both equal and mixed characteristic are allowed; no coefficient ring or
  residue characteristic is fixed in the signature.
- Locality in Mathlib includes nontriviality. This agrees with the source's
  local ring having a maximal ideal, so the zero ring is not inadvertently an
  omitted local ring. The zero finite algebra is nevertheless allowed by the
  J-2 predicate, and has empty regular locus.
- Completeness is separated completeness at the maximal ideal; it is neither
  precompleteness alone nor completeness at an unspecified ideal.
- Dimension zero and a zero-variable Cohen presentation require no extra cases
  in the signature. An arbitrary universe binds the ring and the dependency's
  same-universe finite type algebras, consistent with its recorded interface.

Searches for an existing statement (all via the authorized `msearch.py` wrapper):

- LeanFinder: “Every complete Noetherian local commutative ring is excellent”:
  eight hits, concerning local dimension, DVR criteria, Hausdorffness, Henselian
  rings, and adic completeness; no excellence theorem.
- LeanSearch: “Complete Noetherian local rings are excellent”: eight hits,
  including `Ideal.isLasker`, Noetherian local finite dimension,
  `AdicCompletion.flat_of_isNoetherian`, and Henselian locality; no match.
- Loogle: `"IsExcellent"`: zero hits.
- Mathlib grep: `IsExcellent|[Ee]xcellent|isExcellent_of_isAdicComplete`
  in `RingTheory`: zero hits.
- Wrapper grep: `complete.*[Ee]xcell|[Ee]xcell.*complete` in both
  `WeilConjectures` and `Sheaf`: zero hits.
- Direct `rg` in the source `WeilConjectures` and project `lean/Sheaf`:
  `IsExcellent|complete.local.excellent|lem-per-complete-local-excellence`.
  The source has no match; the project has the excellent-ring definition,
  field/integer excellence and preservation theorems, but no complete-local
  excellence statement. The exact new name has no existing declaration.
- `rg` in `dag/lean_names_upstream.json`: `IsExcellent|excellent_of_isAdicComplete`:
  no match. All three statement dependency declarations and docstrings were read
  directly in their recorded source files.

No statement dispute or node fault was found.

## Second reading by N3

Author self-check, with the node and completed module open; independent review
is performed by the maintainer under this dispatcher's direct-delivery workflow.
The node's single universal implication is rendered by precisely the four
instances `CommRing`, `IsNoetherianRing`, `IsLocalRing`, and maximal-ideal
`IsAdicComplete`, followed by `IsExcellent A`. The completion argument is the
ring itself as its own module, and the ideal is the unique maximal ideal.
The full excellent predicate was inspected: the conclusion retains both
quasi-excellence and universal catenarity. No assumption that A is a domain,
regular, reduced, or of equal characteristic has entered the declaration.
The proof docstring follows all eight steps rather than only citing Tag 07QW.
There is one declaration, with explicit universe, and its entire proof is
`sorry`. No mismatch was found and no statement change was made.

Validation: `scompile.py N3 lem-per-complete-local-excellence` compiled the
sandbox and library module cleanly (1.8 seconds each). The prescribed
`deliver2.py N3 lem-per-complete-local-excellence --no-push` returned
`OK (dry run): commit 086ac19031 passes the preflight and compiles; nothing pushed`.
A local source check also confirmed that the node changes only in `lean`, every
Lean line has at most 100 characters, and there is exactly one `sorry` proof.
