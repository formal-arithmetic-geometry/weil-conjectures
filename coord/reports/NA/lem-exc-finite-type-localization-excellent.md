## Worker report

The new module `Sheaf.RingTheory.IsExcellentFiniteTypeLocalization` states
`isExcellent_finiteType_localization`, with its only proof `sorry`. It uses the
existing predicates and constructions without adding definitions. The item node
copy changes only its `lean` field. No statement correction, new node, dependency
repair, or statement dispute is needed.

The source was read at `literature/stacks-project/more-algebra.tex`,
`lemma-finite-type-over-excellent` (Tag 07QU): any localization of a finite type
ring over an excellent ring is excellent. The node asks for the excellent case
and its finite type special case; no quasi-excellent assertion has been added.

Clause-by-clause correspondence:

- The commutative ring `R` is `{R : Type u} [CommRing R]`.
- The hypothesis that `R` is excellent is `(hR : IsExcellent R)`.
- The commutative `R`-algebra `A` is `{A : Type v} [CommRing A] [Algebra R A]`.
  The independent universes `u v` impose no equality of the rings' universes.
- The finite type hypothesis is `[Algebra.FiniteType R A]`, the recorded Mathlib
  definition, allowing any finite number of generators, including zero, and not
  requiring injectivity of the structure map.
- The multiplicative subset is `(S : Submonoid A)`. A `Submonoid` has precisely
  the required unit-membership and multiplication-closure conditions; it need
  not avoid zero.
- The localization `S⁻¹A` is `LocalizedModule S A`, the recorded declaration of
  `def-weil-pbc-module-localization` specialized to `M = A`. Its ring structure
  is supplied by Mathlib. This is definitionally `Localization S`: both reduce
  to `OreLocalization S A` with the canonical multiplication action. The source
  of `LocalizedModule` even checks this with the private example
  `example_localization_eq_localizedModule`. Thus this is the canonical fraction
  construction, not an arbitrary isomorphic ring or a new definition.
- Excellence of the localization is the first conjunct
  `IsExcellent (LocalizedModule S A)`.
- The final sentence, that `A` itself is excellent by the trivial localization,
  is the second conjunct `IsExcellent A`. The docstring also explains taking
  `S = {1}`.

Statement dependency declarations read and used:

- `Sheaf.RingTheory.ExcellentRing`, `IsExcellent`, whose full definition is
  `IsQuasiExcellent R ∧ IsUniversallyCatenary R`. The definitions and docstrings
  for J-2, catenary chains, universal catenarity and quasi-excellence in the same
  module were read. The theorem does not substitute a weaker excellence notion.
- `Mathlib.RingTheory.FiniteType`, `Algebra.FiniteType`, whose field asserts that
  the top `R`-subalgebra of `A` is finitely generated.
- `Mathlib.Algebra.Module.LocalizedModule.Basic`, `LocalizedModule`, whose full
  signature and fraction construction were read, including `r`, `mk`, `mk_eq`,
  and the zero-denominator criterion `LocalizedModule.subsingleton`.

The module also imports the recorded, stated proof dependencies: finite type
Noetherianity from `Mathlib.RingTheory.FiniteType`; the G-ring permanence theorem
from `Sheaf.RingTheory.FiniteTypeGRing`; localization Noetherianity from
`Mathlib.RingTheory.Localization.Submodule`; prime/local-ring/residue-field
comparison from `Sheaf.RingTheory.LocalizationPrimeResidueFieldIso`; completion
transport from `Sheaf.RingTheory.AdicCompletionRingEquiv`; the G-ring definition
from `Sheaf.RingTheory.GRing`; regularity transport from
`Sheaf.RingTheory.RegularRingEquiv`; spectrum continuity/embedding from
`Mathlib.RingTheory.Spectrum.Prime.Topology`; and regular local rings from
`Mathlib.RingTheory.RegularLocalRing.Defs`. Proof-only imports have no `public`.
The theorem docstring explains all eight steps of the DAG's proof, including
its image-subalgebra/common-denominator construction and prime-interval
argument, rather than only citing the source's omitted localization argument.

Edge cases checked before writing:

- `0 ∈ S` is allowed. The fraction relation makes the localization the zero
  ring; it has no primes, and its algebras are zero, so the relevant excellence
  conditions are vacuous except for the valid Noetherian condition.
- `S = {1}` gives `A`, accounting for the explicit final conclusion.
- The zero base ring and zero algebra are allowed; no `Nontrivial` hypothesis
  is introduced.
- No finite-presentation, domain, nonzero-characteristic, or injectivity
  hypothesis is introduced. Quotient algebra structure maps are included.
- Zero generators and all characteristics are included. The localization may
  be at an infinite multiplicative subset.

Searches performed with `msearch.py NA lem-exc-finite-type-localization-excellent`:

- LeanFinder: `Any localization of a finite type algebra over an excellent ring
  is excellent`. Eight hits, including
  `Algebra.instEssFiniteTypeLocalization`,
  `RingHom.finiteType_localizationPreserves` and
  `Algebra.EssFiniteType.of_isLocalization`; none states excellence permanence.
- LeanSearch: the same query. Eight hits about finite type, essentially finite
  type, quasi-finiteness and formal unramifiedness of localizations; no match
  for this theorem.
- Loogle: `IsExcellent, Algebra.FiniteType, Localization`. Zero hits; the service
  reports the unknown identifier `IsExcellent`, consistent with excellence
  belonging to this project's library.
- Mathlib grep: `IsExcellent|excellent|Excellent`, subdirectory `RingTheory`.
  Zero hits. Direct source inspection found the existing finite type and
  localization definitions used above, not a theorem about excellence.
- `rg -n 'IsExcellent|isExcellent|excellent|Excellent|lem-exc-finite-type-localization-excellent'`
  in the upstream `WeilConjectures` tree and project `lean/Sheaf`: upstream only
  has an incidental comment mentioning quasi-excellence. The project contains
  the excellence definition and other permanence results (fields, weakly etale
  algebras, strict henselizations), but no finite type/localization theorem.
  Occurrences of this item's id are proof-plan citations in consumer modules.
- Exact-name `rg` for `isExcellent_finiteType_localization` in Mathlib, upstream,
  `lean/Sheaf`, and `dag/lean_names_upstream.json`: no collision.

Validation: `scompile.py NA lem-exc-finite-type-localization-excellent` compiled
this delivered module in the sandbox and as its library module, with no errors
or warnings (1.7 seconds and 2.0 seconds respectively). All variables and
universes are explicitly bound; `autoImplicit` is disabled. The independent
second reader will supply the required second-reading section and deliver.

## Second reading by NA

I independently opened the item node, its sandbox Lean module, every statement
dependency node and its actual declaration, and the Stacks source. Tag 07QU is
`more-algebra.tex`, `lemma-finite-type-over-excellent` (lines 13372–13383).
The surrounding section introduces no base field, domain, nonzero, or additional
finiteness assumption: it refers to the excellent-ring definition 07QT. Its
excellent case says precisely that any localization of a finite type algebra
over an excellent ring is excellent. The node selects that case and explicitly
includes the trivial-localization consequence. No source correction is needed.

My object/hypothesis/conclusion checklist, matched with the Lean:

- Commutative base ring R: `{R : Type u} [CommRing R]`. Exact; zero rings allowed.
- R excellent: `(hR : IsExcellent R)`. Exact. I read
  `Sheaf.RingTheory.ExcellentRing`: `IsExcellent` is the conjunction of
  `IsQuasiExcellent` and `IsUniversallyCatenary`; these supply Noetherianity,
  `IsGRing`, the open regular locus of every finite type algebra, and the
  catenary condition for every finite type algebra. Its prime-chain definitions
  include both the finite bound and equal saturated-chain-length conditions.
  They agree with 07QT, 07P7 and algebra.tex 00NI/00NL; no weaker surrogate is used.
- Commutative R-algebra A: `{A : Type v} [CommRing A] [Algebra R A]`. Exact;
  the structure map may have a kernel and the universes are independent.
- A finite type over R: `[Algebra.FiniteType R A]`. Exact. I read the recorded
  declaration in `Mathlib.RingTheory.FiniteType`: its field is
  `(⊤ : Subalgebra R A).FG`, equivalent to the node's finite polynomial
  presentation with an arbitrary ideal. No finite-presentation hypothesis.
- Multiplicative subset S of A: `(S : Submonoid A)`. Exact; it includes 1,
  is multiplication closed, and need not avoid zero. No hypothesis on its size.
- The fraction ring S⁻¹A: `LocalizedModule S A`. Exact use of the recorded
  `def-weil-pbc-module-localization`, specialized to the module A. I read its
  parameters, `LocalizedModule.r`, `mk`, and `mk_eq` in
  `Mathlib.Algebra.Module.LocalizedModule.Basic`. The relation is precisely
  equality after multiplying the cross-products by another denominator.
  The private check `example_localization_eq_localizedModule` (lines 92–94)
  verifies by reducible reflexivity that this is `Localization S`. Thus the
  inherited commutative ring is the actual ring of fractions, not a private
  construction or merely a module with an unrelated multiplication.
- Principal conclusion: `IsExcellent (LocalizedModule S A)`, the first
  conjunct. Exact; the same recorded excellence predicate is used.
- In-particular conclusion: `IsExcellent A`, the second conjunct. Exact;
  it records the node's final sentence. Its position under the S binder adds
  no restriction since the conclusion is independent of S and S = {1} exists.

Edge cases: S = {1} gives A; S containing zero gives the zero ring; S can be
infinite or all of A. Empty S is outside the source because 1 must belong to S.
The zero base ring and zero algebra, noninjective structure maps (including
quotients), zero algebra generators, and every characteristic are included.
There are no scheme or cohomological index parameters to restrict. Universes u
and v are explicitly bound without an equality. The same-universe test algebras
inside the recorded excellence definition do not remove a mathematical case:
any finite type algebra has an isomorphic copy in the base ring's universe,
as also expressed by `Algebra.FiniteType.small` in
`Mathlib.RingTheory.Finiteness.Small`. Thus its quantifiers are not vacuous.

Independent searches on 2026-10-16, using words different from the worker's:

- LeanFinder via msearch: "If a commutative ring is excellent, adjoining
  finitely many elements and then taking fractions preserves excellence".
  Eight hits about essentially finite type algebras and fraction rings,
  including `Algebra.instEssFiniteTypeLocalization`; none states excellence.
- Loogle via msearch: `"isExcellent"`. Zero hits.
- LeanSearch via msearch: "Excellence of a localization of a finitely generated
  commutative algebra". Eight hits about finite type/localization infrastructure,
  including `Algebra.EssFiniteType.of_isLocalization`, with no excellence theorem.
- Direct case-insensitive rg for
  `excellent|excellency|iscatenary|universallycatenary` in Mathlib RingTheory,
  upstream `WeilConjectures`, and project `lean/Sheaf`. Mathlib has no hit;
  upstream has only an incidental quasi-excellence comment. The project has the
  recorded definition, excellence of fields and weakly etale algebras, and
  downstream applications, with no theorem giving this finite type/localization
  assertion. Exact-name search of `dag/lean_names_upstream.json` has no collision.

H4/H5/H6/H8/H9: all three recorded statement-dependency modules are public
imports. The stated proof dependencies are imported without public, and I also
opened the G-ring permanence, localization prime/residue comparison, completion
equivalence and regularity-transport modules. There are no new nodes or dependency
modules to audit, no definitions or extra theorems in this delivery, and the
sole theorem proof is `sorry`. The source/blueprint docstrings are present;
the theorem docstring covers all eight node proof steps, including the image
subalgebra/common-denominator model and the full prime-interval argument.
No local notation or instance hides the signature; no line exceeds 100 columns.

Mismatches and changes: none found in the statement, dependency choices, proof
docstring, or node record. I preserved the correct Lean and node and added only
this independent review. No statement_change or citer audit is applicable.
The node differs from the base only in `lean`; a direct string check confirms
`lean.statement` is verbatim the theorem signature before `:= by`.

Validation: I reran the prescribed scompile.py from the sandbox directory on
`lean/Sheaf/RingTheory/IsExcellentFiniteTypeLocalization.lean`. Both its sandbox
and library-module compiles passed in 2.1 seconds each with no warnings or errors.
The initial invocation from the read-only repository used a relative path that
was absent there; rerunning from the sandbox resolved that invocation error.
