## What changed

Proved `AlgebraicGeometry.isRegularRing_snc_finiteRoot` with its signature unchanged.
The proof imports `Sheaf.AlgebraicGeometry.SNCRootLocalPresentation` and
`Sheaf.RingTheory.TransverseLocalRootFamilyRegular` privately and follows the current
three-step DAG argument. It constructs the component enumeration from the given range
equality, proves the reduced branch ideals prime, applies the geometric localization
statement, and applies the local algebra statement at the empty coefficient stratum.
Explicit ring equivalences remove the quotient by the zero ideal and reindex the full
variable set; their maps carry the root relations to the desired relations. Regularity
then transfers to each original prime localization.

Validation: the complete item compiled cleanly through `lcompile.py` in 3.7 seconds,
with no warnings. Its signature is byte-for-byte unchanged, all lines are at most
100 characters, and both new proof imports pass the import-cycle check.

No statement, definition, public import, or source-library module changed. The node proof
now records these interface identifications and removes obsolete direct tool approvals.
Edge cases remain included: the zero ring has no prime q, the empty branch set uses the
same full-set equivalence, and n=1 is accepted without any n>1 hypothesis.

## Proved and sorry left

Closed one existing hole: `AlgebraicGeometry.isRegularRing_snc_finiteRoot`
(node `lem-sfb-snc-finite-root-regular-ring`). Zero holes remain in the item and zero
holes were added. No new intermediate statements were split off.

The proof uses the already stated, still unfinished declarations
`AlgebraicGeometry.snc_root_local_presentation` and
`RingTheory.isRegularRing_transverseLocalRootFamily`; those existing dependency holes
are unchanged. This is a proof from the named DAG dependencies, not an axiom-free
closure of their entire dependency chain.

## No longer needed

Removed the item's old private proof imports:

- `Mathlib.AlgebraicGeometry.AffineScheme`
- `Mathlib.AlgebraicGeometry.Noetherian`
- `Mathlib.RingTheory.FiniteType`
- `Mathlib.RingTheory.Localization.Ideal`
- `Mathlib.RingTheory.AdjoinRoot`
- `Mathlib.RingTheory.RegularLocalRing.Polynomial`
- `WeilConjectures.RingTheory.RegularLocalLocalization`
- `WeilConjectures.Mathlib.RingTheory.RegularLocalRing.Defs`
- `WeilConjectures.RingTheory.RootAlgebraRegularAtRoot`
- `WeilConjectures.RingTheory.LocalizationOfRegularRing`
- `WeilConjectures.RingTheory.HypersurfaceDerivationRegular`

The current assembly does not directly need the old algebra tools
`lem-weil-pbc-regular-local-localization`, `lem-sc-regular-local-domain`,
`lem-sbc-root-algebra-regular-at-root`, `lem-weil-pbc-localization-of-regular-ring`,
and `lem-weil-pbc-hypersurface-derivation-regular`; removed their obsolete top-level
`tool_uses` approvals. They remain relevant below the local-family dependency, so this
packet does not withdraw any of their nodes or modules. Both current substantive proof
dependencies are used; no declared proof dependency is bypassed and no module is withdrawn.

## Where the brief, the DAG or earlier work was wrong

The item's old docstring/import list still describes the seven-step expansion, while
the current reviewed DAG has already factored it into two declared lemmas. The proof
uses that reviewed factorization. The geometric lemma expects prime branch ideals
and a component equivalence; the item instead gives reduced quotients, injective supports
and an equality of support ranges. These interfaces are equivalent here and the conversion
is proved explicitly. The local-family lemma returns a quotient over R/(0) with variables
indexed by the full finset subtype; those presentation differences are also explicitly
resolved, without changing either dependency.

Short-route searches: LeanFinder returned smoothness/normalization declarations, Loogle
returned only polynomial-ring regularity, and Mathlib grep returned the polynomial-ring
regularity instance. None proves this ramified simultaneous quotient. Local searches in
both library roots found the two planned declarations and no shorter exact theorem.

## Second reading by Q9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
