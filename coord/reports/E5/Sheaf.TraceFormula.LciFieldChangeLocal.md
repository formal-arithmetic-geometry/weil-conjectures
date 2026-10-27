## What changed

Proved `Algebra.isCompleteIntersectionLocal_fieldChange` without changing its signature.
A finite polynomial presentation and its scalar extension have identical local dimensions
and conormal fibre dimensions. Applying the proved numerical conormal criterion to both
presentations gives the equivalence.

Added `Sheaf.TraceFormula.LciConormalNumericalCriterion`, proving
`Algebra.isCompleteIntersectionLocal_iff_conormal_finrank`. Its proof compares the
polynomial and quotient conormal fibres by tensor cancellation, applies the existing
conormal rank theorem in the forward direction, and uses Nakayama and the existing
conormal-generator criterion in the reverse direction. Principal CI neighbourhoods give
regular polynomial local presentations by the existing regular-sequence theorem.
Universe lifts transport the regular local presentation to the definition's required
universe. Updated both nodes to record the actual proof route. No definition, existing
statement, public import of the item, or source-library file changes.

Repair of return at `f55ab5220`: removed both duplicate private declarations
`Algebra.conormal_rank_congr` and `Algebra.conormal_finrank_congr`. Both call sites
now perform equality substitution directly in a local proof term with explicit prime
binders. No duplicate congruence declaration remains. Importing the
item into its own numerical-criterion dependency would create a cycle, and the
existing helper was private to the returned packet rather than a public library API.
The current main item still has its original single hole and no congruence helper;
this packet retains its proof and the fully proved criterion against that source.

Both delivered modules compile cleanly with `lcompile.py --all`: the numerical
criterion in 19.1 seconds and the field-change theorem in 11.7 seconds. Each has
zero `sorry` tokens and no line exceeds 100 characters.

## Proved and sorry left

Closed the sole original hole: `Algebra.isCompleteIntersectionLocal_fieldChange`
(`lem-trf-lci-field-change-local`). Original holes: 1; closed: 1; remaining in the item: 0.

Added the fully proved theorem `Algebra.isCompleteIntersectionLocal_iff_conormal_finrank`
(`lem-trf-lci-conormal-numerical-criterion`), with fully proved private helpers.
Holes added: 0. Split-off unfinished statements: 0. Existing imported statements may
still depend on `sorryAx`; this delivery proves from their recorded declarations.

## No longer needed

Removed these private imports from the item:

- `Sheaf.TraceFormula.EssentiallyFiniteTypeCIKernelInvariance`;
- `WeilConjectures.RingTheory.LciConormalFreeRankCodimension`;
- `Sheaf.RingTheory.ConormalGeneratorsGlobalCompleteIntersection`;
- `WeilConjectures.RingTheory.LCIRegularSequenceGlobalCompleteIntersection`;
- `Mathlib.Algebra.MvPolynomial.Basic`;
- `Mathlib.RingTheory.Noetherian.Defs`;
- `Mathlib.RingTheory.LocalRing.Module`;
- `Mathlib.RingTheory.RegularLocalRing.Polynomial`;
- `Sheaf.TraceFormula.LciPointwiseCriterion`.

`lem-trf-lci-pointwise-criterion` / `Sheaf.TraceFormula.LciPointwiseCriterion` is no
longer needed by this proof: localized regular equations directly construct the local
presentation. No module is withdrawn and no global pruning is claimed. Kernel invariance
and spreading regular equations remain transitive dependencies through
`TraceFormula.ciLocalRingPrincipalNeighbourhood`. Conormal rank, the generator criterion,
Nakayama and polynomial regularity are used in the proved numerical criterion rather
than imported directly by the item. Finite-type presentation base change and the
conormal-fibre and dimension comparisons remain needed. The unit route is unchanged.

Removed both duplicate private conormal-congruence helpers from the returned packet;
core equality substitution supplies the two transports directly.

## Where the brief, the DAG or earlier work was wrong

No mathematical error was found. The DAG's broad pointwise criterion is unnecessary for
this local argument. Its elementary local-presentation direction is proved directly.
The numerical criterion packages the repeated local algebra in the two directions;
it has a genuinely separate statement, independent of field extension, and is proved
in this delivery. Empty equation lists, zero conormal rank, arbitrary field extensions,
and independent universes are retained. A zero algebra cannot carry the given prime.

## New nodes

`lem-trf-lci-conormal-numerical-criterion` in
`dag/nodes/sec-trace-formula/lem-trf-lci-conormal-numerical-criterion.json` records the
numerical criterion for an arbitrary finite polynomial presentation at a prime.
It follows Stacks Algebra Tags 00SC, 00SF and 00SG, and realizes the local numerical
step used in Tag 00SI. Its new module is fully proved. No change record is required:
no existing statement or definition was changed.

## Second reading by E5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
