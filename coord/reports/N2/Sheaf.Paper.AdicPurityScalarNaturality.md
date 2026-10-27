## What changed

Restored lean/Sheaf/Paper/AdicPurityScalarNaturality.lean from its quarantine
archive for the timeout repair in coord/rework.tsv. Data now inherits the same
operation properties and comparison equations through OperationData and
ComparisonData. Seven exposed irreducible definitions name the original operation
class propositions. Explicit unfold recovers the exact original requirements.
No equation, normalization, scalar square or reduction requirement is dropped.

sourceShift and scalarShift keep their original bodies and types, with no_expose
to prevent automatic expansion in importers. The comparisons are locally folded,
and the final records respect that transparency boundary. composeShift and
ShiftCompatibility pass their existing shift structures explicitly to Mathlib.
coefficientTriangulated fixes the finite field stage in the existing closure
proof, replacing the broad projection import's instance.

The mathematical statement and planned proof route are unchanged. The Data
constructor representation changes and needs the normal independent statement
review. Change record:
coord/changes/adic-purity-scalar-naturality-unfolding.md.

## Proved and sorry left

This is an assigned definition and timeout repair. Holes closed: 0. Holes added
relative to the quarantined source: 0. Split off: 0. One existing hole remains:
WeilConjectures.AdicPurityScalarNaturality.adicPurityScalarNaturality,
node lem-pur-adic-purity-scalar-naturality. No definition contains sorry.

The candidate passed the full stage-3 axiom probe in 37.0 seconds, reporting only
that original theorem's hole and no forbidden axioms. Final root and unchanged
consumer checks are recorded by delivery and the final verification below.

## No longer needed

Removed public imports Sheaf.AlgebraicGeometry.SfOpenExceptionalBaseChange and
Sheaf.Paper.AdicProjectionShiftCoherence, and the unused private proof import
Sheaf.SecSmoothPurity.AdicScalarTraceCoherence. The narrower public imports
Sheaf.Paper.FiniteTorAmplitudeSites and
Sheaf.SixFunctors.IntegralOperationShiftData provide the structures used here.
No module, node, declaration or quarantine archive is withdrawn. The original
mathematical proof dependencies remain needed by the retained theorem's plan.

## Where the brief, the DAG or earlier work was wrong

The assigned item is absent from lean because it was quarantined for a timeout;
its original source and Lean attachment must be restored, not withdrawn.
Three advertised assembly dependencies currently lack Lean attachments:
lem-pur-adic-operation-domains-source-comparison,
lem-pur-adic-unit-trace-transpose-reductions, and
lem-pur-adic-trace-transpose-coefficient-calculus. They cannot be imported for
the mathematical assembly. The theorem and full proof plan are retained.

LeanFinder returned unrelated perfectoid, Witt-vector and spectrum results;
Loogle had no match for Functor.CommShift.ofComp; Mathlib grep for smoothPurity,
purity.*scalar and scalar.*purity returned no replacement. Both library roots
were searched. The actual Mathlib shift composition implementations were read.
The downstream index does not recognize the quarantined item. Direct searches
in both library and quarantine roots found its sole consumer,
Sheaf.Paper.NormalizedIntegralPurityTrace; no current claim was found for it.

## Second reading by N2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
