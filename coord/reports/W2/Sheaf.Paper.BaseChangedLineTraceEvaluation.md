## What changed

Replaced the sole hole in `Sheaf.Paper.BaseChangedLineTraceEvaluation` by an explicit
projection-naturality and trace-contraction calculation. The private generic
`trace_evaluation` helper proves that calculation with abstract functors and morphisms;
the private `evaluation_of_origin` specializes it to the actual geometric maps, and
the original theorem supplies the proved source witness and normalized traces. Added a proved private
`source_origin` helper: extract a bounded constructible ordinary representative of M,
reflect its Tor interval, apply the existing affine-line source witness, then transport
along the specified Tate pullback isomorphism. The finished item compiles cleanly in 18.9 seconds through lcompile.py.
Existing public statements, definitions,
attributes and public imports are unchanged.

Added `Sheaf.Paper.CompactSupportProjectionRightUnit`, stating precisely the remaining
right-unit normalization of the published compactification projection in the literal
comparison-unit coordinates. This is Step 2 of the original argument, independent of
affine-line traces, compact-support exchange and the compositor. Its complete proof in
words follows the specified proper counit mate and normalized open tensor comparison.
The original evaluation theorem and its proved private helper perform the rest of the argument.

The item proof privately imports the new unit module and the existing source-library
HomComparison module. No source-library file is changed; no consumer adaptation is needed.

## Proved and sorry left

Original holes: 1. Closed in the item:
`AlgebraicGeometry.ProEtale.BaseChangedLineTrace.baseChangedLineTraceEvaluation`
(blueprint: lem-pur-base-changed-line-trace-evaluation).

Added holes: 1, the whole proof of
`AlgebraicGeometry.ProEtale.AffineLinePurity.compactSupportProjection_rightUnit`
(blueprint: lem-pur-compact-support-projection-right-unit).

This is a decomposition, with net hole change zero, not a complete proof of the original
mathematics. The abstract cancellation helper compiles independently in 2.6 seconds; the version
with the geometric parenthesization compiles in 1.3 seconds. The private
source-origin proof, the naturality calculation, cancellation of
the invertible projection, and contraction using TraceCompatible contain no holes.

## No longer needed

Removed direct private imports of `Sheaf.Paper.DerivedPullbackTensorIso`,
`Sheaf.SixFunctors.OpenTensorNormalization`, and `Sheaf.Paper.ProjectionMateExact` from
the item. These remain planned DAG proof dependencies of the strictly smaller unit-normalization
module. They are not imported there because its proof is still a named hole; none of
their mathematics is claimed pruned from the target closure. The item
node records this dependency change and withdraws its obsolete direct tool-use entries.
Naturality needs only the published projection natural transformation, with no further
proper/open naturality theorem. No modules are withdrawn or deleted.

## Where the brief, the DAG or earlier work was wrong

The existing dependency statements are available, but they do not directly state the
right-unit equation for the actual fixed-module compactification projection in the
literal compared coefficient coordinates. ProjectionMateExact is expressed on supplied
ringed tensor models; OpenTensorNormalization gives normalized ringed-site operations;
DerivedPullbackTensorIso uses its intrinsic coefficient coordinates. The ordinary-site
source theorem Etale.projectionMap_rightUnitality does not directly apply on the
pro-etale site. The remaining step is therefore isolated explicitly, instead of assuming
that these coordinate identifications are definitional.

The original DAG also omitted its existential source-origin applicability argument from
the numbered proof steps. It is now recorded and proved from the existing sourceWitness
and Tor-interval reflection. The unit route through affine-line integration is preserved.
No statement is disputed. Zero objects, the zero ring and empty schemes require no
additional assumptions in the normalization or in the formal trace calculation.

## New nodes

`lem-pur-compact-support-projection-right-unit`, in
`dag/nodes/sec-smooth-purity/lem-pur-compact-support-projection-right-unit.json`, owns the
single new public theorem in `Sheaf.Paper.CompactSupportProjectionRightUnit`. Its equation
is PF at the coefficient unit followed by the canonical contraction equals the right
unitor, for arbitrary compactification and ambient M. It is strictly one step of the
original proof and has no trace-compatibility hypothesis or evaluation conclusion.
Its source, three kinds of Mathlib search, edge-case check, full proof plan and verbatim
Lean attachment are recorded. There are no interface change records because no existing
public interface changed.

The blueprint ancestor command identifies `prop-pur-affine-space-composition-law`; a
whole-blueprint search for `projection.*unit|unit.*projection` returned no matching node.
The three previously approved cross-unit tools (DerivedPullbackTensorIso,
OpenTensorNormalization and ProjectionMateExact) remain tools in the new unit lemma: they
normalize the existing proper/open projection construction, without bypassing the
affine-line integration route. Their approvals are not recreated in the new node.

## Second reading by W2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
