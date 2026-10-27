## What changed

Replaced the hole in `WeilConjectures.compactSupportProjectionFormula_finiteStages`
with a uniform proof for `SixFunctorFiniteOperations`, instantiated at all three
families of finite stages in the original statement. All existing signatures and
public imports are preserved. The item adds private proof helpers and proof imports.

Refactored the unclaimed `Sheaf.Paper.ConstructibleProjectionMates` definition
`WeilConjectures.CompactSupportFiniteProjection.fixedComponent` through the proved
generic-category construction `WeilConjectures.projectionTensorCoordinateComponent`.
Its equality and IsIso APIs perform the native-bifunctor/tensor-coordinate conversion
before concrete coefficient specialization. This avoids repeatedly reducing large
derived tensor expressions. The helper is the same published proper/open projection,
not data selected from an existence theorem. These three new declarations are attached
to the existing definition node. The change record is
`coord/changes/T1-finite-projection-coordinate-evaluation.md`; it lists the definition module and its 117
transitive consumers, including the primary item and the direct consumer held by V5,
and both new coherence consumers.
The definition's semantic review reopens under AGENTS.md §4. No mathematical meaning
or input domain changes.

Invertibility uses the already proved general finite-ring theorem
`AlgebraicGeometry.ProEtale.hasProjectionFormulaOfCompactification_of_boundedConstructible`.
The proof supplies bounded constructible etale origins and transfers only the second
input's Tor interval. Naturality is proved first at an arbitrary coefficient category by
conjugating the canonical bifunctor transformation and deriving its tensor-coordinate
equation. Specialize this equation, identify its two components through the proved
realization comparisons, and reflect the equation through the full subcategory.
Proper coincidence is deduced from compactification compatibility by cancelling
the recorded proper-identity isomorphism.

Two new modules isolate the remaining operation-coordinate coherence calculations:
`FiniteProjectionCompactificationTransport` and `FiniteProjectionCompositionTransport`.
Their statements are respectively one coherence square and the composition square
with its compositor pentagon. Neither asserts the whole projection-laws conjunction.
The parent DAG proof and dependency list now follow this reduction.

Validation: `lcompile.py --all` compiled the four delivery modules and the
unchanged `Sheaf.Paper.ProjectionFormulaCoherence` consumer against the refactored
definition (exit code 0). The consumer copy was then removed from the packet;
no consumer adaptation or withdrawal is needed. All profiler settings and temporary
probes are removed. The original target signature is textually unchanged.

## Proved and sorry left

Closed the original hole in
`WeilConjectures.compactSupportProjectionFormula_finiteStages` (1 original hole).
Its module has no remaining holes. The adapted definition module also has zero holes.
Invertibility, naturality, proper coincidence,
and assembly across finite levels are proved by private helpers.

Added two holes:

- `WeilConjectures.CompactSupportFiniteProjection.component_compactification`,
  node `lem-sf-finite-projection-compactification-transport`.
- `WeilConjectures.CompactSupportFiniteProjection.component_composition_coherence`,
  node `lem-sf-finite-projection-composition-transport`.

This is a decomposition: 1 hole closed and 2 strictly smaller coherence holes added,
not a claim that the entire finite projection theorem is now proved without sorry.
Each new theorem has a source, an argument in words, and its own DAG node. Its
edge cases include identity arrows, empty schemes, zero inputs, n=1, arbitrary
bounded constructible first inputs without finite Tor amplitude, and nonseparated
structure maps. The geometric assumptions concern f, g and h only.

## No longer needed

No existing Lean module is withdrawn, and no public import is removed. The original
item imported only its statement/definition module, which remains necessary.

The parent no longer uses the specialized declaration
`AlgebraicGeometry.Etale.isIso_finiteCompactProjection` of
`lem-weil-finite-compact-projection-formula`: it uses the already proved general
finite-ring source theorem instead. The new source attachment
`lem-sf-finite-ring-projection-invertibility` records that exact declaration without
duplicating its proof or adding a Lean module. Its proof follows the same finite
geometric-fiber, proper/open and comparison argument. The direct dependencies
`lem-sf-proetale-constructible-origin` and `lem-sf-comparison-tor-amplitude`
are replaced at the parent by the actual
finite-ring origin, constructible-sheaf comparison and intrinsic Tor transport
nodes used by its proof. Those old nodes may still be needed by the remaining
coherence arguments; no global pruning of them is claimed.

The arguments of `lem-sf-projection-refinement-descent`,
`lem-sfb-ringed-projection-tensor-composition`, and
`lem-sf-projection-compatible-triangle-assembly` remain in the proof dependencies
of the new coherence nodes. They are
not pruned: they supply the remaining argument, below the unchanged unit route.

## Where the brief, the DAG or earlier work was wrong

The stated plan is mathematically compatible with this reduction. Its declarations
are mostly expressed in fixed-scalar coordinates or require a whole operation
datum, while the parent must also handle every normalized finite stage. The new
lemmas isolate the transport to a generic finite operation stage, with its retained
normalization witnesses. No target statement, source-library
interface, or unit route is changed. The definition repair changes only how the same
canonical finite component is presented; its proved generic equality supplies the
comparison for the reopened semantic review.

The finite-ring derived-origin and constructible-sheaf comparison nodes are generic
coefficient-presentation tools from proper base change; intrinsic Tor transport is
the corresponding generic change-of-presentation tool. They supply the finite
formula's input domain, while the unit retains its finite projection and
proper/open coherence route. No tool approval entries are added by this worker.

## New nodes

`lem-sf-finite-projection-compactification-transport` states precisely the
compactification comparison square for the actual finite component and normalized
recorded comparison. Its proof plan is refinement normalization followed by the
existing local refinement calculation and common-refinement cancellation.

`lem-sf-finite-projection-composition-transport` states the composition square and
pentagon for the recorded finite compositor. Its proof plan is compatible-triangle
assembly, normalization through the actual origin witnesses, and origin-compositor
associativity. Its compactification transport dependency is the first new node.
The existing node `def-sf-constructible-projection-mates` additionally records the
three proved generic coordinate declarations and the component refactor. Its statement
and unit route are unchanged. Definition change record:
`coord/changes/T1-finite-projection-coordinate-evaluation.md`.

`lem-sf-finite-ring-projection-invertibility` attaches the existing fully proved
`AlgebraicGeometry.ProEtale.hasProjectionFormulaOfCompactification_of_boundedConstructible`
in the adopted source. It adds no theorem, module or hole; the original finite
projection node has a different specialized Lean attachment. The new attachment
makes the parent dependency describe the declaration actually used.

## Second reading by T1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
