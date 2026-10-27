## What changed

Restored the assigned module from its rework quarantine source, preserving its sole
public theorem and all its hypotheses. Replaced its sorry with a proof from the existing
ambient `refinementProjectionCounit` and the new comparison-realization lemma.

The item proves conjugation through the explicit source and target isomorphisms, applies
that calculation to each single-refinement reverse square, and assembles any two
compactifications through a common refinement using `comparison_trans`. Only comparison
isomorphisms are cancelled; no projection map is inverted. The positive level is written
as `m + 1` to use the existing ambient theorem.

Added `Sheaf.Paper.FiniteRefinementProjectionRealization`, with one named theorem comparing
only the two endpoint transports. It contains no projection morphism or projection-square
assertion. Its source, proof in words, and new DAG node describe the remaining normalization
calculation. No existing definition, public signature, public import, instance or exported attribute
was changed, and no other existing module was edited. The original unit route is retained.

## Proved and sorry left

Original hole closed:
`WeilConjectures.CompactSupportFiniteProjection.component_compactification`
(node `lem-sf-finite-projection-compactification-transport`). Its combining proof has no sorry.
The private conjugation, generic endpoint-conversion, and single-refinement arguments
are also complete.

New hole:
`WeilConjectures.CompactSupportFiniteProjection.refinement_realization`
(node `lem-sf-finite-refinement-projection-realization`). This states only identification
of the prescribed reverse support comparison at the tensor endpoints; the existing ambient
counit theorem supplies the independent projection equation used by the item.

This is a decomposition: one original hole closed, one strictly smaller normalization hole
added, net zero textual holes. The item has zero holes; the new module has one. It is not a
claim of a net sorry-free proof. The ambient theorem retains its existing dependencies,
including the already-stated local tensor calculation; those are not new holes.

Validation: the new normalization module compiles. Final item compilation and delivery
checks are recorded by the launcher when completed.

## No longer needed

The item does not import `Sheaf.SixFunctors.ProjectionRefinementDescent` or use
`lem-sf-projection-refinement-descent`: the existing ambient reverse refinement counit
identity supplies the required projection equation directly, without a whole operation
datum or a new descent transformation. This removes that planned direct proof dependency.

The item does not directly import `Sheaf.Paper.RingedProjectionTensorComposition` or use
`lem-sfb-ringed-projection-tensor-composition`: its naturality and compositor work is already
encapsulated by `refinementProjectionCounit`. These dependencies remain needed by that
ambient theorem and are not withdrawn globally.

`lem-weil-pbc-finite-ring-constructible-derived-origin` is needed in the new normalization
node, rather than directly by the item. Its module remains in the defining dependency's
closure. No original import was removed: `ConstructibleProjectionMates` is still needed by
the statement. No module or declaration was withdrawn.

## Where the brief, the DAG or earlier work was wrong

The planned `ProjectionRefinementDescent.finite_descent` takes an entire
`SixFunctorOperationDatum`, including higher coefficient stages, whereas the assigned theorem
has only `SixFunctorFiniteOperations`. That declaration cannot be applied directly to the
supplied datum. The already-stated `refinementProjectionCounit` avoids that extra hypothesis
and applies to arbitrary unbounded fixed-scalar inputs. The remaining work concerns only
normalization of the given operation comparison, not another proof of projection coherence.

At the start the item and some dependencies were absent from `lean/` and preserved in
`quarantine/`; the rework row was checked before restoration. The original item baseline
compiled against the published library, so this was not treated as withdrawal or a tool
failure. No archive was deleted.

The identity-refinement, zero-input and empty-scheme cases use the same categorical
cancellation. No Tor restriction on K or separatedness of the structure maps was introduced.

## New nodes

`lem-sf-finite-refinement-projection-realization` records the two coefficient-realization
identities for the prescribed inverse comparison along one refinement. It is strictly a
normalization step: neither conclusion involves `component`, `fixedComponent`, a projection
morphism, or a projection square. The item combines this with the separately proved ambient
counit square and then performs the common-refinement argument in Lean. Mathlib searches
were run through leanfinder, loogle and grep; none states this specific normalization.
There is no existing-interface change record because no existing interface was changed.

## Second reading by N3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
