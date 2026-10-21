## What changed

Restored lean/Sheaf/Paper/BoundedConstructibleBaseChange.lean verbatim from its quarantine
archive, as assigned by coord/rework.tsv. The module was absent from the live library.
The four restored definitions are boundedConstructibleBaseChangeUnitStepOfPreserves,
boundedConstructibleBaseChangeSquareStepOfPreserves,
boundedConstructibleBaseChangeCounitStepOfPreserves, and
boundedConstructibleBaseChangeOfPreserves, all in AlgebraicGeometry.ProEtale.CondensedRing.
They insert the restricted adjunction unit, transport the existing pullback comparison,
and contract the restricted adjunction counit under the explicit preservation hypothesis.

Both existing public imports are retained. No signature, definition body, attribute,
coefficient scope, geometric hypothesis, or upstream source file is changed from the archive.
Change record: coord/changes/D3-restore-bounded-constructible-base-change.md.

The restored module compiles on the project server without errors or warnings (3.2 seconds).
The consumer review covers the archived ProperBaseChangeRational public importer: its
use of the preservation proof and .app K retains exactly the same type. A scratch probe
checks this component type and agreement with upstream base change for finiteness
coefficients (3.2 seconds, no errors or warnings): rewrite by the upstream
boundedConstructibleBaseChange_eq_unit_square_counit theorem, then rfl. The upstream
base-change definition is no_expose, so bare rfl does not suffice. The archived consumer itself is not part of this restoration.
The delivery tool performs the independent review and axiom checks.

## Proved and sorry left

Assigned repair completed: four complete definitions restored; zero holes initially,
zero holes left, zero holes closed, zero holes added, and zero statements split off.
There are no sorry declarations in the item and none added elsewhere. Axiom inspection
of each restored definition still reaches existing admitted results in its dependencies;
this repair does not claim the whole dependency closure is proved.
This is a missing-interface restoration, not a decomposition or a claim of new proof progress.

## No longer needed

None. No imports, nodes, modules, declarations or dependencies are pruned or withdrawn.
Both public imports supply definitions used by the construction. Preserve the attachment
of sk-def-sfb-base-change-morphism and all its existing dependencies and parent edges,
including the quarantined ProperBaseChangeRational parent.

Searches: msearch leanfinder for the unit/comparison/counit construction returned generic
adjunction and pullback declarations, not this conditional condensed-coefficient interface.
Loogle did not know the project-specific Adjunction.exchangeRight name. msearch grep
returned zero hits; direct rg found Mathlib's mateEquiv, the project's squareTransport,
exchangeRight, and the existing upstream boundedConstructibleBaseChange. These provide
or verify the existing construction but do not replace its arbitrary-coefficient H interface:
the upstream base-change map requires IsFinitenessCoefficient. No new lemma is needed.

## Where the brief, the DAG or earlier work was wrong

The generic item description suggests a proof hole; the actual assignment is the listed
restoration of an absent, zero-hole definition module. coord/rework.tsv records the archive
and cluster-restore reversion. The archive compiles unchanged against the restored dependency
modules. The DAG statement, unit route, Lean attachment and dependency records remain valid;
no node edit, statement correction, new node, deletion or forced adaptation is needed.

## Second reading by D3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
