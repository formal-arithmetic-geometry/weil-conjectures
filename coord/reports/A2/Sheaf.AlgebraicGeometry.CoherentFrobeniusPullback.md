## What changed

Definition and consumer changes are recorded in
`coord/changes/A2-coherent-frobenius-adopted-comparison.md`.

Repaired the returned A2 packet by recording the omitted
`Sheaf.AlgebraicGeometry.CoherentFrobeniusComparison` consumer and rebasing onto
B2's landed comparison proof. Proved structural Frobenius pullback naturality
from coefficient transport, the fixed resolution comparison, the structural
coefficient adjunction square and exact-functor Ext naturality.

The additive action now uses the native components of the same fixed resolution
isomorphism. A proved generic certificate in the Frobenius-comparison consumer
identifies it pointwise with the original large-Ext action. The comparison file
packages universe change on the native bundled sheaf-cohomology groups before
specialization to a scheme, and packages resolution composition and conjugation
generically. Their evaluation theorems preserve the original component formulas.
The module-group cache and Ext universe map retain their original constructions.
The scalar comparison uses a generic identity constructor for restriction of scalars,
which retains the same additive equivalence.

## Proved and sorry left

Closed one hole: `AlgebraicGeometry.Scheme.Modules.coherentFrobenius_pullback`
(blueprint: `new-coherent-frobenius-pullback`). No `sorry` remains in the item,
the canonical-comparison module or the adapted Frobenius-comparison consumer.
No holes were added or split off. All new construction/evaluation APIs and
private transport helpers are proved. Existing dependency holes are unchanged.

Validation: the complete three-module set compiled successfully with `lcompile.py --all`
(59.1 s, 18.3 s and 33.4 s respectively).

## No longer needed

No declared dependency, module or DAG node is pruned. The proof uses the canonical
comparison, coefficient transport, resolution naturality, edge compatibility and
structural pullback adjunction square. Stale consumer-import adaptations from
the returned packet are omitted because they are already in the current base.
The old private `iso_composite_apply` and `iso_component_natural` helpers are
replaced by the generic module comparison evaluation and naturality APIs. No source-library declaration or module is withdrawn.

## Where the brief, the DAG or earlier work was wrong

The prior landing omitted the quarantined Frobenius-comparison consumer from the
change record's Users table. Its active source, now restored, and its archive are
accounted for. The retained packet also predated B2's proved normalized comparison;
all stale edits that would undo that proof are removed. Concrete conversions
between inherited additive structures caused expensive kernel reductions.
The native bundled-group and generic construction APIs avoid specializing those
conversions repeatedly, while the evaluation formulas and universe-naturality
certificate preserve the mathematical maps.

## New nodes

None. The new construction/evaluation APIs belong to the existing canonical
comparison definition node. The three affected nodes describe the actual proofs.

## Second reading by A2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
