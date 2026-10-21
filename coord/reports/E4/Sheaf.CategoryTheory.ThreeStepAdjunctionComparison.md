## What changed

Restored lean/Sheaf/CategoryTheory/ThreeStepAdjunctionComparison.lean from the
quarantine path named in coord/rework.tsv, with its complete archived proof,
original public import, exact theorem signature and original docstring.
The assigned repair is restoration after the 2026-10-20 cluster-restore revert,
not a definition repair. No archive is deleted and no consumer is changed.

The four vertex isomorphisms are constructed explicitly. The first square uses
hunit and naturality of be.unit. The second uses naturality of δ', hcube and
naturality of θe. The third uses naturality of δ', hcounit, cancellation of αU
with its inverse, and naturality of αH. This is exactly the existing node plan;
no node changes or new proof dependencies are necessary.

Single-file remote compilation of the restored module passed in 3.2 seconds.
A separate axioms probe passed in 3.4 seconds and printed exactly propext,
Classical.choice and Quot.sound. The probe is removed from the delivered file.
An additional compile of the unchanged quarantined consumer
Sheaf.Paper.CoefficientExchangeFromComparisons hit its existing 60-second limit.
It is not included in this delivery: restoring its byte-identical dependency
has not changed a definition, signature or public environment relative to the
archive. No consumer success is claimed and no forced adaptation is made.

Loogle found the four unit/counit mate identities. LeanFinder found generic
adjunction lifting-square lemmas, not this three-factor construction. The
live/quarantine source search found the already complete assigned archive;
there is no reason to replace it or introduce a duplicate theorem.
The relevant Mathlib mate signatures and the comparison structure's fields
were read directly.

Change record: coord/changes/E4-three-step-adjunction-restoration.md.

## Proved and sorry left

CategoryTheory.Adjunction.threeStepComparison has a complete proof. Its source
module in quarantine contained zero sorrys; the restored module also contains
zero sorrys. Holes newly closed: 0 of 0. Holes added: 0. Split-off statements: 0.
This delivery restores an existing proof; it does not claim a new hole closure.
No sorry remains in the item and no theorem with sorry is added elsewhere.

## No longer needed

None. Sheaf.Paper.FiniteDiscreteRealizationFunctor is the sole public import
and defines the structure used in the theorem's statement. No import or DAG
edge is removed. The node has no proof_deps, and the proof follows its two
existing elementary steps.

The quarantined CoefficientExchangeFromComparisons module imports and directly
specializes threeStepComparison. ClassicalProEtaleProperBaseChange also has a
proof import of this module. Both DAG parents remain needed, and their records,
the unit statement and the unit route are preserved. Absence from the live Lean
tree is not treated as evidence for pruning.

## Where the brief, the DAG or earlier work was wrong

The generic brief describes proving a module with holes, but this rework row
instead requires restoring an already proved quarantined module. The archive
compiles as recorded; no false statement, missing glue or hollow definition
was found. Its four explicit isomorphisms and three equations also cover empty
categories and zero objects, without any invertibility assumption on exchange.
No mathematical statement or definition is changed.

The live-only downstream tool reports this absent module as unknown. Consumer
checks therefore use both live and quarantine sources, which identify the two
importers listed in the change record. This expected consequence of quarantine
does not prevent restoration.

## Second reading by E4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
