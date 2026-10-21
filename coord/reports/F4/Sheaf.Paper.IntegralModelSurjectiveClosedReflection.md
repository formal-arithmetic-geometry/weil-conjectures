## What changed

Restored lean/Sheaf/Paper/IntegralModelSurjectiveClosedReflection.lean byte for byte from
its assigned quarantine source. This restores integralModelCondensedCoefficients, its
IsCommMonObj instance, the private comparison/cover helpers and the already proved
integralModel_surjective_closed_reflection theorem. The missing live path is the repair:
this is not a rebase or a change to an already present source file.

All public imports, definitions, signatures, proof imports and theorem proofs are
preserved. The existing nodes def-sfb-integral-model-condensed-coefficients and
lem-sfb-integral-model-surjective-closed-reflection keep their Lean attachments and all
dependencies. No node edit is necessary because the restored proof is their current plan.

Change record: coord/changes/F4-restore-integral-model-surjective-closed-reflection.md.

## Proved and sorry left

Zero original local holes; zero closed, zero added, zero split off, zero left.
The restored integralModel_surjective_closed_reflection and all five private theorem
helpers have complete proofs. Its existing transitive dependencies still include
unresolved proofs; no transitive proof closure is claimed here.

The coefficient definition and commutativity instance have only propext, Classical.choice
and Quot.sound in the axiom probe. The restored theorem's axiom probe also lists sorryAx
from its existing dependencies, not from any local hole or newly introduced declaration.

The restored item compiles alone (3.6 seconds) and in import order with a separate importer
(6.3 seconds for the item, 4.7 seconds for the importer). The importer checks commutativity
instance synthesis, the finite free point-module coefficient type used by the tensor
consumer, and reflection with the unchanged hypotheses used by the stratum consumer.

## No longer needed

None. No import, module, declaration, node or dependency is pruned. The existing monoidal
point comparison, change-of-scalars, module-pullback composition, cover-refinement and
surjective-closed equivalence dependencies are exactly those used by the restored proof.
The unit statement and realized route are unchanged. Searches through LeanFinder, Loogle
and the project sources found no new direct replacement for the existing proof.

## Where the brief, the DAG or earlier work was wrong

The assigned module is absent from lean/ rather than currently containing a sorry.
Its coord/rework.tsv row identifies the quarantine source and the cluster-restore
reversion; the archive already proves the theorem. Thus the substantive repair is to
restore the real coefficient construction and its proved reflection interface, with
zero local holes, rather than inventing a fresh split or withdrawing the missing module.

The source-downstream script cannot enumerate an absent live module. Scanning both
live and quarantined sources gives exactly two direct consumers: IntegralTensorShriek
and IntegralStratumHomFormula. Their sources and unchanged uses were checked; no consumer
adaptation is required. The local transparency attributes and existential pullback-cover
helper already in the archive keep the restored proof well below the compile limit.

## Second reading by F4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
