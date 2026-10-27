## What changed

Repaired the DIFFERENT retirement item: the assigned source is already a withdrawn
stub with no declarations, but its node still names an absent small-model theorem.
Added Sheaf.AlgebraicGeometry.StrictLocalSmallModel.ExchangeCubeStalkIsos with the
fully proved theorem
AlgebraicGeometry.Etale.smallModel_isIso_strictHenselization_exchangeCube_stalkComparisons.
Its statement is the original node signature, unchanged modulo its new declaration
name and whitespace. The proof pairs the existing small-model source and target
comparison theorems with all the original arguments. Their modules are private
proof imports; the three public imports supply only the recorded statement's API.

Updated the existing node's Lean attachment, proof text and proof_origin. Kept its
original id, mathematical statement, dependencies and sk-thm-p1 unit. The colliding
item module remains withdrawn through deleted.txt. Change record:
coord/changes/J6-small-model-exchange-cube-stalk-isos.md.

## Proved and sorry left

The assigned stub has 0 sorry declarations before and after: this is a retirement
and attachment repair, not a claimed proof-hole closure. Holes closed: none (0 of
0). Holes added: none. Split off: none. No sorry remains in any delivered module.
The restored theorem named above is fully proved from the two existing proved
component theorems, realizing
lem-weil-pbc-strict-henselization-exchange-cube-stalk-isos.

## No longer needed

Keep the already withdrawn module
Sheaf.AlgebraicGeometry.StrictHenselizationExchangeCubeStalkIsos retired; its full
original small-model conclusion now lives in the distinct replacement module.
No existing import is removed: the assigned stub has none. Both planned component
nodes and their modules remain needed, with exactly the existing proof_deps. No
other node, module or approved tool-use entry is pruned. The adopted full-model
counterpart and its dependencies remain unchanged and required by its consumers.

## Where the brief, the DAG or earlier work was wrong

The brief describes a proof obligation, but the assigned current source is a
withdrawn stub with zero holes. Its DIFFERENT retirement row and stale node
attachment are the actual repair. The adopted unprefixed theorem has a different
strict-localization model, so it cannot replace the original small-model signature
verbatim. Existing small-model component proofs make the exact conjunction direct;
no new lemma or further decomposition is needed.

The consumer census finds no current or quarantined exact importer of the stub.
The complete DAG dependency census finds the abelian-stalk-exchange-localization
parent, whose node dependency and conclusions remain satisfied by this replacement.
No source-library boundary exception, target change or forced adaptation is used.

## Second reading by J6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
