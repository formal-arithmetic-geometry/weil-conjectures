## What changed

Restored lean/Sheaf/AlgebraicGeometry/ScalarCupPullbackCoefficientNaturality.lean
from its quarantine archive specified by coord/rework.tsv. Replaced its stale
public import of the withdrawn empty scalar operations module with the canonical
WeilConjectures.AlgebraicGeometry.FieldLinearModuleCohomologyOperations import.
The complete archived proof, theorem signature, visibility, docstring and both
proof-only imports are unchanged. No adopted source file was modified.

The proof composes the recorded derived-functor coefficient maps using
Functor.map_comp, applies scalarCup_pullback_naturality, and then applies
scalarCup_coefficient_naturality. All stated proof dependencies were read and
remain used. The DAG proof, dependency lists and Lean attachment already describe
this exact proof, so no node update or new lemma is needed. The unit route stays.

Change record: coord/changes/scalar-cup-pullback-coefficient-upstream-import-S1.md.

## Proved and sorry left

AlgebraicGeometry.Scheme.Modules.scalarCup_pullback_coefficient_naturality
(node lem-sc-scalar-cup-pullback-coefficient-naturality) retains its complete proof.
This is a zero-hole quarantine repair: 0 original sorries, 0 holes closed,
0 holes added, 0 split off and 0 remaining in the delivered module.
No new theorem or dependency obligation is introduced.

## No longer needed

Removed the public import of the empty withdrawn module
Sheaf.AlgebraicGeometry.FieldLinearModuleCohomologyOperations, replacing it with
the canonical upstream operations. No mathematical nodes or dependency modules
are pruned. Both proof imports are necessary and retained.

LeanFinder found group cohomology functoriality results, which do not state this
scheme-module scalar cup identity. Loogle found Functor.map_comp, already
used in the proof; msearch grep returned no matching scalar naturality result. Direct searches of the project found the existing two compatibility
lemmas already used by the complete archived proof. No shorter route is needed.

## Where the brief, the DAG or earlier work was wrong

The module is quarantined, not withdrawn, and its archive contains zero sorries.
Its public import had not followed the retirement of the duplicate scalar
operations module. The operation node already names the canonical upstream
module. This restoration repairs the import without changing any statement,
definition, mathematical dependency or proof route.

The sole archived direct consumer PicardKunnethQcohFunctoriality has an independent
stale public scalar operations import. Its use of this theorem has the same
signature. No consumer adaptation is forced by the restored import.

A read-only `tools/batch_land.py status` request was refused by the maintainer-only
shell guard. No merge or build action was requested. The refusal was respected;
subsequent waiting checks use only the published build record.

Validation is blocked by a missing published dependency artifact. Repeated
lcompile.py attempts and both deliver3.py attempts fail before elaborating the
item: the published build has no
Sheaf/AlgebraicGeometry/ScalarCupPullbackNaturality.olean. The last delivery
attempt at 2026-10-20 23:49 UTC failed in 0.9 seconds and pushed nothing.
The read-only landing status still reports dependency restoration landing
20261020T233054-L-890329 as waiting; the last published green build is
7dccc799763f32125d66fb62b2962dbce8d32d6d at 2026-10-20T23:29:59Z,
which predates that restoration. Waited and rechecked through 23:49 UTC.
No replacement theorem or dependency copy was introduced to bypass the published
build rule. Consumer compilation and final preflight remain pending publication.
The validation-only consumer files are under scratchpad/, outside the delivery.

## Second reading by S1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
