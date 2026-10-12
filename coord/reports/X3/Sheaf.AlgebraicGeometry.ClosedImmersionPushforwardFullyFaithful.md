## What changed

Proved `AlgebraicGeometry.closedImmersion_pushforward_fullyFaithful` with its signature
unchanged. Added the proof-only import `Sheaf.AlgebraicGeometry.ClosedImmersionUnitKernel`.
Its epi-unit clause, combined with the right triangle identity, makes the pushed-forward
counit invertible. Naturality and invertibility of closed-pushforward stalk comparisons
then give invertibility of the original counit on every stalk; Mathlib's stalk criterion
and reflection by `Scheme.Modules.toPresheaf` give the counit isomorphism. Mathlib's
`Adjunction.fullyFaithfulROfIsIsoCounit` supplies injectivity and surjectivity on homs.
The node's proof, proof dependencies, and proof origin now describe this argument.

LeanFinder, Loogle, and grep searches were run with `msearch.py` and recorded in
`searches.jsonl`. The existing fully faithful module pushforward instances apply only to
open immersions; the needed categorical split-mono/epi result is in Mathlib.
The single-file compile passed with no warnings.

## Proved and sorry left

Closed the one hole in `AlgebraicGeometry.closedImmersion_pushforward_fullyFaithful`.
No holes were added or split off, and no `sorry` remains in the delivered module.
The proof uses the existing, still unproved declaration
`AlgebraicGeometry.Scheme.Modules.closedImmersion_unit_kernel`
(node `lem-weil-pbc-closed-immersion-unit-kernel`); that module is not part of this delivery.
This is a proof from an existing stated dependency, not a claim of axiom-free closure.

## No longer needed

Removed proof-only imports:
- `Sheaf.AlgebraicGeometry.Modules.TensorPullbackStalk`
- `Sheaf.Topology.PresheafModuleStalkFunctor`

The target's argument no longer directly needs nodes `lem-weil-pbc-module-stalk-pullback`,
`def-weil-pbc-module-stalk`, or `lem-weil-pbc-locally-surjective-iff-stalks`.
The tensor stalk calculation remains below the existing unit-kernel dependency, so this
report does not claim it disappears from the overall target import closure.
The Mathlib closed-immersion and tensor-pullback public imports remain needed by the
statement; `ClosedPushforwardStalks` remains needed by the proof.

## Where the brief, the DAG or earlier work was wrong

No statement error was found. The DAG's direct tensor computation can be replaced, below
the unit level, by the existing epi-unit result and the triangle identity. The blueprint
unit's realized statement and steps are untouched. The intermediate counit-isomorphism
module explored during development was deleted and is not delivered.

## Second reading by X3

1. Compared the delivered module with the repository version. The theorem signature is unchanged; only the proof and proof-only imports differ. The node statement was restored byte-for-byte to the repository version.
2. Compiled the module with `lcompile.py`; it succeeds without warnings. The delivered theorem has no `sorry`, `axiom`, `unsafe`, `opaque`, `extern`, or `implemented_by`; its proof relies only on the existing unit-kernel theorem and categorical/stalk results.
3. No new split-off statements or nodes were added. The existing unit-kernel dependency is a genuine lower-level statement and is used directly; the target statement is unchanged.
4. The proof takes the shorter categorical route through the epi unit, triangle identity, closed-pushforward stalk comparison, and Mathlib's fully-faithful adjunction theorem. The removed imports and dependencies are listed above, and the unit route remains represented by the target node.
5. The DAG proof, proof dependencies, and proof origin now match the Lean proof. No statement or definition was changed.

Changed during second reading: restored the node's original statement serialization and added this review section; no Lean proof changes were needed.
