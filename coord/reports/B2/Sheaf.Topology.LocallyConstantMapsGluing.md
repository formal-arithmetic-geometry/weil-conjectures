## What changed

Proved `TopCat.locallyConstantMaps_gluing_exists` in
`Sheaf.Topology.LocallyConstantMapsGluing`, with its statement and imports unchanged.
The proof follows the node's two steps: choose a covering member for each point of
its union, use compatibility to prove the restriction equations, and transport a
constant open neighbourhood from that member along its open inclusion into the union.
Mathlib's `IsLocallyConstant.iff_exists_open`, `IsLocallyConstant.exists_open`, and
`IsOpen.isOpenMap_inclusion` provide the topological steps.

## Proved and sorry left

Proved `TopCat.locallyConstantMaps_gluing_exists`
(node `lem-weil-pbc-locally-constant-maps-gluing-exists`): one of one original sorries
removed. No sorries remain in the module and none were added elsewhere.
Local compilation with `lcompile.py` succeeded without warnings.
The construction works for empty covers and empty target types, since it chooses an
index only for points of the union. It makes no nonemptiness assumption on the target.

## No longer needed

None. Both existing public imports are needed by the unchanged statement. The node
already has no proof dependencies, and the implemented proof follows its existing
pointwise construction and local constancy argument. No modules or nodes are pruned.

## Where the brief, the DAG or earlier work was wrong

None. LeanFinder found closed-set piecewise gluing and continuous-map cover gluing;
Loogle and source searches found the local constancy and open inclusion APIs. Direct
pointwise gluing gives the stated result without importing further sheaf machinery
or adding intermediate statements. No DAG or unit route change was required.

## Second reading by B2

1. Compared the delivered module with the repository version: the theorem statement and imports are byte-for-byte unchanged; only the proof body is filled.
2. Compiled the module with `lcompile.py`; it succeeds without warnings, has no `sorry`, forbidden declarations, or hollow definitions. `#print axioms` reports only `propext`, `Classical.choice`, and `Quot.sound`.
3. The proof uses the existing theorem statement and no split-off statements; the pointwise choice, compatibility equation, and transported local constancy establish exactly the stated gluing result. No weaker or stronger hypotheses were introduced.
4. The proof follows the DAG's two proof steps and uses both existing imports; no shorter unused dependency or prunable node was found.
5. The DAG node's proof, dependencies, origin, and unit route agree with the Lean proof; no node or statement changes are needed.

Changed nothing during second reading.
