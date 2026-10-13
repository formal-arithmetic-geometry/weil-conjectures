## What changed

Proved `AlgebraicGeometry.Scheme.Modules.exists_degreewise_finite_aux` in
`Sheaf.AlgebraicGeometry.FiniteFreeStalkDegreewiseLiftAux`, preserving its signature
and both public imports. Added the proof-only import
`Sheaf.AlgebraicGeometry.StalkRestrictionSubopenCompatibility`.

The proof first shows that a representative survives restriction to any smaller
neighbourhood, using the existing compatibility theorem and cancellation of the
comparison isomorphisms. Finset induction then intersects the neighbourhoods for
all degrees in I. Outside I, the supplied top-open representatives restrict to
that intersection. Updated the existing node's proof, proof_deps and proof_origin
to record these steps. The unit route is unchanged (the unit's realized lists are
empty, and this implements the original finite intersection argument).

## Proved and sorry left

Closed 1 hole:
`AlgebraicGeometry.Scheme.Modules.exists_degreewise_finite_aux`
(node `lem-pc-finite-free-stalk-degreewise-lift-core-aux`).
No sorry remains in the item's module. Added 0 holes and split off 0 statements.

This is a complete proof from existing statements, including
`AlgebraicGeometry.Scheme.Modules.stalkRestrictionComplexIso_map_subopen`
(node `lem-pc-stalk-restriction-subopen-compatibility`), which remains sorry in its
own, unchanged module. The delivery does not prove that dependency.

The single-file compiler passed with no warnings. Empty I takes the top open;
inserting a degree uses the intersection of two opens containing y. No nonzero,
finite-free, boundedness, or chain-equation hypothesis is introduced.

## No longer needed

Removed imports: none. Both existing public imports are retained.
The proof does not need `def-pc-derived-pullback` or its module
`Sheaf.AlgebraicGeometry.DerivedPullback` as a direct proof dependency; this edge
is removed from the item's node. The needed maps are underived module pullbacks.
No claim is made that the derived-pullback module leaves the whole targets' closure,
or that its statement dependency is removed. No other original proof dependency
is pruned; the comparison definition remains needed.

## Where the brief, the DAG or earlier work was wrong

The original node named the general derived-pullback definition for this underived
restriction argument but did not name the existing subopen compatibility theorem
that states the required transport equation. The proof dependency list now names
that theorem explicitly. No statement or definition is changed.
The referenced literature markdown is absent from this read-only clone; the
argument follows the complete finite-intersection proof recorded in the item's
node and the compatibility theorem's existing docstring and node.

## Second reading by T3

1. **No accidental interface changes.** Compared the delivered module and node with the repository versions. The theorem signature, declaration name, and existing public imports are byte-for-byte unchanged. The only module addition is the proof-only import of `Sheaf.AlgebraicGeometry.StalkRestrictionSubopenCompatibility`; the node changes record only the proof route, proof dependencies, and proof origin.

2. **Proof and axioms.** Compiled the delivered file with `lcompile.py`; it compiled cleanly with no warnings and contains no `sorry`, `axiom`, `unsafe`, `opaque`, `implemented_by`, or `extern`. A scratch `#print axioms` reports only the permitted foundational axioms plus `sorryAx` inherited from the still-open compatibility theorem `stalkRestrictionComplexIso_map_subopen`.

3. **Statements and dependencies.** No statement was split off. The finite-intersection argument is carried out directly: `shrink` is a local proof of the needed restriction implication, finite induction intersects neighbourhoods, and top-open witnesses handle degrees outside `I`. The existing compatibility theorem is the precise imported result used; no duplicate library theorem or weakened/strengthened public statement was introduced.

4. **Pruning and route.** The proof uses the stalk restriction comparison and subopen compatibility only. The old direct proof dependency on `def-pc-derived-pullback` is removed from the node's `proof_deps`; the module itself remains publicly imported where required by the unchanged interface. The finite-intersection route and the unit's realized route are preserved.

5. **DAG agreement.** The node's three proof steps, `proof_deps`, and `proof_origin` match the Lean proof: restriction transport with comparison cancellation, finite-set induction, then outside-I transport. The unit and chapter identifiers are unchanged and no new node or change record is needed.

Changed during second reading: appended this review section only; no Lean declarations or DAG statements were altered.
