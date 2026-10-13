## What changed

Proved `AlgebraicGeometry.Scheme.Modules.stalkRestrictionComplexIso_map_subopen`.
The proof adds private categorical calculations for compatibility of restriction with
pullback composition and the stalk comparison triangle. The public theorem statement is
unchanged. The unused `Sheaf.AlgebraicGeometry.TensorPullback` import was removed.

## Proved and sorry left

The target theorem `AlgebraicGeometry.Scheme.Modules.stalkRestrictionComplexIso_map_subopen`
is proved. No `sorry` remains in the delivered module, and no new theorem or node was added.

## No longer needed

`Sheaf.AlgebraicGeometry.TensorPullback` was removed because the proof uses only declarations
available through `Sheaf.AlgebraicGeometry.StalkRestrictionComplexIso`. No DAG proof dependency
node is unused.

## Where the brief, the DAG or earlier work was wrong

The earlier module contained only the target theorem with `sorry`; the first report incorrectly
described removal of a private `pullback_triangle` helper. The delivered diff instead adds the
needed private pullback compatibility calculations and removes the unused import. The node and
unit route remain correct.

## Second reading by B3

1. **Interface and accidental changes.** Compared the delivered module with the repository
version. The public theorem statement is byte-for-byte unchanged; only its proof and imports
changed. No target or definition was changed.

2. **Proof and axioms.** Compiled the module with `lcompile.py`; it succeeds with no errors.
The module contains no `sorry`, `axiom`, `unsafe`, `opaque`, `extern`, or hollow definition.
The proof uses the stated categorical pullback and stalk comparison constructions.

3. **Statements and duplication.** No new public statement or node was added. The private
helper calculations are proof infrastructure, and the existing DAG node statement is
unchanged. The theorem has exactly the original hypotheses and conclusion.

4. **Shortest route and pruning.** The proof follows the node route: identify the stalk-map
triangle by pullback composition, use naturality, then cancel comparison isomorphisms. The
removed import is unnecessary; all used declarations arrive through the remaining import.

5. **DAG and unit route.** The node declaration, statement, proof origin, and proof dependencies
agree with the Lean proof, and the unit's realized route is preserved. No split-off statements
or nodes were introduced.

Changed during second reading: corrected the report's description of the diff, recorded the
removed import, and added this review section.
