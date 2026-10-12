## What changed

Kept the existing singleton-fibre theorem's signature byte for byte and proved its
body by combining its two implications. Added two new modules with proof-only imports
in the item. The backward lemma is proved from the existing
`AlgebraicGeometry.strictHenselizationResidue`, using the canonical residue algebra
structure and mutual specializations to transport the closed point through `e`.
The forward implication remains open. Updated the parent node's proof route and both
new nodes, including their self-contained statements, sources, searches and proof plans.
No existing statement, definition, public import, attribute or visibility changed.

## Proved and sorry left

Closed the original hole
`AlgebraicGeometry.Scheme.strictHenselizationStructuralMap_fiber_eq_closedPoint`.
Also closed the first worker's proposed backward hole
`AlgebraicGeometry.Scheme.strictHenselizationStructuralMap_closedPoint_eq`; this is a
new helper with a Lean proof, not a new sorry.

Added exactly one hole:
`AlgebraicGeometry.Scheme.strictHenselizationStructuralMap_fiber_eq_closedPoint_of_eq`
(node `lem-weil-pbc-strict-henselization-closed-fiber-forward`). Its entire proof is
`by sorry` in its own module, with the source and full mathematical proof in its docstring.
No other delivered theorem or definition contains sorry.

This is a decomposition with one original hole closed and one new hole added (local net
zero), not a complete axiom-free proof of the item. The backward proof depends on the
existing residue theorem, whose pointed-map inputs remain open upstream. All three
delivered declarations have only `propext`, `Classical.choice`, `Quot.sound` and `sorryAx`
in their transitive axiom lists. Target-closure progress is for the pinned ledger to measure.

## No longer needed

No import was removed, and no module is claimed pruned. The parent node no longer directly
uses its old proof dependencies `def-weil-pbc-strict-henselization-limit`,
`def-weil-pbc-strict-henselization-structural-map`, `lem-weil-pbc-etale-local-ring-triples`,
and `lem-weil-pbc-strict-henselization-triples`: its proof now uses the two new helpers.
The old dependencies remain needed below those helpers and for their signatures; this
is relocation of proof dependencies, not pruning of those nodes from the target closure.
All proof-only imports are plain `import`; the existing public structural-map import stays.

## Where the brief, the DAG or earlier work was wrong

The first worker split both implications without using the existing residue clause in
`Sheaf.Paper.StrictHenselizationFunctoriality`. That clause proves the backward result
after transport of the closed point. The parent node was not updated, and the new nodes'
prose statements omitted their hypotheses. The first report did not explicitly distinguish
a decomposition from a complete proof. These faults were repaired in the second reading.
The forward colimit comparison still needs to preserve the structural map, beyond the
local-ring-only comparison supplied by `strictHenselizationLocalStructure`.

## New nodes

`lem-weil-pbc-strict-henselization-closed-fiber-forward` names the forward implication
in `Sheaf.AlgebraicGeometry.StrictHenselizationClosedFiberForward`. It retains the
original chart/triple-colimit argument and remains open.

`lem-weil-pbc-strict-henselization-closed-fiber-backward` names the closed-point image
equation in `Sheaf.AlgebraicGeometry.StrictHenselizationClosedFiberBackward`. It is
proved using the existing residue clause of the functoriality node and Mathlib
specialization tools. Neither new lemma repeats the entire equivalence.
No change record is required because every existing interface is unchanged.

## Second reading by H3

1. PASS. Diffed the only existing delivered module against the repository. Its existing
   declaration signature, docstring and visibility are unchanged; only two plain imports
   and the proof body differ. The other two modules are new. No definition is delivered.
2. PASS. Compiled all three modules in import order with `lcompile.py`; no errors or
   warnings. Checked the declaration axiom lists in a scratch copy: only the three
   permitted axioms and `sorryAx`. There is exactly one direct sorry, the named forward
   theorem listed above. No prohibited declarations, foreign implementation or bypass.
3. PASS. The forward statement is a proper implication of the target; the backward
   statement only evaluates its closed point. Checked the field case (closed point zero),
   empty target scheme (no geometric point), and zero ring A (no isomorphism to the
   nonempty strict henselization). No extra hypotheses were added. Read Stacks Tags
   [04GW](https://stacks.math.columbia.edu/tag/04GW),
   [04GP](https://stacks.math.columbia.edu/tag/04GP) and
   [04HX](https://stacks.math.columbia.edu/tag/04HX), and checked the existing triple APIs.
   Repeated LeanFinder, Loogle and grep searches with different queries; the generic
   local-ring tools do not prove the forward fibre assertion. Source search found
   `strictHenselizationResidue` and it was used to close the backward hole.
4. PASS. The shortest existing route found proves the backward helper, using no new
   axiom or data chosen from an undetermined existence theorem. Imports are used and
   proof-only dependencies are private imports. Reviewed `dag/units/sk-thm-p1.json`:
   its realized statement and steps are retained; this refinement is below that level
   and the forward helper follows the original affine-chart/triple route. The four
   replaced direct proof dependencies are fully listed above; no global pruning claimed.
5. PASS. Parent proof/proof_deps/proof_origin now describe the actual conjunction of
   implication proofs. New nodes have self-contained hypotheses, verbatim Lean signatures,
   source, complete proof plan, dependency union, searches, provenance, chapter/unit and
   blueprint origin. The backward node records the existing residue theorem actually used.

Changed in this reading: proved the backward helper; expanded both new docstring proofs;
repaired parent and new-node metadata; corrected the hole count and no-longer-needed report.
