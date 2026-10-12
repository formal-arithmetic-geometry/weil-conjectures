## What changed

Closed the proof of `AlgebraicGeometry.Etale.etale_limit_binary_eventual_zero`.
The proof obtains the two-open comparison ladder, applies Mathlib
`AddMonoidHom.injective_of_surjective_of_injective_of_injective`, and uses `Concrete.colimit_rep_eq_iff_exists` to turn equality in
the filtered colimit into a later-stage zero witness. The target signature is
unchanged.

Added the proof-only import of
`Sheaf.AlgebraicGeometry.EtaleLimitBinaryComparisonLadder` and the Mathlib
filtered-colimit/concrete-category APIs used by the proof. The ladder theorem
is a named intermediate result whose geometric construction remains a
separate hole.

## Proved and sorry left

Proved `AlgebraicGeometry.Etale.etale_limit_binary_eventual_zero`, including
the Mathlib four-lemma application. The item's module has no remaining
`sorry` declarations.

Added one named `sorry`:
`AlgebraicGeometry.Etale.etale_limit_binary_comparison_ladder`, recorded by
node `lem-weil-pbc-etale-limit-binary-comparison-ladder`. This strictly smaller
statement supplies the exact ladder and neighboring comparison properties;
the target proof combines it with a complete algebraic chase. Thus one upper
hole is closed and one geometric intermediate hole is added: this is a
decomposition, with net zero holes closed, not an unconditional proof.

## No longer needed

The proof does not use the old planned affine-transition-limit construction
(`Sheaf.AlgebraicGeometry.LimitAffineTransition` and node
`lem-weil-pbc-limit-affine-transition`); the target already supplies a limit
cone, and the ladder node uses the existing Mathlib projection/open-limit
results directly. The other old direct dependencies now belong to the geometric ladder's plan,
rather than the completed eventual-zero proof: 
`def-weil-pbc-etale-cohomology-stage-continuity`,
`def-weil-pbc-scheme-conventions`,
`lem-weil-pbc-cohomology-pullback-functorial`,
`lem-weil-pbc-colimit-initial-full-subcategory`,
`lem-weil-pbc-etale-inverse-image-restriction`,
`lem-weil-pbc-etale-mayer-vietoris`,
`lem-weil-pbc-etale-mayer-vietoris-pullback`,
`lem-weil-pbc-filtered-colimit-abelian-groups-exact`,
`lem-weil-pbc-inverse-image-composition`, and
`lem-weil-pbc-left-adjoint-preserves-colimits`.
They remain needed for the ladder; their modules are not claimed globally
pruned. No existing import was removed from the repository's item module.
Only `lem-weil-pbc-limit-affine-transition` is absent from the new combined
proof route, replaced by the existing Mathlib projection/open-limit leaf.

## Where the brief, the DAG or earlier work was wrong

The old route unnecessarily constructed a new affine-transition limit despite
the supplied limiting cone. The replacement ladder node records the shorter
route while preserving the unit's two-open Mayer--Vietoris route. No target
statement or existing interface was changed. The ladder is agent-written from
Stacks Tags 09YQ and 0A50 plus the project's pullback/naturality declarations;
no exact assembled theorem was found in Mathlib.

## New nodes

`lem-weil-pbc-etale-limit-binary-comparison-ladder` in
`dag/nodes/sec-proper-base-change/lem-weil-pbc-etale-limit-binary-comparison-ladder.json`
is realized by
`Sheaf.AlgebraicGeometry.EtaleLimitBinaryComparisonLadder` and isolates the
geometric restricted-system and Mayer--Vietoris ladder construction needed by
the target.

## Second reading by M1

1. Compared the item module with the repository by `diff` and checked the
   existing theorem signature byte for byte: unchanged. Only proof code and
   plain proof imports were added. The other delivered module is new; no
   existing definition or public import changed, and no change record is needed.
2. Compiled both modules in import order through `lcompile.py`, without errors
   or warnings. The only delivery-local hole is the named ladder theorem.
   No forbidden declaration, hollow definition, or data definition chosen from
   an unproved existence theorem occurs. The ladder's existential witnesses
   are eliminated solely inside a proposition proof. A scratch axiom check
   and the delivery's all-declaration probe check the permitted standard axioms
   plus `sorryAx` from the documented open ladder/upstream dependencies.
3. Read the ladder's statement, docstring, node, and the local Stacks source
   for Tags 09YQ and 0A50. Its two top exact pairs, first bottom exact pair,
   neighboring comparisons, and restriction square are precisely the
   Mayer--Vietoris construction needed before the group chase. Degree zero
   uses zero left terms and injective restriction, so no negative degree is
   hidden. Empty, coincident, and singleton-index cases obey the same maps.
   Quasi-separatedness of the union stage ensures compact intersection,
   without assuming ambient X is quasi-separated. Independent Lean Finder,
   Loogle, and source searches found the Mathlib four-lemma but no assembled
   geometric continuity ladder. The hole excludes both the group chase and
   the filtered-colimit witness argument, so it is a genuine decomposition.
4. Reviewed downward from eventual-zero to the ladder and then its geometric
   plan. Replaced the private chase by the exact Mathlib four-lemma match.
   All imports serve signatures, colimit instances, the witness criterion,
   or that proof. The pruning section now lists every removed old direct
   proof dependency and distinguishes dependencies moved to the ladder from
   the affine-limit construction no longer needed. Inspected
   `dag/units/sk-thm-p1.json`: no realized unit statement or step is bypassed;
   the two-open Mayer--Vietoris route remains.
5. Compared the Lean with both nodes: the old node has only the stage-3-owned
   route fields changed; its proof now records the Mathlib four-lemma and
   concrete-colimit equality criterion. The new node has the required source,
   proof steps, dependency union, searches, creation/blueprint metadata, and
   Lean record. Its signature matches the new Lean statement.

Changed the private chase to a Mathlib application and added its proof-only
import; updated the old node's proof description and completed the report's
pruning and net-hole accounting. The geometric ladder remains open; closing
its restricted-system and naturality construction is not a few-minute repair.
