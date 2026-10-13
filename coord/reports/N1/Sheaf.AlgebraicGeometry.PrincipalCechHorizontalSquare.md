## What changed

Proved `AlgebraicGeometry.principalCechHorizontal_square` in
`Sheaf.AlgebraicGeometry.PrincipalCechHorizontalSquare`, preserving its signature,
visibility, existing docstrings and imports. The proof follows the existing node
`lem-sc-principal-cech-horizontal-square`: project to a target subset, expand
both sums, identify composite restrictions, then cancel the deletion-order pairs.
The route and proof dependencies therefore remain unchanged; no DAG edit is needed.

Fully proved private helpers establish the deletion sign identity, cancellation
of an alternating double erase sum using `Finset.sum_involution`, composition
of section restrictions by presheaf functoriality, the double-erased cardinality,
and symmetry of the double-restriction term. Private auxiliary definitions are
explicit constructions, with no postponed data or proof. Their conditions let
terms be defined independently of membership proofs; empty erased sets give zero.

Searches: LeanFinder for alternating deletion cancellation returned exterior-power
alternatization results, which do not fit these categorical products. Loogle found
`Finset.sum_involution`, used in the proof. Mathlib grep found finite-sum involution
infrastructure and `Finset.filter_erase`; source-library and Sheaf searches found
ordered Čech constructions but no result for this explicit subset-indexed horizontal
map. The existing column module already provides everything else needed.

Validation: the complete file compiles through `lcompile.py` without warnings.
The argument treats all integers p, all r (including zero), singleton target
subsets, empty first deletions, and empty second deletions without extra hypotheses.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.principalCechHorizontal_square`
(node `lem-sc-principal-cech-horizontal-square`).

No holes remain in this module. No holes were added or split off. This is a proof,
not a decomposition through newly postponed statements. Dependencies are unchanged;
this report does not claim to close other modules' existing holes.

## No longer needed

None. The sole import, `Sheaf.AlgebraicGeometry.PrincipalCechColumns`, is required
by the unchanged public statement and by the explicit differential formula.
No planned dependency node or module was bypassed. The unit's `realized` arrays
are empty, and its route is unchanged.

## Where the brief, the DAG or earlier work was wrong

The node's first proof step correctly places S in horizontal degree p+2,
which means cardinality p+3, as the Lean docstring states. There is no indexing
error or statement change. No unusable dependency or tool workaround
was needed. Local source files for the cited Stacks text are absent on this
machine; the cited Tags 01FP and 08D1 were read on the official Stacks website.

## Second reading by N1

1. Compared the entire delivered module with the repository baseline. The only
   changes are fully proved private helpers, explicit private constructions, and
   the replacement of the original theorem's `sorry`. The existing public
   signature, visibility, docstrings and sole public import are byte-for-byte
   unchanged. No change record or forced adaptation is needed. Verdict: pass.
2. Read every helper and the main proof. Local compilation is clean. There are
   no remaining holes or forbidden declarations, and no data chosen from an
   unproved existence theorem. A scratch copy additionally checks the public
   theorem with `#print axioms`; the delivery tool checks every declaration.
   Verdict: pass (only `propext`, `Classical.choice` and `Quot.sound`).
3. No statement is split off and no new public statement is introduced. The
   sign helper uses exactly membership of the smaller deleted element; the
   involution exchanges distinct members and cancels symmetric terms. Empty
   sets and singletons have empty off-diagonal sums. The double-erase cardinality
   follows from two actual membership proofs. Restriction composition is
   presheaf functoriality; the private term definitions return zero explicitly
   when an index is absent. Verdict: pass.
4. Read the column definitions and searched the source library and Mathlib for
   deletion-sum and off-diagonal cancellation infrastructure. The proof already
   uses `Finset.sum_involution`; generic alternating coface infrastructure would
   require constructing an additional model and comparison. No shorter direct
   library proof was found. The sole import is needed in the public signature.
   The only old proof dependency, `def-sc-principal-cech-columns`, remains used;
   there is nothing to prune. The unit `sk-thm-picard-duality` has empty realized
   arrays, and its route is untouched. Verdict: pass.
5. Read `lem-sc-principal-cech-horizontal-square` and its dependency. Its three
   proof steps, dependency union and proof origin describe the actual Lean
   argument: project, identify restrictions, cancel paired deletions. Its phrase
   degree p+2 correctly refers to horizontal degree (cardinality p+3), so the
   earlier report's indexing remark is a clarification, not a DAG error. No new
   node or change to the existing node is needed. Verdict: pass.

Second reading changed only this report: added the independent review and
clarified the interpretation of the DAG's indexing. The Lean proof needed no
repair. One original hole closed, zero added, zero split off.
