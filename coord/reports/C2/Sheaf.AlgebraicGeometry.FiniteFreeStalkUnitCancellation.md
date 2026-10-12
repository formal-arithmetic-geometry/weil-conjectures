## What changed

Replaced the first worker's invalid decomposition with a support/degree reduction.
The existing `AlgebraicGeometry.Scheme.Modules.exists_stalk_unit_cancellation`
signature and visibility are byte-for-byte unchanged. Its proof now extracts a
nonzero residue differential, proves that its source and target are consecutive
and within the support interval using Mathlib, converts its source to a natural
number `i < d`, and applies cancellation at that supplied degree.

Added `Sheaf.AlgebraicGeometry.FiniteFreeStalkUnitCancellationAt`, containing the
remaining geometric construction as the named theorem
`AlgebraicGeometry.Scheme.Modules.exists_stalk_unit_cancellation_at`.
The original module imports this new module only for its proof. The new module
imports the matrix-splitting and associated-sheaf tools only for its proof plan.
No existing definition, declaration signature, or public import changed.

## Proved and sorry left

Hole closed: `AlgebraicGeometry.Scheme.Modules.exists_stalk_unit_cancellation`
(node `lem-pc-finite-free-stalk-unit-cancellation`). Its support/degree selection
is now proved, and the remaining conclusions are assembled from cancellation at
the selected degree.

Hole added and left open:
`AlgebraicGeometry.Scheme.Modules.exists_stalk_unit_cancellation_at`
(node `lem-pc-finite-free-stalk-unit-cancellation-at`), in its own new module.
It has a source and a full natural-language proof in its docstring. Its proof is
exactly `by sorry`. This is a decomposition: one upper hole closed, one lower
hole added, net zero holes closed. It is not a complete proof of cancellation.

Removed the unlanded first worker's `exists_stalk_unit_cancellation_data` and
`stalk_unit_cancellation_ranks`, with their two unlanded nodes. They are not
counted as baseline holes closed. No definition or data construction uses sorry.

## No longer needed

Removed the original module's direct proof import
`Sheaf.Algebra.Homology.UnitEntrySplits`; it remains imported by the new
fixed-degree cancellation module. Both old parent proof dependencies,
`lem-weil-pbc-spec-tilde-free-module` and
`lem-weil-pbc-free-complex-unit-entry-splits`, are no longer used directly by the
parent's Lean proof: they now belong to the new cancellation node's proof plan.
They remain reachable through that node. No module is pruned from the targets'
import closure. No unit-route node is bypassed.

## Where the brief, the DAG or earlier work was wrong

The first worker's rank bookkeeping theorem was false. It assumed only that
P' has free terms of sizes n', with no relation to P or n. Take a scheme with a
point (for example Spec of a field), the zero complex P', n'=0, and n=0.
The zero complex has the required rank-zero free identifications, but its
claimed second rank equality becomes 1=0. Even adding a homotopy equivalence
would not supply the missing information about which particular cancellation
constructed the complementary complex. All rank equations must concern the
same actual cancellation construction.

Both proposed child nodes also cited the parent cancellation node as their
proof dependency, while the submitted parent Lean proof depended on those
children. The old parent node was not updated to match that proof. The repaired
DAG has a parent-to-fixed-degree-child edge; the child depends only on the
original associated-sheaf and module-splitting tools, never on the parent.

## New nodes

`lem-pc-finite-free-stalk-unit-cancellation-at` is the cancellation part after a
specific nonzero differential and an in-range degree have been supplied. Unlike
the original item, it does not choose or locate a cancellation degree. The
parent proves that step rather than transferring the whole statement to a new
name. The remaining matrix construction, contraction, sheafification, support,
and exact ranks are described together so their witnesses cannot become
unrelated. The node includes its verbatim Lean signature, source, proof steps,
and independent Mathlib searches. LeanSearch returned Internal Server Error;
this is recorded as unavailable, not as evidence of absence. LeanFinder,
Loogle, and grep found no existing fixed-degree sheaf cancellation theorem.
There are no change records because no existing interface changed.

## Second reading by C2

1. Compared the first submission and the repaired delivered module with the
repository original using diff. Also extracted and compared the entire existing
theorem signature as literal bytes: unchanged. Its original docstring, namespace,
visibility, and public imports remain unchanged. Only the proof and its private
import change. The added theorem lives in a new module. Verdict: pass after repair.

2. Compiled both delivered modules locally in import order through lcompile.py:
no errors or warnings. Scanned both files for forbidden declarations and for
sorry: the sole sorry is the named new fixed-degree theorem, never a definition.
Scratch copies with #print axioms report only propext, Classical.choice,
Quot.sound, and sorryAx for both the parent and child. The parent still depends
on the documented geometric hole. Verdict: valid decomposition, not axiom-free
completion.

3. Rejected the rank theorem by the rank-zero counterexample above. Checked the
new fixed-degree statement against Stacks Project Tag 00MT
(https://stacks.math.columbia.edu/tag/00MT), read during this review. Over the
local stalk a nonzero residue coefficient lifts to a unit; the source's splitting
removes exactly one adjacent basis vector in each term. The identity summand is
contractible and additive sheafification preserves the homotopy equations.
For d=0 the hypothesis i<d is impossible; a zero affected rank makes the nonzero
residue differential impossible; for d=1 and a unit map between two rank-one
terms the complement has both ranks zero. Other degrees keep their original
terms. No arbitrary data is chosen from an unproved existence statement.
Repeated searches with degree/support and fixed-degree unit-coefficient wording,
and inspected nearby local splitting, finite-free shortening, residue homotopy,
and module unit-entry splitting declarations. The available splitting theorem
is module-valued, and the minimal-complex theorem depends on this item, so it
cannot prove this item. Verdict: the one remaining statement is true, needed,
and a strict part of the original argument.

4. The proof starts at the original hole and uses Mathlib first: shape,
map_zero, zero-object source/target uniqueness, strict support, and integer
arithmetic. It leaves precisely the geometric cancellation at a known degree.
Checked dag/units/sk-thm-picard-perfect.json: its realized statement and step
lists are empty, and this repair keeps the original cancellation route and both
original tool dependencies under the child. Proof imports are private; the
original direct unit-entry import is replaced by the fixed-degree child, with
the old tool still reachable. No longer needed lists both old parent dependency
edges and explains their migration rather than claiming global pruning.
Verdict: pass; no chapter or unit route changed.

5. Updated the parent proof, proof_deps, and proof_origin to its actual Lean
reduction. The new node's fields describe the fixed-degree statement verbatim,
record its searches and creation, and cite the two original tool nodes. Its
proof_deps is the union of its proof-step uses. Neither node depends on the
false discarded rank theorem or cyclic child nodes. Verdict: pass.

Second reading changed: removed the false rank lemma and the unsupported data
split, removed their unlanded nodes, proved the actual support/degree-selection
step, added one documented fixed-degree cancellation theorem and node in a new
module, updated the parent DAG proof, and corrected this report's accounting.
