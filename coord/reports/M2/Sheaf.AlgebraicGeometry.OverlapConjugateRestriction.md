## What changed

Repaired reviewer X-fcf50 point C1. Removed the proposed
OverlapPairSquareNativeBridge module and its unlanded node. The conversion is
proved locally in OverlapConjugateRestriction using private modules_map_eq and
pair_square_native: expand the generic square, use the existing canonical
transition formula, and reassociate. The helper takes abstract chart families,
so the conversion does not unfold concrete iterated-cover objects. It has a
complete Lean proof and remains in the same module as the native calculation.
No definition changes or external adaptations are delivered.

Kept the justified hθ correction in overlap_conjugate_restriction_explicit and
its caller adaptation. The outer theorem retains its signature. Change record:
coord/changes/overlap-conjugate-explicit-hypothesis.md.

## Proved and sorry left

Repaired and proved AlgebraicGeometry.overlap_conjugate_restriction_explicit
(node lem-pc-overlap-conjugate-restriction-explicit) after restoring the
canonical-transition hypothesis already required by its mathematical statement.
The old, unrestricted Lean statement is false and is not claimed as proved.
This is a statement repair, not a proof of the original signature.
AlgebraicGeometry.overlap_conjugate_restriction has its original signature and
now follows from the corrected intermediate without sorryAx.
No sorry remains in the delivered module and no new holes are added.
The previously proposed AlgebraicGeometry.overlap_pair_square_of_native hole
is removed with its unlanded module. The existing single-chart theorem is used
twice; this delivery does not claim to prove its dependencies.

## No longer needed

Removed import Sheaf.AlgebraicGeometry.OverlapPairSquareNativeBridge, its module
lean/Sheaf/AlgebraicGeometry/OverlapPairSquareNativeBridge.lean, and its proposed
node lem-pc-overlap-pair-square-native-bridge. This unlanded node is omitted
from the delivery and removed from the item's proof and proof_deps. The
conversion is elementary and proved locally. All original planned dependencies
remain used. No repository import or original dependency is pruned. Both original public
imports remain: canonical comparisons occur in signatures, and the tensor
adjunction is used by the existing data definitions. ZariskiDescent is proof-only.

## Where the brief, the DAG or earlier work was wrong

The previous delivery incorrectly split elementary definitional conversion
because of slow compilation; reviewer C1 correctly rejected that split under
stage 3 §4. This repair proves that conversion in the original module instead.
Temporary experiments changing definitions were removed from the delivery.
The local helper abstracts chart maps and uses explicit map equalities to avoid
unnecessary unfolding; the full module must still pass the unchanged time limit.

The original explicit intermediate omitted the canonical-transition equation
required by its node and docstring. For identity base changes and repeated
charts on a nonzero module, an arbitrary zero transition need not commute with
the canonical identity transition. The justified hθ correction and change
record remain. Only the outer theorem calls it and already has this equation.
No target signature or unit route changes.


## Second reading by M2

1. Compared the delivered module with the repository by diff and declaration
   parsing. All six public definitions, their bodies, and the outer theorem's
   signature are byte-for-byte unchanged. The only public signature change is
   hθ in overlap_conjugate_restriction_explicit, exactly as recorded in
   coord/changes/overlap-conjugate-explicit-hypothesis.md. The node's original
   mathematical statement already fixes θ to this conjugate. With identity
   base changes, repeated charts, a nonzero module and zero θ and φ, the old
   premise holds but the canonical square would equate an isomorphism with
   zero. Restoring hθ repairs that false intermediate. No external module
   uses the intermediate; the only caller supplies rfl after substitution.
   Verdict: documented statement repair; no accidental interface change.

2. Compiled the complete file through lcompile.py, cleanly in 24.3 seconds.
   Compiled a full scratch copy with #print axioms for all eight public
   declarations and all nine private helpers, in 24.4 seconds. Every result
   lists only propext, Classical.choice and Quot.sound, with no sorryAx.
   No sorry, axiom, unsafe, opaque, implemented_by or extern occurs in the
   delivered Lean. No definition changed or contains a hole. The inherited
   choice of tensor adjunction is pinned by its prescribed unit on every
   section; that determines the natural transformation and hence the
   adjunction, and its existence theorem is now proved.
   Verdict: fully checked proof, with no residual holes or undetermined data.

3. No statement is split off and no new public declaration or node is added.
   The private helpers are proved calculations strictly within the argument:
   categorical cancellation, single-chart compatibility, and conversion of
   the generic pair square to module notation. Their invertible comparisons
   require no nonzero or nonempty hypothesis; zero modules, empty overlaps,
   repeated charts and identity maps remain valid.
   Verdict: no relocated hole or restatement.

4. Read OverlapSingleChartRestriction, OverlapPairCanonicalComparisons and
   the canonical descent-transition formula in ZariskiDescent. The proof uses
   the existing single-chart result twice, then cancellation and reassociation.
   Independent leanfinder, loogle and grep queries, plus rg on the overlap and
   upstream modules, found no shorter theorem for the entire comparison.
   All four imports serve either signatures/data or this proof; both proof
   imports are plain import. Every original proof_deps entry remains used.
   The removed bridge was unlanded, so actual repository pruning is none.
   Inspected sk-thm-picard-semicon: realized.statement and its one step are
   empty; this local calculation neither changes nor bypasses a unit route.
   Verdict: shortest available route found; pruning report is complete.

5. Compared the old and delivered node. Only lean.statement, proof and
   proof_origin change; proof_deps is unchanged. Verified lean.statement
   against the delivered signature byte-for-byte. The two proof steps track
   the two single-chart equations, the structural-map identity, cancellation,
   restriction-comparison identification and the generic/native conversion.
   The outer node still correctly cites the explicit intermediate. The
   change record includes the exact old and new signatures.
   Verdict: DAG and Lean agree, with no new-node obligations.

Second-reader changes: corrected the claim that the old false intermediate
was proved, clarified that no repository module or dependency was pruned,
and refreshed the downstream count in the change record. The Lean proof
needed no repair.
