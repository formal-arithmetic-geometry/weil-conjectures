## What changed

Filled AlgebraicGeometry.Etale.etale_limit_affine_stage_eventual_zero_tail using
one geometric intermediate theorem, etale_limit_affine_stage_tail_colimit,
and Mathlib's IsColimit.eq_iff'. The proof constructs the directed upper tail,
compares x with zero in its filtered group colimit, and sends the resulting
later-index witness back to I. The existing proof for arbitrary i remains
unchanged: move to a common upper bound with i0 and compose transitions.
All existing signatures and visibility are unchanged. Updated both existing
nodes to record the actual proof route. No forced adaptations or interface changes.

Both delivered modules compile cleanly with lcompile.py. The tail comparison
statement was checked against Stacks Tag 09YQ at
https://stacks.math.columbia.edu/tag/09YQ (2026-10-13).

## Proved and sorry left

Closed one original hole:
AlgebraicGeometry.Etale.etale_limit_affine_stage_eventual_zero_tail
(node lem-weil-pbc-etale-limit-affine-stage-eventual-zero-tail).
AlgebraicGeometry.Etale.etale_limit_affine_stage_eventual_zero was already proved
and retains its proof. The item's module now has no sorry.

Added one hole:
AlgebraicGeometry.Etale.etale_limit_affine_stage_tail_colimit
(node lem-weil-pbc-etale-limit-affine-stage-tail-colimit), the whole proof of the
public theorem in Sheaf.AlgebraicGeometry.EtaleLimitAffineStageTailColimit.
This is a decomposition, not a net reduction in holes: one closed, one added.
The geometric comparison is separated from the proved group-colimit zero criterion.
No definitions, arbitrary witness choices or axioms were added.

## No longer needed

No import present in the repository's original module was removed; its sole
public import supplies the existing signatures. The earlier sandbox attempt's
Sheaf.AlgebraicGeometry.EtaleLimitReindexCoherences and
Sheaf.AlgebraicGeometry.EtaleLimitAffineEventualZero proof imports were removed.
No reindex-coherence module or node is delivered.

The original node's direct references to
lem-weil-pbc-colimit-initial-full-subcategory,
def-weil-pbc-scheme-conventions and
lem-weil-pbc-etale-limit-cohomology-affine-comparison now belong to the new
geometric intermediate node; these are retained work, not global pruning.
lem-weil-pbc-etale-limit-affine-eventual-zero
(Sheaf.AlgebraicGeometry.EtaleLimitAffineEventualZero) is no longer a direct
proof dependency of the tail-vanishing node. It remains a dependency of affine
comparison, so no module is claimed globally pruned.
The filtered-colimit equality leaf remains needed through Mathlib's concrete
category version of that criterion.

## Where the brief, the DAG or earlier work was wrong

The earlier sandbox attempt had an unregistered reindex-coherence sorry and
no node or report. Its conversion of hB did not actually rewrite the zero
hypothesis; the resulting type mismatch is avoided here by applying the
filtered-colimit criterion directly to B. Direct inverse-image reindexing
attempts repeatedly exceeded the file timeout during elaboration/kernel
comparison of dependent types. The final delivery follows the original
comparison-then-equality plan and isolates its first geometric step.
The new claim is not eventual-zero with repackaged hypotheses: its conclusion
is the universal colimit property of the restricted comparison cocone, with
no class x, zero hypothesis, later-index witness or vanishing conclusion.
The original unit statement and every realized unit step are retained.

## New nodes

lem-weil-pbc-etale-limit-affine-stage-tail-colimit is the geometric comparison
on the directed affine tail. Its proof in words constructs the tail, proves
finality, preserves the scheme limit and coefficient colimit, establishes
that tail schemes are affine and transports the supplied coherences, then
applies the existing affine cohomology comparison declaration. Singleton
indices, degree zero, zero sheaves and empty affine schemes satisfy the same
argument. Earlier stages need not be affine. Searches by LeanFinder, Loogle
and grep found no exact replacement; LeanSearch was unavailable (Internal
Server Error). Its signature is verbatim in its node.
No change records are required.


## Second reading by D3

1. Compared both delivered modules against the repository. The new tail-colimit
   module has no repository counterpart. The existing module differs only in
   three proof-only imports and the body of
   AlgebraicGeometry.Etale.etale_limit_affine_stage_eventual_zero_tail.
   Existing theorem signatures, visibility and definitions are byte-for-byte
   unchanged; the arbitrary-index proof is unchanged. No change record is needed.
   Verdict: pass.
2. Compiled both modules in import order with lcompile.py, then compiled a
   scratch copy with explicit #print axioms for both existing theorems and the
   new theorem. No forbidden declaration, hollow definition or arbitrary
   data witness occurs. The only new sorry is the complete public theorem
   AlgebraicGeometry.Etale.etale_limit_affine_stage_tail_colimit; the item's
   two theorems have no local sorry. All three explicit #print axioms results are exactly propext,
   Classical.choice, Quot.sound and sorryAx, as expected from the remaining
   geometric hole; deliver3.py also passed its axiom probe. Verdict: pass
   as a decomposition, not a closed proof.
3. Read Stacks Tag 09YQ (theorem-colimit), Tag 04AX's eventual-equality
   description, the existing affine-comparison declaration and the two
   Mathlib leaves used by the plans. The new statement supplies only the
   geometric comparison; the item separately proves directedness and applies
   IsColimit.eq_iff' to x and zero, then transports its witnesses. It is a
   genuine comparison/equality decomposition, not a renamed vanishing claim.
   On the upper tail, D_j -> D_i0 is affine, hence D_j is affine by
   isAffine_of_isAffineHom (Mathlib/AlgebraicGeometry/Morphisms/Affine.lean:185).
   Restriction preserves all the supplied leg equations. Singleton indices,
   degree zero, zero coefficients, empty affine schemes, and a directed
   preorder with incomparable indices cause no exception: common upper bounds
   give the needed finality without a linear-order hypothesis.
   Independent LeanFinder, Loogle and grep searches used cofinal restriction
   and whiskering terms; Mathlib's Final.isColimitWhiskerEquiv only transfers
   an already known colimit, and structure-sheaf results do not supply this
   abelian etale-cohomology comparison. Repository/upstream searches found no
   replacement independent of this item; affine-stage continuity imports the
   item itself and cannot be used circularly. The source-backed docstring
   gives the full remaining argument, and its node matches the signature.
   Verdict: pass; the dependent coherence reindexing is the remaining hole.
4. Read the proof top downward and Mathlib's concrete IsColimit.eq_iff'
   (ConcreteCategory/Filtered.lean:36). Each proof import is needed: group
   colimits supply preservation, concrete filtered colimits supply eq_iff',
   and the new theorem supplies the tail comparison. Removed the new module's
   unused public Mathlib.Order.Interval.Set.Final import and recompiled.
   Added a plain proof-only affine-comparison import to make the remaining
   geometric plan available to its next worker. Every removed old proof
   dependency is accounted for: affine-eventual-zero leaves the tail node;
   scheme conventions, initial-full-subcategory and affine-comparison move
   from the arbitrary-index node to the geometric intermediate; the
   filtered-colimit-sets-elementwise leaf moves to the tail node. None is
   claimed globally pruned. Read sk-thm-p1's realized statement and four
   step lists; no realized node or unit route is bypassed or changed.
   Verdict: pass.
5. Compared existing node JSONs field by field: only proof, proof_deps and
   proof_origin change. Both updated proofs match the Lean bodies; each
   proof_deps is the union of its steps' uses. The new node has the source,
   searches, creation, blueprint, chapter, unit and exact lean.statement
   fields required by the brief. Expanded its informal statement to state
   every system hypothesis and comparison datum explicitly, and corrected
   blueprint.from to the nearest blueprint ancestor already recorded by
   the parent, retaining the intermediate route in via. Verdict: pass.

Changes by the second reader: removed the unused public interval-finality
import; added a proof-only affine-comparison import; made the new node statement
self-contained and corrected its blueprint ancestry; added this review.
No theorem proof or signature was rewritten. One original hole closed and one
new hole added, net zero; no globally pruned module. The item's original hole
count is one (the arbitrary-index theorem was already proved).
