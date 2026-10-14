## What changed

Second reading rejected the proposed extra `hlift` hypothesis: it follows from
`hb` by Mathlib's `Pullback.exists_preimage_pullback`. Restored the repository's
signature of `AlgebraicGeometry.Scheme.stalk_normalization_depth_two_section_flat_core`
and its direct point-lifting proof. Restored both caller files byte for byte;
there are no forced adaptations and no statement-change record in this delivery.
Clarified the proof comment; namespace openings and imports are unchanged.
Updated the existing node's `proof_origin.note` to record the review finding.

## Proved and sorry left

`AlgebraicGeometry.Scheme.stalk_normalization_depth_two_section_flat_core` is fully
proved, with exactly the existing signature. It was already proved in the repository:
this is a review/repair of a stale queued complaint, not a new hole closure.
Holes closed: none. Holes added: none. Split-off statements: none.
No delivered module contains `sorry`. The scratch axiom check of the core reports
only `propext`, `Classical.choice`, and `Quot.sound`.

## No longer needed

No imports, proof-dependency nodes, or modules were pruned. Both existing
`proof_deps` remain used: `lem-weil-pbc-flat-algebra-faithfully-flat-descent` and
`lem-sbc-finite-flat-target-locus`. The proposed lifting premise, the two proposed
caller adaptations, and `coord/changes/stalk-normalization-flat-core.md` were removed
from the proposed delivery as unnecessary. No library declaration is removed.

## Where the brief, the DAG or earlier work was wrong

The first reader's report treated point lifting as the rational-point/dense-fibre
hypothesis in Stacks 0EYJ. It is not that hypothesis: every pair of scheme points
with the same image lifts to the scheme pullback, as Mathlib proves unconditionally.
Thus the added premise was redundant, and moving its proof to callers changed no
mathematical content while needlessly changing an interface.

Review #1428 refers to an older core whose normalization statement and cone
counterexample were superseded by the landed E4 repair documented in
`coord/changes/stalk-normalization-depth-two-section-flat-core.md`. The current core
asserts only descent of already established flatness along a flat test meeting x,
followed by openness for a finite morphism. Its explicit pullback-flatness hypothesis
is essential: the normalization counterexample cannot be applied without supplying it.
The rational-section calculation belongs to the caller's formal-splitting input,
not this descent step. The previous report and proposed cyclic `stmt_deps` were
therefore discarded; the existing node statement and dependencies are restored.

## New nodes

None.

## Second reading by P2

1. Compared all three proposed Lean files with the repository by textual diff.
   The core's proposed new hypothesis was declared but unnecessary; its restoration
   leaves the existing signature byte for byte unchanged. Both callers are restored
   byte for byte. No definition, target, visibility, or public import changes.
2. Compiled the core and both unchanged callers in dependency order through
   `lcompile.py --all`. Compiled a scratch copy of the core with `#print axioms`.
   The axiom check reports only the three permitted axioms. Inspected the complete
   proofs: no sorry, axiom, unsafe, opaque, implemented_by, extern, or data selected
   from an unproved existence theorem. Verdict: valid faithful-flat descent proof.
3. There are no split-off statements or new declarations. Verified the proposed
   premise directly against Mathlib's `Pullback.exists_preimage_pullback` in
   `AlgebraicGeometry/PullbackCarrier.lean`; it follows from `hb`. Empty E is vacuous;
   empty T cannot supply b; an empty fibre over x makes membership in the target
   flat locus vacuous. Verdict: no extra premise or new lemma needed.
4. Read the imported finite-flat-locus theorem and the source-library
   `Module.Flat.of_flat_of_faithfullyFlat`. The proof already uses those proved
   inputs directly. All imports serve the signature or those proof steps. Namespace openings
   are retained to preserve the existing module interface. The unit `sk-prop-input-spreading` and its
   `realized` field are unchanged; this remains the descent-and-openness substep,
   without bypassing the formal-section calculation. Verdict: retain the route.
5. Checked the node's Lean signature, two proof steps, `proof_deps`, and
   `proof_origin` against the proof. Restored the original statement and `stmt_deps`
   (the proposed additions pointed from the core back to its callers), retained both
   actual proof dependencies, and recorded the second-reading correction in
   `proof_origin.note`. Verdict: DAG agrees with Lean; no new node required.

Changes made during second reading: removed the redundant lifting hypothesis and
its misleading explanation, restored both callers, removed the unnecessary change
record, restored the node interface/dependencies, corrected the report and provenance,
and clarified the proof comment. No net sorry reduction is claimed.
