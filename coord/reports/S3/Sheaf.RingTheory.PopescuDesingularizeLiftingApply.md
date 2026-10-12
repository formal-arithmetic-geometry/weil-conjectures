## What changed
The target module now proves `Algebra.popescu_desingularize_lifting_apply` by obtaining
fourth-power lifting data, applying the existing
`Algebra.exists_desingularization_strictlyStandard`, and proving the final smoothness
and ideal containment. Its existing signature and visibility are unchanged.
Added the proof-only import `Sheaf.RingTheory.PopescuLiftingWitness`; removed the direct
proof import `Sheaf.RingTheory.PopescuLifting`, which the witness module imports instead.
The new witness states only the 07CP lifting part (no strictly standard assumption and
no final factorization), with quotient compatibility and singular-ideal control.

## Proved and sorry left
Hole closed: `Algebra.popescu_desingularize_lifting_apply`.
Hole added: `Algebra.popescu_lifting_witness`, node `new-popescu-lifting-witness`.
This is a decomposition, not a net proof: one hole closed, one hole added, net zero.
The target also still depends on any open proofs of the imported existing library.
The first worker's two proposed holes were not landed. The vacuous witness was replaced
and the restatement `Algebra.popescu_desingularize_lifting_core` was removed entirely.
No definitions or arbitrary witness choices were added.

## No longer needed
Removed the direct import `Sheaf.RingTheory.PopescuLifting` from the item; it is still
needed transitively by the new lifting witness and is not a module to prune.
Removed the proposed module `Sheaf.RingTheory.PopescuDesingularizeLiftingCore` and its
proposed node `new-popescu-desingularize-lifting-core` from this delivery.
Old direct proof dependencies no longer used directly by the target:
`lem-weil-pbc-popescu-lifting`, `def-weil-pbc-finitely-presented-algebra`,
`def-weil-pbc-noetherian-ring`, `def-weil-pbc-singular-ideal`,
`def-weil-pbc-strictly-standard-element`, `lem-weil-pbc-zero-locus-eq-iff-radical-eq`,
`lem-weil-pbc-smooth-ring-map-base-change-composition`,
`lem-weil-pbc-localization-base-change`, `def-weil-pbc-smooth-ring-map`.
These remain used in signatures, in the witness or existing 07CT, or are replaced by
Mathlib's scalar-extension criterion. No existing module is asserted globally prunable.
The retained direct nodes are 07CT and singular-ideal localization smoothness.

## Where the brief, the DAG or earlier work was wrong
The first worker's witness only asserted a finitely presented R-algebra mapping to Λ;
the base algebra R already supplies that. It discarded all quotient compatibility and
smoothness properties. Its core therefore merely restated the original theorem with a
vacuous extra assumption. The report's claim of a genuine construction boundary was
incorrect. Neither proposed docstring supplied a complete proof of its statement.
The repaired reduction retains the actual quotient compatibility and the ideal
properties of the 07CP algebra; the 07CT application is now in the target's proof.
The repository lacks the cited local smoothing.tex on this machine. The second reader
checked the source at https://stacks.math.columbia.edu/tag/07CP,
https://stacks.math.columbia.edu/tag/07CT and https://stacks.math.columbia.edu/tag/07F0.

## New nodes
`new-popescu-lifting-witness` is stated in
`lean/Sheaf/RingTheory/PopescuLiftingWitness.lean`. Its docstring gives the annihilator
induction, fourth-power 07CP application, quotient factorization, and prime/radical
verification. Its node records the same route and actual second-reader searches.
It is strictly below the target: it does not assume strict standardness, construct the
final B, or conclude that A factors through B. No change record is needed because no
existing declaration's interface changed.

## Second reading by S3
1. Compared the delivered target with the repository using diff: its existing theorem
signature, docstring and visibility are byte-for-byte unchanged. Only proof imports
and the proof body changed. The other module is new; there are no adapted modules.
2. Compiled both modules through lcompile.py, with no errors or warnings. The sole
literal sorry is the named new witness theorem, with its node and complete proof in
words. There are no forbidden declarations or hollow definitions. Axiom probes of
both declarations show only propext, Classical.choice, Quot.sound and sorryAx.
3. Rejected the vacuous original split and removed its core. Checked the repaired
statement against 07CP and 07F0: compatible quotient map plus singular-ideal properties
are all required in the target proof. Checked π=0, unit π, nilpotent π and the zero ring;
no nontriviality or nonzerodivisor hypothesis is assumed. LeanSearch was attempted but returned Internal Server Error; LeanFinder, Loogle and
Mathlib grep plus local rg searches found no packaged equivalent; the closest existing theorem is 07CP itself,
which requires the fourth-power specialization, quotient transport and radical
verification left in the new hole. This is an honest decomposition, net zero holes.
4. Read the existing 07CP, 07CT, singular-ideal definition and localization theorem.
The final argument uses existing 07CT directly and Mathlib's formally-unramified
scalar-extension criterion, avoiding an additional tensor-product localization lemma.
All proof-only imports are plain imports. Removed the unused strictly-standard import
from the new witness. Read dag/units/sk-thm-p1.json realized: no unit statement or step
is bypassed; the same 07CP then 07CT route is retained below that unit. The complete
old direct dependency difference is recorded above.
5. Updated the target node's proof, proof_deps and proof_origin to the actual reduction.
The new node matches the exact Lean signature and docstring argument, with source,
statement dependencies, search records, creation record, chapter, unit and blueprint.
Changes made by this reader: replaced the vacuous witness with substantive lifting
data, deleted the restatement core and node, wrote the 07CT/smoothness/ideal proof,
pruned imports, corrected both DAG records and rewrote the report with honest counts.
