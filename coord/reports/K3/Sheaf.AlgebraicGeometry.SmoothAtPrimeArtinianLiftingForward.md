## What changed

Proved `AlgebraicGeometry.smooth_on_open_artinian_lifting_forward` in the existing
module, with its signature byte for byte unchanged. Added only the proof import
`Mathlib.RingTheory.Artinian.Ring`. The proof chooses a principal open inside the
smooth neighbourhood, obtains a smooth localization, factors the given map through
it, and applies Mathlib formal smoothness with a nilpotent kernel. The kernel is
nilpotent because it is a proper ideal of an Artinian local ring. No new public
declarations, definitions, or modules are delivered.

## Proved and sorry left

Closed: `AlgebraicGeometry.smooth_on_open_artinian_lifting_forward`
(node `lem-weil-pbc-smooth-at-prime-artinian-lifting-forward`).
Added holes: none. Remaining holes in the delivered module: none.
This is a proof, not a decomposition: one existing hole closed and zero added.
Removed the first worker's unneeded declarations `ArtinianLiftCondition`,
`artinianLiftCondition_of_smooth_localization`, and
`exists_artinian_lift_condition_of_smooth_open`, together with their proposed core
module and new nodes. None of these had been delivered or existed in the repository.

## No longer needed

No existing imports, old proof-dependency nodes, or existing library modules are
pruned. All original proof dependencies still describe the localization and formal
smoothness argument. The proposed new core module and its two proposed nodes were
removed from the sandbox, since the original theorem now has a complete proof.

## Where the brief, the DAG or earlier work was wrong

The first worker's alleged localization lemma already asserted the entire desired
lifting condition, with an irrelevant witness g (one could always take g = 1).
Extracting that condition did not reduce the problem. Its docstring described a
smooth localization, which its conclusion did not actually provide. The original
DAG plan does admit a direct Mathlib proof; its length-one kernel argument can be
shortened to nilpotence of a proper ideal in an Artinian local ring. The DAG proof
now records this route. The finite-type and length-one assumptions remain unchanged
in the signature but are unnecessary for this direction.

## Second reading by K3

1. Compared the delivered module with the repository using diff. The existing
   declaration signature, visibility, universes, and public imports are unchanged.
   Only its proof, explanatory docstring, and a proof-only import changed. No change
   record is required. The other proposed module and new nodes were removed.
2. Compiled locally with lcompile.py. No sorry or forbidden declaration remains.
   A scratch copy checks `#print axioms` for the target; its only axioms are
   propext, Classical.choice, and Quot.sound. No data is selected from a holed theorem.
3. No split-off statements remain. Checked the discarded split: its extra witness
   contributes nothing since 1 is outside every prime. For the actual proof, local
   rings are nonzero, ensuring a proper kernel; the zero source/target edge cases
   are excluded by these assumptions. Mathlib's nilpotent-kernel lifting works
   across the universes in the unchanged statement.
4. Searched the library and Mathlib with alternative terms, and queried Loogle for
   Algebra.FormallySmooth.liftOfSurjective. Used that existing theorem rather than
   adding lemmas. No proof imports are unused. Read dag/units/sk-thm-p1.json:
   this node is below its realized steps; none of its realized nodes or routes is
   removed or bypassed. The original geometric localization route is retained.
5. Updated the original node's proof and proof_origin to describe the nilpotent
   kernel argument and Mathlib lifting. Its proof_deps remain the union of the
   proof steps' uses. No new nodes or statements are introduced.

Second reading changed: replaced the tautological decomposition with a complete
Mathlib proof, removed the proposed core module and nodes, updated the original
node and this report, and preserved the existing signature.
