## What changed

Replaced the only sorry in `Sheaf.AlgebraicGeometry.DescendFinite` with a complete
Lean reduction. The theorem's signature is unchanged. A proved private lemma relates
its `Over.pullback.map` presentation to the raw pullback map used by `DescendAffine`,
using a source isomorphism and pullback hom-ext.

The proof descends affineness, chooses `Y₀.left.affineCover.finiteSubcover`, applies local
finiteness descent separately to each covering affine open, takes a common directed
upper bound, and applies finiteness local on the target. Including the affine stage
in the upper-bound choice handles an empty cover without assuming a nonempty target.

Added `Sheaf.AlgebraicGeometry.DescendFiniteAffineOpen` to isolate the local coordinate-ring
calculation. Its hypothesis is finiteness only over one affine open at the limit and a
known affine stage; its conclusion concerns only restrictions over that open at later
stages. It requires no global qcqs hypotheses. The main proof performs the affineness
reduction and the finite-cover assembly; it is not a single application of a renamed
version of the original theorem.

Updated the existing DAG proof and its dependencies to follow these Lean steps. Read
Stacks Limits 01ZO and Algebra 07RG in the downloaded copies at
`/home/ubuntu/c1-stacks-review/limits.tex` and `algebra.tex` (the repository's canonical
literature paths are absent on this machine). The unit `sk-thm-p1` is unchanged; this
node is below its realized unit statements and steps.

## Proved and sorry left

Proved/reduced `AlgebraicGeometry.exists_isFinite_baseChange_stage`
(node `lem-weil-pbc-descend-finite`): no sorry remains in the item's module.

The sole sorry added by this delivery is
`AlgebraicGeometry.exists_isFinite_morphismRestrict_baseChange_affine_open`
(node `lem-weil-pbc-descend-finite-affine-open`). Its proof is exactly `:= by sorry`,
and its docstring and node give the local affine-cover, colimit, tensor-product and
module-generator argument. The existing affineness descent theorem remains an imported
dependency with its own sorry; it is unchanged by this delivery.

Both delivered modules compile locally without errors or warnings. The main proof's
private pullback comparison is fully proved. Edge cases checked mathematically:
empty affine open (empty restriction is finite), empty target/cover (include k in the
common upper bound), a constant diagram or single index (local finite hypothesis is
already the desired restriction), and a directed preorder without antisymmetry
(no equality of indices is used). The local statement uses only the compactness of
an affine open, so dropping global qcqs assumptions in that local statement is valid.

## No longer needed

Removed the unused public import `Sheaf.AlgebraicGeometry.LimitAffineTransition`.
The statement needs none of its declarations; affineness descent privately imports it.
The interface removal is recorded in `coord/changes/DescendFinite-imports.md`.
All four direct importers have independent imports for the relevant Mathlib API;
the downstream declaration-use scan found zero uses of `exists_limit_affine_transition`.

Removed the proof import `Sheaf.RingTheory.FiniteMapColimitDescent` from the main
module. The ring argument remains part of the local split-off node's proof plan.

Every old direct `proof_deps` entry absent from the new main node is listed here:

- `lem-weil-pbc-cartesian-square-pasting`
- `def-pc-fibre-product`
- `lem-weil-pbc-lft-base-change`
- `lem-weil-pbc-open-fibre-product`
- `lem-weil-pbc-fibre-product-affine-spectra`
- `lem-weil-pbc-morphism-into-affine-scheme`
- `lem-weil-pbc-lft-affine-pairs`
- `def-weil-pbc-category-colimit`
- `lem-weil-pbc-limit-affine-transition`
- `lem-weil-pbc-spec-colimit-limit`
- `lem-weil-pbc-colimit-finite-ring-map`

These entries remain dependencies of the local affine-open node; none is globally
pruned. No mathematical node or unit route is pruned entirely.

## Where the brief, the DAG or earlier work was wrong

No false statement was found. The raw pullback map in `DescendAffine` and the
`Over.pullback.map` map in this item have source objects identified by an isomorphism,
not a definitional equality. Naive rewriting by `Over.w` inside the dependent
pullback-map expression fails; the fully proved private comparison handles this.

The existing ring-map descent theorem is usable for the local algebra step, but the
original DAG has no Lean declaration for the full geometric passage from its rings
to the restrictions of this morphism. The new node isolates that part of the plan.
The LeanSearch service returned Internal Server Error; this is recorded as unavailable,
not as a negative search result. LeanFinder, Loogle and Mathlib grep found no matching
local finiteness descent theorem. Blueprint searches found no existing local node.

## New nodes

`lem-weil-pbc-descend-finite-affine-open`, in
`dag/nodes/sec-proper-base-change/lem-weil-pbc-descend-finite-affine-open.json`, is realized
by the single theorem in `Sheaf.AlgebraicGeometry.DescendFiniteAffineOpen`. It isolates
steps 2–7 and the local version of step 8 of the original plan, assuming the affine
stage supplied by step 1. Its six proof steps retain the original affine-coordinate
and ring-colimit route. The existing definition and statement are unchanged. The public import removal
is recorded in `coord/changes/DescendFinite-imports.md`.

## Second reading by F2

1. Compared every delivered module with the repository: the only existing public
   theorem signature is byte-for-byte unchanged, and there are no definition changes.
   Restored its original docstring to avoid an unnecessary API documentation edit.
   The removed public import has the change record named above; all other new imports
   serve proofs and are private. The new module has only imports needed by its signature.
   Verdict: unchanged mathematical interface, documented import interface pruning.
2. Both modules compiled locally without errors or warnings before review repairs.
   The sole direct sorry is exactly the public named local theorem listed above;
   no definitions or forbidden declarations occur. Scratch copies with explicit
   `#print axioms` checked the main theorem, the private comparison, and the local lemma.
   The private comparison uses only propext, Classical.choice, and Quot.sound; both
   public theorems additionally use sorryAx from the documented open dependencies.
   The main theorem is a reduction over open dependencies, not yet a proof with no
   `sorryAx`: affineness descent and the local affine calculation remain open.
3. Read the local theorem, its full docstring argument, its node, and the source
   proofs of Stacks 01ZO and 07RG. An affine V is quasi-compact, so finitely many
   affine subopens can be chosen over affine base opens without global qcqs.
   Affine transition base changes and the known affine stage make their source
   and target restrictions affine; finite type ring-map descent applies on each.
   Base-change stability gives all later indices. Empty V, empty target, constant
   systems, singleton indices, and preorders without antisymmetry cause no failure.
   This is strictly the local algebraic part of the original proof, not its restatement.
   Independent LeanFinder and Loogle queries used different wording; neither found
   a descent theorem. Focused grep of Mathlib AffineTransitionLimit and the upstream
   and Sheaf geometry sources found no existing local result. The split cannot be
   closed in a few minutes: coordinate-ring and pullback comparison work remains.
   Verdict: true, sufficient, nonduplicated, sourced local statement with a matching node.
4. Checked the private pullback comparison, affine descent, finite affine subcover,
   directed upper-bound argument, and locality assembly from the top downward.
   The empty-cover bound explicitly includes k. No shorter available proof was found.
   Removed the unused public LimitAffineTransition import, recorded its downstream
   effects, and completed the exact list of removed direct proof dependencies.
   Neither node realizes a unit step or statement; sk-thm-p1.realized is unchanged.
   Verdict: genuine reduction with the unit route preserved; no global node pruning.
5. Compared proof steps and their union of uses with proof_deps in both nodes, checked
   proof_origin, all new-node required fields, and the recorded Lean signature.
   The main node follows the implemented affine reduction and finite-cover assembly;
   the local node describes precisely the sole new sorry. Verdict: DAG and Lean agree.

Second reading changed: removed one unused public import with its change record,
restored the existing theorem docstring, and completed the pruning report. The
compiled proof and the new local theorem statement required no mathematical repair.
