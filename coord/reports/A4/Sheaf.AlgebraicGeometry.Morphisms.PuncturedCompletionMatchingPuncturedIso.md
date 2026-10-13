## What changed

Replaced the sorry in
`AlgebraicGeometry.Scheme.CompletionGluingData.puncturedMap_isIso` by a complete Lean
assembly from a principal-open section-ring comparison. The theorem's signature and
visibility are unchanged. The only added proof import is
`Sheaf.AlgebraicGeometry.Morphisms.PuncturedCompletionMatchingAffineSections`.

For each target point, choose a principal open D(f) contained in U around its image.
Prove its inverse image in U affine by the open-immersion criterion. Prove the
inverse image in the matching model affine using the affine structural map.
`puncturedMap_over` identifies the source restriction with the inverse image under
the finite map q, proving that restriction affine as well. Bijectivity of the
section-ring comparison then gives a local isomorphism by Mathlib's affine criterion.
Mathlib's target-local criterion gives the global isomorphism, including the empty case.
No new object is chosen from an unproved existence theorem.

Added one public theorem in its own new module:
`AlgebraicGeometry.Scheme.CompletionGluingData.puncturedMap_basicOpen_appTop_bijective`.
It isolates the localized first-projection calculation from Stacks Tags 05ER and 05EU
used in the proof of 0BLH. Its statement concerns a single principal-open ring map;
it does not assert the global scheme isomorphism, completed comparison, or finiteness
of the matching candidate. Updated the assigned DAG node to match the proved assembly.

Validation: both delivered Lean modules compile together with lcompile.py --all.
A separate Mathlib-only scratch test checked the local-to-global argument before the
new baseline artifacts became available. The scratch file is outside lean/ and is
not part of the delivery. deliver3.py --no-push printed OK: the delivery compiles and passes preflight,
with the second reading reserved for the independent reader. Nothing was pushed.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.Scheme.CompletionGluingData.puncturedMap_isIso`
(node `lem-sbc-punctured-completion-matching-punctured-iso`). No sorry remains in the
assigned module.

Added one hole:
`AlgebraicGeometry.Scheme.CompletionGluingData.puncturedMap_basicOpen_appTop_bijective`
(node `lem-sbc-punctured-completion-matching-affine-sections`), in
`Sheaf.AlgebraicGeometry.Morphisms.PuncturedCompletionMatchingAffineSections`.
Its proof is exactly `by sorry`. The docstring states the source and a full proof in
words using the formal-gluing localization comparison and the explicit matching-ring
construction. This delivery is a decomposition: one hole closed and one added, net zero.

Edge cases checked before stating it: f=0 and any nilpotent f give an empty principal
open and zero section rings on both sides; if A is a field then U is empty and these
are the only allowed principal opens; if U is affine the usual affine section criterion
still applies; neither reducedness nor positive dimension is assumed. The main proof's
pointwise locality criterion also covers an empty punctured target without a separate
nonemptiness assumption.

## No longer needed

No imports removed. No modules or nodes are pruned from the transitive proof route.
The original matching-sections public import is retained because it defines the
statement. The original conventions, Noetherian-ring, adic-completion and fibre-product
nodes remain needed by the new local comparison, even though the assembly itself
uses only the matching construction, finite-morphism affineness, and the new comparison.
Neither the completed comparison nor matching-model finiteness is imported or used.
The unit's route is preserved: its realized field assigns no separate node to this
local assembly, and the formal-gluing step remains the cited local calculation.

## Where the brief, the DAG or earlier work was wrong

The assigned node listed only definitions as proof dependencies, despite using the
substantial localized formal-gluing comparison of 05ER. No existing lower comparison
theorem was found in either library root, the DAG, or the blueprint. This delivery
isolates precisely that calculation, and proves the remaining geometric assembly.

The blueprint ancestor command returns None because the original created.item is a
module rather than a node id. The new node therefore inherits the original node's
explicit blueprint.from ancestor and prepends the original node to its via chain.

Initially the shared compiled library lacked PuncturedCompletionMatchingSections.olean.
No library source or compiler tool was changed; the artifact appeared on the normal
sync, after which the sandbox compilation succeeded.

## New nodes

`lem-sbc-punctured-completion-matching-affine-sections` states bijectivity of the ring map
on a single principal-open restriction. Source: Stacks Project Tags 0BLH, 05ER and 05EU,
read online. LeanSearch returned an Internal Server Error, recorded as unavailable;
LeanFinder returned localization-of-sections theorems but no matching-ring comparison;
grep found no formal matching-ring gluing theorem. The blueprint searches for 05ER and
matching sections returned no match. Its module is
`lean/Sheaf/AlgebraicGeometry/Morphisms/PuncturedCompletionMatchingAffineSections.lean`.
There are no statement changes, forced adaptations, or change records.

## Second reading by A4

1. Compared the delivered punctured-isomorphism module with the repository version. The
   theorem signature and visibility are byte-for-byte unchanged; the only interface addition
   is the separately recorded split-off comparison theorem and its required proof import.
   Verdict: pass.
2. Compiled both delivered modules together with `lcompile.py --all`. There are no forbidden
   declarations and no `sorry` in a definition. The sole remaining `sorry` is the named,
   documented split-off theorem `puncturedMap_basicOpen_appTop_bijective`; the target theorem
   depends on its `sorryAx` exactly because that lower node remains open. Verdict: pass.
3. Checked the split-off statement against the restrictions used by the proof and its edge
   cases (empty principal opens and nilpotent generators). It is a strictly local section-ring
   bijectivity claim, with the source and proof route documented in its docstring and DAG node;
   it does not restate the target isomorphism or choose an arbitrary gluing object. Searches in
   the library and recorded Mathlib searches found no existing declaration. Verdict: pass.
4. Read the proof top-down. It uses the affine structural-map restriction, principal-open
   basis, finite preimage affineness, `puncturedMap_over`, the split-off local comparison, and
   Mathlib's affine and target-local criteria. The unit route is retained; no unused import was
   identified and no old proof dependency is needed beyond the matching-sections construction.
   Verdict: pass.
5. Compared the updated DAG proof and dependency records with the Lean proof and checked the
   new node's required metadata, source, docstring, and declaration record. Verdict: pass.

Changed in this second reading: appended this review record only. No Lean or DAG repairs were
needed.
