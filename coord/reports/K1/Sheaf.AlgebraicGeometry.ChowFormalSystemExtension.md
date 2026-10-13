## What changed

Replaced the sole hole in `Sheaf.AlgebraicGeometry.ChowFormalSystemExtension` by an
explicit construction. Its statement and public imports are unchanged. Proof imports
supply formal pullback, support constancy, support pullback, coherent finite-type
comparison, proper inverse-image support, proper closed-image support, and the new
closed-support direct-image object-condition lemma.

The proof obtains the pulled coherent system from the uniquely specified formal
pullback functor, constructs its closed ambient support, defines H using the actual
termwise pushforward (objects and transitions), and builds the system isomorphism
by uniqueness of left adjoints and the invertible restriction/direct-image counit.
There is no arbitrary selection of extension data. Existing proof-dependency
statements that contain holes are used as intended by stage 3.

## Proved and sorry left

Closed: `AlgebraicGeometry.exists_chow_formal_system_extension`
(lem-weil-pbc-chow-formal-system-extension), proved from the stated dependencies
and one strictly smaller new lemma. No direct hole remains in the item's module.

Added: `AlgebraicGeometry.coherentFormal_pushforward_of_closed_support`
(lem-weil-pbc-formal-system-closed-support-pushforward), in
`Sheaf.AlgebraicGeometry.FormalSystemClosedSupportPushforward`.
This only proves the object conditions for an already specified direct-image
inverse system with a fixed closed ambient support. It has no base, properness,
formal pullback, existence, or restriction-isomorphism conclusion. The upper proof
establishes all these other parts in Lean. This is a decomposition: one upper
hole closed and one lower hole added, net zero. There are no other holes added.

Both delivered modules compile together with lcompile.py. Edge cases of the new
statement: for empty Y or empty T, support assumptions force the source terms to
be zero and the direct-image system is zero; for j the identity it is precisely
the input object condition; for the unit ideal every term is zero by annihilation.
The argument requires no completeness, affine base, or algebraization.

## No longer needed

No original imports are removed. No original proof-dependency nodes are pruned
from the combined route. The original direct dependencies
`lem-weil-pbc-pushforward-coherent-on-open` and
`lem-weil-pbc-module-pullback-ideal-power-product-image` are no longer called by
the upper proof; both remain in the new lemma's planned proof dependencies.
`lem-weil-pbc-module-restriction-open-immersion-colimits` is still used upstairs
for the Mathlib restriction adjunction and also in the lower lemma's plan.
These are relocations, not pruned modules. Coherent pushforward on an open is
already proved in the repository; it is not an open hole. The actual upper proof adds
pqf-lem-coherent-ft-locnoeth to convert level-zero coherence to the hypotheses of
the support pullback theorem. No blueprint unit statement or proof step is bypassed.

## Where the brief, the DAG or earlier work was wrong

The original node's step 3 describes a substantial locality verification without
an applicable combined Lean declaration. The new lemma isolates that verification;
it does not restate the extension theorem. The original node does not explicitly
name the coherence/finite-type comparison needed for the support theorem; the
updated proof dependencies do.

The cited local Stacks tex files are absent on this machine. Read the official
source pages https://stacks.math.columbia.edu/tag/088E (extension paragraph after
Chow's lemma) and https://stacks.math.columbia.edu/tag/0CYJ. The docstring and node
spell out the locality details omitted by the sentence asserting that the extended
system is an object of Coh. LeanSearch returned Internal Server Error; recorded as
unavailable. LeanFinder returned restriction and adjunction results but no matching
formal-system direct-image theorem. Grep found none. Blueprint searches for
formal system closed support and 0CYJ found no duplicate.

## New nodes

`lem-weil-pbc-formal-system-closed-support-pushforward` records the object-condition
verification for the concrete termwise direct image, following the extension
paragraph of Stacks 088E and coherent pushforward lemma 0CYJ. Its new module is
`lean/Sheaf/AlgebraicGeometry/FormalSystemClosedSupportPushforward.lean`.
The new statement is strictly smaller than the extension theorem: the given
system and fixed closed support are input, and only the adic object predicate
on a specified functor is concluded. No existing interfaces changed and no
change record is required.

## Second reading by K1

1. Interface check: PASS. Compared the delivered extension module with its repository
   version using diff. Its existing declaration signature and docstring are byte for
   byte unchanged. The only additions are seven plain proof imports and the proof
   body. The helper is a new module with one new theorem. No definition, target,
   existing visibility or public import changed; no change record is needed.
2. Proof check: PASS as a decomposition. Both modules compile in import order with
   lcompile.py, without warnings or errors. The extension module has no direct sorry;
   the helper's sole sorry is the whole proof of the public named theorem listed above.
   Scratch-copy #print axioms checks of both declarations show only propext,
   Classical.choice, Quot.sound and sorryAx. There are no prohibited declarations,
   trust bypasses or hollow definitions. The chosen pullback functor is specified by
   its equality after full-subcategory inclusion; the chosen support sets are specified
   by their carrier equalities. H is the actual termwise direct image, not an arbitrary
   witness from an unproved existence assertion.
3. Split statement check: PASS. Read IsCoherentFormalModule's three clauses and the
   complete helper docstring argument, and checked Stacks 088E's extension paragraph
   and 0CYJ directly. On the open image all conditions are transported from F; on the
   complement of T all terms are zero. Annihilation and the canonical quotient factor
   are local, including their equations with the original transitions. Checked empty
   Y, empty T, identity j, the unit ideal (zero terms), and the zero ideal (isomorphic
   transitions). No extra properness or completeness is needed. Independent searches
   using "adic inverse systems direct image extension by zero supported away from
   boundary", Loogle "pushforward", "IsCoherent", and word-boundary searches for
   adic/formal systems in Mathlib found no matching theorem. Searches in lean/ and
   the upstream source found no duplicate: closedImmersion_formal_pushforward_conditions
   applies to a different class of immersions; restriction results give only the
   conditions on the open. Closing this helper requires substantial support transport
   and local ideal-product/cokernel comparisons, not a few-minute existing-lemma proof.
4. Route and pruning check: PASS. Read the imported dependencies, checked every new
   proof import is used, and compared the old and new proof_deps. The support
   pullback/constancy and proper-image route is retained. The old pushforward and
   ideal-product nodes move into the helper's plan as explicitly listed under
   No longer needed; no module is pruned. Read dag/units/sk-thm-p1.json realized:
   neither this auxiliary node nor its helper replaces any realized statement or
   step, and the surrounding unit route is unchanged. No shorter existing theorem
   supplies the whole extension or the helper's combined object conditions.
5. DAG check: PASS. The updated extension node's steps match the support construction,
   ideal equality, concrete H and adjunction-counit isomorphism in Lean. Its dependency
   list is the union of its steps. The helper node has the source, complete proof plan,
   statement dependencies, all required search/creation/blueprint fields and its exact
   Lean signature (normalized whitespace); its dependencies describe its remaining
   proof obligation. Its assertion is strictly part of the extension argument and
   contains no existence or restriction-isomorphism conclusion.

Second reading changed only this report: corrected the description of relocated
proof dependencies and the already proved coherent pushforward lemma, and recorded
these independent checks. The Lean proof and nodes needed no repair. One upper hole
closed and one smaller lower hole added remains a decomposition, net zero holes.
