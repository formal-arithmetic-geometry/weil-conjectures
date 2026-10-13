## What changed

Preserved the complete signature and docstring of
`AlgebraicGeometry.Scheme.picardCupProduct_baseChange_square` and closed its original hole
by a genuine decomposition of the three steps of its argument.

`PicardCanonicalBaseChange` constructs tensor-composition comparisons, the top map
`X_T → X_W`, the non-iterated direct-image base-change morphism, and the canonical
pullback-dual comparison. These are real constructions. Its proved generic assembly
lemma derives the transpose square from a commuting square of pairings; the proof
includes tensor-comparison naturality, uncurrying, contravariant duality, and cancellation.
The internal uncurrying and transpose helpers are private and fully proved.

`PicardDirectImageBaseChangeIso` proves transport from the iterated fibre product using
`moduleBaseChangeMap_pasting` and `moduleBaseChangeMap_open_square_isIso`, including the
explicit pullback-projection identities. `PicardTensorDualComparisonIso` proves
invertibility of the specified canonical comparison from finite duality and
`ExactPairing.map`; it does not choose an unspecified dual isomorphism.

The one remaining step is stated in `PicardCupPairingBaseChange`: an equality of the
actual cup pairings under the actual direct-image base-change morphisms. It assumes
neither their invertibility nor the rank condition. The original theorem combines the
proved comparison invertibility, this pairing equality, and the proved generic assembly.

All five delivered modules compile together in import order without warnings. Existing
library modules outside the assigned item are untouched. A change record documents the
additive support API in `coord/changes/j1-picard-base-change-comparisons.md`.

## Proved and sorry left

Closed the original hole in
`AlgebraicGeometry.Scheme.picardCupProduct_baseChange_square`
(node `lem-sc-picard-cup-product-base-change-square`).

Fully proved the new declarations
`AlgebraicGeometry.Scheme.Modules.picardBaseChangeSquare_of_pairings`,
`AlgebraicGeometry.Scheme.picardDirectImageBaseChangeMap_isIso`, and
`AlgebraicGeometry.Scheme.picardTensorDualComparison_isIso`, with all their private
helpers proved. There are no holes in any definition.

Added exactly one hole:
`AlgebraicGeometry.Scheme.picardCupPairing_baseChange`
(node `lem-sc-picard-cup-pairing-base-change`). Its whole proof is `:= by sorry`, in its
own module, with the source and the full mate-calculation proof in its docstring.
This is a decomposition: one original hole closed, one strictly lower hole added,
net zero, rather than a claim of a complete axiom-free proof of the target.

The new pairing statement was checked on zero modules, rank-zero bundles, identity
base change, and the empty base. The construction and proof use no reducedness or
flatness hypotheses. The pairing statement is independent of finite local freeness
and invertibility of either direct-image base-change morphism.

## No longer needed

Removed the target's proof import of
`Sheaf.AlgebraicGeometry.PullbackDualFiniteLocallyFree` and its dependency
`lem-ag-pullback-dual-finite-locally-free`. Its assertion that some dual isomorphism
exists is insufficient to prove compatibility for a specified morphism; the delivered
route proves invertibility of the canonical evaluation transpose directly.

The planned uses of `nonempty_tensorPullbackId` and `nonempty_tensorPullbackComp`
(node `lem-pc-module-pullback-identity-composition`) are unnecessary. The explicit
composition comparison instead uses ordinary `Modules.pullbackComp` and the proved
`picardTensorComparison`. The module `TensorPullback` itself still supplies the tensor
pullback construction through existing imports and is not claimed pruned.

Removed `Sheaf.AlgebraicGeometry.ModuleBaseChangeMapPasting` from the target's direct
imports, but retained it as a proof import of `PicardDirectImageBaseChangeIso`; neither
its module nor its node is pruned from the delivered argument. The cup-product-map and
rank-condition public imports remain unchanged. No other existing module is claimed
removed from the target closure. For completeness, the old proof dependencies
`def-sc-picard-cup-product-map` and
`lem-weil-pbc-module-base-change-map-open-restriction` remain used through the
canonical-comparison and pairing modules, even though they are no longer direct
parent-node proof dependencies. Together with the retained pasting node, these
account for every old dependency not listed as unnecessary above.

## Where the brief, the DAG or earlier work was wrong

The previous attempt's unresolved comparison-isomorphism glue is now constructed and
proved. The original pullback-duality dependency supplied only an existential
isomorphism, which cannot be chosen and then assumed compatible with evaluation.
The new canonical comparison fixes this gap while preserving the original statement.

A preliminary uncurried existential restatement was rejected during this work and is
absent from the delivery. The remaining theorem is instead only the pairing-naturality
step, without rank or invertibility assumptions; the isomorphism construction and the
transposition argument are separately proved.

Concrete internal-Hom rewrites initially made the kernel unfold large fibre-product
expressions. The proved generic transpose/assembly interface isolates those operations
on arbitrary modules. The resulting assigned module compiles in about five seconds;
all support modules are below the single-file time limit. No compiler limit was raised.

Mathlib/library and blueprint searches found no duplicate canonical-map theorem.
LeanSearch was unavailable; LeanFinder returned free-pullback comparisons, and direct
search found the tensor, currying, finite-duality, and mate-pasting lemmas actually used.
The source was checked at Stacks Tags 0BDP, 0FNV and 08HY. The omitted categorical details
are marked as agent-written expansions in the new nodes. No unit-level route is changed.

## New nodes

`lem-sc-picard-canonical-base-change-comparisons`, in
`PicardCanonicalBaseChange`, records the explicit constructions and the proved generic
assembly of transpose squares.

`lem-sc-picard-direct-image-base-change-iso`, in
`PicardDirectImageBaseChangeIso`, records the proved transport of invertibility from the
iterated fibre product to the direct one.

`lem-sc-picard-tensor-dual-comparison-iso`, in
`PicardTensorDualComparisonIso`, records the proved invertibility of the specified
pullback-dual comparison.

`lem-sc-picard-cup-pairing-base-change`, in `PicardCupPairingBaseChange`, is the sole new
unproved statement and the next item. Each new node has a source, proof steps, search
record, Lean signature, and the original item's chapter/unit/blueprint ancestry.

The parent node's proof and proof dependencies follow the delivered argument. The
additive API change record is `coord/changes/j1-picard-base-change-comparisons.md`.


## Second reading by J1

1. **Interfaces: PASS.** Read the diff of every delivered module against the
   repository. Only PicardCupProductBaseChange existed there; its theorem signature,
   docstring, visibility and both public imports are byte-for-byte unchanged.
   The four support modules are additions, documented in the additive API change
   record. No target or existing definition is changed.

2. **Proofs and constructions: PASS as a decomposition.** Compiled all five files
   in dependency order through lcompile.py, without errors or warnings. Read the
   tensor comparison, transpose cancellation, isomorphic-top pasting and exact-pairing
   proofs. A separate scratch module printed axioms for all nine public declarations:
   the four constructions and three proved support theorems use only propext,
   Classical.choice and Quot.sound; the pairing theorem and parent theorem additionally
   use sorryAx. Text inspection found exactly the reported whole-proof sorry and no
   prohibited declaration or hollow definition. No arbitrary witness of an unproved
   existence statement is introduced. The scratch module was removed.

3. **Split statement: PASS.** Read picardCupProductMap, picardPushforwardPairing,
   its proved counit formula and the adjoint definition of moduleBaseChangeMap.
   The remaining equality concerns their specified maps. It isolates the compatibility
   of pairings, without the parent's rank hypothesis or either base-change invertibility
   assumption; it neither constructs the two isomorphisms nor repeats the parent's
   existential conclusion. Zero E gives zero pairings, empty schemes give unique maps,
   and identity base change reduces to the unit/counit and comparison identities.
   Arbitrary E is legitimate: evaluation and the mate calculation require no dual
   basis. The full natural-language proof and matching node are present. Independently
   searched LeanFinder for evaluation pairing naturality via Beck-Chevalley mates,
   Loogle for uncurry, and the library for pairing/evaluation and base-change declarations.
   Results supplied generic naturality and uncurry lemmas, not this equality.
   Re-read Stacks Tags 0BDP and 0FNV; the categorical expansions are correctly identified
   as agent-written. Finishing the remaining mate/coherence calculation is substantial,
   not a few-minute application of a discovered lemma.

4. **Route and pruning: PASS.** The proof uses the existing pasting, open-square,
   finite-duality and closed-category machinery rather than restating the item.
   Each public support import is needed by a signature or construction; imports used
   only in proofs are plain imports. Checked every old proof dependency: only the
   existential pullback-duality node and the tensor identity/composition existence node
   are unnecessary; the cup-map, rank-condition, open-restriction and pasting nodes
   remain in the argument. The unit sk-prop-av-cube and its realized fields are unchanged;
   this is a refinement below its route, with no unit step bypassed. The accounting is
   one upper hole closed and one lower hole added, net zero, not an axiom-free target proof.

5. **DAG: PASS.** Read all five delivered nodes and the parent-node diff. Existing
   node edits are confined to proof, proof_deps and proof_origin. Their steps and used
   node unions match the written proofs or, for the open pairing node, its documented
   next proof. New nodes include source, searches, creation record, ancestry, Lean
   signature and split status. The generic assembly and two invertibility results are
   proved, and only the pairing node is left open.

**Second-reading changes:** completed the No longer needed accounting for the two
retained indirect dependencies and added this independent review. No Lean proof,
statement, construction, import or node needed repair.
