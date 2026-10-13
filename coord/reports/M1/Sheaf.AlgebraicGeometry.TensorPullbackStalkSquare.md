## What changed

Second reading repaired the previous submission rather than accepting its replacement of the existing theorem. Every existing declaration signature in TensorPullbackStalkSquare.lean is byte-for-byte unchanged. Its original public imports are retained. Two new modules supply its proof, through a single plain import of PinnedTensorSquareCompatibility:

- PinnedStalkTensor proves AlgebraicGeometry.exists_pinned_stalk_tensor by the existing degreewise comparison and differential compatibility lemmas.
- PinnedTensorSquareCompatibility leaves only AlgebraicGeometry.pinned_tensor_pullback_stalk_compatibility open. It fixes the source and target coordinate isomorphisms to the canonical constructions; it has no existential isomorphism conclusion.

The existing theorem constructs the existential witnesses from the fixed comparison isomorphisms and applies the remaining equality. The earlier unused ModuleTensorPullbackStalkSquare module and node have been removed from this submission. The corrected node now describes the proved pinned comparison. The existing chain-square declaration is registered under an assembly node; its caller's DAG proof dependency is updated, without changing its Lean file.

## Proved and sorry left

Closed body hole: AlgebraicGeometry.exists_tensor_pullback_stalk_square, registered by lem-pc-tensor-pullback-stalk-square-assembly. This is a decomposition, not an axiom-free proof: it uses the one new compatibility hole.

New proved declaration: AlgebraicGeometry.exists_pinned_stalk_tensor (lem-pc-tensor-pullback-stalk-square). This proof closes the first worker's pinned-construction hole and uses only the existing proved canonical module comparison, degreewise comparison, differential compatibility, and Mathlib's component assembly.

Added hole: AlgebraicGeometry.pinned_tensor_pullback_stalk_compatibility (lem-pc-pinned-tensor-square-compatibility). It is the sole remaining direct sorry in the three delivered modules. Its complete generator/coproduct proof and source are in its docstring and node. It verifies the equation for already constructed isomorphisms and does not reassert the original existential conclusion.

Against the repository baseline, one hole is closed and one added: net zero. No whole chain-square proof or positive ledger progress is claimed. Relative to the first worker's sandbox, the pinned-construction hole is proved and the unused module-helper hole is removed. No sorry is in a definition; no data is chosen from the deferred compatibility theorem.

## No longer needed

No existing public import is removed, and no module is claimed pruned from the target import closure. The old direct proof dependencies are accounted for as follows: def-pc-derived-pullback-tensor-comparison and lem-weil-pbc-module-pullback-tensor remain necessary to state/calculate the lower compatibility equation; def-pc-single-complex-base-change-stalk-condition still supplies the actual comparisons. The unpinned lem-pc-stalk-tensor-complex route is replaced by lem-pc-stalk-tensor-complex-degrees and lem-pc-stalk-tensor-complex-differential, because the proof needs the prescribed degreewise equation. StalkTensorComplex is not imported by the new construction. Its other users remain, so this is not a closure pruning claim.

The first worker's unused ModuleTensorPullbackStalkSquare helper, its unused imports, and its node are not delivered. Neither new proof imports nor proof-dependency changes bypass a realized unit step.

## Where the brief, the DAG or earlier work was wrong

The prior sandbox removed exists_tensor_pullback_stalk_square while TensorStalkChainCoordinates still applied it. It left the requested pinned theorem sorry, used a stale exists_pinned_stalk_tensor_base signature in its node, retained an irrelevant module-level helper, and had an incomplete change record. The second reader restored the original theorem's exact signature, proved the pinned theorem from existing library lemmas, and isolated only the remaining chain equation. The derived-chain hypotheses in the retained statement have not been weakened or removed.

## New nodes

lem-pc-tensor-pullback-stalk-square-assembly registers the existing unchanged declaration and its genuine existential assembly reduction. Its isomorphism-existence work uses the proved pinned comparison; only the equation is delegated.

lem-pc-pinned-tensor-square-compatibility registers the remaining equality for the explicitly constructed comparisons. It is the equation-verification step, strictly below the original existential construction, and has one named theorem with sorry, a complete proof in words, and three kinds of searches.

Change record: coord/changes/tensor-pullback-stalk-square.md.

## Statement corrected

Reviewer X-56534 requested that lem-pc-tensor-pullback-stalk-square describe exists_pinned_stalk_tensor(Y,z) and its exact injection formula. It now does, with a compiled proof using the canonical chosen module comparison. Its sole existing citer, lem-pc-tensor-stalk-chain-coordinates, remains true and its proof dependency is retargeted to the assembly node carrying the same existing Lean declaration. No adaptation of a consumer Lean file is required and no Challenge.lean statement or definition is changed.

## Second reading by M1

1. Compared every delivered module with the repository and checked all existing declaration signatures with the declaration parser: byte-for-byte identical. The prior accidental deletion is repaired. The corrected DAG statement and added interfaces are declared in the change record; the existing caller still finds its original theorem.
2. All three files compile individually through lcompile.py, within the 60-second limit. Exactly one direct sorry remains, the reported public named compatibility theorem. Scanned all files for axiom, unsafe, opaque, implemented_by, extern and definition holes: none. Axiom checks are recorded below.
3. Read the pinned proof and the remaining equality from their statements down to the canonical module interfaces. The pinned comparison has a genuine proof; its prescribed component equation determines its maps on all coproduct injections. The compatibility statement only checks the equation for these already constructed isomorphisms; its proof in words reduces to the known germ and pure-tensor formulas, then linear generation and coproduct extensionality. Zero rings, zero factors, unbounded degrees and noninvertible a impose no missing hypotheses. Repeated searches with different words using leanfinder, loogle and grep, and recorded the LeanSearch service failure; no ready combined compatibility theorem was found. The existing degree and differential lemmas were used to avoid a redundant construction hole.
4. The construction uses the shortest available proved component lemmas and Mathlib isoOfComponents. Original public imports remain necessary for the original signature. The item has one new plain proof import; the compatibility module's pinned-comparison import is public because its statement uses that theorem. Every former dependency is accounted for above. Read dag/units/sk-thm-picard-semicon.json: neither this node nor these lower nodes realizes a unit step; realized and the unit route are unchanged.
5. Checked Lean declaration names and full signatures against the node records; proof_deps are exactly the union of proof-step uses. The corrected pinned node follows the actual construction; the assembly node follows witness construction; the lower node and its docstring specify the genuine remaining equation calculation. The caller's DAG now points to the assembly declaration it actually uses. No extra body holes or unused module helper remain.

Changes by second reader: restored the original API; proved the pinned comparison; removed the unused module-level helper; split off only the equation-verification step; corrected node signatures, proof routes and the citer dependency; rewrote the incomplete change record and corrected progress accounting.

Axiom verification: #print axioms exists_pinned_stalk_tensor reports exactly propext, Classical.choice and Quot.sound. The compatibility theorem and the original chain-square assembly report those three plus sorryAx, attributable to the single named compatibility hole. The unchanged TensorStalkChainCoordinates caller also compiles against the delivered modules (16.1 seconds).
