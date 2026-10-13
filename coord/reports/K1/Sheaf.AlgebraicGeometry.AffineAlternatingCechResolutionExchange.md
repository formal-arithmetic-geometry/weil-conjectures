## What changed

Replaced the proposed representative-level restatement with a genuine reduction. The existing theorem `AlgebraicGeometry.affineAlternatingCech_resolution_exchange` now proves finite-product transport, termwise invertibility of the complex map, passage to the homotopy quotient, transport across the representative isomorphism, and preservation of invertibility by localization. Its signature and original docstring are unchanged.

Added `lean/Sheaf/AlgebraicGeometry/AffineOpenPushforwardExchange.lean` for the strictly smaller ordinary exchange assertion on one affine-open pushforward. Its sole theorem remains open. The item replaces its proof-only import of `AffinePushforwardBaseChange` by the proof-only import of this new module. All original public imports remain unchanged. The new module retains affine pushforward base change as its proof-plan import.

Updated the existing item's node to follow the actual Lean proof and added the affine-open node. No definitions, existing signatures, visibility, target statements, or unit routes changed. No change record is needed.

## Proved and sorry left

Hole closed: `AlgebraicGeometry.affineAlternatingCech_resolution_exchange` (node `lem-pc-s3-affine-alternating-cech-resolution-exchange`). Its proof depends on the open factor assertion below, so this is a decomposition, not a completed mathematical proof.

Hole added: `AlgebraicGeometry.affineOpen_pushforward_exchange` (node `lem-pc-s3-affine-open-pushforward-exchange`), in `Sheaf.AlgebraicGeometry.AffineOpenPushforwardExchange`. Its whole proof is `by sorry`. The docstring gives a full argument by affine base change and vertical pasting under the tensor-pullback adjunction. It involves no complex, finite product, homotopy category, or derived localization.

One original hole closed, one lower hole added: net zero. No sorry remains directly in the item's module. The rejected `AlgebraicGeometry.affineAlternatingCech_resolution_exchange_representative` and its proposed node were removed before delivery; they are not additional closures against the repository baseline.

## No longer needed

Removed the direct proof-only import `Sheaf.AlgebraicGeometry.AffinePushforwardBaseChange` from the item. It remains imported by the affine-open subproblem and remains needed in that node's proof plan. The original proof dependency `lem-weil-pbc-affine-pushforward-base-change` is now indirect through `lem-pc-s3-affine-open-pushforward-exchange`; no original dependency is discarded from the argument. No existing module or node is pruned.

Removed the proposed, unlanded representative-level theorem/node as a restatement. Redundant experimental proof imports of Mathlib product-preservation and morphism-property modules were removed after checking that the existing imports already supply these results.

## Where the brief, the DAG or earlier work was wrong

The first worker's helper unpacked the original existential hypothesis but kept the same conclusion at D. It was logically equivalent to the original obligation and isolated no mathematical substep; the previous second-reading verdict calling it strictly smaller was wrong. The existing DAG plan already identifies the affine-factor step, so the claim that it omitted a representative-level obligation was unfounded.

The remaining issue is formalizing vertical direct-image pasting and cancellation for one affine-open factor. The library's `moduleBaseChangeMap_pasting` proves horizontal pasting for successive base changes, not this vertical assertion. Searches found no existing declaration of the needed factor result. LeanSearch was unavailable (Internal Server Error); its failure is recorded rather than treated as an absence verdict.

## New nodes

`lem-pc-s3-affine-open-pushforward-exchange` in `dag/nodes/sec-picard-framework/lem-pc-s3-affine-open-pushforward-exchange.json` records ordinary exchange on one quasi-coherent affine-open pushforward. Its natural-language proof uses affine base change twice, identifies the outer exchange by transposition, and cancels invertible maps. The source, statement dependencies, proof dependencies, blueprint location, searches, creation metadata, and verbatim Lean signature are recorded. No change records.

## Second reading by K1

1. Compared every delivered module with the repository. The item changes only its proof body and one plain proof import. Its existing theorem signature is byte-for-byte identical, its public imports and docstring are identical, and it adds no data construction. The other module is new and has one public theorem. Verdict: existing interface preserved.
2. Both modules compile locally through lcompile.py in import order without warnings or errors. Checked for forbidden declarations and for holes in definitions: none. The sole remaining sorry is the whole proof of the named affine-open theorem. Explicit scratch `#print axioms` checks show only `propext`, `Classical.choice`, `Quot.sound`, and the permitted open dependency `sorryAx`. Verdict: the formal lifting proof is kernel checked, conditional on the named lower obligation.
3. Read the new factor statement and its complete proof. It removes all complex, product, derived-category and localization obligations from the original problem. In the affine case it agrees with affine pushforward base change; for zero sheaves and an empty affine scheme both sides are zero. No flatness assumption is needed because both affine exchanges hold for arbitrary base change. The finite empty-product case is covered by the proven product argument. Semantic, type-pattern, Mathlib grep, and project/upstream searches found no exact existing factor theorem; LeanSearch failed and was recorded unavailable. Verdict: a true, strictly smaller subproblem, not a restatement.
4. Read the proof from the original target downward. It uses Mathlib product comparison, naturality, componentwise isomorphism and functorial preservation of isomorphisms, leaving only the affine-factor geometry open. Removed unused experimental imports. The unit `sk-thm-picard-f-representable` and its `realized` fields are unchanged; this decomposition lies below that unit and preserves the affine Cech route. Verdict: genuine reduction with net zero holes, no claimed pruning.
5. Compared the node records with the Lean proof. The existing node now depends on the affine-open node; its steps match the finite-product and homotopy/localization proof. The new node matches the exact Lean statement and its source proof, with its own complete record. Verdict: DAG and Lean agree.

Second reading changed: removed the representative-level restatement and its node, introduced the affine-open factor obligation, proved the finite-product and homotopy/localization lifting, minimized proof imports, and rewrote the node records and report to count the result as a decomposition.
