## Worker report

Files written:
- `dag/nodes/sec-trace-formula/lem-trf-finite-stage-span-pointed-etale-refinement.json`: statement, split in four steps; not a Mathlib leaf.
- `citations.json`: a verbatim statement quote for every dependency of every step.

## New nodes

None. No new Mathlib leaves. All ingredients were already in the DAG, so no statement-only nodes or copies of clauses were introduced.

## Attachments

None for this item. Searches of `lean/WeilConjectures/` for the exact blueprint id, `finite.stage.span`, and pointed/span terminology found no exact project declaration. The existing closed declarations `AlgebraicGeometry.Etale.exists_stage_on_affine_chart` in `EtaleAffineChartDescent.lean` and `AlgebraicGeometry.Scheme.Pullback.exists_residueField_equiv_ofPointTensor` in `FibreProductPointResidueField.lean` supply ingredients, not the complete span theorem.

## WANTED

None. The named `coord/dag-sync.md` is absent in this read clone; the explicit current brief supplies the applicable live/shared-repository instructions.

## Source and blueprint audit

The item statement is unchanged. I read Stacks `more-morphisms.tex`, Tag 0GDX, `lemma-relative-map-approximation-pre`, especially the paragraph constructing the span at a finite stage and the displayed chain of residue fields. I also read `limits.tex`, Tag 07RP, `lemma-descend-etale`, with Situation 081D, and `algebra.tex`, Tag 0H9M, `remark-local-ring-fibre`. The latter compares the local ring of a fibre with a quotient; it does not on its own assert the arbitrary base-change comparison needed here. I therefore use the existing general canonical residue-field theorem for fibre-product points, Schemes Tag 01JT (`lemma-points-fibre-product`), whose full statement and source proof I read. This is a proof refinement, not a statement correction.

The 0GDX wording about residue fields is justified here by an explicit tensor calculation, rather than interpreting abstractly isomorphic fields as canonically identical. The supplied stage arrows are arbitrary initially. Their local finite presentation must be proved before 07RP is applied; this is now explicit in step 1.

I read the chapter and unit records and latest `literature/blueprint/latest/blueprint/sec-trace-formula/sk-i-curve-zero/lem-trf-local-term-locality.md`. The current ancestor is about contracting correspondences and no longer contains the historical nodal approximation input. The item's preserved `blueprint.from.place` already records this historical role through the fixed-family span node; the split report names that history explicitly. This delivery does not propose replacing a current unit step by an approximation route.

## Searches and duplicates

I searched the whole DAG by tags 07RP, 0H9M, 0GDX and by finite-presentation, etale descent, fibre and residue-field terminology, then read the statements of all dependencies used. `tools/blueprint_refs.py ancestor` returned `lem-trf-local-term-locality`. Whole-blueprint searches for `descend etale`, `07RP`, `0H9M`, `finite-stage span`, `pointed etale`, `residue fields`, and `finite presentation` found no blueprint node stating this item. The related finite-data and pointed-neighbourhood nodes do not state simultaneous pointed refinement of the supplied arrows. Accordingly `same_as` remains empty.

Five fresh msearch queries were executed and their results read; the exact tool/query records were appended to `mathlib_searches` from the command's own `searches.jsonl`. Both LeanFinder phrasings, Loogle, LeanSearch, and source grep were used. The open-immersion residue-field instance at Mathlib `AlgebraicGeometry/ResidueField.lean:177` does not apply to these projections. `Morphisms/LocalFlatDescent.lean:47–48` concerns fpqc descent, not inverse-limit eventual etaleness. The tensor and prime-correspondence hits in `PullbackCarrier.lean` and `RingTheory/Etale/QuasiFinite.lean` do not state the whole item. In particular `Ideal.fiberIsoOfBijectiveResidueField` is a correspondence of primes, not the needed canonical scheme residue-field assertion. The already closed DAG node supplies that assertion. No search was recorded as unavailable when it succeeded, and the inherited historical searches were retained.

## Not duplicates

No new nodes; there are no new/existing pairs to distinguish. The existing affine-chart descent, map-over-base finite-presentation, and fibre-product point residue-field nodes are cited directly.

## Review by Q22

I reviewed the actual four proof steps against their cited statements, with the item and the Stacks sources open.

Step 1 uses `lem-weil-pbc-fibre-product-affine-spectra` precisely for affineness of the pullbacks. It uses clause (3) of `lem-weil-pbc-qcqs-morphism-permanence` for finite-presentation base change, not merely a definition of that property. `lem-a1-map-over-base-finite-presentation` asserts local finite presentation of an arbitrary map from a locally finitely presented source to a locally finite type target over the same base. Its hypotheses hold: V_r is finitely presented over S_r, and P_r and Q_r are too, hence are locally finite type by their finite polynomial generators. The result is not being inferred from etaleness at stage r. I read Morphisms 01TS and 02FV(1), including the algebra argument for 02FV. This latter DAG node is already marked Lean-closed; it is a generic permanence tool, not a replacement route through another unit.

Step 2 uses `pqf-lem-affine-local-target` to establish affine transitions: the whole affine target is a one-member affine cover and its preimage is the affine source. The affine-chart descent statement explicitly gives etaleness at every later stage. Its W, V, U are the whole affine base, target and source, so their containment conditions are automatic; the local finite presentation condition is from step 1, and the limit morphisms are the actual pullbacks specified in the item. I read both this node's statement and its existing project declaration. Directedness gives a common upper bound of the two thresholds. I chose this persistent affine-chart result instead of citing a one-stage theorem and leaving persistence uncited.

Step 3 uses only the fibre-product universal property for the canonical identification of T_B with T_j times over S_j B, and the actual conclusion of `lem-weil-pbc-fibre-product-point-residue-field`: its canonical tensor map induces the residue-field isomorphism and is compatible with both inclusions. It is not just the points-bijection node, which would omit the required clause. For E=kappa(t_j), K=kappa(b_j), and L=kappa(b), the hypothesis makes the actual map lambda:K to L invertible. I checked the explicit inverse tensor map on a pure tensor using the balancing relation. Thus E tensor_K L is a field; a unital map from it into kappa(t) has zero kernel; the cited theorem identifies that map with the field isomorphism. Its compatibility clause makes the map from E exactly the projection residue map. This argument works for each of the three indicated points without a finite-residue-extension assumption. It is a short specialization of the existing general theorem, so creating a separate base-change residue lemma would be unnecessary. The step is 1081 characters before any formatting, well below the long-step threshold.

Step 4 is elementary: the pullback projection equations give the two point equalities, and composition of local homomorphisms descends to composition on residue fields. The definition of residue fields explicitly supplies these induced maps. Solving the two commuting equations for the stage maps expresses each as a composite of three field isomorphisms. I checked their directions: c_V alpha_j# = a_B c_P, not its reverse. This proves precisely the two canonical maps in the conclusion.

I checked small cases: a singleton directed set gives the original arrows; all three models equal to the base with identity arrows give identity residue maps; points with transcendental residue extensions still satisfy the tensor argument, since no finite-dimensionality was used. Empty V_B cannot satisfy the supplied-point hypothesis, rather than requiring an extra nonemptiness assumption. Empty schemes elsewhere and non-Noetherian bases are not excluded. Dropping the base residue-field isomorphism would invalidate the tensor collapse (a nontrivial field extension already shows this), which confirms where that hypothesis is used. All conclusions persist for every j above k, while the residue comparisons actually hold for all j above r.

Against delivery-errors B–E: no new unsearched or hollow node; every non-elementary fact is an existing cited statement; no citation uses a proof instead of a statement; no new clause restates the item; no circular argument or new hypotheses; every canonical identification and residue-field equation is written. The statement and its dependencies were preserved. `citations.json` was checked for literal containment in each cited statement. All four steps are shorter than 2000 characters. A server `review_split` check passed before this report was written. The full dry run and direct delivery follow.

## Unfinished work

None in the stage-1 split. No Lean was written and no compiler, Lake or build command was run.
