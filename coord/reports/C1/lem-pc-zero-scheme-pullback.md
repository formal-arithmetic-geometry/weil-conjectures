1. Files written:

- `dag/nodes/sec-picard-framework/lem-pc-zero-scheme-pullback.json`: statement item, split proof, and blueprint reference.
- `dag/nodes/sec-picard-framework/lem-pc-zero-scheme-pullback-local-coefficient.json`: one new unsplit statement node; Mathlib searches found no exact match.
- `citations.json`: verbatim quotes for each cited proof step.

2. Attachments: none.

3. WANTED: none.

4. The prior attachment was not used because its abstract `Modules.pullback` conclusion did not establish the tensor-product pullback identification required by the item. The split keeps the item statement unchanged and isolates the missing local coefficient compatibility as a new node. I searched the DAG and blueprint for duplicate local-coefficient or zero-locus pullback statements and found none. The item search found only the set-level Mathlib theorem `AlgebraicGeometry.Scheme.preimage_zeroLocus`, which does not state equality of ideal sheaves; the new-node searches found only lower-level free-module pullback APIs.

## Review by C1

I read the source theorem `AlgebraicGeometry/Modules/ZeroLocus.lean`, lines 502-533. Step 1 follows its construction of affine neighbourhoods and uses the new local-coefficient statement exactly for the pulled-back free generators and coefficient. Step 2 uses the existing `lem-pc-zero-scheme-ideal-local` statement exactly for both the original and pulled-back zero loci; the remaining principal-ideal map identity is an elementary calculation from ideal span and the structure-map ring homomorphism. Step 3 is the source's final cover argument and is elementary from equality of ideal-sheaf data on an affine cover. I checked that all hypotheses (scheme morphism, invertibility, affine containment, and free generators) are present at the cited steps. I also checked the item and new statement on the identity morphism and on a principal coefficient over an affine scheme; both reduce to the same principal ideal. The rejected attachment was corrected by making the coefficient/pullback identification an explicit dependency rather than assuming the two pullback definitions coincide.

5. Nothing remains unfinished in this split; the new coefficient node is intentionally statement-only for the next stage.

## Second reading by C1

- Item statement: checked against `Hom.comap_zeroLocus` in `ZeroLocus.lean:502-533`; both sides are the same closed subschemes and the theorem assumes invertible `M,N`, an arbitrary scheme morphism `g`, and no flatness. On an identity map, on `Spec(k)` with zero or unit coefficient, and on the empty scheme, both sides agree.
- Step 1: checked against `IsFreeGenerator.exists_pullback` at `ZeroLocus.lean:388-446` and the new node. The common affine trivialization requires restricting the first generator after shrinking for the second; the revised step states this and the coefficient `b` explicitly.
- Step 2: checked against `ideal_comap_appLE` at `IdealSheaf/Affine.lean:95-105`, `Hom.ideal_zeroLocus` at `ZeroLocus.lean:491-500`, and the statements of `lem-pc-closed-subscheme-base-change-ideal-image`, `lem-pc-zero-scheme-ideal-local`, and the new coefficient node. The existing base-change node gives the ideal image; its affine sections give extension by the structure-map ring homomorphism. The principal-ideal calculation is written out. The base-change node is a generic tool from another unit, with no local replacement in this unit.
- Step 3: checked against `IdealSheafData.le_of_iSup_eq_top` at Mathlib `IdealSheaf/Basic.lean:242` and the source proof at `ZeroLocus.lean:529-533`; both ideal inclusions on the affine cover give equality by antisymmetry.
- New node `lem-pc-zero-scheme-pullback-local-coefficient`: checked hypothesis by hypothesis against the sorry-free `IsFreeGenerator.exists_pullback` at `ZeroLocus.lean:388-446`. Its conclusion is a restriction of that lemma from `g^{-1}(U)` to `V`; zero coefficients, unit coefficients over a field, the identity map, and the empty scheme give the expected generators and coefficients. It is statement-only, self-contained with the scheme, invertible-module, and pullback definition nodes, and has one TeX statement. DAG, blueprint, LeanFinder, Loogle, and Mathlib source searches found no existing node or Mathlib declaration with this scheme-local conclusion; Mathlib has general free-sheaf pullback naturality only. The source locator was corrected, and the Lean declaration was recorded as a candidate for attachment.
- Changes: cited the existing base-change ideal node in step 2, expanded steps 1-3, added exact citation quotes, corrected the new node source locator, and recorded the sorry-free Lean candidate. The original item statement and the original review remain unchanged.
