# Stage-1 delivery: lem-sfb-unitriangular-coordinate-filtration

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-unitriangular-coordinate-filtration.json`: statement, now split into seven steps. The statement is unchanged. Mathlib does not state this group-scheme filtration, its coordinate quotients, or the Borel conjugation characters.
- `citations.json`: 26 quotations, one for every step/node incidence, verified against the current repository statements.
- `report.md`: this report.

There are **0 new nodes and 0 new Mathlib leaves**. Existing Mathlib leaves supply polynomial-projection flatness, affine-source separatedness, affine-morphism permanence and fpqc descent of representable functors. The additional sandbox files `milne.txt`, `write_split.py`, `refine_split.py`, and `searches.jsonl` are reading, preparation and search records, not DAG deliverables.

## Attachments

None. Searched `lean/WeilConjectures/` for the blueprint tag, `unitriangular`, `Unitriangular`, `upper triangular`, and related terms. The few matrix and sequential-colimit occurrences do not state the item. No sorry-bearing declaration is claimed as finished.

## WANTED

None. Read the local Milne PDF and local Stacks sources. No SGA source is used.

## Errors, changes and route

No statement dispute. The coordinate order, normality in the upper triangular group, one-coordinate additive quotients and diagonal weights agree with Milne, *Algebraic Groups* (2017), Example 6.49(a)--(c), printed pp.136--137. I also read Theorem 16.21 and its proof on printed p.330, which uses exactly these coordinate quotients.

The imported statement was retained byte for byte. Its statement dependencies now explicitly include flat morphisms, local finite presentation, the fppf site and sheafification, notions already present in the statement. The previous unsplit node had no proof; none was discarded. The five inherited Mathlib search records are preserved; five actual Q58 searches were appended from `searches.jsonl`. Two semantic phrasings, Loogle and grep were checked. The hits concern abstract central series, modular-form subgroups, or multiplication of block triangular matrices, not this item. I read the relevant block triangular multiplication and abstract central-series definitions in Mathlib.

Read the chapter and unit records and the latest blueprint's `sk-thm-sf-ctf-stability-direct-images.proof.md`, at snapshot `main-20261023-1620`. This remains supporting algebraic-group work on the inherited alteration chain; no unit or chapter route was changed and no unit realization was claimed. The ancestor command returns `None` for this existing chain. Its inherited `blueprint.from.node = null`, concrete `from.place` and `via` list are retained. Searches of the whole imported blueprint for `unitriangular`, `upper triangular`, `affine space` and `polynomial projection` found no node stating the item; the two Engel nodes about endomorphisms of vector spaces are different. The related DAG nodes for a triangular diagonal kernel and for rational fixed vectors use this filtration, and cannot serve as proofs of it.

During self-review I repaired the finite-presentation step: the finite polynomial presentation supplies local finite presentation, but the global claim also needs quasi-compactness and quasi-separatedness. The final step now explicitly cites the three existing affine-morphism leaves giving separatedness of the affine target, affineness of the map and the required two properties. I also replaced generic definition quotations with the actual closed-subgroup, group-of-points and multiplicative-group clauses used by the respective steps.

## Unfinished work

None in this one-level split. There are no new statement-only nodes to split later. No Lean file was written and no compiler, Lake or build command was run. The shared repository and launcher were read only; all written files are under the assigned sandbox.

## Not duplicates

No new nodes were created, so there are no new/existing node pairs. In particular, polynomial-projection flatness reuses `lem-nagata-polynomial-projection-flat`; representable descent reuses `lem-weil-pbc-fpqc-representable-descent`. I initially considered the more general algebraic-space sheaf result but found and used this existing scheme result instead.

## Review by Q58

I checked the split against delivery-errors B--E with the item, every cited statement and the relevant sources open. The mathematical review is as follows.

1. Step 1 uses the actual coordinate ring and R-point description of `def-sc-general-linear-group`, the polynomial universal property in `def-weil-pbc-mv-polynomial-ring`, contravariance in `def-weil-affine-spectrum`, the affine quotient-ring criterion in `def-weil-closed-immersion`, and finite type in `def-weil-finite-type-morphism`. The determinant's upper triangular expansion forces only the identity permutation to survive. Commutativity is precisely what makes each diagonal entry a unit when their product is a unit. Imposing coordinates therefore gives the claimed polynomial rings without losing nilpotent test points. The finite lists of coordinates also verify finite type. This is an explicit coordinate calculation, not an appeal to a new lemma restating the construction.

2. Step 2 uses the group-of-points definition in `def-sc-group-scheme`, the closed-subgroup criterion in `def-sc-group-scheme-subgroup`, and the matrix operations of `def-sc-general-linear-group`. The finite geometric inverse is verified by telescoping. Every product term contributing to a killed coordinate contains a smaller-height entry, which is killed. The same observation applies to every chain in a power. Thus the actual group laws restrict over every algebra; no reducedness, perfectness or algebraic closedness is assumed.

3. Step 3 uses the triangular matrix operations and the normality-on-every-algebra criterion of those same definition nodes. The displayed conjugation sum supplies both normality and the weight formula. For a proper interval inside (a,b), the height is strictly smaller; the tie-breaking by increasing row never changes that observation. At an already killed pair, the full-interval term vanishes too. At the next pair, it is exactly the surviving diagonal-weight term. This is the argument for normality, not a citation to another node's proof. Computing b inverse by its diagonal part and a finite geometric inverse is valid over arbitrary commutative rings.

4. Step 4 uses the matrix operations, the additive Hopf-coordinate description in `def-sc-gm-ga`, the fibre-product kernel definition in `def-sc-group-scheme`, and the affine and polynomial universal properties. The intermediate product terms have strictly smaller height, so p_r is additive. The root-matrix section is genuinely a homomorphism since its matrix unit squares to zero. The displayed tensor-product coordinate ring proves equality of scheme-theoretic kernels, not merely equality on field-valued points.

5. Step 5 applies `lem-nagata-polynomial-projection-flat` with B=k[t] and precisely the remaining finite variable set. Its statement allows every commutative coefficient ring and any variable set, including the empty one. I read its Mathlib match and the monomial-free-module source. The actual section proves surjectivity. `def-sbc-locally-finite-presentation` supplies both the finite-presentation-at-a-point criterion and the additional global requirements. For those requirements, `lem-weil-pbc-affine-source-morphism-separated` applies to the affine target's structure map, `lem-weil-pbc-affine-source-separated-target-affine-morphism` then applies because the source is affine and the target separated, and clause (3) of `lem-weil-pbc-affine-morphism-permanence` gives quasi-compactness and quasi-separatedness. Their statements supply exactly these conclusions. I read Stacks morphisms.tex, labels lemma-affine-separated (01S7) and lemma-affine-permanence (01SG), in addition to the flatness and presentation sources. No smoothness result or unstated flatness criterion is used.

6. Step 6 first proves the quotient-presheaf identification explicitly, using the homomorphism and section already constructed, with kernel from step 4. It then uses the actual morphism-gluing conclusion of `lem-weil-pbc-fpqc-representable-descent`, not full faithfulness of a descent functor or a sheafification definition. I read descent.tex, lemma-fpqc-universal-effective-epimorphisms (023Q), including its displayed compatibility and unique-gluing statement. For affine faithfully flat finitely presented coverings, the hypotheses of `def-weil-pbc-fpqc-covering` hold. Apply the descent lemma to the scheme Ga; uniqueness also verifies that the descended morphism is over k. Finally the universal property of `def-weil-pbc-sheafification` fixes the presheaf which is already a sheaf. This gives the represented quotient, not just a pointwise assertion over fields.

7. Step 7 uses the diagonal multiplication formula from `def-sc-general-linear-group` and the multiplicative-group law from `def-sc-gm-ga`. It applies the weight calculation and quotient identification already proved. The character is multiplicative in its diagonal arguments, so the action factors through the diagonal homomorphism. Setting all diagonal entries to 1 gives centrality for U_n. The n=1 clause follows directly from the empty coordinate ring presentation.

I checked the small cases n=1, n=2 and n=3. For n=2 the single projection is U_2=Ga itself. For n=3, the order is (1,2),(2,3),(1,3); the product's cross term in (1,3) is u_12 v_23, and the first two coordinates have been killed when the last projection is used. Over F_2[epsilon]/(epsilon^2), conjugating I+epsilon E_23 by I+E_12 introduces epsilon E_13 but preserves the already killed E_12 coordinate; the retained E_23 coordinate has the required weight 1. Thus the proof respects nilpotents and characteristic 2. At r=m the polynomial projection has zero free variables, which is included by the cited flatness leaf. Empty variable sets and n=1 were not silently excluded.

Every non-elementary input is an existing cited node and says what its step takes from it. The remaining steps are finite coordinate calculations from the cited definitions and are marked elementary. No step exceeds 2000 characters, no new node restates an item clause, and no proof is hidden in an unsplit node. All dependencies were checked as unmerged, the quoted strings were verified verbatim, and proof_deps is exactly the union of the step uses. The server review_split check passed before the final affine-permanence citation refinement; the required full delivery dry run follows this report.
