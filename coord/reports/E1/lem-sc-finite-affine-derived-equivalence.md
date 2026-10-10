1. Files written:

   - `dag/nodes/sec-picard-framework/lem-sc-finite-affine-derived-equivalence.json` — repaired four-step ringed-space proof; Mathlib searches found no match.
   - `dag/nodes/sec-picard-framework/def-pc-ringed-spaces-derived-direct-image.json` — statement-only K-injective definition for ringed spaces.
   - `dag/nodes/sec-picard-framework/lem-pc-ringed-spaces-derived-adjoint-general.json` — statement-only ringed-space derived adjunction.

2. Attachments: none.

3. WANTED: `literature/stacks-project/perfect.tex`, Tag 0AVW, for the full source prose.

4. The returned version was wrong because it applied an equivalence of `QCoh` abelian categories to `D_QCoh` without the needed comparison, and because termwise pushforward on arbitrary complexes does not compute `Rf_*`. I removed the unnecessary exact-equivalence child node. The repaired proof follows the 0AVW route through the ringed-space morphism `g:(X,O_X)->(Y,f_*O_X)`, with `Lg^*` and `Rg_*`, and separately identifies restriction of `Rg_*` with `Rf_*`.

## Review by E1

I reread Tag 0AVW and the statements of `lem-weil-pbc-affine-module-correspondence` and `lem-sc-affine-derived-cohomology`. The returned scheme-only mismatch is repaired by defining `D(\\mathcal A)`, `Lg^*` through inverse image and derived change of rings, and `Rg_*` through the new ringed-space K-injective definition. I added and checked the statement-only ringed-space adjunction node against Tag 079W; Mathlib searches for both new nodes found no exact declaration. Step 1 uses exactly the affine module equivalence. Step 2 first uses the ringed-space adjunction and Step 4's restriction comparison, then applies the affine cohomology formula to `Rg_*`, so it does not apply an `Rf_*` statement to `Rg_*` prematurely. Step 3 explicitly computes `h(G)=g^*G` and notes exactness of `g^*` and `g_*`, so the cohomology maps of the derived unit and counit are the underived `beta` and `alpha` maps. Step 4 uses the K-injective definition to identify restriction of `Rg_*` with `Rf_*`. I verified every citation quote verbatim against the cited node and checked the identity affine map and `Spec A -> Spec B` cases.

## Not duplicates

- `def-pc-ringed-spaces-derived-direct-image` vs `lem-pc-ringed-spaces-derived-adjoint`: the existing node states an adjunction for scheme morphisms; this new definition states the K-injective construction of $Rg_*$ for arbitrary ringed-space morphisms, which is needed to define the item’s $Rg_*$. 
- `lem-sc-finite-affine-derived-equivalence` vs `lem-sc-affine-derived-cohomology`: the existing node gives only the cohomology formula for `Rf_*`; this item proves the full derived equivalence and identifies its quasi-inverse.
- `lem-sc-finite-affine-derived-equivalence` vs `lem-pc-ringed-spaces-derived-adjoint`: the existing node gives only the general `Lg^* ⊣ Rg_*` adjunction; this item proves that the adjunction is an equivalence for the affine ringed-space morphism.
- `lem-sc-finite-affine-derived-equivalence` vs `lem-weil-pbc-affine-module-correspondence`: the existing node is underived and abelian; this item is the derived-category lift and restriction identification.

5. Nothing remains unfinished in the split. No Lean compilation is performed at stage 1.

## Second reading by E1

- Item statement: checked against Stacks `perfect.tex`, Tag 0AVW (`lemma-affine-morphism-equivalence`), including the equivalence target and the restriction-of-scalars identification; verdict: correct.
- Step 1: checked against Tag 0AVW and the full statement of `lem-weil-pbc-affine-module-correspondence`; verdict: the underived affine correspondence is exactly the input used.
- Step 2: checked against the local stalk computation in Tag 0AVW and the statements of `def-pc-derived-pullback`, `lem-pc-ringed-spaces-derived-adjoint`, `lem-sc-affine-derived-cohomology`, and the affine correspondence; verdict: repaired the unsupported bounded-above-flat representative claim by spelling out exact localization on a K-flat resolution.
- Step 3: checked against the unit/counit paragraph of Tag 0AVW and the cited alpha/beta, derived-pullback, adjunction, and cohomology statements; verdict: repaired the arbitrary-complex pullback argument and made the cohomology objects explicit.
- Step 4: checked against the K-injective construction in Tag 0AVW and `def-pc-derived-direct-image`; verdict: repaired the citation and stated the common underlying K-injective complex argument.
- New nodes: none; the split creates no child nodes, so B1-B7 and duplicate/search checks are vacuous. Existing cited nodes were opened and their quoted statements verified.
- Small cases checked: identity affine map, `Spec A -> Spec B`, the zero complex, and the empty affine scheme; all give the stated unit, counit, and restriction behavior.
- Changes: removed the stale flat-complex tool use and citations, added the exact-localization/K-flat argument to steps 2-3, replaced the irrelevant adjunction citation in step 4 with `def-pc-derived-direct-image`, and synchronized `citations.json`.
- Contract repair: the sandbox item had temporarily replaced the repository target statement with a stronger ringed-space formulation. I restored the exact existing Tag 0AVW target statement and retained the ringed-space construction in the proof. Step 4 now also cites `def-pc-derived-direct-image` for the scheme-level $Rf_*$ definition; its citation quote was added to `citations.json`.
- New-node audit correction: `def-pc-ringed-spaces-derived-direct-image` and `lem-pc-ringed-spaces-derived-adjoint-general` are genuine supporting statements, not restatements of the item; both are statement-only, self-contained, and have recorded grep, LeanFinder, and Loogle searches. Their blueprint `from` entries point to the affine-derived-equivalence proof clause.
