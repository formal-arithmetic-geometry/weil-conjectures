1. Files written:

- `dag/nodes/sec-picard-framework/lem-sc-p1-ext-resolution-derived-connecting.json` (item, split)
- `dag/nodes/sec-picard-framework/lem-sc-p1-right-derived-triangle-connecting.json` (statement, unsplit; Mathlib search found only the derived-triangle APIs)
- `citations.json`

2. Attachments: none.

3. WANTED: none.

4. The imported item was unsplit and had no Lean declaration with its blueprint tag. Its statement agrees with the intended Tags 05TE and 06XR comparison. I searched the DAG for existing connecting-map and Ext-resolution statements. The existing node `lem-weil-pbc-ext-via-injective-resolution` gives the explicit cocycle-to-derived-morphism comparison, while `lem-weil-pbc-horseshoe-delta-functor` gives the injective-resolution long exact sequence but explicitly does not assert its relation to the derived triangle. I therefore added the strictly more general bridge statement `lem-sc-p1-right-derived-triangle-connecting`; it is not a restatement because it concerns arbitrary left exact additive functors and only identifies the two constructions of the right-derived connecting map. The item proof first applies that bridge to `Hom(M,-)`, then applies the existing Ext-resolution comparison to obtain the displayed Ext identification and cocycle formula.

## Review by C1

I read the item source pointers in `literature/stacks-project/derived.tex` (Tags 05TE and 06XR), the imported blueprint ancestor `thm-sc-p1-duality`, and the full statements of `lem-weil-pbc-ext-via-injective-resolution` and `lem-weil-pbc-horseshoe-delta-functor`. Step 1 uses exactly the new bridge statement: it supplies the canonical identification of the horseshoe right-derived connecting map with the homology connecting map after applying the derived functor to the standard triangle. Step 2 uses the existing Ext-resolution node's explicit sentence that a cocycle `f : M -> I^i` maps to the composite `M[0] -> I^bullet[i] <- N[0][i]`; this is the required comparison and says the formula used in the step. The hypotheses match: `Hom(M,-)` is left exact and additive on the abelian category with enough injectives, and the short exact sequence is the one in the item. I checked the degree-zero case (`i = 0`) reduces to ordinary Hom and the zero sequence case gives zero connecting maps.

For the new node I searched the whole DAG and blueprint before writing it; no existing node states this bridge. I ran LeanFinder, Loogle, grep, and LeanSearch searches with the new id. LeanFinder returned only `ShortExact.singleδ`, `DerivedCategory.HomologySequence.δ`, and related triangle APIs; Loogle and grep found no comparison theorem, and LeanSearch was unavailable. The node is consequently statement-only and unsplit. The item itself was searched with LeanFinder, Loogle, grep, and LeanSearch; no project declaration or exact Mathlib theorem states the resolution-to-triangle comparison. All citation quotes in `citations.json` are verbatim portions of the cited node statements.

5. Nothing remains unfinished in this split; the new bridge is intentionally left as the next DAG item.

## Not duplicates

lem-sc-p1-right-derived-triangle-connecting vs lem-sc-p1-ext-resolution-derived-connecting: the new node is the generic left-exact-functor comparison between horseshoe and derived-triangle connecting maps; the item additionally specializes to Hom(M,-), identifies Ext by injective resolutions, and states the explicit Ext comparison.
lem-sc-p1-right-derived-triangle-connecting vs lem-weil-pbc-site-cohomology-pullback: the existing node concerns pullback maps for site cohomology; the new node concerns the construction of right-derived connecting maps from arbitrary short exact sequences and derived triangles.
lem-sc-p1-right-derived-triangle-connecting vs lem-weil-pbc-module-cech-vanishing-criterion: the existing node is a Cech vanishing criterion for module cohomology; the new node is a derived-category compatibility statement and has no Cech hypotheses.
lem-sc-p1-right-derived-triangle-connecting vs lem-weil-pbc-derived-functor-long-exact: the existing node states exactness of a right-derived long sequence; the new node identifies its horseshoe connecting maps with the derived-triangle homology maps.
lem-sc-p1-right-derived-triangle-connecting vs lem-weil-pbc-derived-functor-injective-vanishing: the existing node states vanishing of higher derived functors on injectives; the new node compares connecting morphisms and does not assert vanishing.
lem-sc-p1-right-derived-triangle-connecting vs lem-weil-pbc-right-derived-universal-delta-functor: the existing node states universality and existence of a canonical delta-functor; the new node identifies its connecting maps with those obtained by applying the derived functor to the standard distinguished triangle.

## Second reading by C1

- Item statement: checked against Stacks Derived Categories Tags 05TE and 06XR (labels `derived-lemma-right-derived-delta-functor` and `derived-lemma-compute-ext-resolutions`), hypothesis by hypothesis; verdict: agrees, including enough injectives, the short exact sequence, injective-resolution Ext, and derived-category Ext.
- Item Step 1: checked against `lem-sc-p1-right-derived-triangle-connecting` and the horseshoe and homology-long-exact statements it cites; verdict: the generic bridge supplies exactly the asserted equality after specializing to `Hom(M,-)`, whose additivity and kernel preservation are spelled out elementarily in the step.
- Item Step 2: checked against `lem-weil-pbc-ext-via-injective-resolution`; verdict: repaired to quantify the resolution object, state the cocycle comparison explicitly, and identify the relevant $N=A$ terms without the unsupported word “transports”.
- New node `lem-sc-p1-right-derived-triangle-connecting`: checked against Tags 05TE and 015B and all ten statement dependencies; verdict: self-contained generic bridge, strictly more general than the item, with no duplicated DAG node and no Mathlib exact match.
- New node form: statement-only, all notions carry definition or theorem dependencies, TeX is escaped once, source tags and labels are recorded, and LeanFinder/Loogle/grep/LeanSearch searches are recorded with their actual results.
- Small cases checked: zero short exact sequence gives zero connecting maps; $n=0$ is the ordinary Hom boundary; for a field and split short exact sequence the boundary is zero; the empty/zero object specialization is consistent.

Changes made: corrected the item node's `created.item` metadata to the delivered item; rewrote Step 2 to remove the undeclared variable and spell out the Ext identification; appended this second-reading audit.
