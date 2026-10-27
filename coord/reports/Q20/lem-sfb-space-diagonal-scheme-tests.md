## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-space-diagonal-scheme-tests.json`: split item; no new nodes were needed.
- `citations.json`: 15 verbatim statement citations, one for each use in each proof step.

## Attachments

None. No sorry-free declaration in the source checkout states this item exactly.

## WANTED

None.

## What was wrong or corrected

The imported item had an empty proof despite its source (Spaces Morphisms, Tag 03HK) giving the standard atlas proof. I supplied the missing proof. I did not change the statement: in particular, the test is over an arbitrary scheme `B`, and no finiteness or separation hypothesis is added. The proof uses the existing DAG node `lem-sfb-space-diagonal-locally-finite-type` only as background comparison material; that node is explicitly stated over Spec ℤ, whereas this item has arbitrary base B. I therefore kept B throughout and used the equality-locus and atlas proof instead of assuming a change-of-base equivalence without a cited theorem. No duplicate node was created.

## What I could not finish

Nothing remains for this stage-1 split. The proof is natural-language only, as required; no Lean file was written and no compiler or Lake command was run.

## Review by Q20

I read the item node, the chapter and unit records, the current blueprint text, and the Stacks source at Spaces Morphisms Tag 03HK and Spaces Tags 025Y and 02WZ. I also read every statement cited by every proof step: `def-trf-algebraic-space` supplies representable diagonals and scheme atlases; `lem-trf-space-fibre-products-etale-covers` supplies sheaf fibre products and etale base change; `def-pc-fibre-product` supplies the scheme universal property; `lem-trf-space-chartwise-etale-permanence` supplies chartwise etale stability; `def-weil-etale-morphism` and `def-weil-unramified-morphism` justify that an etale scheme map is locally of finite type; `lemma-nagata-finite-type-to-separated-target` supplies the scheme cancellation clause; `lem-weil-pbc-lft-base-change` supplies local finite type after the scheme test's base change; and `lem-sfb-scheme-etale-source-target-properties` descends local finite type through the two etale charts. The 15 entries in `citations.json` quote those statements verbatim.

I checked the hypotheses at each step. Steps 1–2 identify the scheme test with the equality locus and prove monomorphy from the forced first coordinate. Step 3 checks that `R=A×_U A` and `P=A×_V A` are schemes, that the atlas map `q:P→U×_V U` is surjective etale, and that the presentation square is cartesian. Step 4 uses only the local-finite-type part of etaleness and the cancellation lemma, with no hypothesis on the second projection. Step 5 checks the scheme test after the atlas base change and applies the cited base-change lemma. Step 6 checks that both vertical maps are etale and the upper one is surjective, so the cited source-and-target criterion returns local finite type for `d_T`. I tested the degenerate cases (empty schemes and identity maps) against these constructions; all arguments remain valid. The Mathlib searches were rerun for the item with LeanFinder, Loogle, grep, and LeanSearch; all returned scheme-only declarations or no match, so the item is not a Mathlib leaf.

The first required server dry run passed. In a final source-tag check I corrected the base-change source tag in step 5 from 01T6 to 01T4 (the label lemma-base-change-finite-type); the cited node already had the right tag. I then reran the complete dry run before pushing. All steps are shorter than 2,000 characters and expose their comparisons and hypotheses explicitly.
