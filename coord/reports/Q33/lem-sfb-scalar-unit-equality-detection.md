## Worker report

Files written:
- `dag/nodes/sec-proetale-coefficients/lem-sfb-scalar-unit-equality-detection.json`: statement node, now split; unchanged statement, four proof steps, no whole-item Mathlib match.
- `citations.json`: one verbatim statement quote for every step/node citation.
- `report.md`: this report. The search command maintains `searches.jsonl`.

Attachments: none. Searches under `lean/WeilConjectures/` for the exact blueprint id, scalar/equality terminology, and unit/telescope terminology found no declaration stating the item. The more specific CategoryTheory and ProEtale searches also found none. No Lean was written or compiled.

WANTED: none.

The original node had no proof. Its statement is correct and was kept byte-for-byte; its old searches, provenance and metadata were retained. The proof expands the equality-detection portion of the ancestor's Full faithfulness paragraph without claiming that Hom commutes with any additional colimits. In particular it does not use the blueprint's informal constructibility reduction as a proved premise: preservation of this particular Hom telescope is an explicit hypothesis of this item. No source error or statement dispute was found.

Nothing remains unfinished in this one-level split. The two non-elementary ingredients already exist as Mathlib leaves. No new definitions or statements were introduced.

## New nodes

None: 0 new nodes, 0 new Mathlib leaves. Reused `lem-weil-pbc-abelian-groups-forget-filtered-colimits` and `lem-weil-pbc-filtered-colimit-sets-elementwise` (both Mathlib leaves), as well as the existing preadditivity and colimit definitions.

## Searches and blueprint

Read the chapter and unit records, the ancestor `thm-sfb-extend-scalars-localization.proof.md` in snapshot main-20261015, and SETUP's three levels. The route is the unit's rationalization full-faithfulness argument. No chapter or unit statement or route was changed.

DAG-wide searches for finite-stage equality, filtered-colimit elements, `isColimit_exists_of_rep_eq`, `isColimit_eq_iff`, and module-colimit statements found the existing leaves. Opened the candidate module-elementwise leaf too; using the existing abelian-group forgetful leaf and set-elementwise leaf avoids any unnecessary module/abelian-group identification. Whole-blueprint searches were `filtered colimit`, `scalar unit equality`, `colimit modules elementwise`, `eventually become equal`, and `adjunction unit`. No imported node states this adjunction-plus-scalar-telescope criterion. `blueprint_refs.py ancestor` returned `thm-sfb-extend-scalars-localization`; the item's from.place now identifies its Full faithfulness paragraph and displayed Hom-colimit comparison, and same_as is empty.

Five searches actually executed with msearch.py, preserved in searches.jsonl, were appended to the inherited Mathlib search records with exactly their tool and query text. LeanFinder's first phrasing found adjunction/colimit-adjunction material; its second, simpler phrasing found `Types.FilteredColimit.isColimit_eq_iff'` and related equality lemmas. LeanSearch found adjunction extensionality and adjoint colimit-preservation results; Loogle with the two expected category-theory names found no hits; grep found adjunction naturality applications. None states the whole item or specializes to it in one step. The finite-stage hit is already the existing set-elementwise leaf and was read in Mathlib source, not made into a duplicate.

## Review by Q33

I read the main-20261015 ancestor proof, specifically Full faithfulness and its displayed Hom-colimit comparison. The item isolates the equality implication of that comparison. Its natural number scalar, arbitrary preadditive source, arbitrary target category, adjunction unit at B, and assumed Hom colimit all occur explicitly in the argument; no assumption that F or U is additive, faithful, exact, or fully faithful was inserted. I also read Stacks categories.tex, Tag 0037 (`definition-adjoint` and its following unit/counit paragraph), and Tag 04AX (`section-directed-colimits`, after Definition 002V), and the actual statements of all four cited DAG nodes. No new node needs a separate source comparison.

Step 1 uses the given unit's naturality as part of its definition. For f and g, the displayed equations pass through UF(f) composed with eta_K and UF(g) composed with eta_K, which are equal by applying U to the assumed equality. The leg at zero is exactly eta_B by hypothesis, so the result is equality under q_0. This is a direct naturality substitution, not a theorem asserting faithfulness or any linearity of the adjunction.

Step 2 uses `def-weil-preadditive-category` for abelian Hom groups and bilinear composition, and `def-weil-pbc-category-colimit` for the cocone and filteredness definitions. Both statements were opened and say these things explicitly. It writes out additivity of q_i and its successor compatibility. The only preservation theorem used is `lem-weil-pbc-abelian-groups-forget-filtered-colimits`: its statement gives the underlying-set colimit for any abelian-group colimit cocone on a small filtered category. The index is the assumed small copy of N, its nonemptiness and common-upper-bound/parallel-arrow properties are spelled out, and a universe can contain both Hom groups and that index. The preservation conclusion retains the actual q_i, so it also retains the equality from step 1. I read Mathlib/Algebra/Category/Grp/FilteredColimits.lean lines 195–218; the to_additive forget_preservesFilteredColimits instance at lines 212–215 is the named source of the existing leaf.

Step 3 cites clause (3), not merely the representation clause, of `lem-weil-pbc-filtered-colimit-sets-elementwise`. Its statement explicitly says equality of images of two elements at one index is equivalent to equality after a single later transition. I read Mathlib/CategoryTheory/Limits/Types/Filtered.lean lines 125–165: isColimit_eq_iff' at line 153 states exactly this for any colimit cocone. The hypothesis supplied is the underlying-set colimit from step 2, the index supplied is zero, and the elements supplied are f,g. Thus the cited statement really gives the arrow 0 to n used in the next step. No assertion about individual q_i being injective is used.

Step 4 cites only the preadditivity definition and computes the transition explicitly. Its induction starts at n=0 with the identity map and has successor a times the previous transition, yielding a^(n+1) by repeated addition in the Hom group. Substituting both f and g into step 3 gives the conclusion. This is elementary scalar arithmetic, so no separate node for scalar powers is warranted. The longest step has 784 characters; none exceeds 2000 or hides a separate comparison lemma.

For the mathematical edge checks, n=0 yields f=g with a^0=1 even when a=0. For a=0, stage one kills every element, and the claimed eventual equality is automatic with n=1; no cancellation was used. For a=1, every transition is the identity, so finite-stage equality really gives f=g. In a category with zero Hom groups, both representatives are already equal at zero. Arbitrary torsion in the Hom group causes no issue because the proof only multiplies, and never divides or cancels. Neither existence of a colimit in the original category nor Hom preservation for another object is needed: the given cocone and the expressly assumed abelian-group colimit suffice.

Against delivery-errors B, no new node was created, all objects in the unchanged item are introduced, and TeX is written once; inherited data and actual search results were retained. Against C, every non-elementary fact is a cited statement, checked above; citations.json quotes the opened statements verbatim. Both off-unit theorem citations are existing Mathlib leaves and are generic tools; no route is replaced or maintainer tool_uses field written. Against D, the argument stays in the item's steps and is not moved into a node restating the item. Against E, smallness, filteredness, zero leg, equality hypothesis, and the absence of additivity/cancellation assumptions were all checked at the steps where needed. The correction to the initial empty proof is the explicit distinction between an abelian-group colimit and its underlying-set colimit; the preservation theorem is now cited rather than implicitly assumed.
