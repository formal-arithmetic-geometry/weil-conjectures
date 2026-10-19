# Stage-1 report: lem-coef-reedy-colimit-comparison

## Files written

- `dag/nodes/sec-six-functors/lem-coef-reedy-colimit-comparison.json`: existing statement unchanged, now split into five proof steps; no new nodes and no new Mathlib leaves.
- `citations.json`: one verbatim statement excerpt for every (step, cited node) pair.
- `searches.jsonl`: six searches actually run for this item, retained in the command's original log format. The node preserves its seven inherited search records and appends these six.

## Attachments

None. Searches of `/home/ubuntu/weil-src-slopmaster2/WeilConjectures/` for the item id, blueprint docstring tag and Reedy/colimit terminology found no declaration stating the item. Upstream master was also checked as reference material only. The existing Brown factorization declaration is a prerequisite, not an attachment for the colimit theorem.

## WANTED

WANTED: an archived copy of Hovey, *Model Categories*, Lemmas 1.1.12 and 1.3.4 and the proof of Lemma 5.2.6, for this item. I read these places online in [the imported source PDF](https://ericmalm.net/ac/projects/symmetric-spectra/hovey--model-cats.pdf); no file was downloaded or written into the shared literature. Since the document is not archived under `literature/`, `proof_origin.by` remains `agent`.

## Findings and corrections

The item was an unsplit node with no proof or Lean audit declaration. Its statement is mathematically correct, so no statement dispute or change is needed. Its source describes the generalization of the cube-lemma proof to any small Reedy category whose constant functor preserves the two right classes. Hovey's Lemma 1.3.4 supplies the intervening adjoint-lifting argument; I have written that argument out instead of treating the Quillen criterion as an uncited theorem.

I read the unit `sk-prop-sf-biduality-general` and the chapter record. I located and read both the master ancestor and the current ancestor at `literature/blueprint/main-20261015/blueprint/sec-six-functors/sk-thm-sf-package/prop-coef-integral-exceptional-adjoint.proof.md`. Its second paragraph is the derived coefficient adjunction and inverse-limit calculation recorded in this item's preserved ancestry. This item is a technical descendant supplying a model-category foundation, not the unit's statement node, so the unit realization record is not changed. No SGA source is used.

I read the inherited search results, then ran two new semantic phrasings with LeanFinder, one LeanSearch query, a Loogle name-fragment query and two source grep queries through `msearch.py`. The hits concern the inclusion of the cofibrant subcategory, its localization/derivability, ordinary preservation of colimits, and Brown split factorizations; none supplies this Reedy-colimit assertion. I inspected BrownLemma.lean:48–87, Homotopy.lean:176–207, Reedy/Basic.lean:13–24, and the coproduct/cofibration statements in ModelCategory/Instances.lean:120–158. In particular the pinned Reedy source leaves construction of the diagram model structure as TODO. The inherited invalid Loogle identifier query remains honestly marked unavailable. No new node was created, so no duplicate-pair justification is needed. Whole-blueprint searches for Reedy and cofibrant-colimit terminology return no equivalent blueprint node, consistently with `same_as: []`.

## Review by Q04

For the item I read Hovey's online Brown lemma, the adjunction/lifting criterion, and the colimit–constant argument in the cube-lemma proof. I also read Stacks Tag 002F directly in `literature/stacks-project/categories.tex`, label `categories-definition-colimit`, and confirmed its tag in `tags/tags`. There are no new-node sources to review.

Step 1 cites `def-weil-pbc-category-colimit`. Its statement gives the chosen cocone and unique factorization; precomposing a map with every colimit leg gives a transformation to a constant diagram, and unique factorization reverses this operation. Checking on legs gives the naturality. Thus the adjunction is derived from exactly the cited definition.

Step 2 cites that same universal property and `lem-coef-reedy-model-structure`. I opened the Reedy node's statement: it asserts the diagram model structure and defines the weak factorization systems by their exact lifting classes. A square against a colimit map restricts to the diagram square, whose right side is the constant image of the ground right map. The item's explicit hypothesis ensures that this image is in the required right class. A diagram filler induces a colimit filler with both triangle equations checked on the legs. The two choices of weak factorization system give preservation of cofibrations and trivial cofibrations. This is a routine two-case lifting argument, not an extra hidden lemma.

Step 3 cites those two nodes again. The universal property makes the colimit of the constant initial diagram initial; preservation from step 2 applied to the initial map is exactly the Reedy node's definition of cofibrancy. I included the inverse-filler check for the initial-object isomorphism rather than assuming an uncited closure theorem.

Step 4 cites `lem-coef-brown-split-factorizations` and the Reedy node. The Brown statement gives precisely `pi=f`, `ps=1`, `p` trivial fibration, and both `i,s` cofibrations. Its cofibrant-endpoint hypotheses hold in the Reedy model category, because the item assumes Reedy cofibrancy, not just objectwise cofibrancy. Small diagram limits and colimits and retract closure of lifting classes are checked directly to match its category hypotheses. Two-out-of-three gives that `i,s` are trivial cofibrations; identities are in the trivial classes by the immediate identity filler. No fibrancy assumption is added.

Step 5 cites the Reedy node's two-out-of-three axiom in the ground category. Preservation from step 2 gives weak equivalences `Li,Ls`; applying the functor to `ps=1` gives that `Lp` is a weak equivalence, and applying it to `pi=f` finishes. This uses the statement of the Brown node through the equations already obtained in step 4, not its proof.

I checked B–E of `coord/delivery-errors.md` against these files: all notions have their existing statement dependencies, every non-elementary input is an existing cited statement, the quotes are verbatim, and the dependency union is exact. There are no new statement-only nodes to audit and no clause-restating or duplicate node. Each step is shorter than 2000 characters. The direct lifting, initial-object and two-out-of-three computations are marked elementary; the application of Brown factorization is marked non-elementary and cites that lemma.

For small cases I checked the empty category (unique diagram, initial colimit and identity comparison), the one-object identity category (the ordinary ground theorem), and a discrete category (cofibrant components and their coproduct). All colimits stay small in the fixed/enlarged universe. The hypothesis on the constant functor is retained throughout; nothing assumes arbitrary Reedy colimits always preserve weak equivalences.

## What I could not finish

None of the requested split work. The sandbox is for the second reader to inspect and deliver; I do not push the delivery.

## Second reading by Q04

- Statement: checked the complete model-category hypotheses, the Reedy structure, the constant-functor preservation hypothesis, both conclusions, and universe/smallness clause against the preserved item statement and Hovey Lemma 5.2.6 (pp. 126–127); verdict: faithful and neither weakened nor strengthened.
- Step 1: checked against the statement of `def-weil-pbc-category-colimit` and Stacks Tag 002F (`categories-definition-colimit`), including the empty indexing category; the cocone/natural-transformation bijection and initial-object claim are correct and elementary.
- Step 2: checked every lifting square against the WFS and Reedy lifting-class statements of `lem-coef-reedy-model-structure`, with Hovey Lemma 1.3.4 (p. 14) and the colimit–constant argument on pp. 126–127; the adjunction correspondence transports both triangle identities, and the two preservation claims follow under exactly the stated constant-functor hypothesis.
- Step 3: checked the pointwise initial diagram, its unique cocone using `def-weil-pbc-category-colimit`, and the cofibrant-object definition in `lem-coef-reedy-model-structure`; the chosen-initial-object isomorphism and composition argument are valid, including the empty category.
- Step 4: checked the Brown input against the full statement of `lem-coef-brown-split-factorizations`, and checked the Reedy category's completeness, WFS classes, retract closure, and two-out-of-three against `lem-coef-reedy-model-structure`; the Reedy-cofibrancy hypotheses are exactly those needed, and the derivation that both cofibration factors are weak equivalences is correct.
- Step 5: checked the identities `pi=f`, `ps=1`, preservation of trivial cofibrations from step 2, and both two-out-of-three applications against `lem-coef-reedy-model-structure`; the final weak-equivalence conclusion follows without a hidden fibrancy assumption.
- New nodes: none; therefore B1–B7, duplicate checks, and new-node source audits are vacuous. Existing cited nodes were opened directly, and `citations.json` quotes their statements verbatim.
- Edge cases: tested the empty category (initial colimit and identity comparison), singleton identity category (the ground model-category assertions), and a discrete category (componentwise cofibrancy and coproduct behavior); no counterexample or statement dispute arose.
- Changes: no mathematical or JSON repair was needed. Confirmed that the inherited item searches and six logged searches are actual records, that `proof_deps` is the exact union of step uses, and that the report's source and blueprint entries remain accurate.
