Files written:

- `dag/nodes/sec-abelian-varieties/lem-sp-cartan-eilenberg-comparison-homotopy.json` — statement, split proof, and recorded searches.
- `citations.json` — verbatim statement quotes for every proof citation.

Attachments: none.

WANTED: `literature/stacks-project/derived.tex`, Lemma 015I and Remark 015K were referenced by the imported node but are not present in this checkout; the proof is written from the stated comparison construction and existing project lemmas.

What was wrong or incomplete: the imported item had no proof, no proof dependencies, and status `unsplit`. The item’s existing Mathlib search records were stale relative to the required search log; I reran LeanFinder, Loogle, grep, and LeanSearch and recorded their actual outputs. No duplicate child node was needed: the existing lifting lemmas already state the non-elementary row-extension facts.

What I could not finish: no Lean declaration exists for this project statement, and the unavailable Stacks source prevented a line-level source check. The mathematical induction follows the existing Cartan--Eilenberg functoriality node and the two cited lifting statements.

## Review by J1

I read the item, its ancestor `thm-sp-grothendieck`, the existing Cartan--Eilenberg existence node, the repaired double-complex node, and the total-complex and filtration definitions. Step 1 uses only additivity and the augmentation equations. Step 2 uses the existence node for injective target B/Z/H rows, checks exactness of the source rows after applying the exact functor, and applies the repaired child node with $w=u-u'$. Step 3 uses the child node for the two components, and Step 4 uses its total homotopy identity together with the totalization and filtration definitions. I checked that all cited quotes are verbatim excerpts from their node statements, that every proof dependency is listed, that no new node duplicates an existing statement, and that the item’s blueprint ancestor and exact proof place are recorded.

## Second reading by J1

- Item statement: checked the hypotheses and conclusion against the imported Cartan--Eilenberg comparison claim and Tags 015H, 015I, and 015K as recorded in the node; the local checkout has no `derived.tex`, so no line-level source inspection was possible.
- Step 1: checked subtraction, augmentation equation, and prescribed component directly from the item statement; verdict: elementary and self-contained.
- Step 2: checked the target injective row clauses against `lem-sp-cartan-eilenberg-exists`, the source exactness after applying F, and the full construction against `lem-sp-cartan-eilenberg-double-complex-homotopy`; verdict: all non-elementary dependencies used by the repaired step are cited.
- Step 3: checked totalization and filtration notation against `def-sp-double-complex-total` and `def-sp-filtration`; verdict: the componentwise equation and one-step resolution-degree shift are stated.
- New nodes: none; no child node was created, so B1--B7 and duplicate-node checks are vacuous. The existing Mathlib searches remain recorded in the item.
- Small cases: the zero complex and the identity case `u = u'` give `s = 0` and the zero homotopy; a complex concentrated in degree zero reduces to the usual injective-resolution comparison lift.
- Changes: corrected `created.item` to the delivered item; added `def-sp-abelian` and `def-sp-enough-injectives` dependencies; removed an unused functoriality dependency; expanded the induction step to expose the defect and its three row lifts; removed the stale step-1 citation and synchronized `citations.json`.
- Source limitation: the requested Stacks source file is absent from `literature/` on this checkout; the source tags and imported statements were checked, but this limitation remains for maintainer review.

## Repair review by J1

The return identified three substantive gaps. I repaired the child node `lem-sp-cartan-eilenberg-double-complex-homotopy` so it introduces complexes $K,L$, a complex map $w:K\to L$, and homotopy components $s^p:K^p\to L^{p-1}$ satisfying $w=d_Ls+sd_K$ and $\delta\epsilon_I=\epsilon_Jw$. Its source hypothesis is exact augmented B/Z/H rows (including $0\to Z\to I\to B\to0$), while only the target J rows are injective resolutions. The conclusion is now type-correct: $s_1^{p,0}\epsilon_I^p=\epsilon_J^{p-1}s^p$.

In the repaired item, Step 1 checks the augmentation defect $\delta=\phi-\psi$ and the prescribed homotopy $s$. Step 2 checks exactness of the source rows after applying the exact functor F, injectivity of the J rows from the CE existence statement, and applies the repaired child node with $w=u-u'$. The old citations to `lem-weil-pbc-lift-to-injective-unique-up-to-homotopy` and `lem-weil-pbc-horseshoe-morphism-lift-exact-source` were removed from Step 2, Step 3, `proof_deps`, and `split_report.tool_uses`; the child lemma carries the full construction. Step 3 cites only the child node, and Step 4 cites the child plus totalization and filtration definitions. I updated `citations.json` with verbatim quotes from exactly these cited statements.

I reran the required Mathlib searches for the new node. LeanFinder returned only generic `Homotopy` declarations, Loogle and source grep returned no Cartan--Eilenberg result, and LeanSearch was unavailable; these exact outputs are recorded in the new node. Small cases checked are $u=u'$ (so $s=0$ and the zero homotopy is allowed), a zero double complex, and a complex concentrated in one degree (where the construction reduces to the ordinary injective-resolution comparison homotopy).

## Not duplicates

lem-sp-cartan-eilenberg-double-complex-homotopy vs lem-sp-cartan-eilenberg-comparison-homotopy: the new node isolates the two bidegree components and their exact-sequence assembly; the item additionally assumes an exact functor and concludes comparison-map uniqueness for its specific augmentations.
lem-sp-cartan-eilenberg-double-complex-homotopy vs lem-sp-cartan-eilenberg-properties: the new node concerns homotopies between two maps and totalization; the existing node only lists the Cartan--Eilenberg resolution axioms.
lem-sp-cartan-eilenberg-double-complex-homotopy vs lem-sp-cart-eilenberg-left-exact-cohomology: the new node constructs filtered total homotopies; the existing node identifies cohomology after a left exact functor.
lem-sp-cartan-eilenberg-double-complex-homotopy vs lem-sp-cartan-eilenberg-exists: the new node compares two already-given resolutions; the existing node proves existence of one resolution.
lem-sp-cartan-eilenberg-double-complex-homotopy vs lem-weil-pbc-cartesian-eilenberg-functorial: the new node compares homotopic maps and gives horizontal/vertical homotopy components; the existing node constructs one comparison map for a single map.
lem-sp-cartan-eilenberg-double-complex-homotopy vs lem-weil-pbc-horseshoe-morphism-lift-exact-source: the new node assembles two bidegree homotopies over both CE exact sequences; the existing node lifts one middle map of a short exact sequence of augmented complexes.
lem-sp-cartan-eilenberg-double-complex-homotopy vs lem-sp-cartan-eilenberg-comparison-independence: the new node gives the component-level homotopy identity; the existing node applies filtered homotopy invariance to deduce spectral-sequence independence.

The two generic homological nodes from the returned version are no longer cited: the repaired child node carries the complete B/Z/H and exact-sequence construction, as required by the return.

## Second reading repair

- Rewrote the child statement as a self-contained existence claim: it now introduces the abelian category, augmentations, horizontal cycle/boundary/cohomology objects, and the precise augmented null-homotopy equation.
- Removed proof-like wording ("constructing ... yields") from the child statement and replaced it with an explicit existential conclusion.
- Synchronized the three child-node quotations in `citations.json` with the repaired statement.
