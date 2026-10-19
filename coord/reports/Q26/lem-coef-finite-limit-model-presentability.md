# Q26 stage-1 report: lem-coef-finite-limit-model-presentability

## Files written

- `dag/nodes/sec-six-functors/lem-coef-finite-limit-model-presentability.json`: statement, now split into three steps; existing general sketch-model theorem reused; not a Mathlib leaf.
- `citations.json`: one verbatim cited-statement witness for each of the three proof steps.
- `report.md`: this report.

No new nodes and no new Mathlib leaves. The search command also produced `searches.jsonl`; its seven actual search records were appended to the item's inherited Mathlib searches without deleting the inherited records.

## Attachments

None. Searched the project Lean under `/home/ubuntu/weil-src-slopmaster2/WeilConjectures` for the exact blueprint tag/id and for finite-limit theories, sketches, Lex/local presentability, and the general theorem's id. No project declaration states the item. The upstream master was checked for the exact id too; its sorry declarations would not count as finished proofs. No Lean was written, opened in a compiler, or built.

## Sources wanted

WANTED: G. M. Kelly, *Structures defined by finite limits in the enriched context, I* (1982), Sections 4 and 9, especially (9.2), (9.4), (9.7), (9.8), for lem-coef-finite-limit-model-presentability. Read online at https://www.numdam.org/article/CTGDC_1982__23_1_3_0.pdf ; not archived locally.

WANTED: Adamek-Rosicky, *Locally Presentable and Accessible Categories* (1994), Chapter 1, Corollary 1.52, full proof, for the already-existing lem-coef-finite-limit-sketch-models. The publisher synopsis was opened, but does not expose that full proof; the publisher excerpt also did not provide usable extracted text here. I do not claim to have read that full proof. The split uses the existing DAG statement as a theorem, leaving its proof to that existing unsplit item.

No Stacks tag for the general finite-limit-sketch model theorem was identified. I did read the local Stacks `categories.tex`, labels `definition-limit` (002E) and `definition-colimit` (002F); these provide the universal-property conventions, not the general sketch theorem.

## Corrections and observations

The mathematical statement and its statement dependencies are unchanged. The proof was empty. It is now a specialization of the existing same-unit node `lem-coef-finite-limit-sketch-models`. That node already includes the final sketch formulation and every required conclusion; manufacturing another node would duplicate it.

Kelly (9.2) defines theory models as left-exact functors; (9.4), (9.7), and (9.8) support the theory assertion. The original source metadata's assertion that (9.3) supplies the sketch formulation needs care: (9.3) completes an ordinary small category, and restriction then gives all functors on that category. Forgetting specified sketch cones would therefore give the wrong models. The unchanged statement's phrase “its free finite-limit completion” must mean completion of the sketch respecting its cones. This proof requires no such completion construction: step 3 uses the already existing general sketch theorem directly. No mathematical assertion is weakened, and no statement dispute is raised.

The new Mathlib searches found `CategoryTheory.Limits.isIndObject_iff_preservesFiniteLimits` and `CategoryTheory.Ind.leftExactFunctorEquivalence`; I read `IndObject.lean:209-216`, `Category.lean:285-286,308-310`, and `Presentable/LocallyPresentable.lean:38-65`. These supply parts of the theory case or definitions, not the entire sketch theorem in one line. Both semantic phrasings and the Loogle/grep results were read. All seven fresh logged calls succeeded; none was reported unavailable.

## Unfinished work

None required for this one-level split. The cited general sketch-model theorem remains an existing unsplit node; it is not silently treated as Mathlib or as Lean-closed. The delivery is for a second reader; no push is authorized or performed.

## Not duplicates

No new nodes. `lem-coef-finite-limit-model-presentability` specializes the pre-existing `lem-coef-finite-limit-sketch-models`; the latter is cited instead of copied or recreated. Searches of the whole DAG for finite-limit sketch/theory and essentially algebraic terminology, and whole-blueprint searches for “finite-limit”, “finite limit”, and “locally finitely presentable”, found no blueprint node asserting this theorem. The inherited `blueprint.from` is retained and `same_as` is `[]`.

## Review by Q26

I read the worker contract, delivery-errors B through E in full, the three-level route rule in SETUP, GOAL and dag-sync, the chapter and the assigned unit, the current blueprint ancestor's statement and proof, the item, its parent `lem-coef-simplicial-interval-lifting`, and the complete statement of `lem-coef-finite-limit-sketch-models`. The unit is `sk-prop-sf-biduality-general`; both theorem nodes have that same unit. The technical input serves paragraph 2 of the coefficient adjunction's enhancement and the parent's steps 1 and 4, without replacing a unit step. No unit record is changed.

In step 1 I use only the cited node's definition of sketch and model. Every finite index category is represented by a finite code, and the diagrams and cones in a small T form a small set; hence the specified family is small. The models preserve precisely all finite limit cones, and the morphisms on both sides are all natural transformations. This elementary identification changes neither objects nor maps. I included the empty diagram so terminal-object preservation is not lost.

In step 2 I checked the cited statement sentence by sentence: it asserts all U-small limits and colimits, pointwise limits and filtered colimits, and a U-small family with precisely the Hom-preservation and filtered-generation properties needed. T and the family constructed in step 1 are U-small, so the hypotheses match. A larger universe in the cited node only houses the category of U-small-set-valued functors; it does not enlarge the allowed diagrams or introduce a new hypothesis on T. The literal full-subcategory identification makes its universal properties and pointwise evaluations exactly the item's ones. I take none of these theorems from a definition node or from a cited node's proof.

In step 3 the item's arbitrary sketch has exactly the data in the cited statement, including finite cones and natural transformations. I verified that all conclusions again appear explicitly there. I repaired the tempting incorrect use of plain-category free completion by avoiding it, as explained above. All non-elementary content of steps 2 and 3 is this existing cited theorem, not an uncited source quotation. `citations.json` was checked against the exact statement text, with one witness per step.

For small cases, T cannot be empty because it must have a terminal object. For terminal T the empty-cone condition forces the unique value to be a singleton, giving the terminal category of models as expected. For the sketch with no sorts there is one model; for a discrete family of sorts with no specified cones the theorem gives a product of set categories. A specified empty cone forces its apex to be singleton and stays included in the construction. Filtered diagrams are nonempty as in the item's definition; the proof never treats the empty colimit as a filtered colimit, and never claims general colimits are pointwise. There are no new statements needing separate small-case tests.

For B, there are no new nodes, and the original self-contained statement, TeX, provenance and source fields are retained. For C, every uses-entry is the exact same-unit statement just examined, no hidden theorem is imported, and the dependency union is exactly that one id. For D, no new restatement or one-node replacement was created; reuse of the already existing more general theorem is the duplicate-avoidance rule. For E, the empty cone, size bounds, identical morphisms, and limits versus general colimits were checked explicitly. The mathematical statement and blueprint import fields were preserved. The server dry run is the final mechanical check.

## Second reading by Q26

- Item statement: checked against Kelly, *Structures defined by finite limits in the enriched context, I*, §§4 and 9, especially (9.3), (9.4), (9.7), and Theorem (9.8), with the Set specialization; the theory hypotheses and conclusions agree. I additionally read Kelly (10.1) and Theorem (10.2), printed p. 40, for the sketch definition and the equivalence with models of a small finite-limit theory. Empty finite cones and the filtered-colimit convention are included.
- Step 1: checked against the statement of `lem-coef-finite-limit-sketch-models`; the finite-cone coding gives a small specified family, and its model/morphism definitions identify the full subcategory with `Lex`.
- Step 2: checked clause by clause against `lem-coef-finite-limit-sketch-models`; its completeness, cocompleteness, local finite presentability, and pointwise limit/filtered-colimit clauses give exactly the asserted conclusions under the step-1 identification.
- Step 3: checked against the same existing sketch-model statement and Kelly's free finite-limit-completion discussion; an arbitrary finite-limit sketch is already in the cited theorem's hypotheses, so the conclusion follows directly without an uncited completion construction.
- New nodes: none; no B1--B7 node-form review or new-node small-case review was required. The existing cited node was opened and its exact statement was copied into `citations.json`.
- Small cases and edge hypotheses: checked the terminal one-object theory, the empty-sort sketch, discrete sorts, a specified empty cone, nonempty filtered indexing, and the distinction between pointwise limits/filtered colimits and general colimits.
- Mathlib search records: read the item's recorded results and the sandbox search log; they contain definitions or partial Ind/presentability facts rather than an exact leaf. There are no new nodes requiring additional independent searches.

Changes made: corrected step 3's proof-source metadata to Kelly (10.1) and Theorem (10.2), read directly on printed p. 40. The inherited top-level source incorrectly names Kelly (9.3) for sketch completion; `source` is maintainer-owned, so its necessary metadata correction is reported here rather than installed through a split. Requested source correction: retain §§4 and 9 for the theory case and cite (10.1)–(10.2), printed p. 40, for the sketch clause. That theorem retains specified cones and gives the model-category equivalence claimed in the original statement. The full Adamek–Rosicky chapter remains WANTED, but it is unnecessary for independently checking this item's source. The mathematical statement, proof argument, statement dependencies, citations, and search records are unchanged. Added this independent review; no new nodes were needed.
