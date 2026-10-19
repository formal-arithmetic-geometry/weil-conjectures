# Stage-1 report: lem-coef-combinatorial-cofibrant-density

## Files written

- `dag/nodes/sec-six-functors/lem-coef-combinatorial-cofibrant-density.json`: statement, now split into five steps. The statement is unchanged. The three explicit cardinal hypotheses suffice at the stated fixed cardinal.
- `dag/nodes/sec-six-functors/lem-coef-presentable-canonical-density.json`: statement, Mathlib leaf. This is ordinary essential smallness, density and cardinal-filteredness of presentable objects, without any model or homotopy conclusion.
- `citations.json`: eight entries, one for each step/node pair, quoting the cited statements literally.

No Lean, compiler, Lake, shared-project files, unit records or launcher files were changed. Only the required delivery tool may prepare its own temporary worktree. There is one new node, which is one Mathlib leaf.

## Attachments

None. Searches of `/home/ubuntu/weil-src-slopmaster2/WeilConjectures/` for the exact blueprint tag, the item id, Dugger, cofibrant density and presentable/cofibrant wording found no project declaration for the item. The same reference searches in the read-only upstream master did not give an attachment. Ordinary density is present in Mathlib rather than in a project declaration.

## Wanted literature

WANTED: Daniel Dugger, *Combinatorial Model Categories Have Presentations*, Remark 2.5, Proposition 4.7 and Appendix A.3-A.5, printed pp. 180, 187, 198-199, for lem-coef-combinatorial-cofibrant-density. Read the PDF online at https://www.sas.rochester.edu/mth/sites/doug-ravenel/otherpapers/dugger-comb.pdf; it is not archived under literature/. Nothing was downloaded into the shared project or sandbox. In accordance with the brief, proof_origin.by is agent for the expanded proof, although its argument was checked against Dugger.

No Stacks tag states this homotopy-density theorem or the ordinary locally presentable category input. The source identifies the actual proposition and Mathlib declarations rather than assigning an unrelated Stacks tag.

## What was wrong or missing

The imported item was a statement-only frontier node, with no proof and no project attachment. Its statement is correct and needed no repair. Dugger states the result for sufficiently large regular cardinals; the item's three explicit hypotheses are exactly the inputs used by the proof. In particular, one must not cite the existential bounded-resolution theorem to obtain information at this already fixed lambda. The new leaf gives ordinary density for every locally lambda-presentable category at its own lambda.

The genuine remaining comparison is between the comma category of all presentable domains and that of cofibrant presentable domains. The proof now constructs both functors, their natural transformations, and the representative conjugations explicitly. It does not assert that the cofibrant comma category is filtered. It also verifies the augmentation using a lift of projective replacements, so invertibility in the homotopy category is not silently turned into equality of actual maps to X.

The current main-20261015 blueprint ancestor proof, paragraph 2, concerns the coherent finite-coefficient mapping-complex adjunction. The inherited presheaf/model-presentation ancestry makes this a technical input to that paragraph. The unit record sk-prop-sf-biduality-general and chapter sec-six-functors were read; no unit or chapter route was replaced. No SGA source was used.

## Unfinished work

No part of this item's one-level split is left unfinished. The existing reindexing and Reedy/model-category nodes are cited by their statements and remain for their own workers; their proofs are not imported as assumptions beyond those statements. The added ordinary-category leaf needs no further split.

## Not duplicates

lem-coef-presentable-canonical-density vs lem-coef-combinatorial-cofibrant-density: the new leaf is entirely ordinary category theory and asserts no weak equivalence or homotopy colimit; the item proves the cofibrant homotopy-density conclusion using the replacement functors and filtered weak-equivalence hypothesis.

lem-coef-presentable-canonical-density vs lem-coef-combinatorial-bounded-resolutions: bounded resolutions existentially choose a suitable cardinal and model-category replacement data; the new leaf proves essential smallness and ordinary density/filteredness at any specified locally presentable cardinal, with no model category or resolution.

lem-coef-presentable-canonical-density vs lem-coef-object-presentability-rank: the latter assigns a presentability rank to one arbitrary object and does not state the canonical density or comma-filteredness theorem.

lem-coef-presentable-canonical-density vs lem-coef-space-yoneda-density: the latter is space-valued infinity-presheaf Yoneda density, not ordinary presentable-object density in a locally lambda-presentable category.

Before adding the leaf I searched the whole DAG for the exact Mathlib declaration names, Remark 2.5, density, canonical colimits and cardinal-filtered comma statements, and read the potentially relevant accessible-category and bounded-resolution node statements. The blueprint searches for `presentable`, `density`, `cofibrant`, `locally presentable` and `canonical colimit` found no matching imported statement. Both ordinary-category semantic phrasings and the Loogle/grep results are recorded from searches.jsonl. The Mathlib leaf is a conjunction of three instance statements, one per clause, as allowed by the leaf rule.

## Review by Q48

I read Dugger's Proposition 4.7(i)-(ii), its full proof on printed p. 187, Remark 2.5 on p. 180, and the Appendix A reindexing discussion on pp. 198-199. The source proves the all-presentable case by ordinary density and preservation of objectwise weak equivalences under filtered colimits, then compares the cofibrant subcategory by the replacement functor. My five steps give exactly that argument. Reading the current blueprint ancestor confirmed that this is below its second-paragraph mapping-complex input rather than a change to its unit route.

For the new leaf I read Mathlib/CategoryTheory/Presentable/Dense.lean in full, CardinalFilteredPresentation.lean:130-178, LocallyPresentable.lean:34-57, and the definitions of IsDense and DenseAt in Functor/KanExtension/Dense.lean:47-55 and DenseAt.lean:46-61. Loogle names the exact dense-inclusion and comma-filteredness instances; the source also supplies the essentially-small instance, and the local-presentability-to-accessibility instance discharges their hypotheses. The grep searches on the Presentable directory give the relevant file paths and lines. This is an exact clause-by-clause Mathlib match; no comparison between two different notions of presentability is postponed. Hom preserving filtered colimits is exactly the ordinary notion in both places.

Step 1 uses the new leaf's essential-smallness, cardinal-filteredness and colimiting canonical cocone, at the very same lambda from the item. I checked the model definition in lem-coef-reedy-model-structure: its cofibrations are a lifting class, so cofibrancy is invariant under isomorphism. Choosing representatives, transporting comma arrows by conjugation, transferring cocones along the inverse equivalences, and counting the small object/arrow sets are written out in the step. This justifies applying the filtered-colimit hypothesis to a genuinely small comma category. There is no illicit colimit over an unrestricted large category.

Step 2 uses the statement of lem-coef-hocolim-reindexing-zigzags to obtain projective replacements and its definition hocolim = colim Q. The weak equivalence of colim Q to colim U is an immediate application of the item's explicit filtered-colimit hypothesis, after Step 1 establishes filteredness; it is not an extra model-category theorem hidden in the prose. The model definition gives weak-equivalence composition/two-out-of-three. I marked this computation elementary because every map and the hypothesis being applied are displayed.

Step 3 only uses the model definitions and the replacement data assumed in the item. Both preservation of lambda-presentability by Q and cofibrancy of Qb are checked before restricting Q into C. The formulas with theta give actual functors for any representative choices, and naturality checks the comma morphism equation. The transformations gf to id and fg to id are written separately, with the correct value functor on each side. This is elementary construction, not a new lemma restating a clause of the item.

Step 4 cites lem-coef-hocolim-reindexing-zigzags for its actual statement about two inverse functors up to diagramwise weak-equivalence transformations. I opened that node and verified both zigzag conditions, the direction g:J to I, and its conclusion about an actual comparison being a weak equivalence. No weaker nerve-contractibility result is substituted for that statement.

Step 5 again uses the reindexing node's projective model structure: g-star p_I is an objectwise trivial fibration, hence a projective one. The model lifting axiom from the Reedy/model node gives the lift from Q_J, which is projectively cofibrant. Taking colimits yields a representative of the canonical comparison. Its composite to X has component u p_J, so equality with the required augmentation follows from the colimit universal property. Thus composition of the two actual weak equivalences proves the requested assertion, including the particular augmentation map. This explicit lift is the detail I added instead of leaving the final compatibility implicit.

I checked the imported statement and the new leaf on the initial object, on a one-object category, and in a category with the discrete model structure (weak equivalences are isomorphisms). The argument still works: the full presentable comma category is nonempty and filtered, cofibrant replacements land in C, and no assertion of filteredness of J is needed. Lambda = aleph_0 is allowed; there is no countable-closure argument that would require an uncountable cardinal. Non-fibrant X is permitted throughout: neither replacements of the domain nor projective diagram lifts impose a fibrancy condition on X. The three fixed-cardinal hypotheses are used separately, in Steps 1, 2 and 3.

I checked delivery-errors B-E: the leaf has a self-contained statement with inline definitions, sources and exact Mathlib declarations/files/lines and has no proof sketch; the duplicate search found no usable existing ordinary density statement; every non-elementary input is a cited statement; each step/node pair has a verbatim quote in citations.json; elementary steps give the actual formulas rather than invoking an unnamed standard theorem. No source statement was weakened, no new node repeats the homotopy-density conclusion, no auxiliary proof is hidden in a new unsplit node, and no dependency on the item or a downstream presentation theorem was added. The original statement and all maintainer metadata are retained.

A final logged grep corrected one bibliographic off-by-one error: the local-presentability-to-accessibility instance starts at LocallyPresentable.lean:53. Both the leaf's search verdicts and its match explanation now use that exact line. The mathematical statement and proof were unaffected; the final sandbox is dry-run again after this correction.

The first server preflight returned the leaf for lacking a separate numeric mathlib_match.line field. I added line = 60, verified by the logged directory grep and the source reading; the other matched clauses retain their files and exact lines in how. No mathematical change was required.

## Second reading by Q48

- Item statement: checked hypothesis by hypothesis against Dugger Proposition 4.7(i)-(ii), printed p. 187, Remark 2.5, printed p. 180, and the fixed-cardinal Mathlib density instances; PASS. The explicit three hypotheses replace Dugger's sufficiently-large-cardinal choice exactly, and no fibrancy hypothesis is required.
- Step 1: checked the ordinary-density leaf, the lifting-class definition in lem-coef-reedy-model-structure, and Dugger 4.7(i); PASS. Presentability and cofibrancy survive the representative isomorphisms, the comma categories are small, and both canonical density and cardinal-filteredness pass through their equivalence.
- Step 2: checked the projective replacement definition in lem-coef-hocolim-reindexing-zigzags, the functorial weak factorization systems in lem-coef-reedy-model-structure, and the item's filtered-colimit hypothesis; PASS after specifying that the chosen replacement map is a trivial fibration. This is the precise input later pulled back in Step 5.
- Step 3: checked both comma-functor formulas and both natural transformations against Dugger 4.7(ii), and the cited model definitions; PASS. The hypotheses ensure that each replacement domain is presentable and cofibrant, and the displayed naturality equation has the correct source and target.
- Step 4: checked every hypothesis and the conclusion of lem-coef-hocolim-reindexing-zigzags against Step 3 and Dugger Proposition A.4 / Remark A.5, printed pp. 198-199; PASS. Both transformations become weak equivalences on their respective value diagrams.
- Step 5: checked the cited projective fibrations and weak equivalences, the model lifting axiom, and the colimit universal property; PASS. Restriction preserves the chosen trivial fibration, the cofibrant-domain lift gives the comparison over the value diagram, and its augmentation has exactly the components of the required map to X.
- New node lem-coef-presentable-canonical-density: checked all three clauses against Mathlib CategoryTheory/Presentable/Dense.lean:60-73, CardinalFilteredPresentation.lean:174-178, LocallyPresentable.lean:53, and the definitions of dense and DenseAt; PASS after naming its comma morphism t. It is a Mathlib leaf, not an elementary auxiliary claim, a duplicate, or a reformulation of homotopy density.

I independently ran LeanFinder, Loogle and source grep with different queries. Their actual records are appended to searches.jsonl and copied into the leaf's mathlib_searches. The whole-blueprint searches for cofibrant and presentable, and the DAG searches for the density instances, canonical filtered density, Remark 2.5 and related accessible-category statements found no existing ordinary density node. The nearby bounded-resolution node chooses a cardinal existentially, object-presentability-rank handles one object, and the infinity-category density nodes concern different diagrams. Read-only searches of both named Lean source trees and dag/lean_names_upstream.json found no project declaration to attach. The current blueprint ancestor proof and the existing unit/chapter records preserve the inherited presentation route. No Stacks tag states this result, so no unrelated Stacks citation was added.

Edge cases checked: the terminal one-object category; Set with the discrete model structure, lambda = aleph_0, and X empty or a singleton; pointed module categories with the discrete model structure and X = 0; and nonfibrant X in the general argument. The full presentable comma category is filtered even at aleph_0; the cofibrant comma category need not be filtered and is never claimed to be. The three cardinal assumptions are used individually, and no uncountability, properness, enrichment or fibrancy is introduced.

Changes made:

- Renamed the new leaf's comma arrow to t and wrote its equation as u' t = u. The former equation used the object name a as a morphism. Updated the corresponding verbatim citation quote.
- Specified the projective replacement in Step 2 by functorial cofibration/trivial-fibration factorization, so Step 5's lifting hypothesis is explicit. Removed the unnecessary assertion that this particular lifting construction works with arbitrary replacement maps; the chosen replacement computation already proves the assertion.
- Added the three independently executed Mathlib search records. The item's statement, dependencies, the single new Mathlib leaf classification, and the first worker's review are otherwise retained. All eight citation quotes were rechecked as literal substrings of the corresponding node statements.
