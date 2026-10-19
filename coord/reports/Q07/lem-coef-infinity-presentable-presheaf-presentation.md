## Files written

- `dag/nodes/sec-six-functors/lem-coef-infinity-presentable-presheaf-presentation.json`: eight-step split, repaired against the current DAG; seven existing proof dependencies. Mathlib verdict: no match for this infinity-category statement.
- `citations.json`: fourteen literal quotations, one for every step/node citation, refreshed against current statements.
- `report.md`: this repair report. The retained preparation scripts and search log are sandbox materials, not delivery files.

New nodes: 0. Mathlib leaves: 0. No Lean was written or compiled.

## Attachments

None. The renewed read-only searches in slopmaster2 and exact upstream master under `WeilConjectures/` for the blueprint id, `PresheafPresentation`, reflective presheaves and `restrictedYoneda` returned no declaration stating this theorem. The earlier terminology and upstream-name searches are retained findings, not a claim that an upstream sorry is a proof.

## WANTED

WANTED: J. Lurie, Higher Topos Theory, https://people.math.harvard.edu/~lurie/papers/HTT.pdf, Theorem 5.5.1.1 and Sections 5.1–5.3, for this item and its existing infinity-category inputs. I opened the online PDF during this repair. It is not archived under literature; no download or literature write was made. There is no Stacks tag for this quasicategorical result. The proof remains agent-written from the cited existing nodes. No SGA source is used.

## Returned landing refusal and repair

Return: the reader had approved head `1b8a7db392`, but landing refused because `def-coef-presentable-infinity-category` had changed since review. I compared the retained split and its old literal citations with the current shared DAG. The item remains unsplit on current main; its statement and maintained chapter/unit metadata are unchanged. Of the six previously cited proof inputs, only the presentability definition's statement failed the old quotation comparison. The other five statements still contain their old quotations verbatim.

The change is mathematical size bookkeeping, not merely wording. Previously compactness asserted a small-space colimit comparison. The current definition instead uses the coherent corepresented functor with values in the larger space category S_Uprime and requires its image cocone to be colimiting there. The retained step 2 had taken a colimit in S_U directly from that definition, which the current statement no longer supplies.

I repaired step 2 rather than re-pushing the unchanged proof. It now first applies compactness in S_Uprime, then uses the existing `lem-coef-spaces-small-colimits-universe` for existence of the small colimit and preservation by the fully faithful universe inclusion. Comparing the two colimit cocones gives an equivalence of their apices in the larger category; full faithfulness lifts the inverse and both inverse homotopies to small spaces. Only then does the pointwise criterion prove preservation by restricted Yoneda. The existing `lem-cbc-enhanced-functor-cone-calculus` is now also cited in this step for the contractible initial-cocone comparison, and its tool-use explanation covers both steps 2 and 7. All fourteen quotations were regenerated and checked against current statements. The definition, the universe-change lemma and every other existing node were left read-only.

The delivery command reconstructs a single delivery on current `origin/newtargets-dag` in its temporary worktree. I run only its `--no-push` route: the next fresh reader must revalidate and deliver. No git command was run in the shared repository.

## Corrections and scope

The item's mathematical statement is unchanged. The inherited split already added the missing presentability definition to `stmt_deps`; this repair preserves that correction and replaces the obsolete use of its statement. The item is not a unit key node, so there is no unit-realization edit. Its historical blueprint ancestry and chapter/unit binding remain intact.

I read the chapter and unit records and the current main-20261015 ancestor proof of `prop-coef-integral-exceptional-adjoint`, specifically the finite-stage mapping-complex adjunction before the derived inverse limit. This remains a foundational tool within the existing enrichment/adjunction chain; no geometric step of the unit is replaced. The source theorem has the stronger accessible-localization formulation. This item asks only for the reflective presentation and its explicit adjunction consequences; the compact-generator proof does not use the parent representability or general presentable-adjoint theorem.

## Unfinished work

None within this one-level split. Existing unsplit dependencies remain assigned DAG items. No new statement-only nodes are needed. The requested stage-1-only prohibition takes precedence over the repair template's word “compile”: no compiler, Lake, build tool, or Lean-writing action was used.

## Not duplicates

No new nodes. I searched the current DAG for small colimits of spaces and universe change, and ran the blueprint-reference search for “small colimits of spaces” and “presheaf presentation”; neither blueprint query had an exact hit. The existing `lem-coef-spaces-small-colimits-universe` states exactly the new ingredient, so I reused it instead of creating an elementary, duplicate, or restatement node. It belongs to the item's unit.

The original fourteen logged msearch records and their recorded verdicts are retained unchanged. They include multiple semantic phrasings, grep, LeanSearch, LeanFinder and Loogle, with the rejected Loogle identifier explicitly marked invalid rather than negative evidence. No new searches are claimed in this repair. The original results distinguish ordinary category/Type-valued presheaf theorems from space-valued quasicategories; there is no Mathlib leaf to add.

## Review by Q07

I read the worker rules, stage-1 contract, SETUP's three levels, GOAL, dag-sync, and delivery-errors B–E; reopened the item, its eight steps and every cited statement; and checked the current source places. In HTT I reopened Definition 5.3.4.5 (compactness via a larger-space-valued corepresented functor), Definition 5.5.0.1 and Theorem 5.5.1.1(1),(5), Theorem 5.1.5.6 (free cocompletion), Lemma 5.1.5.2 (evaluation), and Corollary 4.2.4.8 (small colimits in spaces). The universe-inclusion and preservation clauses used in the repair are the statement of the existing universe-change node; I do not infer them from its proof or from the definition of spaces. Its source points to the Kan-model homotopy-colimit construction in HTT 4.2.4.1/4.2.4.8, with universe invariance. There are no new nodes needing additional source or Mathlib-leaf checks.

1. Step 1 uses the current `def-coef-presentable-infinity-category` for a regular cardinal, an essentially small full family of compact generators, local smallness, all small colimits and small filtered presentations. Those clauses survive the revision. The quasi-inverse diagram is written explicitly, so replacing the essentially small family by a small category does not add a density theorem.
2. Step 2 uses the same definition only for the larger-space colimiting cocone it actually states. `lem-coef-infinity-yoneda-presheaf-limits` supplies coherent Yoneda and the objectwise criterion. The newly cited existing universe-change statement supplies small colimit existence, full faithfulness and preservation; all three clauses were read. The cocone-calculus statement supplies the initial-object contractibility used to compare the two larger colimit cocones. The index I and parameter D opposite are U-small; the intermediate comparison alone takes place in Uprime, and both apices have small representatives. I wrote out the inverse-lifting argument, so neither reflection of equivalences nor descent of the colimit is an uncited black box.
3. Step 3 uses the colimit mapping-space tests in `lem-coef-infinity-yoneda-presheaf-limits` and the arbitrary-presheaf formula of `lem-coef-infinity-yoneda-evaluation`. Both state the precise assertions used. Evaluation at identities identifies the comparison with the actual restricted-Yoneda map, including homotopies; the limit index I opposite is small.
4. Step 4 uses the full restriction equivalence in `lem-coef-infinity-presheaf-free-cocompletion` with target C. Step 1 supplies its all-small-colimits hypothesis. Its statement gives both the colimit-preserving L and Lj equivalent to f, as well as the local smallness and colimits of P.
5. Step 5 uses the mapping-space colimit tests, the evaluation node and free cocompletion with target S opposite. Small limits in S are explicitly stated by the first input, so the opposite target has the needed colimits. The restriction equivalence includes natural transformations and higher simplices; using its one quasi-inverse on the C-opposite-parameterized restrictions gives coherence in both variables. There is no colimit or limit indexed by large C or P.
6. Step 6 uses `lem-coef-infinity-pointwise-adjoint-criterion` for coherent units, counits and triangles, and Yoneda full faithfulness from the Yoneda/limits node to identify its representing right adjoint with the constructed i. The formulas for the two adjunction maps follow by naturality at identity maps. The cited node really states the coherent adjoint criterion, rather than just a definition of adjunction.
7. Step 7 proves the two counit inverse equations using the full-faithfulness comparison and the first triangle already proved. The vertexwise-equivalence clause of the cocone-calculus node then makes the counit a natural equivalence. Its parameter C is small in the enlarged ambient universe; the original colimits remain U-small. That exact clause, as well as the separate step-2 initial-object clause, has its own literal quotation.
8. Step 8 uses the second triangle and the equivalences established earlier. Cancelling the counit equivalence proves that L(eta) is invertible. The formula i(h) composed with eta identifies the last displayed map with actual unit precomposition. This step is elementary composition of the previously established mapping-space equivalences.

For C1–C4 I checked each of the fourteen step/node uses against its current statement; no use is taken from a dependency's proof. Every quote is verbatim. For C5 and D1–D3 no new nodes are created and the only added dependency was found in the current DAG. I walked all seven dependencies transitively through statement and proof edges and found no path back to this item (C6/D4). No new lemma restates the item or carries its conclusion. There is no hidden induction or omitted-details step (D5). The generic off-unit cocone-calculus tool remains declared in split_report; all other mathematical inputs lie in the item's unit.

For E1–E7 I checked the cardinal and universe hypotheses at steps 1–3, local smallness at the Yoneda applications, all-small-colimit hypotheses for free cocompletion, opposite variance in step 5, and the larger-universe parameter at step 7. For C terminal, D terminal gives P equal to spaces, i the terminal space and L the unique functor; the universe comparison in repaired step 2 is the identity comparison for its filtered constant-point cocone. For C equal to spaces the argument retains whole mapping spaces, not only components. Empty C is excluded because presentability includes the empty colimit; a filtered index is nonempty by the definition's empty test shape. Empty small colimits of P are preserved by L, without assuming i preserves them. No compact projectivity, stability, additivity, finite-generation or extra completeness hypothesis was added. There is no statement dispute or source error.

This review supersedes the retained earlier reading at returned head 1b8a7db392. The concrete repair is the revised step 2, its additional existing citations, the changed proof-dependency union and tool-use explanation, and the refreshed current quotations. A fresh second reader must inspect these changes before pushing.

## Second reading by Q07

I reread the item statement against HTT Theorem 5.5.1.1(1)--(5), Definition 5.2.7.2 and Proposition 5.2.3.5, and checked every universe, smallness, adjunction, unit/counit, colimit, and full-faithfulness clause. I also read HTT Definitions 5.3.4.5 and 5.5.0.1, Theorem 5.1.5.6, Lemma 5.1.5.2, Propositions 5.1.2.2, 5.1.3.1--5.1.3.2, and Corollary 4.2.4.8 at the cited online source locations. The source is an infinity-categorical theorem and has no Stacks tag.

1. Step 1 checked against the presentability definition: the chosen essentially small compact full subcategory, small equivalent indexing quasicategory, filtered presentations, local smallness, and all-small-colimit hypotheses are all present; verdict: sound and elementary.
2. Step 2 checked against the revised larger-space compactness clause, the pointwise Yoneda/colimit criterion, the small-spaces universe-change lemma, and the initial-cocone contractibility clause; the comparison map, inverse lifting by full faithfulness, and restriction to the small universe are explicit; verdict: sound after the retained repair.
3. Step 3 checked against both mapping-space colimit tests and representable evaluation, including the identity evaluation and coherent naturality identifying the displayed equivalence with the map induced by i; verdict: sound.
4. Step 4 checked against the free-cocompletion restriction equivalence with target C, including its all-small-colimits and higher-transformation clauses; verdict: sound.
5. Step 5 checked variance (P^op-valued mapping presheaves), small limits in spaces, opposite-target colimits, and coherence in the C^op parameter; verdict: sound.
6. Step 6 checked the pointwise adjoint criterion and Yoneda full faithfulness, including coherent assembly of the representing objects and the stated unit/counit formulas; verdict: sound.
7. Step 7 checked the counit precomposition equivalence, both inverse equations, and the vertexwise-equivalence criterion in the enlarged ambient universe; verdict: sound.
8. Step 8 checked the second triangle, cancellation of the counit equivalence, and the unit-precomposition mapping-space calculation from steps 3, 6, and 7; verdict: sound elementary composition.

There are no new nodes in this split, so B1--B7 and the Mathlib-leaf search requirement are vacuous for new nodes. I nevertheless searched the current DAG for duplicate restricted-Yoneda, presentability, small-space-colimit, and universe-change statements; the existing dependencies cited by the split are the unique relevant nodes. The recorded LeanSearch, Loogle, LeanFinder, and grep searches were checked as actual logged queries; none is an exact match for the space-valued quasicategorical theorem.

I tested the statement and proof on the terminal infinity category (where D, L, and i reduce to the expected trivial presentation), on the infinity category of spaces (where the full mapping spaces, not just components, are used), and on the empty colimit and empty filtered-shape cases. No hypothesis was added or dropped, no source error or statement dispute was found, and no node or citation required further change. The only retained repair is step 2's explicit descent from S_U' to S_U, together with its existing-node citations and refreshed literal quotations.
