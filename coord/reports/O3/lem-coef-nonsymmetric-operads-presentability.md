# Stage-1 report: lem-coef-nonsymmetric-operads-presentability

## Files written

- dag/nodes/sec-six-functors/lem-coef-nonsymmetric-operads-presentability.json — item, statement, now split; no Mathlib match. Statement unchanged.
- dag/nodes/sec-six-functors/lem-coef-categorical-pattern-model.json — one new statement-only node, unsplit; no Mathlib match. It states the general categorical-pattern combinatorial simplicial model theorem, not presentability of operads.
- citations.json — verbatim statement excerpts for every node used by every item proof step, with additional excerpts for the exact axioms and enrichment used.

No Lean, unit, chapter, launcher, shared-repository or live-project file was written. Only this item's sandbox was written. No compiler, Lake or git command was run by the worker.

## Attachments

None. Searched the read-only WeilConjectures project sources for the exact item id, nonsymmetric, operad, and categorical-pattern names. No declaration states this theorem. The upstream master source was also searched as reference material, without treating its sorry declarations as finished proofs. The original item has no Lean attachment; its audit is now explicitly state none on both branches.

## WANTED

WANTED: Gepner–Haugseng, Enriched infinity-categories via non-symmetric infinity-operads, Advances in Mathematics 279 (2015), Definitions 3.2.1–3.2.3, Example 3.2.4(i), Theorem 3.2.5, Corollary 3.2.6 and Definition 3.2.7, printed pp.606–608, for the item and lem-coef-categorical-pattern-model. Read the published PDF online at the source URL already in the item; no archive was downloaded or written to the shared literature. The node's proof_origin is agent because the shared archive is absent. The standard marked simplicial enrichment in the new theorem is the enrichment used to form the fibrant simplicial category in Definition 3.2.7.

WANTED: Lurie, Higher Algebra, Proposition 1.3.4.22 and the model-localization discussion in Section 1.3.4, for the existing combinatorial-localization and simplicial-model comparison tools. The shared archive is absent, and an online fetch timed out. This delivery reuses the full statements already in the DAG; it does not create another node for those results or claim to have reread that PDF. No Stacks tag states the categorical-pattern or infinity-operad presentability theorem, so substituting an ordinary-category Stacks theorem would be incorrect. No SGA source is used.

## Problems found and repaired

The unsplit item correctly includes the relative mapping-fiber axiom, the terminal arity-zero fiber, and smallness conventions. It needed an argument rather than a replacement statement. I left every clause unchanged.

The nearby lem-coef-marked-operadic-model-structures is not safe to cite here: its statement depends on lem-coef-operadic-algebra-presentability, whose proof already uses this item. That would create a dependency cycle. Furthermore its statement does not assert combinatoriality. I introduced the general categorical-pattern theorem, explicitly retaining the combinatorial hypothesis needed by the presentability theorem. I did not copy an operad-presentability clause into a new node.

The coherent nerve of a simplicial fibrant-object category, rather than the ordinary category with a discrete Hom set, is necessary. The final proof explicitly names the enrichment and the existing simplicial-model localization comparison. While reviewing step 3 I added the cocartesian mapping criterion and the argument producing a two-sided inverse for a marked edge above an identity. I also cited lem-coef-infinity-pointwise-equivalences for passing from the evaluated equivalences to equivalence edges in the functor category. Thus the explanation of the space of maps hides neither criterion.

I read the chapter and inherited unit records, the main-20261015 statement and proof files for the blueprint ancestor (now located under sk-thm-sf-package), and the ancestor's current DAG proof. The retained ancestry points to its finite-coefficient mapping-complex adjunction before total derived limit. This is a subordinate foundational split along the existing ancestry, not a change to the unit or the blueprint target. The inherited chapter/unit binding is preserved, as required by coord/dag-sync.md.

## Not duplicates

lem-coef-categorical-pattern-model vs lem-coef-marked-operadic-model-structures: the new node is the general small categorical-pattern theorem with combinatoriality and explicit fibrancy conditions; the existing node concerns two specific operadic structures, their identity Quillen functor and richer marked enrichment, lacks combinatoriality, and is downstream of this item. It cannot supply the required theorem without a cycle.

lem-coef-categorical-pattern-model vs lem-coef-nonsymmetric-operadic-tensor-adjunction: the existing node states the derived categorical tensor, its algebra-category adjunction, colimit preservation and universe compatibility; the new node establishes a general model structure and asserts none of that tensor adjunction. The existing node also depends on this item.

lem-coef-categorical-pattern-model vs lem-coef-nonsymmetric-operads-presentability: the new node constructs a model structure for arbitrary small pattern data, with no presentability conclusion for an infinity category. The item's steps specialize its cones, identify all fibrancy conditions and the coherent category, and apply two independent existing localization theorems.

lem-coef-categorical-pattern-model vs lem-coef-combinatorial-localization-presentability: the existing node assumes a combinatorial model category and proves its localization presentable; it does not construct any marked categorical-pattern model category. The new theorem supplies exactly that input.

Searched the entire DAG for categorical pattern, combinatorial model, nonsymmetric, marked simplicial, B.0.20 and matching source places. The whole-blueprint searches for categorical pattern, nonsymmetric, model structure, B.0.20, operad and presentab found no equivalent blueprint statement. The only operad blueprint hit was a framework remark, not this model theorem. Thus same_as is empty for both delivered nodes. Blueprint ancestor command returned prop-coef-integral-exceptional-adjoint; the new node's via list prepends this item to its retained via chain.

## Mathlib searches

All searches were made using the required msearch.py N3 item command. searches.jsonl is the command's unmodified log; each appended/new mathlib_searches entry quotes that log's exact tool/query and actual response digest/top results. The item was searched as both infinity-operad accessibility/colimits and planar-operad presentability. The child was searched as both a categorical-pattern model theorem and the cocartesian/Segal-limit marked model, using LeanFinder, Loogle, LeanSearch and grep. The broad combinatorial grep was repeated in AlgebraicTopology so unrelated combinatorics hits could not obscure a relevant model theorem. All services returned answers, with no unavailable response.

Read the plausible hits in the read-only Mathlib checkout: QCat in Quasicategory/StrictBicategory.lean:48–55 is an ordinary full subcategory with Cat enrichment; modelCategoryQuillen.cofibrations_eq and fibrations_eq in SimplicialSet/CategoryWithFibrations.lean concern unmarked Kan–Quillen simplicial sets; ModelCategory in AlgebraicTopology/ModelCategory/Basic.lean gives axioms, not the categorical-pattern construction; IsAccessibleCategory in CategoryTheory/Presentable/LocallyPresentable.lean:87–90 uses ordinary set-valued Hom. No hit supplies either infinity-categorical theorem, even by one-line specialization. There are zero Mathlib leaves.

## Review by N3

I read the published Gepner–Haugseng PDF's Section 3.2 opening and Definitions 3.2.1, 3.2.3, Example 3.2.4(i), Theorem 3.2.5, Corollary 3.2.6 and Definition 3.2.7. The new statement is the fully-scaled categorical-pattern theorem: the base is a small quasicategory, the markings contain degeneracies, the family and each cone are small, every cone edge is marked, the classifying fiber diagram is a limit, and each cocartesian section is a relative limit. I included both independent limit conditions; omitting the relative one would produce a different notion of operad. The conclusion includes combinatoriality, monomorphism cofibrations, the exact marking of fibrant objects, and the simplicial marked mapping construction. It has no proof and no proof dependencies; its next worker must split this general theorem.

For step 1 I checked the new theorem's hypotheses against the concrete data: the discrete K_n has exactly n vertices, its left-cone vertex maps to [n], its outgoing arrows are the n consecutive-interval projections to [1], and its only other arrows are identities. The family is countable and small in the smaller universe; the theorem's conclusion explicitly supplies the combinatorial simplicial category and cofibrancy. This is a genuine application of the new statement, not a claim obtained from its source label.

For step 2 I checked both cited statements. The new statement gives each of the four fibrancy requirements and the exact marking. The straightening node explicitly identifies the classifying diagram's value with the fiber and its arrows with cocartesian transport, and explicitly identifies finite products in Cat_infinity. Thus condition (iii) is the n-fold Segal product, while the displayed relative-limit formula (iv) becomes exactly the item's product of mapping fibers. This is an elementary specialization of the cited statements, in both directions; no operadic rectification, additional colors hypothesis, or Kan condition on ordinary operads is introduced. For n=0 both limits are empty limits, so the fiber is terminal and the mapping fiber is contractible. For n=1 the cone arrow is the identity and both comparisons reduce to identities.

For step 3 the new theorem's displayed simplicial Hom provides the parameterized marked maps, and its final clause guarantees Kan mapping objects on fibrants. Definition 3.2.7 fixes their coherent nerve as the source's model of the infinity category. The mapping-criterion node supplies a homotopy pullback square for each cocartesian edge; when its base is an identity this says precomposition is an equivalence. The proof now writes the left and right inverse argument explicitly, establishing the interpretation of the parameter arrows as equivalences. I opened lem-coef-infinity-pointwise-equivalences, which says exactly that an edge of Fun(K,C) is an equivalence if and only if every vertex component is; its hypotheses apply with the small source operad K and fibrant target quasicategory C. I also checked that its dependency closure does not contain the item. The construction retains simplicial compositions. It therefore matches the full intended coherent mapping spaces, rather than replacing the infinity category by its ordinary homotopy category. Every object is cofibrant by step 1, so fibrant and bifibrant subcategories agree exactly.

For step 4 I opened both localization-tool nodes and the presentability definition and checked their complete statements. The combinatorial-localization node really gives infinity-categorical presentability with no monoidal hypotheses for its first assertion; the extra monoidal conclusion is not invoked. The simplicial-model comparison node really gives the equivalence with the coherent nerve of bifibrants and the entire functor-category universal property, not merely an equivalence of ordinary homotopy categories. The new theorem supplies the former's set-generated/functorial factorization conditions and the latter's simplicial model structure. The presentability definition really means accessibility and every small simplicial colimit. All size conventions use small objects in U and the category of them in U'; none applies a small-index theorem to a large diagram. I checked each exact citation excerpt against its node statement; additional excerpts record the finite-products clause, the new fibrancy formula and the enrichment used at their respective steps.

I tested the new general statement on an empty base (the slice has only the empty marked object), a point base with identities marked and no prescribed cones (the categorical marked model), and the singleton cone (no new limit restriction). I tested the specialized split at arities 0 and 1 and on the terminal operad Delta^op over itself: all its fibers and required mapping fibers are points, and every Segal comparison is an equivalence. The empty total simplicial set fails the arity-zero Segal condition, so it is not accidentally identified as fibrant. No counterexample or statement dispute remains.

I checked B through E of delivery-errors against these files: every new object is introduced, all nonbasic notions have an existing statement/definition dependency or an inline definition, TeX is singly escaped after JSON decoding, no unsplit node contains a proof, no clause of the item is relabelled as a node, and the non-elementary inputs are cited statements. Before selecting the tools I traversed their transitive statement/proof closures and verified that none reaches this item or its parent. The server check_dag accepted the first draft; the final version adds only the already-checked acyclic mapping criterion. No definition or target statement is weakened, and no unit route is replaced.

## Unfinished work

No part of this one-level split is omitted. The sole new statement is intentionally unsplit. Shared source archival is requested above. The second reader must independently read the sources and this split and perform the eventual delivery; this worker will run only --no-push and leave the accepted sandbox in place.

## Continuation review by N3

I reread the accepted draft against the online published Section 3.2 and the current shared DAG. Definitions 3.2.1 and 3.2.3, Example 3.2.4(i), and Theorem 3.2.5 agree with the general-pattern input and its specialization. Theorem 3.2.5 states combinatoriality explicitly, so the first assertion of the existing localization-presentability theorem applies; Definition 3.2.7 identifies the coherent nerve used here. I repeated the project-source attachment search on both named read-only checkouts: there is no declaration for the id or its operad/pattern notion. The Loogle model-category search was rerun and still returns model-category axioms, not the categorical-pattern model construction.

I found and repaired one missing direction in step 3. The earlier text showed that a marked parameterized family has equivalence parameter arrows, but did not explain why an equivalence family with inert-preserving vertex functors preserves mixed marked edges. I added the explicit triangle factoring a mixed edge into a source edge and a parameter edge. The existing cocartesian-composition node supplies closure under that triangle; its exact statement is now quoted in citations.json. Its hypothesis is an inner fibration of quasicategories, which holds for every fibrant target of step 2; no global cocartesian-fibration hypothesis is used. The mapping criterion supplies the converse for equivalences over identities. This is an elementary calculation from the cited statements, with no new node. I checked the dependency closure of this additional citation and the other tools for cycles and checked every quote verbatim against its statement.

The other nearby model statements were also reread: the relative Cartesian model concerns lifting over all base edges without prescribed limit cones, the point model concerns only a point base, the cone-straightening theorem is a Quillen equivalence for those models, and the finite-marking criterion characterizes only the point model's fibrant objects. None states the general categorical-pattern theorem needed here. They introduce no duplicate or new same-tag pair.

## Validation

The earlier draft passed the required no-push preflight again at 0ec9fca884. After the continuation repair of the converse marking condition in step 3, the final files and this report are submitted together to the same required no-push dry run. No push is authorized or performed by this worker.

## Second reading by N3

- Item statement: checked against Gepner–Haugseng Definition 3.1.3 and Section 3.2, including inert lifts, inert Segal equivalences, relative mapping-fiber limits, morphisms preserving inert cocartesian edges, and the arity-zero empty product; verdict: agrees clause by clause.
- New node `lem-coef-categorical-pattern-model`: checked against Definitions 3.2.1 and 3.2.3 and Theorem 3.2.5 (printed pp. 606–608); verdict: self-contained general categorical-pattern statement with all four fibrancy conditions, marking, cofibrations, enrichment, and combinatorial model structure.
- Step 1: checked the nerve of `Δᵒᵖ`, inert marking, discrete cones `K_n`, and the monomorphism-cofibration conclusion against Example 3.2.4(i) and Theorem 3.2.5; verdict: cited theorem supplies the model structure and all objects are cofibrant.
- Step 2: checked the specialization of the classifying diagram and relative-limit condition against Definition 3.1.3, Definition 3.2.3, Example 3.2.4(i), and the straightening statement; verdict: gives exactly the Segal and mapping-fiber conditions, including the terminal arity-zero case.
- Step 3: checked the coherent nerve and enriched mapping objects against Definition 3.2.7 and the cited mapping criterion, pointwise-equivalence, and cocartesian-composition statements; verdict: the inverse argument and mixed-edge factorization establish precisely inert-preserving coherent maps and their equivalences.
- Step 4: checked localization and presentability against the combinatorial-localization, simplicial-model nerve, and presentability nodes; verdict: all hypotheses are supplied and the conclusion is exactly accessibility plus all small simplicial colimits.
- Small cases: checked the empty base, point base, singleton cone, arities `n=0` and `n=1`, and the terminal operad; verdict: no edge-case failure or accidental weakening.
- DAG/search audit: searched the existing DAG, blueprint, Mathlib search log, and read-only Lean source for duplicates or closed declarations; verdict: no duplicate or Mathlib leaf, and no dependency cycle.

Changes made in this second reading:

- Corrected the item node's `created.item` metadata from `lem-coef-operadic-algebra-presentability` to the delivered item id, so the delivery provenance is accurate.
- Added this independent source-by-source review and recorded the source checks and edge-case tests required for delivery.
