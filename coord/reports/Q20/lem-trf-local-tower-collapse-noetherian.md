# Stage-1 delivery: lem-trf-local-tower-collapse-noetherian

Group Q20, 2026-10-22. Direct worker delivery.

## Files written

- `dag/nodes/sec-trace-formula/lem-trf-local-tower-collapse-noetherian.json`: existing statement, split into six proof steps. The statement and all five statement dependencies are unchanged. No exact Mathlib match for the complete assertion; its permanence and colimit components reuse existing Mathlib leaves.
- `citations.json`: twelve entries, one verbatim statement quotation for each citation in each proof step.
- `searches.jsonl`: five real searches through the required msearch.py command, comprising LeanFinder twice, Loogle, LeanSearch and Mathlib grep. These supplement, and do not replace, the inherited search history in the item.
- `report.md`: this report.

New nodes: 0. New Mathlib leaves: 0.

## Attachments

None. Searching the live `lean/WeilConjectures/` for the exact blueprint tag found no declaration for this item. Searching the notion found `Module.tensorLocalization_tower_transition` in `RingTheory/TensorLocalizationTowerTransition.lean`, which is only the generic comparison lemma, already attached to an existing DAG node. The Noetherian local model tower and its categorical conversion in `RingTheory/NoetherianLocalModelTower.lean` and `RingTheory/NoetherianLocalModelTowerOfCategoricalLimit.lean` involve additional module data and hypotheses and do not give the complete item under just its hypotheses. I did not treat those as an attachment or introduce a duplicate of the existing comparison node.

## WANTED

None.

## What was wrong and what changed

The item was a correct unsplit statement. There was no previous sandbox split to resume. The proof now separates Noetherianity, composition and finite presentation, transition comparison, limit comparison, and the elementwise colimit clauses. The limit comparison is an application of the generic six-ring lemma with the second tower equal to the limit tower; it does not require the limit rings to be Noetherian. The step proving Noetherianity of the integers is written out rather than hidden behind an uncited arithmetic fact or introduced as an unnecessary node.

No statement dispute, change of source, change of the supplied diagrams, or change of chapter/unit route is needed. The existing blueprint ancestry and its precise place are retained. Searches of the whole blueprint for `Noetherian local tower`, `tensor localization tower`, `00R7`, and `essentially of finite type` found no blueprint node stating this complete item; `same_as` remains empty. A search of the entire DAG by the tags 07DS, 00FN and 00FP and by the relevant titles found the existing component results, which are reused.

## Not duplicates

No new nodes are created, so there are no new/existing same-tag pairs. In particular, composition is cited as `lem-weil-pbc-essentially-finite-type-composition`; finite-type and localization Noetherian permanence and finite presentation are cited as their existing leaves; both comparison clauses use `lem-weil-pbc-tensor-localization-tower-transition`; both colimit clauses use the existing `lem-pc-filtered-colimit-commrings-elementwise` leaf. No clause of the item is repackaged as a new node.

## Review by Q20

I read the item against Stacks `algebra.tex`, Tag 00R7 (`lemma-criterion-flatness-fibre`), especially the approximation paragraphs and the sentence saying that the two adjacent tensor-localization comparisons imply the base-to-top comparison. I also read Tag 00FN (`lemma-Noetherian-permanence`), Tag 07DS (`lemma-composition-essentially-of-finite-type`), and clause (3) of Tag 00FP (`lemma-Noetherian-finite-type-is-finite-presentation`), and checked these tag-to-label correspondences in `literature/stacks-project/tags/tags`. There are no new-node sources to review. I read the unit and chapter records and the current main-20261015 locality statement and proof: this item remains an algebraic helper below the specialization/normal-cone branch of locality (1),(2), not an alternative proof of the unit.

For step 1 I checked `def-weil-pbc-noetherian-ring`: it says that every ideal is finitely generated. The displayed least-positive-element and Euclidean-division argument proves exactly that for the integers, including the zero ideal. This is the only elementary step; it cites its definition and contains the actual argument.

For step 2 I opened all three cited nodes. `def-weil-pbc-essentially-finite-type-algebra` supplies a finite type algebra and a localization presentation, not Noetherianity on its own. `lem-weil-pbc-finite-type-algebra-noetherian` gives Noetherianity of that finite type algebra over a Noetherian base; `lem-weil-pbc-localization-noetherian` then gives Noetherianity of its arbitrary localization. The base is Noetherian successively by step 1, by the assertion just proved for A_i, and then by the assertion just proved for B_i. No conclusion about Noetherianity of A, B or C is taken. I read the corroborating Mathlib `Algebra.EssFiniteType.isNoetherianRing` in `Localization/Submodule.lean:90`, which packages this pair of permanence facts, but reused the existing DAG leaves instead of creating a new leaf.

For step 3 I checked that `lem-weil-pbc-essentially-finite-type-composition` permits precisely the two given ring maps, and that the essentially finite type definition gives the localization presentation as an A_i-algebra, with the correct composite structure. `lem-weil-pbc-finite-type-noetherian-finite-presentation` applies to the finite type algebra P because A_i, not a limit ring, is Noetherian by step 2. I read Mathlib `EssentialFiniteness.lean:140` and `FinitePresentation.lean:69` as additional confirmation. The multiplicative subset need not be finitely generated, and none of the argument requires it.

For step 4 I read the full statement of `lem-weil-pbc-tensor-localization-tower-transition` and its project declaration. The substitutions are (A,B,C)=(A_i,B_i,C_i), (A',B',C')=(A_j,B_j,C_j), and (r,s,t)=(a_ji,b_ji,c_ji). Both required localizations are supplied explicitly by the item; commutation gives the scalar compatibility. Its conclusion includes the pure-tensor formula, so it supplies the desired map itself. `def-weil-pbc-module-tensor-product` states generation by pure tensors; absorbing coefficients into one factor gives additive generation. Thus agreement on that formula proves equality to the supplied canonical ring map, without assuming a comparison is canonical merely because its source and target agree.

For step 5 I checked the same statement with (A',B',C')=(A,B,C) and (r,s,t)=(alpha_i,beta_i,gamma_i). It assumes only commutative rings and the two canonical localization comparisons. In particular it does not require the primed rings to be finite type or Noetherian, or to be stages of an index diagram. The formula for the conclusion is exactly gamma_i(c)(gf)(a), and the same tensor-generation node identifies the resulting ring map. This is the reason the existing transition lemma also handles the limit comparison. These two applications are declared in `split_report.tool_uses` as a generic algebra tool from sk-thm-p1; no node of sk-i-curve-zero supplies this general comparison, and no unit step is replaced.

For step 6 I opened `lem-pc-filtered-colimit-commrings-elementwise`: it asserts both element representatives and eventual equality for any small filtered category and the given ring-colimit cocone. A nonempty directed preorder is filtered, including its parallel-arrow condition; this does not require replacing the preorder by a partial order. I read Stacks Tags 00D6/00D7 for the quotient description and `sheaves.tex` Tag 008N for the stated underlying-set compatibility. I also read the actual Mathlib declarations `Concrete.isColimit_exists_rep` and `Concrete.isColimit_rep_eq_iff_exists` and the commutative-ring forgetful functor's filtered-colimit preservation instance. The existing leaf covers the ring statement, so no inference that an arbitrary forgetful functor preserves colimits is being made. The item supplies the ring-colimit universal properties for exactly alpha_i and gamma_i; the conclusion therefore concerns those original maps.

I checked delivery-errors B through E against the written files. All cited node statements were opened and copied verbatim into citations.json; no proof of a cited node is used as its public statement, no general theorem is inferred from a definition, and every non-elementary imported fact is a cited existing node. No new unsplit node, duplicate, unsupported tag citation, or circular new helper is present. The largest step has 778 characters, well below the long-step review threshold. All notions in the unchanged statement have their existing definition dependencies or inline meanings. Source ownership fields were retained.

I tested the argument on a one-object identity diagram (both tensor comparisons are isomorphisms), on i=j inside a larger diagram, on noninjective transition maps (the colimit leaf explicitly handles eventual equality without injectivity), and on a genuine preorder with equivalent distinct objects. I also checked arbitrary localization denominators and non-Noetherian limit rings: the argument uses finite presentation only for the stage algebra P, and the two comparison steps work for any commutative target rings. Empty indexing is excluded by the hypotheses. These checks require no extra flatness, injectivity, boundedness or finiteness assumption. The proof keeps the original cocones throughout.

## Unfinished work

None in this stage-1 split. No Lean was written and no compiler, Lake or build tool was run. The required delivery preflight supplies the final mechanical checks; independent mathematical review belongs to the maintainer.
