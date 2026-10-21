# Worker report: lem-sfb-constructible-cocone-obj

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-constructible-cocone-obj.json`: statement node, repaired split; Mathlib does not state the finite-coefficient descent assertion.
- `citations.json`: one exact statement quotation for every step/dependency pair.
- `searches.jsonl`: actual additional exact-functor/single-complex searches, retained as emitted by msearch.py.
- `report.md`: this report.

No new DAG nodes and no new Mathlib leaves. The two arguments not previously cited as independent nodes were already present: `lem-sfb-dc-module-devissage` (the finite Postnikov argument), and `lem-sf-exact-functor-derived-triangulated` (a Mathlib leaf which includes the single-complex comparison). The contract requires reusing those nodes rather than creating copies or specializations. This is a finer dependency split, not a new proof of those arguments.

## Attachments

None for the item. I searched `lean/WeilConjectures/` by its blueprint tag and notion/declaration name, and read `WeilConjectures/SixFunctors/ProEtale/ModuleObject/Colimit/TwoColimit.lean:229-238`: `AlgebraicGeometry.ProEtale.constructibleCocone_essSurjObj` has `sorry`. The surrounding section has exactly the prime and topologically Noetherian hypotheses. It is not an attachment.

## WANTED

None.

## Repair of the return

The single numbered issue is the human's 2026-10-21 resplit request: the old proof has 5686 characters, including an inline finite Postnikov induction. Its statement must remain unchanged. The repaired proof has 2157 characters, in six steps of 489, 418, 406, 392, 262 and 190 characters. Every non-elementary argument is now invoked through an existing statement node. No argument was transferred into a new node restating the item, and none was hidden by replacing an explanation with an uncited name.

Old step 1 is the same definitional coefficient/presentation comparison, now stated in three sentences; all ten defining nodes remain cited. Old step 2 is the short application of the finite-model API and flat coefficient calculus. Old step 3 already had the generic directed triangulated-image theorem; its hypotheses and the full-subcategory passage remain explicit. Old step 4 now cites the existing exact-derived-functor node for the previously implicit single-complex comparison. Old step 5 no longer proves the truncation induction inline: it invokes the independently stated module-object devissage theorem, checking its property hypotheses using steps 3 and 4. The final full-subcategory argument is retained.

The sandbox initially contained only dispatcher `.brief*` markers, with no retained node, report, citations or search log to continue. I reconstructed from the current read-only repository node, whose 5686-character proof matches the returned description. I preserved its statement, stmt_deps, original Mathlib searches, blueprint fields, Lean fields, review records and other maintainer metadata. Only `proof`, `proof_deps` and `split_report` changed. The authorized delivery tool rebases those owned fields onto the current server branch; no git command was run by me.

## Searches and reuse

I read the unit and chapter records and the main-20261015 item proof, including both Modules and Complexes paragraphs. Whole-DAG searches covered `prop_of_bounded`, Postnikov, single-complex exact-functor compatibility, triangulated images and constructible cocones. Blueprint searches with `tools/blueprint_refs.py search` covered `Postnikov`, `triangulated image`, `constructible cocone`, `single complex`, `degree zero`, `exact functor`, `triangulated functors`, `finite truncation`, `exact (additive`, and `finite coefficient`. The ancestor command returns the item itself. The generic existing nodes do not duplicate a blueprint statement of this item. No new node is necessary.

The following additional searches were actually run with msearch.py and their results were read:

- leanfinder: `An exact functor between abelian categories induces a functor on derived categories that commutes with the single object complex functor`: matched `CategoryTheory.Functor.mapDerivedCategorySingleFunctor` and the related exact-derived-functor constructions.
- loogle: `"mapDerivedCategory", "single"`: matched the same natural comparison and coherence declarations.
- grep: `mapDerivedCategory.*[Ss]ingle|[Ss]ingle.*mapDerivedCategory|mapDerivedCategorySingle`: located its declaration at Mathlib/Algebra/Homology/DerivedCategory/ExactFunctor.lean:112-119.
- leansearch: `The derived functor of an exact additive functor applied to an object in degree zero is its image placed in degree zero`: returned classical left/right derived functors and zero-degree comparisons, not the total-derived statement needed here.

I read the exact-functor hypotheses at lines 28-31 and the whole natural isomorphism at lines 112-119. The comparison is already the final clause of `lem-sf-exact-functor-derived-triangulated`, so I cited that Mathlib leaf instead of creating another one. The search log was not fabricated or rewritten. The item itself retains the earlier finite-coefficient searches unchanged.

## Review by Q50

I read the item source `literature/blueprint/main-20261015/blueprint/sec-six-functors-basics/sk-thm-sfb-qlbar-two-colimit/lem-sfb-constructible-cocone-obj.md`, its proof file, the unit record including its Modules/Postnikov steps, and the chapter record. The retained statement requires only a scheme with Noetherian underlying space and prime ell; it has not been replaced by the unit's narrower standing-scheme convention. The proof continues the previously accepted condensed local-finite-presentation route. No SGA source is used.

For step 1 I opened all ten defining nodes. `def-sfb-padic-subfield-condensed-ring` gives continuous E-valued sections with the restricted absolute-value topology. `sk-def-sfb-qlbar-condensed` gives functions whose whole image lies in one finite subextension, not all continuous Qbar-valued functions. `sk-def-sfb-pullback-from-point` and `def-weil-pbc-condensed-e-module-category` give the same sheafified left Kan extension followed by the structure-morphism inverse image. The finite-presentation, locally-finitely-presented and constructible-module definitions give exactly the cokernel and finite-stratification predicates in the condensed-module definition. Finally the bounded-constructible and two dcons definitions identify the full subcategories. This step is elementary substitution of those formulas. It imposes neither completeness nor constant local models.

For step 2 I read `lem-weil-pbc-condensed-finite-model-proof-api`: its first sentence states that boundedConstructible for a finite coefficient field is triangulated, with topological Noetherianity exactly as required here. I use only that sentence, not its comments about private helpers. `lem-weil-pbc-condensed-flat-coefficient-calculus` explicitly states exactness, termwise derived tensor, shifts and distinguished triangles, for precisely these coefficients and this same Noetherian-space hypothesis. The two derived-extension definitions identify the functors, the constructible-cocone definition supplies their restrictions and comparisons, and `def-weil-triangulated-subcategory` explicitly says the inherited inclusion is exact. Thus all hypotheses of the ambient cocone are accounted for; no triangulation of the entire Qbar constructible vertex is assumed.

For step 3 I read both Hom-surjectivity and `lem-weil-pbc-directed-triangulated-image` in full. The latter assumes a nonempty preorder, pretriangulated source and target categories, triangulated Phi functors and lifting of arrows after conjugation by the comparisons; it does not require one stage functor to be full or coherent transitions. The finite-subextension definition supplies nonemptiness and the preorder; step 2 supplies the categories and functors. The dcons and bounded-constructible definitions say the vertex is full, so the Hom-surjectivity statement applies to every arrow between image objects in the ambient category. Its conclusion has exactly the comparison conjugations that the generic lemma needs. Isomorphism closure of the existential-image property is just composition of the model isomorphism and a given isomorphism. I also read the already existing proof in `lean/Sheaf/CategoryTheory/DirectedTriangulatedImage.lean:26-68`; no contents of that proof are taken as additional statements.

For step 4 I read `lem-weil-pbc-condensed-finite-presentation-descent`: it includes the globally glued constructible module M_E and its tensor isomorphism under the exact finite-stratified local-cokernel condition of step 1. It is not merely a chartwise matrix descent statement. A degree-zero complex of M_E has only H^0=M_E, and zero is locally the cokernel of the map from zero free rank to zero free rank, so it meets the cited bounded-constructible definition. The Mathlib leaf `lem-sf-exact-functor-derived-triangulated` explicitly says a single complex is carried to the single complex of the image. The flat coefficient calculus identifies the given derived scalar-extension functor with that termwise exact derived functor. These two statements give the needed isomorphism, which was implicit in the returned split.

For step 5 I read the statement of `lem-sfb-dc-module-devissage`: for any scheme and commutative ring object, an isomorphism-closed triangulated object property containing every constructible module in degree zero contains all bounded complexes with constructible homology. This is exactly the non-elementary argument formerly carried inline by old step 5. It has no additional finite-type, standing-scheme or completeness hypothesis. I checked its existing source declaration and proof in `lean/Sheaf/AlgebraicGeometry/BoundedConstructibleDevissage.lean:47-64`: it is the same module-object property and calls the generic `DerivedCategory.prop_of_bounded`. The existing node has a proof of 860 characters, well below the requested bound. Applying its statement is a short assembly of steps 3 and 4. Its generic use from another unit is declared in split_report.tool_uses, for the maintainer to approve; none of the maintainer's tool_uses fields was changed.

For step 6 I read the cocone and filtered-two-colimit definition statements, particularly the (Obj) clause. Fullness puts the ambient isomorphism and its inverse in the target subcategory and preserves their two inverse identities. The resulting E and K_E are exactly the witnesses of the unchanged item, not just a cohomological model.

I checked B1-B9 and C1-C6 against the actual files: no new statement-only or duplicate node was created; all specialized notions in the coefficient comparison cite their definitions; every non-elementary input is in the relevant uses list; proof_deps is their union; citations.json quotes are literal complete statements of the cited nodes, so they cannot conceal a C4 mismatch. The dependency closure of the repaired node contains 1060 nodes and does not return to the item. Existing sources and metadata are retained. There are no long proof steps or extracted proof obligations left above 3000 characters.

For E1-E7 I checked X empty, M=0, K acyclic, a single sheaf in any shifted degree, and a two-degree complex with a nonzero connecting morphism. The empty scheme and zero module are allowed by the presentations. The nonempty field index still contains Q_ell. Devissage handles the acyclic base and arbitrary shifts, and the triangulated-image theorem descends nonzero connecting maps at common finite stages. The proof never assumes a single extension functor is full, or that locally chosen coefficient models alone supply the global sheaf. No hypothesis was strengthened, no coefficient category changed, and no statement dispute arose.

The repair therefore removes the long inline induction by citing the existing node that proves it and makes the single-complex argument explicitly depend on its existing Mathlib leaf. The duplicate-node rule prohibits creating another name for either fact, so the corrected delivery has zero new nodes. There is no unfinished mathematics in this stage-1 repair; validation and delivery are performed by the required delivery command.

## Not duplicates

No new nodes. In particular a new finite-Postnikov lemma would duplicate `lem-sfb-dc-module-devissage`, and a new exact-derived-single lemma would duplicate `lem-sf-exact-functor-derived-triangulated`; both existing nodes are used directly.
