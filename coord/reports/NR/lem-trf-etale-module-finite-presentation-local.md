# Worker report: lem-trf-etale-module-finite-presentation-local

## Files written

- `dag/nodes/sec-trace-formula/lem-trf-etale-module-finite-presentation-local.json`: statement split in four proof steps; not a Mathlib leaf. No new nodes or new Mathlib leaves.
- `citations.json`: eleven step/node entries with verbatim excerpts of the cited statements.
- `searches.jsonl`: six actual searches recorded by msearch.py; their results were read and appended to the item's inherited search history.

## Attachments

None for this item. Searches by its exact blueprint tag and by finite-presentation/etale concepts in `/home/ubuntu/weil-src-slopmaster2/WeilConjectures/` and `Comparator/` found no declaration stating the marked-neighbourhood equivalence. The existing project pullback-preservation and fpqc descent declarations cover inputs, not the item itself. The master checkout was used only as read-only reference; no sorry declaration is treated as finished.

## Wanted literature

None. All sources needed for this split are present.

## Corrections and observations

The mathematical statement is unchanged, including its residue-field isomorphism hypothesis. The proof works without that extra hypothesis, but it was retained as instructed. No STATEMENT-DISPUTED issue was found.

The inherited source locator misidentified its standard inputs: preservation under pullback is Modules Tag 01BQ, not Properties Tag 01PC; sheaf finite-presentation descent is Descent Tag 05B0, not the flatness-of-morphisms Tag 02L2 or the ordinary-module Tag 03C4. I corrected `source.place` and used the exact labels from `tags/tags`. These are citation corrections, not changed hypotheses or conclusions.

The pre-existing DAG already contains all required tools. In particular `lem-pc-fpqc-descent` clause (2), found by whole-blueprint search for `fpqc descent`, states reflection of finite presentation. I did not create a second sheaf descent node or relocate a direction of the item into a new lemma. `lem-pc-tensor-pullback-finite-presentation` has a misleading ordinary-module definition citation in its prose, but its actual statement explicitly concerns a module on a scheme and the tensor pullback, and its cited source Modules Tag 01BQ and the project instance `AlgebraicGeometry.Scheme.Modules.isFinitePresentation_pullback` in `AlgebraicGeometry/Modules/FiniteDescent.lean:218` confirm the sheaf meaning used here. That existing node was not edited.

The item's inherited ancestry points to the local-term locality node through the elementary-devissage finite-presentation node. I read `dag/units/sk-i-curve-zero.json`, `dag/chapters/sec-trace-formula.json`, and the current ancestor statement: the current local-term route is the contracting-correspondence argument, while this imported ancillary branch supplies the Tag 057T finite-presentation comparison. The claimed paragraph “The etale morphism g is open” is in Tag 057T and the immediate parent's proof, not literally in the current ancestor blueprint text. I preserved the maintainer-owned unit and historical ancestry and identified the actual supporting source in `split_report.blueprint`. No unit statement, realization field, or chapter route was changed.

## Unfinished work

None in the one-level split. The two standard scheme-module tools are cited as existing nodes, not re-proved. No Lean files were written and no compiler, Lake, or build command was run.

## Mathlib and duplicate search

The original item's searches were retained. For this item I ran LeanFinder with both the point-neighbourhood formulation and the more general faithfully-flat sheaf-descent formulation, Loogle for `SheafOfModules.IsFinitePresentation`, LeanSearch for etale descent of finite presentation, and grep in `AlgebraicGeometry` and `Algebra/Category/ModuleCat/Sheaf`. All services answered successfully. The hits are finite-presentation predicates/constructors and morphism or algebra finite presentation; none states the marked scheme-module neighbourhood equivalence. I read Mathlib `Algebra/Category/ModuleCat/Sheaf/Quasicoherent.lean:230–315`, including `IsFinitePresentation` at 267, to check the returned candidate rather than mistaking the predicate for a descent theorem. Queries and actual results are recorded by msearch.py and copied into `mathlib_searches`.

Whole-DAG searches used finite-presentation, pullback, descent, and etale-openness concepts and Tags 01BQ, 01PC, 02L2, 03C4, and 03WT. Whole-blueprint searches included `finite presentation`, `finite presentation etale neighbourhood`, `etale module`, `01BQ`, `03WT`, and `fpqc descent`. They located the existing fpqc descent blueprint node and the existing auxiliary tools; no second blueprint formulation of the item was found. `blueprint.same_as` remains the searched empty list.

## Not duplicates

No new nodes. Existing general tools are reused directly, so there are no new/existing same-tag pairs to justify.

## Review by NR

I checked the split against delivery-errors B–E with the sources and dependency statements open. The main source read was `flat.tex`, Tag 057T, label `lemma-devissage-finite-presentation`, specifically the complete (1)–(4) neighbourhood comparison paragraph. Its argument is unchanged: pull back in the forward direction, use the open image of an etale neighbourhood in the reverse direction, and descend finite presentation. I also read `modules.tex` Tag 01BQ (`lemma-pullback-finite-presentation`); `morphisms.tex` Tag 03WT (`lemma-etale-open`); `descent.tex` Tag 05B0 (`lemma-finite-presentation-descends`); `topologies.tex` Tag 0218 (`lemma-etale-affine`) and Definition 022B (`definition-fpqc-covering`); and the main-20261015 `lem-pc-fpqc-descent.md`, whose clause (2) agrees with the existing DAG statement. There are no new statements whose sources need a separate audit.

Step 1 uses `lem-pc-tensor-pullback-finite-presentation`, whose statement explicitly preserves finite presentation under arbitrary scheme tensor pullback, and `def-pc-module-pullback`, whose tensor formula and composition isomorphism identify restriction of the pullback with pullback of the restriction. The domain is the whole open inverse image of the chosen neighbourhood, which contains the marked point; no flatness, quasi-compactness or residue-field condition is required in this direction.

Step 2 uses `lem-weil-pbc-etale-morphism-open-map`, which says that every open subset has open image, and all three clauses of `lem-weil-pbc-etale-composition-cancellation`. The latter states that open immersions are etale, etale maps compose, and an etale composite cancels against an etale second map. Thus the factorization through the open image is etale; its surjectivity is the set-theoretic definition of that image. This checks the hypothesis of the refinement used next rather than assuming every surjective morphism is a cover.

Step 3 again uses that exact composition/cancellation statement for the restricted map over each affine open. `def-weil-etale-morphism` explicitly includes flatness. The statement of `lem-weil-pbc-etale-covering-affine-refinement` supplies finitely many affine OPEN subschemes of the covering member over each affine target. Those same opens are open in the original covering member. Together with flatness this verifies, word for word, the finite-refinement definition in `def-weil-pbc-fpqc-covering`. I specifically checked that the proof does not assert that the entire restricted etale map is quasi-compact, which need not hold.

Step 4 uses only the affine-local quasi-coherence condition in `pqf-def-coherent`, composition and the tensor definition in `def-pc-module-pullback`, and clause (2) of `lem-pc-fpqc-descent`. The source module is the restriction of the given quasi-coherent module. Its pullback along the covering map is exactly the restriction assumed finitely presented upstairs, not a stalk and not a constant-coefficient etale module. Thus every hypothesis of the fpqc reflection clause is available. Canonical descent data are already supplied by pulling back this actual module; no effectiveness or arbitrary descent-data theorem is being inferred from a definition.

The elementary pieces remain inside the steps: inverse images contain the marked point, images contain its image, an open subset of an open subscheme is open in the whole scheme, restrictions use the same ring-sheaf maps, and the final neighbourhood is the open image. The non-elementary preservation, openness, etale permanence, refinement and descent facts all have cited nodes. I checked every citation excerpt in `citations.json` as a literal substring of the current node's statement, and checked that `proof_deps` is exactly the union of `uses`. Every proof step is under 2000 characters; none hides another lemma. The off-unit pullback and fpqc descent results are generic tools, declared in `split_report.tool_uses`, with no replacement of a unit proof step.

For edge cases I checked the zero module, an identity morphism, an open immersion, and a disjoint union of arbitrarily many etale copies (where quasi-compactness of the whole cover fails). The zero and identity cases give the expected tautologies; for an open immersion the image itself is the required neighbourhood; for the infinite disjoint union the finite affine refinement, rather than quasi-compactness of the whole map, is exactly what makes the descent application legitimate. Empty affine opens allow an empty finite refinement, as the cited statements permit. Marked points prevent an empty source or target from creating a missing-neighbourhood case. No Noetherian, finite-type module, separation, global surjectivity of g, or equality of whole stalk and neighbourhood finite presentation was introduced.

The review caused two substantive presentation repairs: replacing the incorrect inherited source tags, and spelling out the fpqc condition rather than merely calling the open-image map a covering. No statement was weakened, no new lemma merely restates a clause, and there are no new nodes, undefined new notions or duplicate obligations.
