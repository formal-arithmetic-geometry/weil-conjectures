## Worker report

Files written: `dag/nodes/sec-six-functors-basics/lem-sfb-space-fpqc-property-affine-criterion.json`: statement, split; no Mathlib match. Also `citations.json`, with one verbatim statement excerpt for each proof-step citation. No new nodes and no Mathlib leaves.

Attachments: none. Searched `lean/WeilConjectures/` for the exact blueprint id, algebraic-space/property terminology, affine criteria, fpqc and DescendsAlong. No declaration states this algebraic-space criterion; the fpqc hits concern scheme sites, constant sheaves or individual geometric properties.

WANTED: none.

The item was unsplit, with an empty proof. Its statement is retained verbatim, including finite coproduct closure for the empty set. The inherited ancestor is null: `blueprint_refs.py ancestor` explicitly reports None. Retained this and the full creation chain rather than inventing a blueprint parent. Read the latest blueprint's `sec-six-functors-basics/sk-thm-sf-ctf-stability/_section.md` and its direct-images proof paragraph (3); the present lemma is a foundational tool on the inherited downstream branch, with no change to the chapter or unit route.

Nothing remains unfinished in this one-level split.

## Searches and reuse

Read the item's inherited five search records and their actual hits; retained them verbatim. Ran LeanFinder with the full affine-test/fpqc-family criterion and a second phrasing about surjective flat affine maps; LeanSearch with the affine-test criterion; Loogle with `"DescendsAlong"`; grep with `AlgebraicSpace|[Dd]escendsAlong|[Ff]pqc` in AlgebraicGeometry. The sandbox `searches.jsonl` records these actual queries. Read Mathlib/CategoryTheory/MorphismProperty/Descent.lean:27-59 and AlgebraicGeometry/Morphisms/Descent.lean:55-81,125-151. The former defines or assumes categorical descent; the latter proves scheme reductions. Neither gives the item for algebraic spaces. Read the existing finite-affine-coproduct match in AlgebraicGeometry/Limits.lean:604-647 and the sheaf extensivity match in CategoryTheory/Sites/LeftExact.lean:313-330.

Searched the whole DAG by 041J, finite/disjoint affine coproduct terminology, flatness, and sheaf-coproduct/pullback terminology. Read existing nodes rather than creating another affine packaging result. Blueprint searches for fpqc, finite coproduct and affine-test found no duplicate criterion. In particular, `lem-weil-pbc-fpqc-local-on-base-criterion` is about scheme morphisms, so it is not an exact attachment or an applicable algebraic-space black box.

## Not duplicates

No new nodes. Existing finite affine coproduct and finite sheaf extensivity nodes are cited directly.

## Review by Q72

I read Stacks spaces-descent.tex Tag 041J, label lemma-descending-properties-morphisms, including its complete proof, and spaces-topologies.tex Tag 03MQ, label definition-fpqc-covering. They give exactly the affine-test, refinement, finite-disjoint-union and flat-surjection route. The item's finite closure includes the nullary case explicitly, a stronger hypothesis already present in the assigned statement; I neither added it nor dropped it. All arrows remain over S, with an arbitrary algebraic-space source, rather than silently restricting the source to schemes.

Step 1 uses the statement of `lem-trf-space-fibre-products-etale-covers` only to know that sheaf pullbacks are algebraic spaces and categorical pullbacks. I checked that this is its first sentence, not something hidden in its proof. The step writes the pair-of-sections inverse for the iterated pullback, then applies (2) twice; it does not assume arbitrary base-change stability without deriving it. This supplies the forward implication and the stability used later.

Step 2 uses the refinement clause written in the item's own hypothesis. The schemes Z_j need not be opens of the covering members, and their maps to Y_i need not be flat: Step 1 gives stability under every base change. It then applies Step 1 to obtain all component properties. No external refinement lemma with extra quasi-compactness or representability hypotheses is used.

Step 3 uses the statement of `lem-weil-pbc-scheme-coproduct-family` for existence, its induced map, and disjoint open pieces covering the coproduct, and `lem-weil-pbc-finite-affine-coproduct-spectrum` for affineness. I read their statements and the latter's Mathlib source. Flatness is checked point by point, using the definition of open immersion (`def-weil-open-immersion`) to identify local rings and `def-weil-flat-morphism` to conclude flatness. This is a two-line stalk argument from definitions, not a hidden appeal to a flat-descent theorem. Surjectivity is proved by choosing the given preimage in a component. Finiteness, not finite presentation, is all that is required here.

Step 4 uses the clopen-partition statement of `lem-trf-fppf-sheaf-coproduct-partition`, whose source I read in spaces.tex Tags 0F15 and 02WO. It explicitly explains why those data are precisely maps to the scheme coproduct; it does not assume that Yoneda preserves arbitrary coproducts. Then it applies the displayed universality formula in `lem-trf-set-sheaf-finite-extensivity` to B mapping to the finite coproduct of the representable Z_j. I read sites.tex Tags 00WI and 00WJ, the cited node, and the Mathlib sheaf extensivity instance. The resulting component isomorphisms commute with projection to Z', which is needed to invoke isomorphism invariance for a property of arrows. These are statement-level uses, recorded verbatim in citations.json. The sheaf-partition and algebraic-space-pullback nodes are declared as generic off-unit tools in split_report, with reasons; the two coproduct Mathlib leaves require no route departure.

Step 5 applies the item's own hypotheses (1), (3), then (2), in that order. I checked that (3) has both an affine source Z' and affine target Z for the covering map, but allows the morphism being descended to have algebraic-space source X times_Y Z. The redundant pullback coordinates are removed by Step 1's explicit maps. There is no circular citation and no new node merely restating a clause of the item.

For small cases I checked an empty refinement, empty Z, an empty original covering, a singleton identity covering, and disconnected finite affine refinements. In the empty refinement case joint surjectivity forces Z empty, the finite affine product is the zero ring, and (1) supplies the property on the empty arrow. Thus no nonemptiness is silently assumed. Every step is under 2000 characters. The seven cited statement excerpts in citations.json were checked as literal substrings of the current node statements. Against delivery-errors B-E: no new statements to hide hypotheses or proofs, no unlogged searches, no tags substituting for node citations, no misuse of node proofs, no new duplicates or clause restatements, and no added geometric hypothesis or changed statement.
