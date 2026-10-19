# Q46 stage-1 report

## Files written

- dag/nodes/sec-six-functors/lem-coef-cartesian-mapping-simplex-prism-extension.json — statement, split in four steps; no Mathlib match.
- citations.json — one verbatim statement excerpt for every step/node citation.
- report.md — this report. searches.jsonl is the search command's own log, preserved unchanged.

## New nodes

None. The apparent missing final-vertex fact is the order dual of the existing lem-coef-infinity-marked-initial-vertex, using the explicit reversal assertion of def-coef-infinity-marked-coanodyne. Creating a final-vertex node would duplicate that theorem up to the elementary order-reversal operation.

## Attachments

None. Searched the project source under /home/ubuntu/weil-src-slopmaster2/WeilConjectures by the exact item tag and by prism, CartesianFibration/cartesianFibration and marked-anodyne terminology; no matching declaration was found. The master checkout is reference material and no master sorry declaration was counted as a proof.

## WANTED

WANTED: Jacob Lurie, Higher Topos Theory, Proposition 3.2.2.11, proof, pp. 184–185, and Proposition 3.1.2.3, for lem-coef-cartesian-mapping-simplex-prism-extension. No HTT copy is archived in this repository's literature/. The IAS URL timed out in the web reader. I read the official Harvard PDF at https://people.math.harvard.edu/~lurie/papers/HTT.pdf instead, especially printed pp. 147–148, 152 and 184–185. Nothing was downloaded or written into the shared repository. The proof_origin remains agent-written, linked to the local blueprint route, with this external source check explicit; the per-step sources identify the exact HTT passages.

## Findings and corrections

The item was an unsplit statement-only child of lem-coef-cartesian-base-equivalence-invariance, extracted from its Step 11. There was no earlier split/report in this sandbox to recover. Its statement agrees with HTT's factorization and prescribed dotted arrow f_0; it needs no correction. In particular, h is only marked on degenerate edges of the minimally marked A_n. It need not preserve arbitrary edges of A_n as Cartesian edges. Its trivial-Kan-fibration hypothesis is stronger than the extension argument uses, but is retained exactly as imported and as required by its parent factorization.

The split now gives the actual argument: order-dual final-vertex marked anodyneness; the degreewise marked gluing; the pushout product with the monomorphism j; and relative marked-anodyne lifting. No new clause-sized surrogate lemma is introduced. The Kan-model statement remains a statement dependency because the hypothesis names a trivial Kan fibration, although no Kan-model theorem is used in the proof.

The current main-20261015 blueprint paragraph 2 was read, together with its parent ancestor metadata, the six-functor chapter record and sk-prop-sf-biduality-general. This is a generic marked-simplicial foundation for the existing finite-coefficient enhancement route and changes no chapter, unit or target. The item has no blueprint_update. The blueprint_refs.py searches for prism, marked anodyne and vertex found no blueprint statement duplicating this prism theorem. DAG searches additionally found and reused the initial-vertex theorem and its coanodyne definition. Both are in the item's own unit, and neither dependency closure contains this item.

## Not duplicates

No new-node/existing-node pairs: this delivery creates zero nodes. In particular the final-vertex lemma was not created after finding lem-coef-infinity-marked-initial-vertex.

## Mathlib searches

Preserved all inherited searches. Ran and read the eight Q46 searches recorded by msearch.py in searches.jsonl, using two plain-language phrasings, Loogle and two source regexes. All services returned successfully. Hits included SSet.horn, SSet.stdSimplex.face, standard simplex terminal-object facts, relative morphisms, subcomplex lifts and the ordinary Quillen I/J properties. They neither introduce the marked Cartesian setting nor prove the required extension. Read source StdSimplex.lean:35–58, HomotopyCat.lean:158–186, CategoryWithFibrations.lean:65–105. The final-vertex terminology in HomotopyCat is a vertex-evaluation definition in a 2-truncated simplicial set; it is not a marked-anodyne theorem. No Mathlib leaf is asserted.

## Review by Q46

I read HTT Proposition 3.2.2.11 from the official Harvard PDF through the web reader. Its proof factors the map at the final vertex, forms exactly the two-piece source used here, invokes Proposition 3.1.2.3 to make its inclusion marked anodyne, and takes the lift f_0 with the specified final restriction. I also read Definition 3.1.1.1 and Remark 3.1.1.2 for the direction of the marked-anodyne convention. This matters: Cartesian fibrations need the final, not the initial, vertex. There is no SGA citation. No new-node sources need review because none are created.

For Step 1 I opened the statement of lem-coef-infinity-marked-initial-vertex: it explicitly covers every n >= 0 with full markings. I opened def-coef-infinity-marked-coanodyne: it explicitly identifies its saturated class with vertex-order reversal of the Cartesian marked-anodyne class. The operator formula is written in the step; it is an involutive reindexing, hence preserves the degreewise diagrams defining pushouts, ordinal colimits and retracts. Full markings remain full, and endpoint 0 becomes n. This is an application of an existing generic theorem, not an uncited new simplex-anodyne claim. def-cbc-enhanced-diagrams-cones supplies the simplex-operator and degreewise conventions. Both nondefinitional facts used are exactly in the cited statements.

For Step 2 I opened the marking/product definitions in lem-coef-marked-anodyne-lifting-calculus and the degreewise product definition in def-cbc-enhanced-diagrams-cones. Monicity of j gives the exact intersection in each degree, and the assumption hj = s restricted to the final fiber gives equality on that intersection. The map h on the minimally marked final piece preserves markings because those edges are degenerate. Thus the universal property of the marked pushout glues the maps, and agreement with the base projection is checked on each piece. This is an elementary explicit construction; no sheaf descent, model-category gluing theorem or unmentioned equivalence theorem is used.

For Step 3 I opened the complete pushout-product assertion in lem-coef-marked-anodyne-lifting-calculus: it requires one marked-anodyne factor and one degreewise injective marked factor, precisely e and j-flat. Product permutation identifies its displayed source with U, including the marking. Its conclusion is marked anodyneness itself, not merely a weak equivalence. This is why the later lift is justified without additional fibrancy assumptions on A or A_n.

For Step 4 I opened lem-coef-relative-marked-anodyne-calculus: its statement gives the right lifting property of Y-natural -> S-sharp for every Cartesian fibration over any small simplicial S. Here S = Delta^n and p is exactly such a fibration. The bottom projection is a marked map to the fully marked base; the top map is the one actually constructed in Step 2. Restriction of the resulting diagonal to the two source pieces proves both requested strict equalities, rather than only equalities up to homotopy.

I tested n=0: the final piece is the whole prism, its map is h, and the intersection equality is the original factorization. For n=1 the order-dual endpoint is {1} -> Delta^1 with its edge marked, exactly the final-edge generator. Empty A leaves only the final-piece prescription and the same pushout-product argument works; empty A_n makes the whole target empty. If Y_n is empty, the given h forces A_n empty, so there is no missing lift-existence/nonemptiness condition. The simplex-order operation and all pushouts stay small. All four steps are under 1000 characters, so no step exceeds the 2000-character long-step threshold or conceals a separate long comparison argument.

I checked delivery-errors B–E against the written file: no new statement-only-node requirements are triggered; notation is actual single-backslash TeX in decoded strings; searches are exact logged queries; every cited statement has a verbatim excerpt in citations.json; proof_deps equals the union of uses; no dependency is merely a proof-internal construction; no new clause restatement, off-unit route, statement change or target weakening is introduced. I checked the two newly used existing nodes' dependency closures to exclude a cycle through this item. The only corrections were to the missing split and missing worker review, not to any statement or existing dependency node.

## Unfinished work

No mathematical part of this one-level split remains. Independent maintainer review and splitting the existing cited open nodes remain the project's normal downstream work. Required server dry run and direct push are run after writing this report.
