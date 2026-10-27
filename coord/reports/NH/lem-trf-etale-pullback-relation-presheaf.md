# Stage-1 delivery: lem-trf-etale-pullback-relation-presheaf

## Files written

- dag/nodes/sec-trace-formula/lem-trf-etale-pullback-relation-presheaf.json: statement, split into five explicit proof steps; no Mathlib match for the entire item.
- citations.json: verbatim statement excerpts for every use in every proof step.
- searches.jsonl: actual msearch results; the existing node's historical search records were retained and today's searches appended to mathlib_searches.

New nodes: 0. New Mathlib leaves: 0. Three existing Mathlib leaves are reused.

## Attachments

None. Searched lean/WeilConjectures for the exact blueprint tag, etale/étale equivalence relations and quotient-presheaf terminology. No declaration states all clauses. PullbackFlat concerns linear relations of modules, and DeformationSpace concerns quotient ring presheaves, not the equivalence relation here.

## WANTED

None. All sources are in literature/stacks-project.

## Issues in the input

No statement dispute or statement change. The item was statement-only. Groupoids 02V8 omits its proof, and Spaces 02WT leaves the two projection factorizations implicit; these are now written out. Groupoids 045Z states a sheaf result, but this item only needs the representative-level argument preceding sheafification. No sheafification theorem is being inferred from the cited definition or used without a node. Stacks' source/target order conventions vary: the proof consistently uses this item's equations s r = g a and t r = g b.

## Unfinished work

None at the stage-1 level. No Lean was written, compiled or built.

## Review by NH

I read Spaces lemma-pullback-etale-equivalence-relation (02WT), Groupoids lemma-restrict-relation (02V8), definition-restrict-relation (02V9), and lemma-quotient-pre-equivalence-relation-restrict (045Z), including its proof and the preceding quotient-presheaf explanation. I also read Morphisms lemma-base-change-etale (02GO) and lemma-composition-etale (02GN). These are the sources for the item; there are no new nodes needing further sources. I read the chapter and unit records and the current main-20261015 local-term-locality blueprint file. This is a low-level tool in the inherited descent route, not a replacement of the unit's local-term argument.

Step 1 uses the statement of def-pc-fibre-product: it explicitly supplies existence and uniqueness of maps with prescribed compatible projections. Applying it twice gives exactly the three coordinates and two equations. Uniqueness of the middle coordinate uses the monomorphism assumed in the item, not a hidden representability or Yoneda theorem. Precomposition of all three coordinates establishes the claimed naturality.

Step 2 uses the same fibre-product statement for equality of maps after their coordinates agree. It spells out reflexivity, symmetry and transitivity of the inverse image of the given equivalence relation; these are elementary implications. Testing maps from every S-scheme is exactly the defining cancellation property for a monomorphism in schemes over S. No new node for an elementary inverse-image-setoid fact is warranted.

Step 3 uses clause (1) of lem-weil-pbc-etale-base-change-finite-limits and clause (2) of lem-weil-pbc-etale-composition-cancellation. I opened both node statements: the former allows ANY scheme morphism as base-change map and an arbitrary etale object over its target; the latter explicitly states composition of two etale morphisms is etale. The four instances pull back respectively g, s, g and t. All are hypotheses of this item. For the last projection I introduced B and verified its cartesian square from the triples, using def-pc-fibre-product; I did not assume an unspecified re-association comparison or cite a definition as proof of etale stability. Both cited statement nodes are already Mathlib leaves, so there is no unapproved cross-unit route. I read the actual Etale.lean instances at lines 63-88 supporting these leaves.

Step 4 has no external theorem use: a witness r restricts to r c, which makes the two rules on equivalence classes well-defined; the functor and quotient-map laws are direct evaluations. Surjectivity of the quotient projections is the defining representative property of a set quotient. Step 5 also needs no external fact: equality of classes for an equivalence relation is precisely being related. The displayed implication in both directions proves well-definedness and injectivity of v. The naturality square evaluates on a class to [g a c] on both paths, and the final compatibility evaluates on a to [g a]. These elementary computations are included, not hidden under the words 'transport' or 'compatibility'.

For B1-B10 and C1-C8, there are no new-node form, line-number, duplication, or source-tag obligations to discharge on a new statement. The existing leaves already cover the non-elementary facts. Every cited node's precise relevant statement is copied verbatim into citations.json; the proof-dependency union has exactly the three cited nodes. No parent is cited, so the added proof edges cannot close a cycle through the quotient/descent ancestors. Whole-blueprint searches for 'equivalence relation' and 'quotient presheaf' returned respectively the unrelated finite-stage-calculus node and no nodes. A preliminary regexp-like query was treated literally by blueprint_refs and returned no results, so I followed it with these actual word searches. The existing item blueprint origin is retained and its searched same_as remains empty.

For D1-D5 the proof is an actual calculation, not a renamed clause in a new node: the omitted triple, cancellation, cartesian-square and quotient arguments are all explicit. The only non-elementary step has 875 characters, so no step exceeds 2000 characters or hides a long lemma. For E1-E7 I checked every domain and codomain of the four base changes, kept all maps over S, and used neither surjectivity of g nor any finiteness/separatedness assumptions. There is no source error requiring a correction.

I tested g = id (the same relation and identity quotient map), U' empty (empty set quotients for nonempty T; at T empty each Hom set and quotient is a singleton), and the diagonal relation with the open immersion D(x) into the affine line (the quotient map v is injective but need not surject). A two-point etale cover of a point with the diagonal relation on the point shows why g itself need not be injective: the pulled-back relation identifies the two lifts, so v on quotient classes is still injective. These tests confirm the distinction between a map of schemes and its map of relation quotients.

Mathlib searches were made only through msearch.py. The scheme-level searches find etale base-change and category instances, not the full item. The second semantic phrasing finds Setoid.comapQuotientEquiv and Quotient.map: these account for the elementary quotient ingredient, not the scheme triple and etale clauses. Accordingly I created no node for those facts. Every new search record is taken from its actual logged query and result; the inherited unavailable LeanSearch record is preserved as unavailable.

## Not duplicates

No new nodes were created.
