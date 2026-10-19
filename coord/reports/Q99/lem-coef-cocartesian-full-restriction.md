# Worker report: lem-coef-cocartesian-full-restriction

## Files written

- dag/nodes/sec-six-functors/lem-coef-cocartesian-full-restriction.json: statement, split into six proof steps; no Mathlib match for the whole item.
- citations.json: exact statement excerpts for every step dependency, including both comparison and composition clauses used in step 3.
- searches.jsonl: actual searches through msearch.py; earlier searches already in the repository node are retained.
- report.md: this report. write_split.py is a sandbox-only generation helper, not a delivery node.

No new nodes, no new Mathlib leaves, no unit file changes.

## Attachments

None. Searched WeilConjectures/ in the read-only slopmaster2 source for the exact blueprint tag, cocartesian, and quasicategory terminology, and searched dag/lean_names_upstream.json for the item. No project declaration supplies the statement. The upstream master remains reference material, not evidence of a completed proof.

## Wanted literature

WANTED: Jacob Lurie, Higher Topos Theory, Remark 2.4.1.4, Proposition 2.4.1.7, Remark 2.4.1.9, Corollaries 2.3.2.4–5, Proposition 3.1.2.1, for lem-coef-cocartesian-full-restriction; read online at https://people.math.harvard.edu/~lurie/papers/HTT.pdf but not archived in literature/.

WANTED: Kerodon Proposition 4.4.2.13 (Kerodon tag 01H0), for the existing generic outer-horn dependency; read online at https://kerodon.net/tag/01H0, not a Stacks tag. No Stacks tag states the quasicategory theorem here.

## What was wrong or missing

The item had a complete statement but no proof. No statement error was found; its exact statement and stmt_deps are unchanged. The source's mapping-space criterion need not be turned into another auxiliary lemma: direct full-subset horn filling proves preservation and restriction, while the existing comparison-of-lifts theorem proves reflection. The diagram assertion requires an actual strict fiber, rather than an unspecified infinity-categorical pullback. Step 4 keeps the entire base simplex constant, and steps 5–6 compute that same strict fiber.

Repleteness is stronger than this proof needs, since existence of a lift with target in R is assumed explicitly. I retained it. It causes no error. No route change, statement dispute, SGA citation, or hidden hypothesis is involved.

## Unfinished work

None at stage 1. The split relies on existing DAG statements, whose further work belongs to those items. It does not claim that their Lean proofs or this item's Lean proof have been written.

## Not duplicates

No new nodes. I searched the whole DAG by cocartesian, full restriction, exponentiation, relative diagrams, outer-horn equivalence, and the cited HTT numbers; blueprint_refs.py searches for cocartesian and full subcategory found no blueprint statement equivalent to this item. I reused lem-coef-infinity-cocartesian-composition-initiality, lem-cbc-inner-fibration-equivalence-outer-horn-lift, and lem-coef-inner-anodyne-pushout-product instead of creating versions of them. The relative-exponential restriction and base-restriction nodes concern different maps, so are not silently substituted for full restriction of the total space.

## Review by Q99

I read the item, its two definition dependencies, the three result dependencies, the chapter and unit records, and the blueprint ancestor prop-coef-integral-exceptional-adjoint (especially the second proof paragraph's finite derived adjunction). This item serves the inherited coherent-enrichment chain below that paragraph, not a new route for the unit's duality theorem. I read HTT online at the horn characterization, composition theorem, initial/final-lift comparison, inner pushout-product corollary and cocartesian exponentiation result. I also read the relative equivalence horn statement in Kerodon 01H0. The proof is recorded as agent-written because the reference is not archived and the full-restriction and strict diagram calculations are supplied explicitly.

For step 1 I checked the actual definition of full subcategory: it contains every simplex whose vertices belong to the selected collection. Every inner horn in dimension at least two contains all vertices, so both the absolute and relative fillers remain inside R. Step 2 uses precisely the outer-horn cocartesian definition; every such horn also contains all vertices, including dimension two. Thus the source and target of the assumed lift suffice, and arbitrary horn fillers cannot introduce a vertex outside R. These are elementary applications of the two cited definitions, not unproved categorical restriction theorems.

For step 3 I checked that the statement of lem-coef-infinity-cocartesian-composition-initiality supplies initiality in the strict lift category over the exact edge, its equivalence-of-targets conclusion, and its composition clause. Both initial lifts are for q, with exactly the same source and base edge, and q was proved to be an inner fibration in step 1. Its comparison really supplies a triangle over the degenerate identity on the endpoint, not a comparison with an unspecified base homotopy. Inclusion sends the inverse triangles to E. The statement of lem-cbc-inner-fibration-equivalence-outer-horn-lift gives fillers over the specified base simplex for any equivalence in an inner fibration, so it applies to this comparison edge for p. Finally composition applies in E to u, v, e. These are exactly the two non-elementary inputs cited in this step. The outer-horn lemma lies in another unit and is declared in split_report.tool_uses as a generic tool, rather than as a replacement route.

For step 4 I read lem-coef-inner-anodyne-pushout-product and its pinned Mathlib theorem SSet.innerAnodyneExtensions_pushoutObjObjι' at AlgebraicTopology/SimplicialSet/AnodyneExtensions/Inner/PushoutProduct.lean:103–108. Its lifting-class statement applies to an inner horn and the injective map from the empty simplicial set to K. Unwinding the product gives exactly K times the horn, so no assertion that arbitrary products preserve an unrelated model fibration is used. Both p and q are inner fibrations, and the base simplex for a horn in a strict fiber is the constant diagram a in every parameter degree. The filler consequently lies in the same strict fiber. K only needs to be small, not a quasicategory or nonempty.

For step 5 I checked the vertices of K times a simplex: they are pairs (k,i), so fullness of R is equivalent to objectwise membership for every diagram vertex. For step 6 I used the actual right-pinched convention: the whole initial face, not merely its vertices, is constant. Fullness puts each mapping simplex inside the smaller category; the equality retains all face and degeneracy operators. Precomposition is literally t times the identity, so it commutes with these equalities. This proves naturality, without assuming transformations are invertible.

I tested R empty, R=E, an ordinary-category nerve, base a point, identity base edges, empty fibers, K a point, and K empty. In the empty K case both relative categories are terminal even if R is empty; the vacuous vertex condition gives that terminal category, not an empty one. No step assumes a nonempty object set. All proof steps are under 2000 characters; none moves an item clause into a newly named lemma. I checked delivery-errors B–E: self-contained statement preserved, definitions cited, exact quotes verified, no new-node or relabelling problem, all non-elementary inputs explicitly cited, and hypotheses checked as above.

The fresh Mathlib searches were made through msearch.py with leanfinder (two phrasings), loogle, grep and leansearch. I read the ordinary IsCocartesian/IsStronglyCocartesian definitions at Cocartesian.lean:46–78. Their unique Hom-set factorization cannot supply the quasicategorical statement. The second semantic search returned fully faithful nerve and strict-Segal results; I read NerveAdjunction.lean:402–407: fullness of the ordinary nerve functor does not prove restriction of an arbitrary quasicategorical fibration. Ordinary comma fullness and colimit-creation hits likewise have ordinary categories as inputs, not the objects in this item. The exact logged queries and results are retained; the inherited unavailable LeanSearch result is not recast as evidence of absence.

## Continuation audit by Q99

I compared the retained sandbox with the current shared item: its statement, statement dependencies, source, blueprint ancestry and maintainer metadata agree; only the split-owned proof and search fields differ. I reopened all five cited node statements and checked every quoted excerpt against them. The resumed dry run rejected the step 4 pushout-product quote as too short. I replaced it by the complete statement, including its hypotheses, formula and inner-anodyne conclusion, and expanded the definition quotes where the steps use horn-cocartesian edges, exponentials or right-pinched mapping spaces. The two excerpts of the comparison/composition node are now one complete-statement entry so neither clause is lost by a dictionary-based citation reader. No mathematical claim or dependency changed. Each of the six proof steps is under 2000 characters.
