# Stage-1 report: lem-weil-pbc-finite-basis-cech-first-limit

## Files written

- `dag/nodes/sec-proper-base-change/lem-weil-pbc-finite-basis-cech-first-limit.json`: existing statement, now split into six proof steps. No Mathlib match for the complete geometric comparison.
- `citations.json`: eleven step/node entries, each checked against the actual statement of the cited repository node.
- `report.md`: this report. `searches.jsonl` is the unmodified output log written by msearch.py.

New nodes: 0. New Mathlib leaves: 0. The statement, statement dependencies, source, chapter, unit, and all maintainer-owned metadata are preserved.

## Attachments

None. I searched `lean/WeilConjectures/` for the exact blueprint tag and for finite Cech/limit/colimit terminology. `AlgebraicGeometry.Scheme.preservesColimitsOfShape_finiteEtaleCechHomology` in `AlgebraicGeometry/FiniteEtaleCechFilteredColimit.lean:163` treats a fixed covering on the small etale site and varies the coefficient sheaf. Its section-preservation hypothesis does not supply this item's continuity in the covering schemes, and it does not state the pro-etale comparison in the item. The other hits concern affine structure-sheaf sections, finite compact topological Cech complexes, or stage-data constructions, and do not give every clause here. The upstream injective-acyclicity module has a sorry and concerns positive derived vanishing; it is not an attachment for this comparison without injectivity.

## WANTED

None. The proof follows the available Stacks source `literature/stacks-project/proetale.tex`, Tags 099S and 099U. The algebraic colimit ingredients are also present in `algebra.tex` and `categories.tex`. No unavailable source is needed to supply a new lemma.

## Problems in the imported item and changes

The item was statement-only. Its seeded source correctly identifies the first of the two separate limit calculations in Tag 099U. I supplied that argument, including the differential equations and the induced maps on cohomology. No statement dispute or hypothesis correction was necessary.

An important distinction is that the finite-stage covering members are etale over U, but U and hence those stages need only be ind-etale over X. The classical continuity definition limited to presentations with stages etale over X would not suffice. I reused `lem-weil-pbc-proetale-classical-continuity-sets`, whose actual statement explicitly permits merely ind-etale stages. I did not cite a definition of continuity as a theorem or use the proof of a different node as an extra assertion.

The current main-20261015 ancestor is under `sec-proetale-coefficients/sk-lem-pe-injective-acyclicity/`. I read both its statement and its separate `.proof.md`, as well as the older master ancestor. Their first-limit argument agrees. The item's existing provenance and its assigned chapter/unit remain unchanged. This supporting split realizes that first-limit argument and does not replace any unit or chapter proof step.

## Not duplicates

No new nodes were created. Before settling this, I searched the entire DAG for Tags 099S and 099U, filtered-colimit exactness, finite products, cochain homology and section continuity; I read the candidate statements, not just the titles. Whole-blueprint searches for `Čech`, `Cech`, `limit-pullback`, and `first limit` found no blueprint node giving this geometric first-limit comparison in a different form. Thus `blueprint.same_as` remains empty. The ancestor command confirms `lem-weil-pbc-comparison-injective-acyclicity` as the blueprint ancestor.

The existing finite-product comparison, elementwise module colimit criterion, filtered-colimit exactness, classical section continuity, and exact-colimit homology preservation nodes are reused. The differential check and colimit-complex construction are routine steps of the item, not new nodes. Neither clause of the item has been relabelled as a new helper.

## Mathlib searches

The pre-existing five searches on the item are retained. Five additional searches were actually run through the required msearch.py command, with their exact tool/query strings copied from `searches.jsonl` into the node. LeanFinder was tried with two phrasings, Loogle with `CategoryTheory.cechComplexFunctor, CategoryTheory.Limits.IsColimit`, grep with the Cech/colimit pattern in `CategoryTheory`, and LeanSearch with the geometric finite-covering statement. All five services returned successfully in this run. I read their returned types. They describe affine structure-sheaf limits, abstract Cech constructions, topological sheaf-condition cocones, connected-complex homology, or condensed locally constant cocones; none asserts this item's classical-module section comparison. I also read `Mathlib/CategoryTheory/Sites/SheafCohomology/Cech.lean`, especially the actual definition at line 65. It constructs the complex but supplies no geometric continuity theorem. No unrun query was added and no unavailable service was recorded as a negative result.

## Review by NI

I read the worker contract, stage-1 rules, SETUP's three levels, GOAL, and both copies of delivery-errors sections B through E in full. I reviewed the actual node and its references against the available source, rather than treating the imported dependency list as an accepted proof. The source passage is Tag 099U, from the presentations indexed by the finite product of the A_i through the first displayed Cech-colimit equality; Tag 099S explicitly gives section continuity for qcqs pro-etale stages with affine transitions. I also read Tag 002W in `categories.tex`, Tags 00D6, 00D7 and 00DB in `algebra.tex`, and the existing general exact-colimit homology declaration in `lean/WeilConjectures/CategoryTheory/DerivedCategory/DegreewiseLimits.lean:142`. There are no new-node sources to review.

For step 1 I opened `lem-weil-pbc-finite-intersection-limit-compatibility` and checked its entire statement: it supplies the small nonempty directed coordinate sets, every ordered intersection including repetitions, affine ind-etale X-objects, the scheme limits, affine transitions, and compatibility with every factor-deletion projection. Smallness and directedness of the finite product are justified coordinatewise in the step. The fact that the limit lies in the same full affine ind-etale category is the immediate universal-property restriction of the supplied scheme limit. No assumption that a first-limit stage is etale over X is used.

For step 2 I read the statements of the site-comparison definition, `lem-weil-pbc-proetale-classical-continuity-sets`, and the elementwise filtered module colimit criterion. The definition explicitly applies the set inverse image to addition, zero, negation and each scalar endomorphism, so the underlying sheaf is the pullback of the underlying set sheaf. The continuity theorem covers all the stages from step 1, and gives the actual restriction cocone. The module criterion, specialized to integer modules, identifies the underlying abelian-group colimit with the same representatives and eventual-equality relation. Consequently the set bijection is the required group isomorphism. This avoids silently changing the finite ring to a commutative ring or changing the coefficients to condensed modules.

For step 3 I read `def-weil-pbc-cover-cech` and `lem-weil-pbc-filtered-colimits-commute-finite-limits`. The definition specifies the full ordered tuple set and the product of section groups. The latter statement explicitly includes abelian groups, not just sets, and finite products as a special case. The product is finite separately in each fixed degree. There is no interchange of a colimit with an infinite product over degrees, nor any need for a uniform finite length of the whole complex.

For step 4 the two cited statements really supply the needed assertions: the intersection-limit node gives each commuting face square, and the covering-Cech definition gives the alternating sum. I wrote the contravariant composition equation and evaluated the two differentials coordinate by coordinate. The same projection equation at transition stages makes the stage maps cochain maps. The signs, deletion positions and repeated indices therefore agree; this is an elementary calculation from those two statements, not an uncited geometric comparison theorem.

Step 5 has no black-box result hidden in it. I construct the degreewise colimit, its differential, its square-zero property and its universal factorization into an arbitrary complex directly from the group-colimit universal properties. The maps commute with the differential because they do so after every colimit leg. Multiplying the cochain equation by the degreewise inverses proves that the inverse is also a cochain map. This routine argument stays in the parent proof, and does not create an elementary auxiliary node.

For step 6 I read the exactness node and `src-weil-homology-preserves-exact-colimits`: the former gives exactness for every pointwise exact sequence of abelian-group diagrams; the latter applies to any abelian category and any complex shape when the indicated colimits are exact. Its hypotheses hold for Ab and the small filtered J. Its conclusion is preservation of the same complex colimit, so its legs are homology of those colimit legs. Composing with the complex isomorphism therefore gives exactly the canonical restriction-induced cohomology map. The Cech definition explicitly uses unaugmented cohomology and zero incoming image in degree zero, so no augmented-degree convention or vanishing assumption has been imported. These nodes are in the same unit or Mathlib leaves; no off-route tool declaration is needed.

I checked the small cases: m=1 still has one ordered tuple in each degree, so the construction and alternating differential remain valid without normalizing the nerve; a singleton J reduces all comparisons to restrictions along the supplied limit isomorphism; an empty scheme and empty intersection objects cause no exception for the section-continuity theorem; a zero coefficient sheaf gives zero complexes; q=0 is kernel cohomology with zero incoming differential. Noninjective F and noncommutative finite Lambda are allowed throughout because the comparison and all colimits in the conclusion are taken in underlying abelian groups. The statement requires m nonzero and the J_a nonempty, so I did not introduce an empty-index assumption or need an empty-index exception. None of the six steps exceeds 2000 characters, and I checked them individually for a hidden comparison lemma nonetheless.

For delivery-errors B, there are no new-node schema, self-containment, tag, search, or duplicate issues; the item's original data and all provenance fields are retained. For C, I read every cited statement and generated eleven verbatim quotes, checked against those actual statement strings. Every non-elementary input is named, and the proof dependencies are exactly the union of the step uses. For D, the six steps carry the argument rather than delegating either conclusion to a clause-restating helper. For E, I checked all continuity, smallness, coefficient and finite-product hypotheses, wrote the face equations instead of saying only that the comparison transports, and verified the cases above. No counterexample or source error was found.

## What remains unfinished

Nothing in the stage-1 split. This delivery writes no Lean, runs no compiler or build, and makes no claim that the comparison has been formally proved. Formalization of the split is outside this task.

## Validation

The standalone server `review_split` check passed with zero new nodes. The complete required dry run and push are performed after this report is written; their terminal outputs are the delivery evidence.
