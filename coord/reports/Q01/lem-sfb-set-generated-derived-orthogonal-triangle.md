# Q01 stage-1 report

Item: lem-sfb-set-generated-derived-orthogonal-triangle. Date: 2026-10-24.

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-set-generated-derived-orthogonal-triangle.json: statement, split; preserved the statement and all inherited metadata, added a five-step proof using existing nodes. Appended the actual sandbox Mathlib searches to inherited searches.
- citations.json: twelve citations, one for each step/node pair, quoting the existing statement verbatim.
- report.md: this report. searches.jsonl was produced by the authorized search command.

New nodes: 0. Mathlib leaves: 0.

## Attachments

None. Searched the live WeilConjectures source for the exact blueprint tag, set-generation, Brown, and orthogonal-triangle vocabulary. Completion.lean constructs a reflector assuming suitable triangles; it does not establish this item's triangle existence. The generic Brown declarations require compact generators, which the arbitrary P_i in this item need not be. No project declaration found states the item.

## Literature wanted

WANTED: Hall--Neeman--Rydh, One positive and two negative results for derived categories of algebraic stacks, arXiv:1405.1888v2, Appendix A, Lemma A.1 and Remark A.2, archive for lem-sfb-set-generated-derived-orthogonal-triangle. Read the online HTML at https://arxiv.org/html/1405.1888; no archive found in the permitted literature search. No literature files were changed.

The assembly is marked agent-written. Its representability input is already split in the DAG through solution sets and a kernel-killing representability theorem; it does not introduce new well-generation assertions or cite an unavailable monograph as a proof step.

## Findings and changes

The imported item had no argument. Its statement is correct and was kept verbatim: U-small generators need not be compact, and the right orthogonal must vanish against every object of the localizing hull. Reusing the existing solution-set theorem avoids duplicating well-generation infrastructure. The proof represents the restricted Hom functor directly, identifies its representing map by naturality, and calculates its cone's orthogonality. No functorial choice of cones or extra adjunction theorem is required.

The inherited blueprint ancestor is null, and the ancestor command confirms None. Its explicit inherited from.place and via list are retained; same_as remains empty after whole-blueprint searches for well-generation, localizing subcategories, solution sets and orthogonal triangles. Read the current latest ctf-stability unit and direct-images proof, and current latest det-existence-localizing.proof.md, Brown step (3). This remains a generic supporting lemma below the assigned direct-image route; no unit statement or route was changed.

The local-smallness node's statement is general for abelian categories with K-injective resolutions, although its stmt_deps name a ringed-site resolution node. Step 1 supplies its actual general K-injective hypothesis from lem-weil-pbc-kinjective-functorial-existence; it does not assume our arbitrary Grothendieck category is a ringed-site category. This upstream dependency discrepancy is reported here, not repaired in another node.

## Not duplicates

No new nodes. Existing set-generated solution-set and solution-set representability statements are reused; neither states an orthogonal triangle. Existing compact Brown criteria were rejected as too restrictive for the arbitrary generating family. The solution-set and representability dependency closures were read and searched and do not depend on the assigned item, preventing a cycle through weak-Serre generation.

## Review by Q01

I read delivery-errors B through E in full, the worker brief, GOAL, the stage-1 rules, the three blueprint levels, and the chapter/unit records. For the item I read HNR Appendix A online: the localization argument in Lemma A.1 represents the inclusion's restricted Hom functors and then takes its counit triangle, while Remark A.2 permits a Grothendieck derived ambient category. I implement that representing-map argument with the existing solution-set interfaces. Sources additionally opened were Stacks injectives.tex, Tag 07D9 (lemma-derived-products), derived.tex Tags 0146 and 0149 (lemma-composition-zero and lemma-representable-homological), and Tag 05QW (lemma-projectors-have-images-triangulated). I also read the actual general local-smallness instance in WeilConjectures/CategoryTheory/GrothendieckAbelian/HasDerivedCategory.lean and the solution-set theorem interface and proof in Sheaf/CategoryTheory/CohomologicalSolutionSetRepresentability.lean. There are no new nodes needing a separate source review.

Step 1 uses the statements of functorial K-injective existence, derived local smallness, derived coproducts, triangulated subcategories, and countable-coproduct idempotent completeness. They respectively provide precisely the resolution hypothesis, U-small Hom sets, ambient coproducts, inherited triangulation, and split idempotents. Fullness and ambient closure transfer the coproduct universal property to the subcategory. The countable indexing set is U-small. Every hypothesis holds for the given Grothendieck category, without a compactness or boundedness assumption.

Step 2 uses the actual two clauses of Hom-out-of-triangle exactness on rotations, and zero consecutive composites from Hom-into-triangle exactness, to make Hom(-,Y) cohomological. The covariance is explicitly reversed. The coproduct-to-product comparison is written by its inverse universal map, so it assumes no continuity theorem or compactness of Y. All values lie in Ab_U by step 1.

Step 3 uses lem-sfb-set-generated-derived-solution-set with the class represented by the U-small family P_i, not a class of all objects or a large skeleton. Its statement explicitly supplies the pairs through which all elements pull back. I checked that the cohomological solution-set representability statement asks for exactly those pairs, U-small Homs and coproducts, split idempotents, and the cohomological/product conditions verified in steps 1 and 2. It gives a set-valued natural representation, which suffices here; an unasserted additive representation is not used.

Step 4 is elementary: evaluating the natural representation at the identity makes every component postcomposition by epsilon. The triangulated-subcategory statement explicitly includes closure under all integer shifts. Using W[-1] and the shift equivalence proves that postcomposition by epsilon[1] is also bijective. No exactness of a newly constructed adjoint is assumed.

Step 5 uses TR1 from the triangulated-category definition to take the cone. I checked that Hom-into-triangle clause (ii) on the first rotation gives factorization through Y, and zero composites on rotations give epsilon[1] d = 0, with the harmless rotation sign removed. Injectivity for epsilon[1] kills d a; surjectivity for epsilon factors b; the original zero composite kills a. This proves orthogonality to every W, rather than only P_i, and keeps X in the hull.

Small cases checked: I empty, or every P_i zero, gives the zero hull and triangle 0 -> Y -> Y -> 0; Y=0 gives a zero representing object and zero cone; for Y in the hull the representing map is an isomorphism and the cone vanishes. For an arbitrary family no compactness was inserted. There are no new statements to test, no relabelled clause nodes, and no proof step exceeds 2000 characters. The five off-unit generic tool uses are declared in split_report.tool_uses for the maintainer to review; the other cited statements are definitions or Mathlib/closed tools.

Mathlib searches were run through msearch.py and their hits read. Natural-language searches returned ambient derived localization and orthogonal-property declarations; Orthogonal.lean defines right orthogonals and their triangulation/locality, not the existence of an approximating object for an arbitrary small family. Loogle returned no hit for the joint orthogonal/adjunction query. The grep returned Orthogonal.lean lines 16, 40, 56, 66, 70, read in context. The alternate Brown semantic search returned cardinal-filtered generators or ordinary derived construction lemmas, not this coreflection. No hit is an exact match or a one-line specialization. All recorded new queries are in searches.jsonl; inherited records were retained.

## Unfinished work

None for this one-level split. Existing dependencies retain their independent proof obligations; none was treated as proved merely because a Lean statement exists.

## Validation and delivery

Server review_split: PASS, zero new nodes. All twelve citation quotes and the exact proof-dependency union were independently checked in the sandbox. Full deliver.py --no-push: OK (not pushed), preflight passed at 42cddd895f0. Final delivery uses the same node and citations, with this validation note added to the report. No local DAG checks, Lean compiler, Lake, or repository git commands were run.
