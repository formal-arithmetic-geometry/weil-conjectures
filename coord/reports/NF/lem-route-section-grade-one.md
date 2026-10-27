# Worker report: lem-route-section-grade-one

## Files written

- `dag/nodes/sec-nagata-compactification/lem-route-section-grade-one.json`: statement, split into two elementary steps; no exact Mathlib match.
- `citations.json`: verbatim statement extracts for both proof-step citations.
- `searches.jsonl`: actual search-command records; all were run in this attempt.
- `report.md`: this report and NF's source review.

There are 0 new nodes and 0 Mathlib leaves. No Lean, repository, launcher, unit, or chapter files were changed.

## Attachments

None. The live declaration `AlgebraicGeometry.RelativeProjAlgebra.sectionGrade_one` in `lean/Sheaf/AlgebraicGeometry/RelativeProjData.lean` contains `sorry`. Searches of `lean/WeilConjectures/` for the blueprint tag, the declaration, `sectionGrade`, `RelativeProjAlgebra`, and degree-zero unit terminology found no declaration giving this statement under its actual input hypotheses.

## WANTED

None.

## What was wrong and what changed

The imported item was provisional: a short title and a Lean signature with implicit ambient data, without statement dependencies or a proof. I wrote out its ambient scheme, algebra sheaf, homogeneous module sheaves, decomposition, unit compatibility, and the definition of the image subgroup. This is the attached Lean statement with its existing `RelativeProjAlgebra` hypotheses made explicit, not a changed mathematical assertion. It does not assume the section ring already has a graded-ring instance, and it does not assume the degree-zero piece equals the structure sheaf. The multiplication compatibility is retained as part of the original input, although this particular assertion uses only its unit compatibility.

The live blueprint currently presents relative Proj using already graded rings on affines. This helper belongs to the implementation's preliminary passage from homogeneous sheaves to those graded section rings. Its blueprint ancestor remains `lemma-nagata-relative-proj-exists` through `lem-nagata-proj-affine-restriction`. Its `from.place` now locates the graded ring C=A(V) in the current proof's first paragraph. I retained the assigned chapter and unit rather than altering any route record. No unit realization was edited: this helper is not the unit's key statement.

## Search evidence and reuse

The mandated archive-list command found no abandoned attempts for this item. The active sandbox initially had only dispatcher `.brief*` files, with no node, report or prior searches. There was no repair note for the item. Thus no archived claim or search was reused.

I searched the whole DAG for the declaration and image-grading terminology, and the blueprint with `blueprint_refs.py search` for `graded`, `graded sheaf`, and `degree-zero unit` (also a broad `unit` search). There is no second blueprint statement of this exact helper. Existing `lem-route-unit-mem` is a separately seeded, more general assertion for every base-ring section; its attached proof is also `sorry`. I did not create another version of it, nor move this item's proof into it: the two-line witness argument is given here directly. The existing graded-sheaf and algebra-sheaf definition nodes provide all the needed notions. No new node or same-tag pair requires a `Not duplicates` entry.

Both natural-language phrasings, Loogle patterns, and local Mathlib greps were run through `msearch.py` and their actual results read. `SetLike.one_mem_graded` at `Mathlib/Algebra/GradedMonoid.lean:489` requires `[SetLike.GradedOne A]`, whose defining field at line 485 is precisely the desired membership. It would be circular to obtain that assumption from `sectionGradedRing`, since that instance uses this theorem. Other returned direct-sum lemmas assume an already supplied grading or a direct-sum ring structure; none establishes the compatibility for the image of the specified sheaf summand. The second semantic search returned scalar-image/submodule/localization results, not this interface. A first grep supplied the nonexistent subdirectory `Algebra/GradedMonoid` and returned zero hits; this is explicitly marked inconclusive in the node. The corrected single-file and containing-directory searches found and were checked against the actual source at lines 485-491, and a whole-Mathlib grep found no `RelativeProjAlgebra`/`sectionGrade` declaration. No unrun search is recorded and no unavailable service was treated as negative evidence.

## Review by NF

I read `GOAL.md`, the stage-1 brief, the three blueprint levels in `SETUP.md`, the stage-1 contract, delivery-errors B-E, the assigned chapter/unit records, the item and its blueprint ancestor. For the mathematical source I read the current `literature/blueprint/latest/blueprint/sec-nagata-compactification/sk-def-nagata-admissible/def-nagata-relative-proj.md` and `lemma-nagata-relative-proj-exists.proof.md`. I also read Stacks Constructions, Tags 01NM (`section-relative-proj-via-glueing`) and 01NN (`situation-relative-proj`), including the initial affine-section setup before 01NO. These explain why the algebra of affine sections must be graded. The exact elementary argument is spelled out in the attached Lean docstring: apply `unit_eq` to 1 and use the structure map's preservation of 1. I read `RelativeProjAlgebra`, its `unit_eq`, `sections`, `sectionGrade`, and the sorried theorem in the live source. I also read the actual `GradedSheafAlgebra.unit` interface in the project. There are no new nodes requiring additional sources.

In step 1, the cited `def-weil-pbc-graded-sheaf-structures` explicitly supplies an O_X-linear unit into B_0. Its quoted sentence says exactly this. Evaluating it at the section 1 on V gives a well-typed b in Gamma(V,B_0); the presentation's unit equation is a hypothesis, so substituting r=1 yields i_0(b)=alpha(1), without appealing to any theorem about quasi-coherence, direct sums of sections, or an existing grading. The direct sum is a direct sum of sheaves, and the proof never replaces its sections by a direct sum of sections. This checks C1/C4 and avoids a hidden affine-sections comparison lemma.

In step 2, the cited `def-weil-pbc-comm-algebra-sheaf` says the structure map is a morphism of ring sheaves. On V it is therefore a unital ring homomorphism; alpha(1)=1 is one of its defining laws, not a separate theorem being used without a node. Substitution into step 1 gives an explicit preimage of 1. Membership in the image additive subgroup is the existential claim that this preimage exists, so the conclusion follows by its definition. The two steps are elementary in the sense of the contract; the complete argument is present rather than replaced by a new node restating its conclusion. Every proof-step node reference has an exact verbatim quote in `citations.json`, checked against the live statements.

I tested the small cases that expose possible hidden assumptions: on the empty affine open the section rings are zero rings, so b=eta(0) and 1=0 still give the same witness; for the zero algebra sheaf the conclusion also says 0 belongs to the zero subgroup. For a degree-zero algebra strictly larger than O_X, for example a polynomial algebra concentrated in degree zero, the proof still uses only the structural map and never identifies B_0 with O_X. If B_0 is zero, unit compatibility forces 1=0 in the section algebra, so this case is consistent as well. No injectivity or surjectivity of eta or alpha is needed. Affineness and quasi-coherence are retained to match the exact attached interface, but are not needed by this argument. Both proof steps are under 2000 characters. No SGA source, unit-route replacement, target change, or statement dispute is involved.

## What remains unfinished

Nothing for this stage-1 split. The existing Lean proof is still `sorry`, as required by the stage-1-only brief; no compiler or Lake command was run. Delivery verification is performed by the required server-side dry run below.
