# Q68: lem-sf-localizing-hom-test

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sf-localizing-hom-test.json`: statement; split into five steps. Its hypotheses and conclusion are unchanged; an explicit reference to the already existing definition of full triangulated subcategory was added to its statement and statement dependencies.
- `dag/nodes/sec-six-functors-basics/lem-sf-shift-stable-left-orthogonal.json`: statement; Mathlib leaf, `CategoryTheory.ObjectProperty.instIsTriangulatedLeftOrthogonalOfIsStableUnderShiftInt`, `Mathlib/CategoryTheory/Triangulated/Orthogonal.lean:68`, with the repleteness instance at `Mathlib/CategoryTheory/ObjectProperty/Orthogonal.lean:58`.
- `citations.json`: one verbatim statement quotation for every citation in every item proof step.
- `searches.jsonl`: the actual msearch.py query/result log; `write_split.py`: sandbox-only JSON preparation script.

## Attachments

None for the item. The project has no exact declaration for this arbitrary-class isomorphism test. In `WeilConjectures/CategoryTheory/Triangulated/LocalizingClosureGeneration.lean:77`, `CategoryTheory.ObjectProperty.isZero_of_forall_eq_zero_localizingClosure` proves the zero-detection part for a shift-stable property, not the full item. `BrownRepresentability/RightAdjoint.lean:77`, `CategoryTheory.BrownRepresentability.CompactGenerators.isIso_of_bijective`, assumes compact generators, stronger than the hypotheses here. Neither justifies an ATTACH answer.

## WANTED

None. All sources used are available locally.

## What needed repair

The imported item was statement-only and mathematically correct. Its requested generator test is not stated in the parent's blueprint proof verbatim: the parent split exposed the formal justification of the closed-adjoint/final-restriction identification as this new item. I expanded that justification, without altering the unit or chapter route. The proof is marked agent-written: Stacks supplies the individual triangulated-category facts, rather than this exact assembled proof. The coproduct-orthogonality argument is also directly visible in the project's existing `LocalizingClosureGeneration.lean:61-92`.

I did not use compactness, a set of representatives of the generating class, Brown representability, or a coproduct indexed by that class. In particular the existing geometric `det-brown-hypotheses-generation` and `det-constructible-compactness-ii-generation` cannot substitute for a theorem on an arbitrary locally small triangulated category. `det-sf-determination-localizing` concerns transformations of coproduct-preserving exact functors; the contravariant Hom functors needed here take coproducts to products, so that theorem is not the item or the needed orthogonal lemma.

## Not duplicates

No existing node states the new general orthogonal lemma. Searches of all DAG nodes for 0FXC, `lemma-orthogonal-triangulated`, the exact Mathlib instance, and left orthogonals were checked; blueprint searches for `orthogonal`, `left orthogonal`, `0FXC`, `shift stable`, and `localizing closure` were checked. References to related orthogonal results in stored search hits do not make those nodes statements of the new lemma:

lem-sf-shift-stable-left-orthogonal vs lem-sf-localizing-hom-test: the new leaf proves only triangulated/replete closure of a left orthogonal to an arbitrary shift-stable class; the item proves an isomorphism criterion on a localizing closure, using coproducts and a cone.

lem-sf-shift-stable-left-orthogonal vs det-ambient-ind-derived-triangulated: that node treats the particular geometric Ind-constructible class, not arbitrary left orthogonals.

lem-sf-shift-stable-left-orthogonal vs lem-sfb-int-closed-complement-finiteness: that node treats integral constructibility and an open-complement direct image, not arbitrary left orthogonals.

lem-sf-shift-stable-left-orthogonal vs lem-weil-pbc-module-derived-complete-products-triangles: that node treats products and triangles of derived-complete modules, not arbitrary shift-stable classes in pre-triangulated categories.

lem-sf-shift-stable-left-orthogonal vs lem-weil-integral-constructible-triangulated: that node concerns the integral constructible derived category, not the general orthogonality construction.

lem-sf-shift-stable-left-orthogonal vs lem-per-qbar-middle-tstructure: that node constructs the geometric perverse t-structure; it does not state closure of arbitrary left orthogonals.

lem-sf-shift-stable-left-orthogonal vs lem-sfb-orthogonal-triangle-counit-normalization: that node identifies a particular triangle with an adjunction counit; it does not state triangulated closure of the orthogonal.

lem-sf-shift-stable-left-orthogonal vs lem-exc-orthogonal-counit-triangle: that node constructs a counit triangle from a fully faithful adjunction and orthogonality; it is not the closure theorem.

## Review by Q68

I read the item's complete statement, its parent unit/chapter records, and the current main-20261015 parent proof. I also read Stacks `derived.tex`, Tags 0145 (definition-triangulated-category), 05QM (definition-triangulated-subcategory), 0146 (lemma-composition-zero), 0149 (lemma-representable-homological), 0FXC (lemma-orthogonal-triangulated), and 05QR (lemma-third-object-zero). For the new leaf I read the left-orthogonal definition and repleteness/zero instances in `ObjectProperty/Orthogonal.lean:44-67`, and the shift and triangulated instances in `Triangulated/Orthogonal.lean:46-68`. Mathlib proves the result already with Pretriangulated, without the octahedral axiom, which is the explicitly stated generality of the leaf. Stacks states the triangulated special case; its argument uses only representable exactness and rotations. The new leaf has no proof steps or proof dependencies.

In step 1, `def-weil-triangulated-category` really gives a distinguished triangle completing alpha (TR1), and `def-weil-triangulated-subcategory` really gives shifts and extension closure. Rotation then puts its cone in every subcategory in the defining intersection. B and G both lie in that intersection by the item's actual hypotheses. This is a direct application of the definitions, not an unproved general closure lemma.

In step 2, I opened `lem-weil-pbc-hom-into-triangle-exact`: its clause (ii) is exactness at the middle vertex, so I explicitly rotate the triangle before using it at C. Its clause (i), applied also to rotations, gives both consecutive composites used. Injectivity for alpha[1] is justified by the shift equivalence and the hypothesis at n-1, not assumed at an unrelated object. Given f, the proof writes out delta f = 0, f = pg, g = alpha h, and p alpha = 0, establishing exactly the required vanishing. The shift identifications come from the automorphism in the cited triangulated-category definition.

In step 3, the new leaf states exactly the replete/triangulated property used for Q, the replete class of all C[m]. Q is stable under all shifts by addition of the indices. The leaf does NOT claim coproduct closure. That assertion is proved in the step: a map out of a coproduct is zero when all its restrictions to summands are zero, by uniqueness in the defining universal property. It is an elementary component of the step, which is marked non-elementary because its other component invokes the triangulated orthogonal lemma. This avoids both a hidden non-elementary lemma and a new node for a two-line universal-property argument.

In step 4, the only transport needed is written explicitly: Hom(S,C[m]) identifies with Hom(S[-m],C). Thus every S belongs to the orthogonal. The defining intersection yields Loc(S) contained in that orthogonal, and the cone from step 1 belongs to both it and Q. I wrote out why its zero identity makes it a zero object. No axiom of smallness is smuggled into this argument: each S is used separately and all coproducts are indexed by small sets in the fixed universe.

In step 5, I opened `lem-kun-distinguished-cone-zero`: it states the first arrow of any distinguished triangle is an isomorphism iff its third vertex is a zero object. It has precisely the pre-triangulated hypothesis available here and needs no geometric finiteness assumptions. Both reused theorem nodes are Mathlib leaves, so no off-unit route substitution occurs. All uses were quoted verbatim in citations.json.

I tested the empty generating class: its localizing closure consists of zero objects, and the argument still forces C to be zero. I tested the class consisting only of zero objects, the zero category, and alpha an identity; the vanishing/cone argument has the asserted behavior. For the new leaf the empty Q gives the whole category, Q consisting of zero objects also gives the whole category, and Q all objects forces a zero identity in every object of its orthogonal. Neither a set-sized generating class nor compactness enters any of these checks. Every step is shorter than 2000 characters; the comparison and vanishing arguments are written explicitly rather than hidden in a long step. There is no statement dispute and no unfinished mathematical part of this split.

## What could not be finished

Nothing in the stage-1 split. No Lean source was written or compiled, and no repository or launcher file was edited. Required server dry-run and push results follow in the delivery output.
