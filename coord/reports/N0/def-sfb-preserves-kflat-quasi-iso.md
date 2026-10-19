# Stage-1 report: def-sfb-preserves-kflat-quasi-iso

## Files written

- dag/nodes/sec-proetale-coefficients/def-sfb-preserves-kflat-quasi-iso.json: existing definition, split with an explicit total tensor construction and a three-step verification; not a Mathlib leaf.
- citations.json: verbatim statements for every node cited in every proof step.
- No new DAG nodes; no new Mathlib leaves.

## Attachments

None. I searched the whole slopmaster2 WeilConjectures tree for the item tag and the K-flat preservation notion, and read CategoryTheory/DerivedCategory/LeftDerivedFunctor/Defs.lean:55–94 and FromJoel/CategoryTheory/Monoidal/KFlat.lean:27–37. CategoryTheory.Functor.PreservesKFlatQuasiIso (Defs.lean:75) defines the functor predicate, and its exact-functor instance (line 92) covers the last clause. The ambient section additionally assumes the graded-object tensor-associativity/exchange conditions. MorphismProperty.kFlat (KFlat.lean:34) is a predicate on an already monoidal category, not the asserted total-tensor construction at the item's weaker hypotheses. These are useful partial implementations, but do not give every clause under exactly the item's hypotheses, so I did not report a whole-item attachment. The upstream master is reference only and was not treated as proof evidence. No Lean was written or compiled.

## WANTED

None. The item, parent unit and chapter are available in the current blueprint, and the Stacks sources used below are present locally.

## STATEMENT-DISPUTED: missing countable coproducts

The imported definition asserted that complexes can be tensored by totalizing in every monoidal abelian category with biadditive tensor. That does not even define an object for general unbounded complexes. For a field k, the category of finite-dimensional k-vector spaces is monoidal abelian and its tensor is additive in both variables. Take P^p = Q^q = k for every integer p,q, with all differentials zero. The alleged degree-zero total tensor requires a countable coproduct of copies of k, which does not exist in this category. Indeed its universal property would identify Hom(V,k), a finite-dimensional space for every object V of this category, with the infinite-dimensional space product_Z k.

I restored the countable-coproduct hypothesis explicitly. This is already a hypothesis of the left-derived-functor bullet in the parent unit sk-def-sfb-derived-categories; it is the intended unbounded direct-sum totalization, not a change of coefficient category or of the unit's route. I specified the degree-n direct sum, the signed differential and the maps on summands. I did not require that tensoring preserve these coproducts: the definition only needs a binary total tensor and the two functors obtained by fixing a factor, rather than an associator on all complexes. This distinguishes the corrected scope from the stronger source Lean ambient assumptions.

The exact-functor assertion is retained, with exactness spelled out as additive and preserving finite limits and finite colimits. Its proof cites an existing more general theorem rather than creating a node that restates this clause. The imported proof's uncited assertion about cohomology is replaced with the precise existing natural comparison and an explicit degreewise conjugation argument.

## Blueprint and dependency audit

I read the current main-20261015 chapter sec-proetale-coefficients/_section.md, the whole unit sk-def-sfb-derived-categories/_section.md, the item's .md and its separate .proof.md. The item carries no blueprint_update. I also read the corresponding DAG node and searched all imported blueprint nodes with blueprint_refs.py for the preservation predicate, monoidal abelian categories, K-flatness and exact functors. Other definitions specialize K-flatness to module sheaves; none duplicates this generic functor predicate. blueprint.same_as is therefore []. blueprint.from stays null because this item is itself imported, not created beneath another blueprint node.

The shared DAG does not contain dag/chapters/sec-proetale-coefficients.json or dag/units/sk-def-sfb-derived-categories.json, and the imported item has no chapter/unit fields. I used the exact current blueprint chapter/unit files above as the route references and did not invent or change maintainer-owned metadata. This item is not the unit's key sk-def-sfb-derived-categories node, so no unit realization record is due from this split.

Statement dependencies now name the generic abelian-category definition, generic cochain complexes/cohomology/quasi-isomorphisms, and the existing generic colimit definition specialized to countable discrete diagrams. The monoidal tensor and its biadditivity are standard Mathlib structures; its binary total tensor formula is given inline. Additivity of F is defined inline on morphism groups. No sheaf-only or commutative/symmetric tensor hypothesis has been silently substituted for the general non-symmetric setting.

## Not duplicates

No new nodes. I reused lem-weil-pbc-exact-functor-complex-cohomology rather than creating an exact-functor preservation or cohomology lemma. I read lem-sp-exact-functor-preserves-homology as an alternative and chose the existing complex-level statement with naturality explicitly included. The blueprint module-sheaf K-flat definitions are specialized notions, not replacements for the generic predicate here.

## Review by N0

For the item I read the current blueprint definition and its one-paragraph proof and the full parent unit, which already assumes the missing coproducts. For the only substantive mathematical tool I read Stacks homology.tex, lemma-exact-functor (Tag 010N), including the kernel/cokernel proof, and derived.tex, lemma-right-derived-exact-functor (Tag 015F), including the sentence that exact functors preserve quasi-isomorphisms. The latter omits the details, so steps 2–3 supply them using the already-existing generic cohomology theorem. There are no new nodes requiring additional sources. I read the actual statements, not just titles, of all four nodes cited by the statement or steps.

Step 1 uses def-weil-pbc-category-colimit only for the universal property of an existing coproduct, with a countable discrete index, and def-weil-abstract-derived-category only for the cochain complex and differential-square-zero definitions. The pure terms of d squared vanish by the complex equations, and the two mixed coefficients have opposite signs. The summandwise maps commute with d and satisfy the identity/composition laws. These are elementary calculations, not an appeal to an uncited theorem about monoidal structures on complexes. The index p+q=n is countable even when both complexes are unbounded. Neither preservation of infinite sums by tensoring nor exactness of coproducts is invoked.

Step 2 uses exactly the statement of lem-weil-pbc-exact-functor-complex-cohomology: an exact functor between abelian categories has the natural comparisons c_K and c_L. Both categories are abelian here, and our explicit definition of exactness is precisely that lemma's hypothesis. Its naturality gives the displayed comparison equation for s. I copied the complete statement to citations.json so the isomorphisms and their naturality are both visible. It is a Mathlib leaf and is used as a generic homological-algebra tool, without replacing the unit's left-derived-functor route.

Step 3 uses def-weil-abstract-derived-category for the fact that a quasi-isomorphism has invertible cohomology maps. The only further inference is that a functor maps an inverse to an inverse, followed by the explicit conjugation formula using step 2. Thus no extra unrecorded theorem about exactness, tensoring or resolutions is hidden in this step. K-flatness is used only by restricting the collection of quasi-isomorphisms, not by claiming an exact functor preserves K-flat objects. D needs no monoidal structure.

For small cases I checked the zero complex and the identity functor, complexes in one degree (the tensor differential is zero and the formula reduces to the ordinary tensor), the signs for p=0,1 and negative p, and zero/identity maps. The finite-dimensional-vector-space test detects the original missing-coproduct fault. Non-symmetric tensors require both preservation conditions in the definition; neither has been dropped. Arbitrary exact F need not preserve countable coproducts, and the proof uses only its termwise action. An additive functor alone has no asserted preservation property.

Against delivery-errors B–E: no unsplit new nodes or duplicated clauses were introduced; all objects and conventions are introduced; mathematical notation uses TeX once; the Stacks citations identify tags and source labels; no Mathlib leaf is claimed without a match; each msearch entry is copied from an actual logged tool/query and the returned hits were inspected, with two semantic phrasings and an all-Mathlib grep before concluding the complete predicate is absent. Each cited statement gives exactly the used assertion (C4), and the only non-elementary step cites the natural cohomology theorem (C1). The construction and inverse calculation stay as elementary steps (D1/D2). No definition is used for a theorem it does not state, no source proof internals are borrowed, and all hypotheses were compared. The statement correction is explicit above, not silent.

## Unfinished work

None in this one-level split. No new nodes are needed. The required delivery dry run is recorded below; nothing is pushed by this worker.

## Second reading by N0

- Item statement: checked against the current blueprint node and parent unit, including the unbounded totalization hypotheses; verdict: the missing countable-coproduct hypothesis is correctly recorded as `STATEMENT-DISPUTED` and repaired, with no dropped K-flat or exact-functor clause.
- Step 1: checked the direct-sum total construction and sign calculation against the displayed statement and the statements of `def-weil-pbc-category-colimit` and `def-weil-abstract-derived-category`; verdict: the countability, differential-square-zero, summand maps, and functor laws are elementary and all cited facts are stated by those nodes.
- Step 2: checked against Stacks homology Tag 010N (`lemma-exact-functor`) and `lem-weil-pbc-exact-functor-complex-cohomology`; verdict: exactness, termwise application, the natural cohomology comparisons, and their naturality equation are exactly the cited statement.
- Step 3: checked against Stacks derived Tag 015F (`lemma-right-derived-exact-functor`) and `def-weil-abstract-derived-category`; verdict: invertibility of cohomology maps, functorial transport of inverses, and restriction to K-flat maps give precisely the stated preservation property.
- New nodes: none; no new-node statement or search audit is required.
- Small cases and hypotheses: checked zero and one-term complexes, the identity functor, positive and negative differential signs, zero maps, and the finite-dimensional-vector-space counterexample to totalization without countable coproducts; verdict: no further statement fault found.

Changes made during this second reading: appended this independent audit section only. The worker's explicit statement correction, expanded proof steps, citations, and search records were retained because they agree with the sources and pass the B–E checks.
