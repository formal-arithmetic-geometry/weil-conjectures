# Worker report

1. Files written:
   - dag/nodes/sec-proetale-coefficients/lem-sfb-filtered-ring-object-cocone-colimit.json: item, unchanged statement; five-step assembly.
   - dag/nodes/sec-proetale-coefficients/lem-sfb-diagonal-tensor-colimit-hom-ext.json: one new statement-only unsplit lemma; no exact Mathlib match.
   - citations.json: verbatim statement excerpts for every proof-step citation.
2. Attachments: none. Searching WeilConjectures for the blueprint tag and filtered_cocone_isColimit gave no declaration. The current Sheaf.CategoryTheory.FilteredRingObjectCoconeColimit file does contain the complete original proof; the human specifically reopened this item for a deliberate stage-1 re-split. Its Lean binding and prior review fields are retained unchanged. Local hdiag/hmixed in that proof are not declarations covering the new generic lemma.
3. WANTED: none.
4. The former split kept the entire tensor-square equality-detection argument inline. This delivery extracts that argument without changing the target, coefficient categories, route, or Lean files. No mathematical statement dispute was found. The task-specific re-split instruction overrides the standing rule against touching already-reviewed splits.
5. Unfinished work: the new lemma is intentionally unsplit and proof-free, for another worker. No part of the item's assembly is left unproved in words.

## Sources and coverage of the original argument

I read the chapter sec-proetale-coefficients and unit sk-prop-sfb-qlbar-colimit-x, including its Third isomorphism paragraph, in the current main-20261015 snapshot. I read the complete old seven-step proof and Sheaf.CategoryTheory.FilteredRingObjectCoconeColimit (particularly its hdiag, hmixed and two hom_ext applications), and the private sifted helper at CompletedCondensedCoefficients lines 219-254. I read Stacks categories.tex at definition-colimit (Tag 002F), definition-directed (Tag 002V), and definition-monoidal-category (Tag 0FFK). The new lemma is an agent abstraction of this argument, not a claim that Stacks explicitly states the entire theorem. No SGA source is used.

Old steps 1, 2, 3 and 7 survive verbatim as new steps 1, 2, 3 and 5. Old steps 4, 5 and 6 are the one independent new lemma, with full argument for its future worker below. New step 4 applies its statement. The original mediator construction, unit calculation, same-stage multiplication calculation, common-stage factorization, both colimit uniqueness arguments, uniqueness of the bundled map, and commutative full-subcategory clause are all preserved.

## Argument assigned to the new node

Let X, A, c_i, f, g be the objects introduced in the new statement. Given i,j, choose k and arrows u:i→k, v:j→k. Naturality of the cocone and bifunctoriality give

(c_i ⊗ c_j) = (c_k ⊗ c_k) ∘ (X(u) ⊗ X(v)).

Precompose the diagonal equality for k with X(u) ⊗ X(v). This proves f ∘ (c_i ⊗ c_j) = g ∘ (c_i ⊗ c_j) for every i,j. It uses only existence of the common successor, not any parallel-arrow equalization.

Fix i. The assumed image cocone with vertex X(i) ⊗ A and legs id ⊗ c_j is colimiting. The maps f ∘ (c_i ⊗ id_A) and g ∘ (c_i ⊗ id_A) agree after each leg because (c_i ⊗ id_A) ∘ (id ⊗ c_j) = c_i ⊗ c_j. Both are mediators for the same cocone, so colimit uniqueness makes them equal. Finally the assumed colimit cocone with vertex A ⊗ A and legs c_i ⊗ id_A makes f and g equal. These are the original three arguments, with every type and preservation hypothesis explicit; no use of elements, joint surjectivity, or an unstated diagonal-colimit theorem occurs.

This is a proper smaller lemma: its statement is about equality of arbitrary morphisms out of a tensor square. It has no multiplication, unit, monoid object or ring-object universal property. Its proof requires a common-successor reduction and two successive universal-property arguments, not a two-line rearrangement. The item's unit and ring-object assembly remain separate. It is not a restatement of the whole item or of one of its ring-object colimit clauses.

## Searches and Mathlib verdict

All new Mathlib searches were run through batch2/msearch.py and remain verbatim in searches.jsonl and the new node's mathlib_searches. Two semantic phrasings were tried, together with LeanSearch, Loogle and grep. The first Loogle query used an unknown tensorHom identifier; that diagnostic is recorded as an invalid query, and the successful IsColimit.tensor query replaces it. Nothing is recorded as absent on the strength of that error.

I read Mathlib/CategoryTheory/Monoidal/Limits/Colimits.lean, especially IsColimit.tensor₂ at 51-54 and IsColimit.tensor at 76-87. The latter requires IsSifted I, whereas the new node only needs common successors. For example the one-object category of a nontrivial group satisfies the new object condition but is not sifted. The Cartesian product comparison of sifted colimits, concrete filtered-monoid multiplication formulas, and the Bimod coequalizer formulas in the semantic hits do not state this result. General IsColimit.hom_ext supplies the two successive uniqueness steps but does not itself discharge the mixed-to-diagonal argument. Accordingly the new node is unsplit, not a Mathlib leaf. The item's existing Mathlib searches are retained in full.

DAG/blueprint searches: blueprint_refs ancestor returns sk-prop-sfb-qlbar-colimit-x; search phrases included tensor colimit, tensor colimit cocone, diagonal tensor, common successor and ring-object cocone. No imported node states the extracted lemma. DAG searches covered the same notions, the prospective id, and all three Stacks tags. I compared the likely concrete tensor-colimit nodes and the coefficient-push and cone-graded hom-ext nodes; none is the arbitrary monoidal equality-detection statement. The new node has the blueprint ancestor and via=[lem-sfb-filtered-ring-object-cocone-colimit], with an exact Third isomorphism place and empty same_as.

## Review by NI

Step 1 uses def-weil-pbc-category-colimit, whose statement gives exactly the unique underlying mediator for the compatible cocone. All diagrams retain the small index of the item.

Step 2 uses sk-def-sfb-ring-object for preservation of units and def-weil-pbc-category-colimit for the mediator equation. The choice of i is permitted by the item's nonemptiness. The displayed composite has domain the monoidal unit and codomain B.

Step 3 uses sk-def-sfb-ring-object for the multiplication equations of c_k and b_k, and def-sfb-monoidal-category for tensor bifunctoriality. Each composite has domain D(k) ⊗ D(k) and codomain B. The mediator equation comes from step 1. The same-stage computation is retained verbatim.

Step 4 uses the new lemma's statement, not its future proof: X is the underlying diagram, its vertex is A, T=B, and f,g are the exact two composites of step 3. I checked that filteredness supplies nonemptiness and common successors, while the original preservation assumptions imply both of the new lemma's image-cocone hypotheses at precisely X(i) and A. Step 3 gives all diagonal equalities. The conclusion f=g and the unit equation are exactly the two equations in sk-def-sfb-ring-object, so no further algebra lemma is hidden.

Step 5 uses def-weil-pbc-category-colimit for underlying uniqueness and sk-def-sfb-ring-object for the nature of its morphisms. A ring-object morphism is an underlying map satisfying equations, hence equal underlying maps are equal morphisms. The commutative case quantifies over a commutative B; the full-subcategory convention in the unchanged item says exactly that the same mediator is eligible. No assertion that an arbitrary full subcategory is colimit-closed is being used.

For the new node I checked nonempty singleton I (c is an isomorphism); directed systems of abelian groups with the usual tensor; and a one-object category with parallel automorphisms, for which the common-successor reduction still works without equalization. The new lemma does not assert that the diagonal tensor cocone is colimiting. Indeed in Set with Cartesian tensor, for the swapping action of C₂ on a two-element set, A is a singleton, whereas the diagonal action on its square has two orbits. The diagonal cocone is not a colimit there, but its leg into A×A is surjective, so the new equality test holds. This rules out misusing the sifted theorem and verifies that the weaker hypothesis is substantive. For the original item, singleton I, the zero ring in Ab, and noncommutative ring objects satisfy the assembly; symmetry is used only in stating the commutative clause.

I checked delivery-errors B-E: the new node introduces all objects and has no proof sketch/steps/dependencies; it cites only its two defining notions and gives exact Stacks tags and labels. Each step's citations were opened and their statements read. The quotes in citations.json are literal substrings. The new lemma has only definition dependencies, so it cannot cycle back to the item; the unit and chapter route stay fixed. Old Lean and blueprint metadata, prior citations and logged searches are preserved. No proof step exceeds 2000 characters; the full new assembly is below 3000 characters. No statement correction was required.

## Not duplicates

lem-sfb-diagonal-tensor-colimit-hom-ext vs def-galois-finite-limits-colimits: the existing statement concerns Finite limits and finite colimits; the new statement is equality detection for arbitrary maps from A tensor A in any monoidal category, under only common successors and the two specified image-colimit hypotheses.

lem-sfb-diagonal-tensor-colimit-hom-ext vs lem-per-noetherian-local-colimit-regular: the existing statement concerns Noetherian directed colimits of regular local rings are regular local; the new statement is equality detection for arbitrary maps from A tensor A in any monoidal category, under only common successors and the two specified image-colimit hypotheses.

lem-sfb-diagonal-tensor-colimit-hom-ext vs def-weil-proetale-geometric-stalk: the existing statement concerns Stalk of a pro-etale sheaf at a geometric point; the new statement is equality detection for arbitrary maps from A tensor A in any monoidal category, under only common successors and the two specified image-colimit hypotheses.

lem-sfb-diagonal-tensor-colimit-hom-ext vs lem-pd-monoidal-adjunction-equivalence-transport: the existing statement concerns Transport normalized lax structures and their mates across monoidal equivalences; the new statement is equality detection for arbitrary maps from A tensor A in any monoidal category, under only common successors and the two specified image-colimit hypotheses.

lem-sfb-diagonal-tensor-colimit-hom-ext vs def-sfb-adjunction-has-projection-formula: the existing statement concerns Adjunctions satisfying the projection formula; the new statement is equality detection for arbitrary maps from A tensor A in any monoidal category, under only common successors and the two specified image-colimit hypotheses.

lem-sfb-diagonal-tensor-colimit-hom-ext vs def-sfb-modobj-extend-restrict-adjunction: the existing statement concerns Extension of scalars is left adjoint to restriction; the new statement is equality detection for arbitrary maps from A tensor A in any monoidal category, under only common successors and the two specified image-colimit hypotheses.

lem-sfb-diagonal-tensor-colimit-hom-ext vs def-sfb-modobj-extension: the existing statement concerns Extension of scalars; the new statement is equality detection for arbitrary maps from A tensor A in any monoidal category, under only common successors and the two specified image-colimit hypotheses.

lem-sfb-diagonal-tensor-colimit-hom-ext vs def-sfb-monoidal-category: defines the tensor bifunctor and coherence data; it does not give equality detection on colimit tensor squares.

lem-sfb-diagonal-tensor-colimit-hom-ext vs def-sfb-strong-monoidal-functor: the existing statement concerns Strong monoidal functors and their structure maps; the new statement is equality detection for arbitrary maps from A tensor A in any monoidal category, under only common successors and the two specified image-colimit hypotheses.

lem-sfb-diagonal-tensor-colimit-hom-ext vs lem-sfb-filtered-ring-object-cocone-colimit: the item concludes a ring-object colimit and its commutative restriction; the new node only detects equality for arbitrary tensor-square maps, without any ring structure.

lem-sfb-diagonal-tensor-colimit-hom-ext vs lem-sfb-regular-scalar-extension-multiplication: the existing statement concerns Normalized scalar extension of regular sheaf modules and multiplication; the new statement is equality detection for arbitrary maps from A tensor A in any monoidal category, under only common successors and the two specified image-colimit hypotheses.

lem-sfb-diagonal-tensor-colimit-hom-ext vs lem-sfb-scalar-unit-equality-detection: the existing statement concerns An adjunction unit telescope detects equality at a scalar power; the new statement is equality detection for arbitrary maps from A tensor A in any monoidal category, under only common successors and the two specified image-colimit hypotheses.

lem-sfb-diagonal-tensor-colimit-hom-ext vs lem-sfb-symmetric-bimod-tensor: the existing statement concerns Tensor products of symmetric bimodules are symmetric; the new statement is equality detection for arbitrary maps from A tensor A in any monoidal category, under only common successors and the two specified image-colimit hypotheses.

lem-sfb-diagonal-tensor-colimit-hom-ext vs def-weil-pbc-category-colimit: defines a colimit and filteredness; the new node combines two preserved colimits with diagonal-to-mixed factorization.

lem-sfb-diagonal-tensor-colimit-hom-ext vs def-weil-pbc-filtered-colimit-smooth-algebras: the existing statement concerns Filtered colimit of smooth algebras ('PT holds'); the new statement is equality detection for arbitrary maps from A tensor A in any monoidal category, under only common successors and the two specified image-colimit hypotheses.

lem-sfb-diagonal-tensor-colimit-hom-ext vs lem-weil-pbc-algebra-colimit-fp-algebras-over-it: the existing statement concerns An algebra is the filtered colimit of the finitely presented algebras mapping to it (Stacks 0BUF); the new statement is equality detection for arbitrary maps from A tensor A in any monoidal category, under only common successors and the two specified image-colimit hypotheses.

lem-sfb-diagonal-tensor-colimit-hom-ext vs lem-weil-pbc-filtered-colimit-sets-elementwise: the existing statement concerns Elements of a filtered colimit of sets; the new statement is equality detection for arbitrary maps from A tensor A in any monoidal category, under only common successors and the two specified image-colimit hypotheses.

lem-sfb-diagonal-tensor-colimit-hom-ext vs lem-weil-pbc-integral-morphism-limit-of-finite: the existing statement concerns An integral morphism to a quasi-compact quasi-separated scheme is a limit of finite morphisms; the new statement is equality detection for arbitrary maps from A tensor A in any monoidal category, under only common successors and the two specified image-colimit hypotheses.

lem-sfb-diagonal-tensor-colimit-hom-ext vs lem-weil-pbc-popescu-product: the existing statement concerns Filtered colimits of smooth algebras and products; the new statement is equality detection for arbitrary maps from A tensor A in any monoidal category, under only common successors and the two specified image-colimit hypotheses.

lem-sfb-diagonal-tensor-colimit-hom-ext vs lem-weil-pbc-proetale-wcontractible-affine-evaluation-colimits: the existing statement concerns Exact colimit-preserving evaluation at an affine weakly contractible object; the new statement is equality detection for arbitrary maps from A tensor A in any monoidal category, under only common successors and the two specified image-colimit hypotheses.

lem-sfb-diagonal-tensor-colimit-hom-ext vs lem-weil-pbc-site-plus-construction-presheaf: the existing statement concerns The plus construction is a presheaf, and its elements and equalities are described by refinements; the new statement is equality detection for arbitrary maps from A tensor A in any monoidal category, under only common successors and the two specified image-colimit hypotheses.

lem-sfb-diagonal-tensor-colimit-hom-ext vs lem-a1-sections-intersection-structure-colimit: the existing statement concerns Structure-sheaf sections on an intersection are a filtered colimit; the new statement is equality detection for arbitrary maps from A tensor A in any monoidal category, under only common successors and the two specified image-colimit hypotheses.

lem-sfb-diagonal-tensor-colimit-hom-ext vs def-coef-bounded-filtered-subcategory-system: the existing statement concerns The bounded non-full filtered subcategory system and its canonical colimit diagram; the new statement is equality detection for arbitrary maps from A tensor A in any monoidal category, under only common successors and the two specified image-colimit hypotheses.

lem-sfb-diagonal-tensor-colimit-hom-ext vs lem-coef-accessible-small-object-factorization: the existing statement concerns Accessible small-object factorizations; the new statement is equality detection for arbitrary maps from A tensor A in any monoidal category, under only common successors and the two specified image-colimit hypotheses.

lem-sfb-diagonal-tensor-colimit-hom-ext vs lem-coef-associative-word-filtration: the existing statement concerns Tensor-word monad and free associative algebra pushout filtration; the new statement is equality detection for arbitrary maps from A tensor A in any monoidal category, under only common successors and the two specified image-colimit hypotheses.

lem-sfb-diagonal-tensor-colimit-hom-ext vs lem-coef-cellular-tree-presentable-approximations: the existing statement concerns Presentable approximations of a fixed cellular tree with compatible supports; the new statement is equality detection for arbitrary maps from A tensor A in any monoidal category, under only common successors and the two specified image-colimit hypotheses.

lem-sfb-diagonal-tensor-colimit-hom-ext vs lem-coef-combinatorial-injective-diagram-model: the existing statement concerns Injective model structures for ordinary small diagrams; the new statement is equality detection for arbitrary maps from A tensor A in any monoidal category, under only common successors and the two specified image-colimit hypotheses.

lem-sfb-diagonal-tensor-colimit-hom-ext vs lem-coef-direct-wfs-extension: the existing statement concerns Weak factorization systems on finite direct diagrams; the new statement is equality detection for arbitrary maps from A tensor A in any monoidal category, under only common successors and the two specified image-colimit hypotheses.

lem-sfb-diagonal-tensor-colimit-hom-ext vs lem-coef-filtered-colimit-cardinal-regrouping: the existing statement concerns Regrouping filtered colimits by bounded filtered subcategories; the new statement is equality detection for arbitrary maps from A tensor A in any monoidal category, under only common successors and the two specified image-colimit hypotheses.

lem-sfb-diagonal-tensor-colimit-hom-ext vs lem-coef-functor-coend-homotopy-prism: the existing statement concerns Prism for coends of simplicial functors; the new statement is equality detection for arbitrary maps from A tensor A in any monoidal category, under only common successors and the two specified image-colimit hypotheses.

lem-sfb-diagonal-tensor-colimit-hom-ext vs lem-coef-ordinal-latching-diagram-lifting: the existing statement concerns Relative latching maps give lifts of arbitrary ordinal diagrams; the new statement is equality detection for arbitrary maps from A tensor A in any monoidal category, under only common successors and the two specified image-colimit hypotheses.

lem-sfb-diagonal-tensor-colimit-hom-ext vs lem-coef-ordinary-directed-cover-colimit: the existing statement concerns Ordinary colimits assembled over a directed cover of the index category; the new statement is equality detection for arbitrary maps from A tensor A in any monoidal category, under only common successors and the two specified image-colimit hypotheses.

lem-sfb-diagonal-tensor-colimit-hom-ext vs lem-coef-presentable-presentation-comparison: the existing statement concerns Comparison of large filtered presentations on small filtered subdiagrams; the new statement is equality detection for arbitrary maps from A tensor A in any monoidal category, under only common successors and the two specified image-colimit hypotheses.

lem-sfb-diagonal-tensor-colimit-hom-ext vs lem-coef-reedy-colimit-comparison: the existing statement concerns Reedy-colimit comparison for cofibrant diagrams; the new statement is equality detection for arbitrary maps from A tensor A in any monoidal category, under only common successors and the two specified image-colimit hypotheses.

lem-sfb-diagonal-tensor-colimit-hom-ext vs lem-coef-reedy-model-structure: the existing statement concerns Reedy diagram model structures and degreewise extensions; the new statement is equality detection for arbitrary maps from A tensor A in any monoidal category, under only common successors and the two specified image-colimit hypotheses.

lem-sfb-diagonal-tensor-colimit-hom-ext vs lem-coef-scat-uniform-presentability: the existing statement concerns Uniform presentability and bounded representatives for simplicial-category diagrams; the new statement is equality detection for arbitrary maps from A tensor A in any monoidal category, under only common successors and the two specified image-colimit hypotheses.

lem-sfb-diagonal-tensor-colimit-hom-ext vs lem-coef-simplicial-bar-latching-decomposition: the existing statement concerns Nondegenerate-chain decomposition of the bar latching object; the new statement is equality detection for arbitrary maps from A tensor A in any monoidal category, under only common successors and the two specified image-colimit hypotheses.

lem-sfb-diagonal-tensor-colimit-hom-ext vs lem-coef-simplicial-category-degreewise-colimits: the existing statement concerns Colimits of simplicial categories computed as ordinary categories in each degree; the new statement is equality detection for arbitrary maps from A tensor A in any monoidal category, under only common successors and the two specified image-colimit hypotheses.

lem-sfb-diagonal-tensor-colimit-hom-ext vs lem-coef-simplicial-latching-degenerate-subset: the existing statement concerns Simplicial latching colimits identify naturally with degenerate subsets; the new statement is equality detection for arbitrary maps from A tensor A in any monoidal category, under only common successors and the two specified image-colimit hypotheses.

lem-sfb-diagonal-tensor-colimit-hom-ext vs lem-coef-small-direct-colimit-lifting: the existing statement concerns Relative left lifting maps over small direct categories induce left lifting colimit maps; the new statement is equality detection for arbitrary maps from A tensor A in any monoidal category, under only common successors and the two specified image-colimit hypotheses.

lem-sfb-diagonal-tensor-colimit-hom-ext vs lem-coef-small-right-lifting-accessibility: the existing statement concerns Accessibility of a small right lifting class; the new statement is equality detection for arbitrary maps from A tensor A in any monoidal category, under only common successors and the two specified image-colimit hypotheses.

lem-sfb-diagonal-tensor-colimit-hom-ext vs lem-coef-split-functor-coend-filtration: the existing statement concerns Relative skeletal filtration for split functors; the new statement is equality detection for arbitrary maps from A tensor A in any monoidal category, under only common successors and the two specified image-colimit hypotheses.

lem-sfb-diagonal-tensor-colimit-hom-ext vs lem-coef-sset-gluing-filtered-equivalences: the existing statement concerns Gluing and filtered-colimit stability for simplicial weak equivalences; the new statement is equality detection for arbitrary maps from A tensor A in any monoidal category, under only common successors and the two specified image-colimit hypotheses.

lem-sfb-diagonal-tensor-colimit-hom-ext vs lem-coef-truncated-coend-skeleton-image: the existing statement concerns Truncated simplex coend embeds as the skeleton; the new statement is equality detection for arbitrary maps from A tensor A in any monoidal category, under only common successors and the two specified image-colimit hypotheses.

lem-sfb-diagonal-tensor-colimit-hom-ext vs det-ind-heart-extensions: the existing statement concerns Ind-constructible sheaves are closed under extensions; the new statement is equality detection for arbitrary maps from A tensor A in any monoidal category, under only common successors and the two specified image-colimit hypotheses.

lem-sfb-diagonal-tensor-colimit-hom-ext vs det-ind-heart-full-faithfulness: the existing statement concerns Constructible sheaves are finitely presented; full faithfulness; the new statement is equality detection for arbitrary maps from A tensor A in any monoidal category, under only common successors and the two specified image-colimit hypotheses.

lem-sfb-diagonal-tensor-colimit-hom-ext vs det-sf-determination-localizing: the existing statement concerns Invertibility propagates to the localizing closure; the new statement is equality detection for arbitrary maps from A tensor A in any monoidal category, under only common successors and the two specified image-colimit hypotheses.

lem-sfb-diagonal-tensor-colimit-hom-ext vs lem-sfb-finite-colimit-matrix-cokernels: the existing statement concerns Finite-colimit transport of entrywise conjugate matrices and cokernels; the new statement is equality detection for arbitrary maps from A tensor A in any monoidal category, under only common successors and the two specified image-colimit hypotheses.

lem-sfb-diagonal-tensor-colimit-hom-ext vs lem-sfb-internal-scalar-extension-finite-presentation: the existing statement concerns Scalar extension preserves finite presentations of internal module objects; the new statement is equality detection for arbitrary maps from A tensor A in any monoidal category, under only common successors and the two specified image-colimit hypotheses.

lem-sfb-diagonal-tensor-colimit-hom-ext vs lem-sfb-monoidal-balancing-diagrams: the existing statement concerns Strong monoidal transport of balancing and quotient-action diagrams; the new statement is equality detection for arbitrary maps from A tensor A in any monoidal category, under only common successors and the two specified image-colimit hypotheses.

lem-sfb-diagonal-tensor-colimit-hom-ext vs lem-sfb-subobject-inclusion-cokernel: the existing statement concerns Cokernel of an inclusion between represented subobjects; the new statement is equality detection for arbitrary maps from A tensor A in any monoidal category, under only common successors and the two specified image-colimit hypotheses.

lem-sfb-diagonal-tensor-colimit-hom-ext vs def-weil-directed-colimit-abelian-groups: the existing statement concerns Directed colimit of a directed system of abelian groups; the new statement is equality detection for arbitrary maps from A tensor A in any monoidal category, under only common successors and the two specified image-colimit hypotheses.

lem-sfb-diagonal-tensor-colimit-hom-ext vs lem-fix-closed-evaluation-dual-criterion: the existing statement concerns Evaluation-isomorphism criterion for a dual pair in a closed monoidal category; the new statement is equality detection for arbitrary maps from A tensor A in any monoidal category, under only common successors and the two specified image-colimit hypotheses.

lem-sfb-diagonal-tensor-colimit-hom-ext vs lem-kun-colim-gbl-gen: the existing statement concerns Filtered colimits of globally generated sheaves; the new statement is equality detection for arbitrary maps from A tensor A in any monoidal category, under only common successors and the two specified image-colimit hypotheses.

lem-sfb-diagonal-tensor-colimit-hom-ext vs lem-kun-colim-of-localizations: the existing statement concerns Colimit of localizations; the new statement is equality detection for arbitrary maps from A tensor A in any monoidal category, under only common successors and the two specified image-colimit hypotheses.

lem-sfb-diagonal-tensor-colimit-hom-ext vs lem-kun-functor-preserves-hocolim: the existing statement concerns Exact coproduct-preserving functors preserve telescopes; the new statement is equality detection for arbitrary maps from A tensor A in any monoidal category, under only common successors and the two specified image-colimit hypotheses.

lem-sfb-diagonal-tensor-colimit-hom-ext vs lem-pur-adjoint-left-projection-action: the existing statement concerns Left-coefficient counit projection: transpose, unit and associativity; the new statement is equality detection for arbitrary maps from A tensor A in any monoidal category, under only common successors and the two specified image-colimit hypotheses.

lem-sfb-diagonal-tensor-colimit-hom-ext vs lem-pur-composite-relative-tensor-action: the existing statement concerns Composition preserves relative tensor-action identities; the new statement is equality detection for arbitrary maps from A tensor A in any monoidal category, under only common successors and the two specified image-colimit hypotheses.

lem-sfb-diagonal-tensor-colimit-hom-ext vs lem-pur-open-left-projection-action: the existing statement concerns Left-coefficient action laws from normalized open restriction; the new statement is equality detection for arbitrary maps from A tensor A in any monoidal category, under only common successors and the two specified image-colimit hypotheses.

lem-sfb-diagonal-tensor-colimit-hom-ext vs lem-pur-tensor-action-trace-contraction: the existing statement concerns Contraction of two trace maps through tensor actions; the new statement is equality detection for arbitrary maps from A tensor A in any monoidal category, under only common successors and the two specified image-colimit hypotheses.

lem-sfb-diagonal-tensor-colimit-hom-ext vs lem-trf-henselization-prime-ind-etale: the existing statement concerns An ordinary henselization at a prime is ind-etale over the original ring; the new statement is equality detection for arbitrary maps from A tensor A in any monoidal category, under only common successors and the two specified image-colimit hypotheses.

lem-sfb-diagonal-tensor-colimit-hom-ext vs lem-trf-module-directed-colimit-fp: the existing statement concerns Every module is a small directed colimit of finitely presented modules; the new statement is equality detection for arbitrary maps from A tensor A in any monoidal category, under only common successors and the two specified image-colimit hypotheses.

lem-sfb-diagonal-tensor-colimit-hom-ext vs lem-trf-point-system-refine: the existing statement concerns One-cover refinement of a pointed inverse system; the new statement is equality detection for arbitrary maps from A tensor A in any monoidal category, under only common successors and the two specified image-colimit hypotheses.

Additional likely tensor-colimit comparisons: lem-weil-pbc-tensor-commutes-with-colimits treats modules over one commutative ring and tensoring with a fixed module; lem-weil-pbc-independent-sheaf-tensor-colimits treats sheaf modules; lem-weil-pbc-directed-tensor-cocones-colimit-n3 treats coherent diagrams of commutative rings built by scalar extension. None covers arbitrary monoidal C or diagonal equality detection under common successors without parallel-arrow equalization.

## Repair of A7/B10: renewed instruction after the closure return

The returned delivery was mathematically accepted but rejected as superseded. I independently reread the live node and the whole module Sheaf.CategoryTheory.FilteredRingObjectCoconeColimit. The live seven-step split is reviewed by NC, the Lean statements by Q107, and reviewed_proof records E4 landing 20261021T061032-L-1687556 with sorry_after []. Both the Mon and CommMon theorems have complete proofs; hdiag, hmixed and the two successive hom_ext applications are inline. Nothing in this delivery disputes or reopens that Lean result. I compared every live metadata field with the sandbox: only proof, proof_deps, proof_origin and split_report differ. The exact statement, Lean binding and all three review records are retained from the current repository.

The earlier generic note predating the E4 landing did not establish a post-closure instruction; the return correctly identified that chronology. This repair relies instead on the current task message, which quotes that very return and then expressly reissues the route instruction: "The node is already split once and stated in Lean; that the live item is already split and reviewed is exactly why it is back: this is a deliberate re-split, not a stale assignment. Deliver it as a stage-1 repair of the existing node with the new statement-only nodes." This instruction is received after the quoted return and expressly addresses its supersession reason. It is the task-specific exception to brief-stage1 l.103, not a claim that HUMAN.md contains a new entry. I have no authority to edit HUMAN.md, retire dispatcher entries, or alter the launcher and have done none of those things.

The repair therefore records this renewed authorization in both this report and split_report.summary. It does not rename the extracted lemma again or pretend to repair sound mathematics. The old argument is retained in the five-step assembly and the independent statement-only equality-detection lemma. The new lemma remains unsplit for a future worker; the already completed Lean module remains available to that worker as a read-only reference.

### Review by NI of the repair

I checked the current blueprint chapter and unit and its Third isomorphism paragraph again, and reread Stacks categories.tex at definition-colimit (002F), definition-directed (002V), and definition-monoidal-category (0FFK). Each original argument is accounted for in the coverage section above. Steps 1-3 and 5 are the unchanged mediator, unit, diagonal multiplication, and uniqueness/full-subcategory arguments. Step 4 uses the extracted statement with its two image cocones supplied respectively by D(i) tensor - and - tensor A. All indices are small; nonemptiness and common successors come from filteredness. I reread the three existing cited definition statements and the new lemma and verified every quote in citations.json as a literal substring. The new statement and the preserved searches have not changed; I read searches.jsonl and the Mathlib candidate source instead of rerunning unchanged questions. Singleton and non-sifted group-action cases still check. The item proof is below 3000 characters, with no individual step above 2000. No statement dispute, missing hypothesis or source-route change was introduced. The initial retained-version dry run exited successfully with OK (not pushed); the repaired report and authorization metadata require a fresh dry run before delivery.
