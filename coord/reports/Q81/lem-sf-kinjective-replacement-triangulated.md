# Worker report

1. Files written
- dag/nodes/sec-six-functors/lem-sf-kinjective-replacement-triangulated.json: item split; statement preserved.
- dag/nodes/sec-six-functors/lem-sf-shift-stable-right-orthogonal.json: statement, Mathlib leaf at Orthogonal.lean:66, with repleteness and zero instances read.
- dag/nodes/sec-six-functors/lem-sf-triangulated-functor-opposite.json: statement, Mathlib leaf at Opposite/Functor.lean:246, coherent shifts at :41.
- citations.json contains verbatim statement quotes for every proof-step use. searches.jsonl retains the actual msearch queries and results.

2. Attachments
None. The live project proves Full, Faithful, EssSurj and IsEquivalence for HomotopyCategory.KInjectives.Qh at DerivabilityStructureKInjectives.lean:196-225, but these do not state the exactness and opposite clauses. No tagged finished declaration states the complete item. These existing proofs are read as the model for step 2, not claimed as attachment of the whole item.

3. WANTED
None. The Mathlib sources provide the exact generic results used here; the Stacks sources used for the mathematical assembly are present.

4. Findings about the item and brief
The statement is correct, including its weaker hypothesis of resolutions by quasi-isomorphisms without requiring monomorphisms. Upstream HasKInjectiveResolutions additionally asks for monomorphisms; step 2 uses only the hypothesis actually present in the item. No internal-Hom exactness is inferred from this lemma.

The inherited blueprint chain ends in a maintainer-created parent with created.item null. Consequently tools/blueprint_refs.py ancestor prints None, despite the parent's explicit anchor lem-a1-local-boundary-duality. The new nodes retain this computed null ancestor, the full via chain, and a precise textual anchor; no ancestry is fabricated. The item retains its existing blueprint fields and records the relevant exactness sentence of thm-coef-qbar-verdier in split_report.

5. What could not be finished
Nothing mathematical remains in this one-level split. All new nodes are verified Mathlib leaves. No Lean was written or compiled and no repository or launcher file was changed.

## Not duplicates
lem-sf-shift-stable-right-orthogonal vs lem-sf-shift-stable-left-orthogonal: the existing node controls maps X to P; the new node controls maps P to I. Its statement cannot be applied to the right orthogonal without an opposite-category triangulation theorem, so it does not specialize to the new statement directly.
lem-sf-shift-stable-right-orthogonal vs lem-sf-localizing-hom-test: the existing statement detects whether a morphism inside a localizing hull is invertible using Hom from shifted generators; it does not state closure of the right orthogonal of an arbitrary shift-stable class.

The opposite-functor leaf has no matching DAG or blueprint statement. The existing lem-trf-exact-equivalence-inverse is reused rather than recreated. The existing lem-pc-triangulated-equivalence-transfer constructs a new triangulation on a target category; it does not say that a fixed K-injective cone triangulation and derived triangulation agree. The item proves that agreement through its exact localization and exact inverse.

## Review by Q81
I read Stacks derived.tex at definition-K-injective (070H), lemma-K-injective (070I), lemma-enough-K-injectives-implies (070K), lemma-K-injective-defined (070Y), lemma-orthogonal-triangulated (0FXC), and lemma-exact-equivalence (05SQ). The cited 070K and 070Y justify the source intent, but neither alone states exactness of this replacement, so the proof explicitly constructs the equivalence and its coherent shifts. I also read the unit and chapter records and the exactness paragraph in the current available main-20261015 thm-coef-qbar-verdier proof. The inherited unit has no numbered steps and this item is not its key statement; no unit realization record is changed. The proof is marked agent assembly because its inverse and opposite transport uses the read Mathlib implementation alongside Stacks rather than following one continuous Stacks proof.

Step 1 uses the actual statement of lem-pur-homotopy-category-triangulated for both the triangulation of K(A) and exactness of Q. It uses the new right-orthogonal statement, not the left-orthogonal node: H^r(M[n])=H^{r+n}(M) verifies its shift-stability hypothesis. The definition of K-injectivity in the item identifies it with precisely that right orthogonal. def-weil-triangulated-subcategory explicitly supplies the inherited triangulation and exact inclusion; it is not merely a predicate definition. I read Mathlib Orthogonal.lean:40-68, ObjectProperty/Orthogonal.lean:35-64 and HomotopyCategory/KInjective.lean:42-96. The new generic node's right-orthogonal result and repleteness/zero clauses are exactly those instances. Empty P gives the whole category; P equal to all objects gives the zero objects; neither requires size restrictions. No saturation claim is added.

Step 2 cites lem-sc-kinjective-quasi-iso-comparison, whose statement supplies the precise localization Hom bijection for arbitrary homotopy-domain and K-injective target. The chosen I,J satisfy these hypotheses. I read DerivedCategory/KInjective.lean:41-46 and the project Qh Full/Faithful proofs. The existing localization-essential-surjectivity node supplies a representing complex (a homotopy-category object is represented by a complex); a hypothesized quasi-isomorphism to I becomes invertible under Q by def-weil-abstract-derived-category. The fully-faithful-essential-surjectivity node then supplies an equivalence in a common larger universe. It needs no boundedness or Grothendieck hypothesis. All three cited result nodes are already Mathlib leaves.

Step 3 uses the two exact functors supplied in step 1 and writes out why their composite is exact. I read lem-trf-exact-equivalence-inverse: its statement requires compatible shift comparisons on the equivalence inverse, so I do not silently assume these exist. The step gives the lift through fully faithful q and explains checking naturality, zero/addition equations, and unit compatibility. I checked this against Mathlib Shift/Adjunction.lean:600-614 and Triangulated/Adjunction.lean:184-205. Applying that cited node then proves inverse exactness. Composing with the exact inclusion gives R. This works for any chosen inverse and even for the zero abelian category. No new node is made for composing exact functors: the two-line triangle and coherence check is written in the step.

Step 4 uses exactly the new opposite-functor statement after step 3 has established its coherent shifts and exactness hypotheses. I read Opposite/Basic.lean:14-26,61-64, Opposite/Pretriangulated.lean:59-79,168-196, and Opposite/Functor.lean:35-44,240-251. The new statement uses shift by -n on underlying objects and the reversed triangle without introducing an extra sign, matching these sources. Its generic assumptions do not contain K-injectives, enough resolutions or the item's equivalence, so it is a genuine tool rather than a repackaged clause of the item. It is a Mathlib leaf, with the declaration and line for both shift and triangle assertions.

Step 5 is a definitional identification: I read upstream DerivabilityStructureKInjectives.lean:167-225 and BifunctorHom.lean:94-98. They use exactly the right-orthogonal full subcategory, Qh as inclusion followed by localization, and its chosen inv followed by the inclusion. I assert exactness only of that replacement factor and its opposite, without adding any claim about the Hom bifunctor.

Against B-E: all new statements introduce their objects and spell out the orthogonal/opposite notions; they have empty proofs and proof dependencies. I searched the whole DAG by tags, statements and declaration names and the blueprint by K-injective, orthogonal, right orthogonal, exact equivalence, quasi-inverse and opposite functor. Actual msearch results are retained; the inverse-result hit is reused as the existing leaf. Every proof use is a node statement read here and quoted verbatim in citations.json. All non-elementary facts used have nodes; the remaining composition and identification arguments are written explicitly. There is no cycle through the parent, no new K-injective resolution-existence hypothesis, and no new node restating the item. Every proof step is shorter than 2000 characters. This is my self-review; the maintainer supplies the independent reading.

Validation: the first server dry run passed. A final line-number read corrected the right-orthogonal repleteness and zero-instance citations to ObjectProperty/Orthogonal.lean:53 and :63. The second phrasing of the whole-item semantic search is recorded as run; it again returned generic infrastructure, not the complete item.
