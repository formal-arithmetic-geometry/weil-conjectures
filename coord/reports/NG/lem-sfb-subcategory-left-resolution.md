## Worker report

Files written:
- `dag/nodes/sec-proetale-coefficients/lem-sfb-subcategory-left-resolution.json`: statement, split; seven-step proof, no Mathlib match.
- `citations.json`: verbatim statement excerpts for every step/dependency pair, including both clauses (a) and (c) used in step 6.

Attachments: none. No project declaration states every clause under the item's hypotheses.

WANTED: none.

The imported statement is correct and unchanged. The missing proof is now the descending-induction construction of Stacks Tag 05T7(1), with the sentence “The reader easily checks that IH_(n-1) holds” expanded into the two epimorphism checks and the cohomology isomorphism check. No unfinished portion remains in this one-level split.

## New nodes

None: zero new nodes, zero new Mathlib leaves. The existing leaf `lem-sp-abelian-refinements` is sufficient for all the non-elementary lifting facts. The kernel construction of a pullback and the verification of the complex equations remain elementary proof steps.

## Sources and searches

Read `literature/stacks-project/derived.tex`, lemma-subcategory-left-resolution, Tag 05T7, statement (1) and the complete proof of (1). Read `literature/stacks-project/homology.tex`, lemma-epimorphism-universal-abelian-category (05PK) and lemma-check-exactness-fibre-product (08N5), to check the abelian-category lifting rules. Read the entire statement of each of `def-sp-abelian`, `def-weil-abstract-derived-category`, and `lem-sp-abelian-refinements`. The last node supplies exactly the lifting-up-to-epimorphic-refinement criterion and the cokernel-zero criterion; its Mathlib source `CategoryTheory/Abelian/Refinements.lean` was also opened, including those declarations.

Searched all DAG records for 05T7, 05T6, the left-resolution label, covering classes, pullback epimorphisms and refinement statements; searched the blueprint using `blueprint_refs.py search` for resolution, pullback, refinement, epimorphic refinement, bounded-above resolutions, quotient-generating and subcategory-left-resolution. Ran the ancestor command. The resulting ancestor is `sk-def-sfb-derived-categories`; the existing `from.place` and `via` already describe this bounded-above ingredient of the K-flat-resolution route and are retained. No blueprint node states the same arbitrary-class bounded-above lemma.

The neighboring `lem-sfb-functorial-bounded-above-class-resolution` assumes a functorial cover and closure under finite biproducts and direct summands. These hypotheses are absent here. The existing truncation-resolution-system node cites this item and cannot be used without a cycle. The right-resolution-05T6 node is the dual theorem; it is not used to replace the source's direct induction.

Searched `/home/ubuntu/weil-src-slopmaster2/WeilConjectures/` for the exact id, the docstring tag, left-resolution/subcategory/quotient-generating vocabulary, and upstream name metadata. Opened the source's `FromJoel/Algebra/Homology/LeftResolution/Basic.lean` and `CochainComplexMinus.lean`. The latter constructs functorial bounded-above resolutions from a LeftResolution datum, requires a full faithful additive source with finite coproducts, and does not give arbitrary nonfunctorial covering classes or the stated termwise epimorphisms. It is not an attachment for this item.

Retained all inherited Mathlib search records, including their corrections of invalid queries/directories. New msearch calls and actual results are in `searches.jsonl` and appended to the item. Two semantic phrasings, Loogle, LeanSearch and grep were run. Read Mathlib `Algebra/Homology/LeftResolution/Basic.lean` lines 15--65, `Factorizations/CM5b.lean` (enough-injectives bounded-below hypotheses), `DerivedCategory/Fractions.lean` lines 69--108, and the projective resolution construction near lines 280--325. The hits either prescribe projective/injective classes, resolve a single object, require functorial cover data, or represent derived-category morphisms without prescribing replacement terms. None is an exact or one-line match. No searches are claimed beyond the inherited records and actual calls.

## Not duplicates

No new nodes were created, so there are no new/existing node pairs to compare.

## Review by NG

I read Tag 05T7(1) against the unchanged item, hypothesis by hypothesis. Both assume an arbitrary abelian category, a class containing a zero object and admitting epimorphic covers of every object, a fixed integer upper bound, and actual vanishing of terms above that bound. Both conclude a termwise epimorphic quasi-isomorphism with terms in that class and the same strict bound. No projectivity, functorial cover, closure under sums, enough injectives, or Grothendieck hypothesis has been introduced. I also read the chapter and current unit records: this proves the bounded-above stage of the existing K-flat-resolution route, without changing the unit or chapter.

Step 1 uses the abelian-category definition and the complex/cohomology definition to state the full descending induction invariant, including the cycle epimorphism at the lower endpoint. The starting stage is a+1, not a; the zero-object hypothesis and the actual termwise upper bound verify every base condition. No induction conclusion is assumed at the starting degree.

Step 2 uses exactly the kernels and finite biproducts stated in `def-sp-abelian`, and the differentials/chain-map conditions of `def-weil-abstract-derived-category`. I checked the pullback base is Z^n(K), with maps the differential from K^(n-1) and the already epic cycle map from Z^n(P). Its explicit kernel formula supplies existence and its projections; the chain-map and square-zero equalities are written out. Choosing an epimorphism onto this kernel is precisely the item's covering assumption, with no lift from projectivity. This is a construction from definitions, not an unnamed resolution lemma.

Step 3 cites `lem-sp-abelian-refinements` clause (a), which really asserts lifting of every morphism into the target after precomposition by an epimorphism. It is applied first to the induction hypothesis's cycle map, then to the newly chosen covering q. The displayed pair obeys the kernel equation, so the resulting first component proves the new component is epic by the same criterion. Composition of epis follows directly by right cancellation.

Step 4 again uses clause (a), now on q and the pair (cycle,0). The second component being zero forces the lift to be a cycle, by the defining formula for the new differential; cancelling the cycle inclusion gives the required cycle-map equation. This verifies the next invariant rather than merely asserting it follows from an arbitrary surjection of complexes (which would be false).

Step 5 uses the cohomology quotient of `def-weil-abstract-derived-category` and clause (a) of the refinement leaf twice, first for the quotient onto H^n(K) and then for the old cycle epimorphism. This proves epimorphy of the new cohomology map. The quotient is a cokernel and hence epic; that is part of the abelian-category quotient construction.

Step 6 uses clause (a) to represent an arbitrary kernel element of the cohomology map by a cycle, and clause (c) to replace its image by a boundary after an epimorphic refinement. Clause (c) explicitly concerns an arbitrary cokernel; H^n(K) is the cokernel of K^(n-1) -> Z^n(K), so all its hypotheses hold. The compatible pair (boundary preimage, cycle) belongs to T_n; lifting through q makes this cycle a boundary in P. Cancelling the composite epic refinement proves the original element was zero. Applying this to differences proves monicity. I made the final mono-plus-epi argument explicit using the definition that an epi is a cokernel: its cokernel witness is zero by monicity, and a cokernel of zero is invertible by its universal property. Thus no uncited five-lemma or hidden comparison theorem is used.

Step 7 closes the successor invariant and performs ordinary recursion indexed by nonnegative integers. For a fixed degree j, the lower endpoint j-1 already determines both adjacent differentials and the degree-j cohomology map. Later choices do not change those data; this is why no infinite-limit exactness theorem is needed. The zero terms above a give the remaining quasi-isomorphism degrees. The three cited node statements supply all definitions used here.

I checked B--E explicitly: statements are self-contained with their definition nodes, old fields and searches retained, sources use Stacks tags and labels, no new statement-only lemma or duplicate is needed, all uses are in proof_deps, and the split carries the actual argument rather than delegating its conclusion. Citations were copied verbatim from the existing node statements. None of the proof steps exceeds 2000 characters. In particular the injection calculation of step 6 is one diagram chase with the same induction-stage pullback, not an independent comparison lemma. The non-elementary refinement steps are marked non-elementary; only setup, kernel construction, and the recursion/retention of fixed data are elementary.

Small-case checks: K=0 works even if the chosen covers of zero are nonzero, because the next stages kill the extra cohomology. At the first new degree n-1=a, T_n=K^a and the construction chooses an arbitrary cover of K^a. For a complex concentrated in degree a, the next T is the kernel of that cover, so the process gives the expected successive kernel covers. There is no assumption that arbitrary epimorphisms split, and all element arguments allow epimorphic refinement rather than claiming an ordinary Hom-set lift. Negative a and unboundedness below only change the recursion's integer indexing. The class need contain just the chosen zero object; no isomorphism-closure or closure under finite biproducts was used.

No source error or statement dispute was found. I expanded the source's omitted invariant check and made the categorical element arguments explicit. This is my direct-delivery review; the maintainer's independent review remains the next content check.
