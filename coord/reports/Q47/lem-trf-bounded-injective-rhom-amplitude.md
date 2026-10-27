# Q47: lem-trf-bounded-injective-rhom-amplitude

## Files written

- dag/nodes/sec-trace-formula/lem-trf-bounded-injective-rhom-amplitude.json: existing statement, now split in five steps; not a Mathlib leaf. Statement, statement dependencies and inherited blueprint ancestry are unchanged.
- citations.json: eight exact statement excerpts covering every use in every proof step.
- report.md and searches.jsonl: worker review and actual search record. No new nodes, no new Mathlib leaves, and no unit record changes.

## Attachments

None. Searched the live WeilConjectures source by the exact blueprint id, bounded injective terminology, Hom amplitude and RHom boundedness. The existing RHom stability declarations concern geometric constructible/perfect inputs with stronger hypotheses, not this ordinary-module statement for arbitrary K. Generic Hom-complex construction and K-injective infrastructure are inputs, not an attachment of the whole item. The Sheaf ordinaryModuleDerivedInternalHom abbreviation was also read for the endpoint convention; it is a definition, not a proof of these bounds.

## Literature wanted

None.

## Findings and changes

The item is correct and was unsplit, without a released repair note or prior sandbox split. No statement dispute, correction or route change is needed. The original source references are contextual: more-algebra.tex Tag 0A5S, definition-injective-dimension, supplies the meaning of the bounded injective representative; dualizing.tex Tag 0A7C, lemma-dualizing, explains the surrounding duality application. The actual elementary amplitude argument is written here by the worker, from homology.tex Tag 0118 (section-truncations), derived.tex Tag 070J (lemma-bounded-below-injectives-K-injective), and sites-cohomology.tex Tags 08J7 (section-internal-hom), 0A95 (lemma-RHom-well-defined), and 0A8X (section-hom-complexes). The proof_origin is agent, not a claim that 0A7C states this result without Noetherianity.

No new lemmas are required. In particular, the support calculation is a few lines using the product formula and must not become a new node; neither should either conclusion be moved into a new node. No SGA source is used.

## Search and blueprint check

Read the current chapter and unit records, the latest blueprint proof of lem-trf-local-term-locality, and the inherited ancestry through lem-trf-complete-local-coherent-duality. The parent records this item as its old Step 7 supporting input. The ancestor command confirms lem-trf-local-term-locality. Whole-blueprint searches for truncation, injective, injective-amplitude and bounded injective found no blueprint statement equal to the present general module assertion; same_as remains empty. Whole-DAG statement/title searches found the existing K-injectivity and truncation nodes, and those are reused. There are no proposed new nodes, hence no duplicate pairs to distinguish.

Ran all four required search services for this item and a second semantic phrasing plus a targeted source grep. Every new search entry is copied from the actual searches.jsonl tool/query record, with actual hit summary. All services answered. The hits include CochainComplex.isKInjective_of_injective (Mathlib/Algebra/Homology/HomotopyCategory/KInjective.lean:133), which was read and is already the leaf lem-weil-pbc-bounded-below-injectives-kinjective. The strict model lemmas DerivedCategory.exists_iso_Q_obj_of_isLE and exists_iso_Q_obj_of_isGE were read at DerivedCategory/TStructure.lean:170 and :175; they provide strict models, not the Hom models and two bounds. DerivedCategory.to_singleFunctor_obj_eq_zero_of_injective treats one injective target and a map, not the present full statement. Neither phrasing returned an exact or one-line specialization for the item. Existing historical search entries have been retained.

## Not duplicates

No new nodes.

## Review by Q47

I read delivery-errors B through E in full and checked this split against their examples with the cited node statements open. Each step is under 2000 characters. I retained the original full statement, including both explicit representatives and the isomorphisms in D(R), both termwise bounds and their cohomological consequences, and the uniformity in K and c. There is no proof sketch hidden in a new statement and no clause relabelled as a new dependency.

Step 1 uses exactly the statement of lem-weil-pbc-bounded-below-injectives-kinjective: it applies in any abelian category to a bounded-below termwise injective complex. I checked its Mathlib source and Stacks 070J. The lower bound is a, and every degree, including the zero degrees outside the interval, is injective by the item's hypothesis. No injectivity of a truncation of the source is asserted or needed.

Step 2 uses the upper-truncation cohomology statement of lem-weil-pbc-truncation-cohomology and the explicit good truncations in def-kun-truncations. I read both canonical cochain constructions and cohomology formulas in homology.tex 0118. The upper cut has kernel at c; the lower cut has cokernel of the preceding differential at c, not a stupid truncation. Its cycles at c are exactly ker(d^c)/im(d^{c-1}), with no incoming boundaries. Above c the boundary image is unchanged because the differential factors through the quotient. Below c the hypothesis kills the old cohomology and the new terms are zero. The two quasi-isomorphisms have their correct opposite directions, P to C and C to Q. The definition of the derived category is cited for inverting these maps, and its statement was read. No boundedness on the other end of C is used.

Step 3 uses def-pur-derived-internal-hom's explicit final clause allowing any K-injective representative and any representative of the first variable; it also cites lem-pur-rhom-well-defined's actual invariance theorem, rather than attributing that theorem solely to a definition. I checked sites-cohomology.tex 08J7 and 0A95. K-injectivity was obtained in Step 1 and the representing isomorphisms in Step 2. The trivial one-object site has exactly R-modules as module sheaves, so sheaf Hom and sectionwise products become ordinary Hom and products. This gives an isomorphism in D(R). It does not substitute a per-degree assertion for a derived isomorphism or invoke an identification of unrelated coefficient categories.

Steps 4 and 5 cite def-pur-hom-complex, whose statement explicitly gives the product over all integers p. I read that whole statement and the Stacks Hom-complex convention. For n<a-c, either p>c kills the source or p+n<a kills the target. For n>b-c, either p<c kills the source or p+n>b kills the target. A product with every factor the zero module has just one element, irrespective of the number of factors. Vanishing of its degree-n term forces H^n to vanish by the kernel/image formula; the isomorphism of Step 3 transfers this. These steps really are elementary, using no flatness, finite-generation, exactness of infinite products or spectral sequence. The non-elementary representative and invariance facts are cited separately before them.

I tested the zero ring, J=0, K=0, a=b, c negative, and sources unbounded in the unrestricted direction. The same factor argument works in each case. Over a field, taking K a nonzero vector space in degree c and J a nonzero vector space in degree a=b leaves nonzero Hom precisely in degree a-c. Thus the strict inequality in each conclusion is necessary; the split correctly makes no endpoint vanishing claim. The fixed a,b come solely from J, independently of the chosen source. Every citation quote in citations.json is a literal substring of its node statement; no node's proof or stronger unstated conclusion is used. The only additional off-unit theorem is explicitly declared as a generic tool in split_report.tool_uses. Nothing remains unfinished in the mathematical split.

## Unfinished work

None in scope; stage 1 only. No Lean was written and no compiler, Lake or build command was run.

The first dry run requested longer citation excerpts for Steps 1 and 3; I replaced those short substrings with the full cited statements, including the hypotheses and the Hom-complex map. The mathematics and uses are unchanged.
