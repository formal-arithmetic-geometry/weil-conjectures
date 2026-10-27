## Worker report

Files written:
- dag/nodes/sec-six-functors-basics/lem-sfb-first-quadrant-product-hull-total.json — existing item, split, no Mathlib match; statement and statement dependencies preserved.
- citations.json — 11 verbatim statement excerpts, one for each citation in each step.
- searches.jsonl — six actual msearch runs, retained with their results in the item's mathlib_searches.

Attachments: none. Searches for the exact blueprint tag and for first-quadrant, column-total, product-hull and Roos notions in lean/WeilConjectures found no declaration proving this full closure statement. RoosSplitComparison.lean proves a useful general cone comparison but not this assertion; no claim of attachment is made.

WANTED: none. The source documents needed for this elementary assembly are present.

The imported item had no proof. Its proposed finite-column quotient route is sound. I kept the hypotheses verbatim, in particular the assumption that termwise products with their projections represent derived products. I did not replace this by exactness of products or assume enough injectives. The finite-column prefixes are QUOTIENTS, not subcomplexes: horizontal differentials leave the prefix. Sections of their transitions exist only degreewise and are never used as chain maps.

The blueprint provenance is contextual: the latest det-sf-comp-coherence-cocycle proof has a paragraph called “Refinement isomorphisms”, but no first-quadrant reconstruction proof. The inherited from.place mentions reconstruction in refinement (2), reflecting the long extraction chain. The item's explicit source also points to supported-hull-proetale-descent steps 8–9; I read those as motivation, not as an extra theorem. The proof_origin honestly records an agent assembly of Stacks 012Z and the split Roos construction of 070M, using the actual general triangle theorem of 0152. This neither changes the unit's compactification route nor uses an SGA source.

Nothing remains unfinished for this level of the split.

## New nodes

None: 0 new nodes and 0 Mathlib leaves. The finite-column induction, product map, recursive graded section, and stabilized kernel argument are the proof of the item itself. They introduce no new black boxes.

## Searches and reuse

Whole-DAG searches included finite-column, column filtration, degreewise split, short exact distinguished triangles, and Roos; source-tag searches included 012Z, 0152 and 070M. The exact general complex short-exact triangle already exists as lem-weil-pbc-complex-ses-triangle. I opened its statement and source, and reuse it twice. The existing lem-weil-roos-split-comparison gives a kernel-to-signed-cone quasi-isomorphism for arbitrary degreewise split towers; the item instead writes the elementary stabilized kernel argument and uses the already-existing triangle theorem, so no duplicate Roos node was made.

Whole imported-blueprint searches with tools/blueprint_refs.py used “first quadrant”, “column”, “total complex”, “Roos”, and “product-closed”. None states the item; def-sp-double-complex-total gives exactly the needed filtration. The ancestor command gives det-sf-comp-coherence-cocycle, matching the inherited from.node and via list. I read the latest blueprint file, not the old snapshot path appearing in historical metadata.

The six new msearch queries are recorded exactly as run. Both semantic phrasings were read: the first returned t-structures, iterated functors and products of triangles; the second returned fractions, degreewise split triangles, cones and DerivedCategory.triangleOfSESδ. LeanSearch returned triangulated object properties, countable AB4* and product triangles. Loogle returned binary-product triangles. The two grep searches found no totalization closure theorem, only finite extension iteration and stability of morphism classes under finite products. I read Mathlib/CategoryTheory/Triangulated/Subcategory.lean, including the defining class and closure instances at 182–191 and the finite results at 422 and 677, and DerivedCategory/ShortExact.lean. None is the item or a one-line specialization. The short-exact triangle hits support the existing cited node rather than a new one. Older searches already on the live item are retained verbatim.

## Not duplicates

No new-node pairs require distinction: there are no new nodes.

## Review by NI

I read Stacks homology.tex, definition-associated-simple-complex (012Z), including its commuting-square convention and the sign d_I+(-1)^p d_II. I read derived.tex, lemma-derived-canonical-delta-functor (0152), and lemma-difficulty-K-injectives (070M), specifically its displayed termwise split product sequence. I checked all three labels in literature/stacks-project/tags/tags. I use only the split-sequence argument from the proof of 070M, which I spell out without its enough-injectives or K-injective assertions; proof_origin is agent, not a claim that 070M's statement applies to the present category. There are no new-node sources to review.

Step 1 cites def-sp-double-complex-total. Its statement explicitly supplies the decreasing first filtration by subcomplexes and finite diagonals. Taking its quotient gives the displayed prefix terms and projected differential. I checked that F^n is stable, whereas the prefixes themselves are not stable. The cutoff n >= r+1 is correct, including r=0 and n=0.

Step 2 cites def-weil-abstract-derived-category for the shift convention, lem-weil-pbc-complex-ses-triangle for a triangle from every degreewise short exact sequence, and def-weil-triangulated-subcategory for shift and extension closure. I opened all three statements: the triangle node applies to arbitrary cochain complexes in an abelian category, not only objects concentrated in degree zero and not only injective complexes. Its hypotheses require exactly what is available. The n-th kernel has term D^{n,r-n} and differential (-1)^n d_II, which is precisely column n shifted by -n. The induction starts at B_0=0 and proves all B_n without truncation closure.

Step 3 cites def-weil-category-product for existence and uniqueness of maps with prescribed projections. The differential, s and i are defined by these projections and their chain equations are checked projectionwise. Membership of QP uses the explicit hypothesis of the item, not any uncited theorem about product preservation by localization. Thus no AB4* or Grothendieck hypothesis has been smuggled in.

Step 4 again uses only that product universal property. The recursive a_n is a morphism from the SAME P^r in every index, with a_{n+1}=sigma_n(a_n-pr_n). Multiplying by f_n gives a_n-pr_n, so pr_n(u a)=pr_n. The sign is correct. The componentwise section a need not commute with d and is used only to prove degreewise epimorphy. This is a finite recursion in each component, not an infinite sum or an element argument in an arbitrary abelian category.

Step 5 cites the product definition and def-sp-abelian. I checked the kernel universal property against arbitrary Z and arbitrary morphisms b, not just global elements. At N=r+1 the quotient is T^r, lower b_n are forced by compatibility and all higher transitions are identities under canonical summand identifications. Thus i^r is the kernel. Together with the explicit section of u^r this gives a degreewise short exact sequence. No existence or exactness of general inverse limits is asserted.

Step 6 uses the exact statement of lem-weil-pbc-complex-ses-triangle a second time and the rotation axiom stated in def-weil-triangulated-category. I opened the latter and verified TR2. The inverse-rotated triangle has endpoints QP[-1] and QP, both in H; extension closure from def-weil-triangulated-subcategory proves QT. All hypotheses remain those of the item.

For B–E of delivery-errors: statement and TeX remain intact; all existing notions used have definition nodes; every non-elementary theorem used is a cited statement, with an actual verbatim quotation in citations.json. No citation uses a proof-internal object. There are no new nodes to be unsplit, duplicated, or to restate a clause. The split supplies the actual quotient induction and product exactness rather than saying “apply totalization closure”. The two genuine theorem-application steps are non-elementary; projection calculations and finite recursive constructions are marked elementary with their complete arguments. Every step is below 2000 characters. I checked zero double complexes, zero columns, degree -1, degree 0, a single nonzero column p (yielding its shift by -p), and the odd-column sign p=1. No statement dispute or added hypothesis was needed. The main correction to the initially empty proof was to distinguish a quotient-prefix tower from the invalid prefix-subcomplex direction and to make the product sequence's surjectivity and kernel explicit.

The sole off-unit theorem is declared in split_report.tool_uses: lem-weil-pbc-complex-ses-triangle, a general homological algebra tool for which the compactification unit has no replacement. Definitions are used only as definitions. No maintainer-owned tool_uses field is written.

## Validation

The first server preflight rejected the phrase “the item’s product hypothesis” in step 3 as non-self-contained wording. I replaced it by “the assumed representation of countable derived products by termwise products”; the hypothesis and mathematical argument are unchanged.
