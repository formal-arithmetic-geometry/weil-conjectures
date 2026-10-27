# Q60: lem-sfb-simplicial-algebra-shuffle-normalization

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-simplicial-algebra-shuffle-normalization.json: statement node, now split into thirteen proof steps; not a Mathlib leaf. No new nodes and no new Mathlib leaves.
- citations.json: seventeen step/node pairs with verbatim statement quotations.
- report.md: this report. searches.jsonl records six actual new Mathlib queries. check_small_cases.py contains the finite mathematical checks described below; these auxiliary files remain in the sandbox.

## Attachments

None. Searches of lean/WeilConjectures for the exact blueprint tag and for shuffle/normalization found no declaration covering the item. The evaluation_shuffle and Koszul sign hits concern other constructions. The additive Moore comparison is already the existing Mathlib leaf lem-cbc-normalized-alternating-homotopy-equivalence; no attachment or duplicate was created.

## Wanted literature

WANTED: C. Weibel, An Introduction to Homological Algebra, section 8.5 (Eilenberg–Zilber), for lem-sfb-simplicial-algebra-shuffle-normalization. The book is already in literature/LIST.md's wanted table and is not present locally. The shuffle argument is therefore explicitly agent-written, using the existing proved lattice-path boundary statement, rather than attributed to an unread source. No external source was downloaded.

## What was wrong or missing

The item had a complete statement but no proof. Its Stacks citations supply additive normalization only, as its source field already acknowledges; they do not establish the shuffle product. I kept the statement verbatim and supplied the missing algebra argument. Added def-weil-pbc-flat-ring-map to stmt_deps because the statement uses module flatness and that node defines it. No source error or STATEMENT-DISPUTED issue was found.

The inherited blueprint ancestor is null, as confirmed by blueprint_refs.py ancestor. I preserved its from.node, from.place and via rather than inventing an ancestor. The current blueprint direct-images proof paragraph (3) gives the application, not this coefficient-model calculation. Read the chapter and unit records and the latest proof file; neither route was altered. The unit has no realization yet; this item is not its key statement, so it does not write realization fields.

## Unfinished work

None within this one-level split. This is stage 1 only: no Lean files were written or compiler/Lake/build commands run.

## Not duplicates

No new nodes. Whole-DAG tag searches for 017V, 019A and 019C, keyword searches for normalized chains, Moore complexes, degenerate subcomplexes and shuffle multiplication, and whole-blueprint searches for shuffle, normalized, simplicial algebra, degenerate and Moore were read. Existing nodes were reused rather than recreated. The bicosimplicial totalization and lattice-path shuffle results concern additive comparisons; the positive-face Moore leaf concerns the additive inclusion; none is the entire algebra-normalization statement.

## Review by Q60

I read Stacks simplicial.tex at lemma-splitting-abelian-category (017V), lemma-decompose-associated-complexes (019A), remark-degenerate-subcomplex and lemma-quasi-isomorphism (019C). Stacks uses the other end of the face sequence, so I did not silently identify conventions: steps 2–4 construct the descending positive-face projector and its kernel explicitly. I also read the latest blueprint direct-images proof paragraph (3), the item, its chapter and unit, and every cited node's full statement. There are no new nodes requiring separate source review.

For step 1, def-weil-pbc-simplicial-object supplies the contravariant functor and its face/degeneracy maps; the cancellation of pairs of deletions and of d_i s_i and d_(i+1) s_i is written out, including n=1. Steps 2–3 use the same definition only: I checked d_j s_(j-1)=1, the identities preserving already killed higher faces, and E_j s_i=s_i E_(j-1) for j>i+1. The next factor annihilates s_i, which proves that the actual degeneracy sum, not some unidentified complement, is the kernel of the projector. Step 4 verifies that K is a subcomplex and q restricted to K is an isomorphism of complexes; the claimed section is a module section in each degree. During review I made its equations explicit as q i a^(-1)=1 and i a^(-1) q=rho to avoid an ambiguous composite.

For step 5, I opened lem-cbc-normalized-alternating-homotopy-equivalence and checked that its statement uses exactly the kernels d_1,...,d_n, differential d_0 and the canonical inclusion, not an unspecified equivalence. Its Mathlib source was read at MooreComplex.lean:64–90 and DoldKan/HomotopyEquivalence.lean:79–87; DoldKan/Normalized.lean:64–125 also confirms the split inclusion. Modules over an arbitrary commutative D are an abelian category, so no field, flatness or boundedness hypothesis was inserted. I read the complete statement of lem-weil-pbc-homotopic-maps-equal-cohomology and use its equality on homology for the two homotopy equations; after n becomes -n these are exactly its cochain equations. The factorization a=q i then proves the quotient map is a quasi-isomorphism.

Step 6 uses the simplicial-object definition to identify repeated positions of the prefix-count surjection with the displayed degeneracy strings. Step 7 cites lem-sfb-simplex-lattice-shuffle-boundary, whose statement I read: it allows weakly increasing strings, integral coefficients, zero-degree boundary conventions and the precise partition sign. Its parameter values are [p],[q] and the identity strings. The evaluation on a pair of monotone maps is written out and commutes with faces because the faces of P are ring maps. Thus the cited boundary formula really evaluates to the requested Leibniz formula over any D; there is no hidden flat tensor argument or characteristic restriction.

Step 8 uses only the simplicial maps of its definition citation. I checked that the horizontal step crossing the repeated coordinate of a degenerate x forces BOTH pulled-back factors to repeat at the same position. They factor through that one sigma_k; multiplicativity of s_k makes their product degenerate term by term. This proves descent without incorrectly treating the degeneracy submodule as an ideal for ordinary levelwise multiplication. The y case is the same explicit vertical-edge argument.

Step 9 gives both inverse reindexings of nested shuffles as three-letter words. Its term identifications are compositions of prefix-count maps; its sign is partitioned into inner and outer inverted pairs. This is the finite expansion of associativity for the actual x,y,z, not a new unproved shuffle theorem. Step 10 uses the explicit block-interchange permutation with pq inversions and the one-shuffle unit formulas. Step 11 checks every term under an arbitrary simplicial algebra map and compares the resulting multiplication, unit and Leibniz law with the full statement of def-sfb-dg-derived-category. That definition is over Z; the central D-action and bilinearity have been supplied explicitly rather than assumed from it. These steps require commutativity of each P_n exactly where factors are swapped.

For step 12 I read lem-weil-pbc-flat-module-retract: it states the module retraction version with no extra finiteness or ring-map hypotheses. The section and quotient of steps 3–4 have precisely its linearity and r i=1 hypotheses. Its zero-term check uses the definition of flatness directly. Step 13 cites the simplicial-object and module-homology definitions: the identity degeneracies make the constant normalization zero in every positive chain degree, with degree zero unchanged. The augmentation factorization is checked degreewise and its homology calculation uses the proved quotient quasi-isomorphism; it is not inferred from a model-category assertion.

All seventeen citations in citations.json quote the actual cited statements verbatim. proof_deps is exactly the union of step uses. No off-unit non-Mathlib theorem is used: the lattice shuffle boundary is in this unit and the other statement tools are existing Mathlib leaves. Every step is under 2000 characters. I checked the small cases p=0, q=0, p=q=1 (s_1 x s_0 y - s_0 x s_1 y), zero ring, constant algebras, and degree-zero augmentations. The argument uses no division, so characteristics 2 and positive characteristic cause no additional assumption.

The sandbox's executable mathematical check tests the projector on 116 representable-module basis cases with simplex parameter at most 2 and chain degree at most 5, including annihilation of all degeneracies and vanishing of all positive faces. A separate formal-monomial model of the free simplicial commutative algebra verifies the Leibniz identity, commutativity and termwise degeneracy for p,q at most 4 and associativity for p,q,r at most 3. All passed. These are finite checks of signs and indexing, not replacements for the written arguments.

The six new msearch.py queries were all actually run and their hits read: LeanFinder on the quotient-algebra formulation, Loogle on shuffle, grep on shuffle and Moore normalization in AlgebraicTopology, LeanSearch on normalized chains as a graded commutative algebra, then a second LeanFinder phrasing using lax symmetric monoidal normalization and a focused Eilenberg–Zilber/shuffle grep. The semantic hits give additive Dold–Kan/Moore functors; the source reads confirm they lack the displayed product. The focused grep had zero hits. Earlier search records in the live item were retained. Server review_split already printed PASS with zero new nodes before this report; the full deliver.py dry run is the next gate.
