# Stage 1 report: lem-per-h1-koszul-quasi-regular

## Files written

- dag/nodes/sec-deligne-laumon-a1/lem-per-h1-koszul-quasi-regular.json: item, statement unchanged, split into seven proof steps; no Mathlib match.
- dag/nodes/sec-deligne-laumon-a1/lem-per-h1-koszul-last-product.json: new statement-only lemma, Stacks 062G (1), M=R; unsplit, no Mathlib match.
- citations.json: one verbatim full statement per cited node per proof step.

One new node, zero Mathlib leaves. No unit or chapter record is changed.

## Attachments

None. Searched WeilConjectures for the exact blueprint tag, quasi-regularity, Koszul regularity, H1 and multiplication/powers. KoszulConormalBasis.exists_koszul_conormal_basis assumes full Koszul regularity and only gives the degree-one conormal basis. QuasiRegular.lean assumes successive nonzerodivisors. Neither states this item or the new multiplication lemma. No Lean was written or compiled.

## WANTED

None. All required sources are available locally.

## Corrections and source observations

The item statement is correct and remains unchanged. Stacks 062I's general-M proof calls (M/JM)^r finite free, which is not true for arbitrary M. Here M=R, so the issue does not affect this item, and the proof bypasses that sentence entirely. The coefficient argument establishes every positive degree, including degree one.

The final paragraph of 062I uses R[x_1,...,x_r,1/x_r], flat base change and change of basis. I specialize its generic-coordinate trick to the triangular substitution f_i=g_i+x_i*g_r (i<r), f_r=g_r in R[x_1,...,x_{r-1}]. Homogeneity makes the r-variable degree-n monomials distinguishable by the first r-1 exponents, so no Laurent localization is needed. The proof supplies polynomial preservation of H1=0 coefficientwise and explicit degree-one and degree-two maps for the triangular change; it does not silently invoke flatness or an unrecorded change-of-basis theorem.

The inherited blueprint.from.place mentions Expose X and a regular local model that the latest ancestor proof no longer spells out. I retain that provenance, and identify the auxiliary Koszul-criterion branch in split_report. I read the latest ancestor and unit, not the old snapshot. No unit route or target statement is changed.

## Searches

Read every logged result. Searches were run only through the prescribed msearch.py and are recorded in searches.jsonl and in the node mathlib_searches. For the item: two semantic phrasings, LeanSearch, Loogle IsWeaklyRegular and grep Koszul/quasi-regular. For the new node: the two tuple/multiplication and H1-regular-last-element phrasings, Loogle "Koszul", and grep H1Regular/H_1/koszul. No service was unavailable. The semantic hits on regular sequences impose stronger nonzerodivisor hypotheses; cotangent H1 and smooth-presentation theorems concern different complexes. Read Mathlib/RingTheory/Regular/RegularSequence.lean, particularly line 21's TODO and the definitions. Its cons lemmas cannot specialize to arbitrary H1-regular tuples. The item retains its earlier recorded searches as well.

Before creating the node I searched all DAG statements/source places for 062G, lemma-mult-koszul-regular, H1 powers/products, and Koszul names; searched the whole imported blueprint with blueprint_refs.py for Koszul, H1 regular, 062I, 062G, quasi-regular, multiply last and product Koszul; and searched the project Lean source. No existing node gives the multiplication assertion. The sole raw regex hit in formal-glueing-complex-exact is not a multiplication theorem: its statement is an exact gluing sequence for modules.

## Not duplicates

lem-per-h1-koszul-last-product vs lem-per-h1-koszul-quasi-regular: the new lemma concerns H1 vanishing after multiplying two last generators with a fixed prefix; it states no associated-graded or coefficient conclusion and is used only for a power induction inside the item's proof.
lem-per-h1-koszul-last-product vs lem-sc-koszul-regular-flat-base-change: full Koszul regularity under flat scalar extension is different from H1 regularity under multiplication in the same ring; 062H rather than 062G.
lem-per-h1-koszul-last-product vs lem-weil-pbc-formal-glueing-complex-exact: the latter concerns a flat map and an exact gluing sequence, with no Koszul multiplication assertion. No existing node has Stacks 062G as its actual source.

## Review by NH

I read Stacks more-algebra.tex, Tag 062I (lemma-H1-regular-quasi-regular), its entire coefficient proof; Tag 062G (lemma-mult-koszul-regular), assertion (1) and its homology exact-sequence proof; and Tag 0625's change-of-basis assertion. I checked tags/tags for the labels. The new node is precisely 062G (1) with M=R, permits an empty prefix, and adds no proper-ideal, local or Noetherian hypothesis. Its proof remains empty as required for a new unsplit node. It is strictly auxiliary to the item: multiplying last entries and polynomial associated graded algebras are distinct assertions.

For step 1 I read def-weil-pbc-mv-polynomial-ring, def-weil-pbc-algebra-hom-quotient, def-weil-pbc-associated-graded-ring and lem-weil-pbc-associated-graded-ring-structure. Their statements give evaluation by the polynomial universal property, ideal generation/powers, the direct-sum graded pieces, their multiplication and quotient algebra action. The step proves its own monomial-generation and lift-independence calculations. It uses the structure theorem as an explicitly declared generic off-unit tool, not merely the definition as a source of ring laws.

For step 2 the new 062G node supplies the exact product implication needed with f=f_r^n and g=f_r; the induction begins at n=1. I read def-weil-pbc-koszul-complex: its statement gives H1=ker(d1)/im(d2), the exterior bases, and d2(e_i wedge e_j)=t_i e_j-t_j e_i. Thus the coordinate-in-the-ideal assertion is proved from the boundary formula, not borrowed from a conormal-basis result with stronger hypotheses.

Step 3 uses the quotient/ideal node and the preceding boundary calculation. I checked both degree-n and degree-(n+1) monomial expansions and the subtraction sign: the last coefficient of the resulting relation is a-b*f_r. Every other monomial contains a prefix generator. Applying step 2 gives a-b*f_r in (prefix,f_r^n), hence a in I. This works for n=1 and an empty prefix; it uses no assertion about H1 of a prefix alone.

Step 4 cites the Koszul and polynomial definitions. Their statements explicitly provide the finite free exterior coordinates and finite monomial expansions, so extracting each monomial from a polynomial cycle and summing finitely many boundary preimages proves preservation of H1=0 directly. This is an elementary finite coefficient argument, not an unsupported application of flat tensor exactness.

Step 5 cites the Koszul definition's d1/d2 formulas. I checked the displayed triangular matrix and its inverse: v_i=e_i-x_i e_r, v_r=e_r, inverse plus x_i e_r. Expanding d2 on v_i wedge v_j yields g_i v_j-g_j v_i. Thus the two maps needed for H1 identify both kernels and images; there is no claim about a derived comparison or a hidden general theorem. The ideal identity follows explicitly from f_i=g_i+x_i*g_r.

Step 6 cites the polynomial and ideal definitions. I checked the coefficient of g_r^n in the formal homogeneous expansion, its membership in IS by step 3 over the commutative ring S (whose H1 hypothesis was established in steps 4--5), and coefficient extraction from p=sum f_j*q_j. Fixed total degree recovers alpha_r uniquely from the other exponents. No infinite series or division is involved. Step 7 uses the polynomial, quotient and associated-graded definitions to separate homogeneous components, obtaining injectivity and the algebra inverse from the already established bijection.

All cited node statements are open in citations.json, copied verbatim; I checked that each supplies exactly the clause used. All non-elementary external input beyond definitions is either the new 062G node or the existing associated-graded structure theorem. No step exceeds 2000 characters. I checked B=0, R=0, r=0 and n=0 separately; r=1 reduces to the usual nonzerodivisor power calculation, with S=R. For R=k[x,y], f=(x,y), the degree-n monomials give the expected k-basis. For R=k[e]/(e^2), f=e has H1 nonzero and does not satisfy the conclusion, confirming that H1=0 was essential. The tuple (1,0) gives the zero quotient and no contradiction. No statement dispute or unresolved mathematical claim remains in the item's proof.

## Unfinished work

Only the new statement-only node remains for a future stage-1 worker. No other requested work is deferred; delivery validation is run below by the required server tool.
