1. Files written:

   - dag/nodes/sec-abelian-varieties/thm-sp-spectral-object-yields.json (item, repaired split)
   - dag/nodes/sec-abelian-varieties/lem-sp-filtered-complex-ZB-description.json (new statement, unsplit, Mathlib no match)
   - citations.json

2. Attachments: none.

3. WANTED: none.

4. What was wrong in the returned delivery: the former quotient display used the same target for Z_r and B_r and was ill-typed for r>=2; at r=1 it forced E_1=0. The helper was also stated in an E1-indexed exact-couple convention while citing the project definition whose couple starts at E_2 and requires f of bidegree (+2,-1). I replaced both image clauses with the well-typed map to $H^{p+q}(X^{[p-r+1,p+1]})$, corrected the helper's $r=1$ clause to say that $Z_1$ and $B_1$ are cycles and boundaries, and made the coordinate change (P,Q)=(2p+q,-p) explicit with standard page R corresponding to filtered page r=R-1. The convergence step now records the shifted filtration index P=p+n.

## Review by G1

I read the project definition of exact couples and its stated bidegrees, the spectral-sequence definition, the page-induction statement, and the convergence and couple-morphism nodes. I checked the corrected image formula at r=1 and r=2 by hand: at r=1 the target is $X^{[p,p+1]}$ and the quotient is the cycles modulo boundaries of $\\operatorname{gr}^pK$, while the r=2 target is $X^{[p-1,p+1]}$, so the displayed map is defined. I also checked the large-r case against degreewise boundedness. Step 2 now explicitly converts the filtered connecting map of bidegree (+1,0) to the standard exact-couple convention by (P,Q)=(2p+q,-p), with standard page R corresponding to filtered page r=R-1. Step 3 cites the helper for both the Tag 012K subobjects and the non-elementary identification with quotient-complex cohomology images. Step 5 records that the convergence filtration index P=p+n is shifted from filtered p. Every citation quote in citations.json is copied from the cited node statement. I reran the required Mathlib searches for the item and helper; LeanSearch was unavailable and the other searches found no matching filtered-complex construction.

## Not duplicates

lem-sp-filtered-complex-ZB-description vs thm-sp-half-plane-convergence: the new node gives the filtered-complex Z_r/B_r subobjects and quotient-complex images, while the existing node treats abstract half-plane exact-couple convergence.

lem-sp-filtered-complex-ZB-description vs lem-sp-half-plane-graded-canonical: the new node is the finite-page filtered-complex description; the existing node is only the E_infty associated-graded isomorphism for a half-plane couple.

5. What I could not finish: no Lean declaration or Mathlib theorem states this construction, so the repaired statement remains an unsplit theorem node.

## Second reading by G1

- Item statement: checked against Stacks Homology Lemma 12.19.2 (Tag 012K); the cycle/boundary formulas and indexing are consistent after repair.
- Steps 1-3: checked against the cited exact-couple, spectral-sequence, and page-induction statements; the reindexing supplies the required bidegrees.
- Step 4: checked against the helper and Tag 012K; the image map is now the well-typed map from $H(X^{[p,p+r]})$ to $H(X^{[p-r+1,p+r]})$.
- Steps 5-6: checked against convergence and couple-morphism nodes; boundedness and functoriality give the stated conclusions.
- Helper node: checked against Tag 012K and searched with leanfinder, Loogle, grep, and unavailable LeanSearch; no Mathlib declaration matches.

Changes: repaired the ill-typed quotient-complex clause in both statements, corrected the helper's Stacks source label, and updated Step 4. The prior blueprint image quotient was a source error because its proposed map from $F^{p-r+1}$ to an $F^p$ quotient does not exist for $r>1$; the well-typed image formulation is recorded here.
