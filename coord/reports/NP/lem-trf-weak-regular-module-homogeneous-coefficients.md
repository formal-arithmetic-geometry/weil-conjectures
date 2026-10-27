# Stage-1 report: lem-trf-weak-regular-module-homogeneous-coefficients

## Files written

- `dag/nodes/sec-trace-formula/lem-trf-weak-regular-module-homogeneous-coefficients.json`: the existing statement, now split in eight explicit elementary steps; Mathlib verdict: no matching module theorem. No new nodes and no new Mathlib leaves.
- `citations.json`: one verbatim quotation for each dependency of each proof step.
- `searches.jsonl`: actual search-command records, retained as generated.
- `report.md`: this report.

The sandbox initially contained no node, proof, report, or search log. I copied the current item and retained its statement, source, original searches, blueprint ancestry and other imported fields. Added the existing ideal-products-and-powers definition to statement dependencies. No unit record changes: this supporting algebra lemma is not the unit's key node.

## Attachments

None. Searched `lean/WeilConjectures/` by the exact item id and by weak regularity and homogeneous coefficients, then read `RingTheory/QuasiRegular.lean`. Its `MvPolynomial.coeff_mem_of_eval_mem_pow_succ` at line 126 has coefficients in the ring itself, and cannot furnish this arbitrary-module statement. The weak-regularity/descent declarations found elsewhere do not assert the coefficient conclusion. No sorry-bearing declaration is treated as finished evidence.

## WANTED

None. The complete source is present locally.

## What was wrong or incomplete

The item had no proof. Stacks `algebra.tex`, Tag 00LN, `lemma-regular-quasi-regular`, proves (1) explicitly and says to prove the module case (2) in exactly the same way. The module argument and its two induction hypotheses are now written out rather than cited as an omitted proof. Its source's final informal phrase that the module coefficients are “in J” means in JM, as equation-quasi-regular, Tag 061N, makes precise. The item's original statement already has the correct module-valued meaning and was not changed.

The current `literature/blueprint/latest/blueprint/sec-trace-formula/sk-i-curve-zero/` statement, proof and unit were read, together with the chapter. The item's recorded historical ancestry is a supporting commutative-algebra branch; no claim is made that the current local-term proof itself states this algebra lemma. The split stays below the unit level and does not alter its route. Searched the whole DAG for 00LN, 061N, weak regularity and homogeneous coefficients, and ran blueprint_refs searches for quasi-regular, homogeneous coefficient and 00LN. No imported blueprint node states the arbitrary-module weak-regularity result. The closest nodes are `lem-pur-regular-sequence-higher-homogeneous-relations`, `lem-pur-regular-sequence-graded-polynomial` and `lem-weil-pbc-regular-sequence-conormal-free`; each requires ring coefficients, and the last only gives degree one. Their proofs are not used as stronger statements than they carry. No new node duplicates them.

## Unfinished work

None in this stage-1 split. Future Lean formalization remains outside this delivery's scope.

## Not duplicates

No new nodes are introduced. Monomial expansion, quotient cancellation, grouping by the last exponent and the explicit correction identity are routine calculations inside the proof, not separate lemma nodes or restated clauses of the item.

## Review by NP

I read Stacks `algebra.tex` lines 16855–16977, including Tag 061N (`equation-quasi-regular`), Tag 061P (`definition-quasi-regular-sequence`) and all of Tag 00LN (`lemma-regular-quasi-regular`). The item states precisely its module coefficient criterion but assumes only the injectivity used in that proof; the nonzero-final-quotient condition is unnecessary. I also opened both cited definition nodes in full. `def-weil-pbc-regular-sequence` explicitly states injectivity on the successive module quotients and separately states nonvanishing. `def-weil-pbc-algebra-hom-quotient` explicitly defines ideal products and recursively defines ideal powers. Neither is being used for a theorem about flatness, exactness, freeness, or an associated graded isomorphism.

Step 1 uses the latter definition to expand a product of finitely generated ideals. The meaning of HN is supplied explicitly as finite sums of ideal elements times module elements. Expanding the generators and collecting equal indices proves the monomial description, including degree zero. It then writes the next ideal power with coefficients in HN. This is just distributivity and the product definition; no module freeness is assumed.

Step 2 uses the ideal-power convention for the empty-list base and the successive-injectivity definition to specify the exact outer induction proposition. The induction hypothesis is the full next-power criterion in every degree for every shorter weakly regular list on this same arbitrary module. For the empty list, n=0 has one coefficient forced to be zero, whereas n>0 has none. Step 3 uses the explicit expansion in step 1, subtracts coefficients in JN and reduces the current-length assertion to zero relations without applying the current-length conclusion circularly.

Step 4 uses precisely the injectivity clause of `def-weil-pbc-regular-sequence`, first for the unchanged prefix and then for multiplication by t on N/KN. Its power cancellation is composition of l injective maps; it never cancels t on N. Ideal inclusions use only the generated-ideal meaning. Step 5 states the inner induction for arbitrary coefficients, with fixed degree n and bounded upper last exponent l. The l=0 case uses the outer hypothesis on the prefix in degree n, since zero belongs to every next ideal power. The same two definition nodes give all notions in these two steps.

Step 6 uses the ideal-power definition to put every lower-exponent term in K^(n-l+1)N. The outer hypothesis then applies in degree n-l to the family with coefficients t^l a_beta,l, not to the unscaled family. Only after getting those coefficients in KN does step 4 cancel on the quotient. The arithmetic uses l<=n and e<l; there are no negative exponents. No statement about nonzerodivisors modulo higher powers is presumed.

Step 7 uses the ideal-power/generator definition and step 1 to write the top coefficients as sums z_i u_beta,i. The formula defining b_gamma explicitly collects beta+epsilon_i=gamma, so its displayed equality is termwise distributivity. The correction at exponent l-1 is t b_gamma, whose product with t^(l-1) equals the former top term. Thus the new relation really has upper exponent l-1 and the same total degree n. The inner hypothesis applies to this arbitrary corrected coefficient family. Subtracting the corrections is legitimate because each correction is in tN, hence JN. This is a finite sum identity, not an unnamed identification or a hidden lemma. In an empty prefix KN=0, the coefficient representations and b sums are empty and the equality remains valid.

Step 8 groups every multi-index as (beta,e), invokes the inner assertion at l=n, and then the already proved subtraction reduction. The two induction parameters are well founded and both bases are present. All eight steps are marked elementary because their only facts beyond the specified induction hypotheses are the displayed finite expansions, submodule closure and composition of injective maps. No step exceeds 2000 characters. Every non-elementary theorem that one could otherwise quote (regular implies quasi-regular, an associated graded basis theorem, or permutation of regular sequences) is instead unnecessary: the actual double induction proves the item directly, as in its source.

Small cases checked: N=0 over any ring; the zero ring; s=0 with n=0 and n>0; degree n=0 for any list (the premise itself is the conclusion); one injective parameter (cancel its nth power after writing the next-power element); a unit parameter such as R=Z, N=Z, y_1=1 (the final quotient is zero, so adding nonvanishing would be wrong); R=k[x,y], N=R/(y), parameter list (x); and a two-parameter list in R=k[x,y], N=R. The empty-prefix subcase at s=1 in step 7 is valid because its top coefficients are already zero. As a negative check, R=k[epsilon]/(epsilon^2), N=R, y_1=epsilon violates injectivity and has the false coefficient conclusion in degree two with coefficient 1; our proof correctly cannot cancel there. No Noetherianity, finite generation of N, separatedness, regularity under permutations, or nonzero final quotient has entered any step.

I checked delivery-errors B–E against these files: no new statement-only obligations, no invented Mathlib leaf, every cited statement opened, verbatim quotations in citations.json, exact proof-dependency union, no use of another node's proof as its statement, and no self-reference or descendant dependency. Mathlib searches were made through msearch.py, in two semantic formulations and two Loogle patterns, with grep hits read. RegularSequence.lean:21 still lists quasi-regular sequences as TODO; its lines 130–148 give only the weak/strong definitions. The leading-coefficient hits and Polynomial.coeff_prod_mem_ideal_pow_tsub concern different polynomial statements, and the Rees filtration submodule hit constructs the filtration without asserting coefficient independence. All actual searches and their outcomes are retained; the existing historical searches were not fabricated or relabelled as new runs. There are no SGA citations and no off-unit statement tools to declare. The only changes after the source review were to expand the omitted module argument and supply the explicit correction formula; no statement dispute was found.
