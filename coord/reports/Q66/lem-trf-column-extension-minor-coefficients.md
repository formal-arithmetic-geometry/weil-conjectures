# Stage-1 report: lem-trf-column-extension-minor-coefficients

## Files written

- dag/nodes/sec-trace-formula/lem-trf-column-extension-minor-coefficients.json: statement, split; unchanged statement and statement dependencies; four proof steps, with the existing Laplace coefficient formula as the sole non-elementary input. Mathlib verdict: no exact or one-line match.
- citations.json: five verbatim statement excerpts for all step/node citations.
- report.md: this report. searches.jsonl was written by the required msearch command.

New nodes: 0. New Mathlib leaves: 0.

## Attachments

None. Searched lean/WeilConjectures both for the item id (including its blueprint tag) and for cofactor/Laplace/column expansion terminology. The project contains uses of single-column expansion and a separate independence-of-functions result, not the recursive coefficient construction and every clause of this item. No project declaration was treated as closed merely because it was present in the source.

## WANTED

None. The source needed here is locally available.

## Findings and corrections

The imported node had a complete recursive statement but no proof. Its statement is correct and was preserved, including the data-level recursion and all zero-size conventions. No STATEMENT-DISPUTED correction is necessary. The previous Mathlib search records remain intact; five fresh searches were performed and appended, including two semantic phrasings, Loogle, logged Mathlib grep, and LeanSearch. All services responded successfully. The results provide Matrix.det_succ_column (Determinant/Basic.lean:787), adjugate identities, or generic polynomial evaluation. I read the expansion at lines 786–792 and the generic evaluation statements in Matrix/MvPolynomial.lean. None proves the full iterated minor identity with these specified recursively constructed coefficients in one specialization.

I searched the whole DAG by 07Z7, column expansion, cofactor, and recursive/adjoining-column terminology; blueprint_refs searches for column expansion, recursive minor coefficients, and minor found no identical blueprint statement. The existing lem-trf-minor-laplace-coefficient-formula supplies more than the single-column expansion needed here and is reused rather than duplicated. It is in the same chapter and unit. The item retains its precise existing auxiliary ancestry: the nearest blueprint ancestor lem-trf-local-term-locality has no separate Fitting clause; the intervening fitting-ideal-minor-inclusions node records where this determinant calculation was introduced. I read the latest blueprint's unit, ancestor statement and proof; this split changes no geometric route or chapter/unit record.

## Unfinished work

None for this one-level split. The existing generalized Laplace formula remains its own independently queued node; this delivery does not edit or claim to prove that node. No Lean was written and no compiler or build was run.

## Not duplicates

No new nodes were created, hence there are no new/existing pairs to distinguish. The selected-column Laplace identity is an input here, whereas this item's conclusion is a different, iterated expression with prescribed recursive polynomial data.

## Review by Q66

I read Stacks more-algebra.tex, Tag 07Z7, label lemma-ideals-generated-by-minors, including its row-extension assertion and its omitted-proof column/row-expansion hint. The polynomial certificate here is the agent-supplied elaboration of that hint, rather than a verbatim Stacks theorem; proof_origin is accordingly agent. I read all three definition-node statements and the full statement of lem-trf-minor-laplace-coefficient-formula. There are no new nodes requiring separate sources.

Step 1 uses only the displayed recursion and integer inequalities. For a nonempty increasing column list, deleting its maximum puts every remaining entry at most n+d-1; the q=1 case is explicitly separate. This justifies the recursive call even when the deleted column belongs to the original first n columns. Finite sums of signed symbol multiples are actual integer polynomials, and the smaller alphabet embeds as the same finite expression. This is elementary data construction, not an existence choice or an ideal-membership argument.

Step 2 states the full induction claim with p,n,r fixed and R,B,I,J quantified at every stage. At d=0 the Kronecker coefficients leave precisely the selected minor of A=B. The determinant definition explicitly supplies det(empty)=1, as quoted in citations.json, so the r=0 base case is covered without an unstated positive-rank hypothesis.

Step 3 uses exactly the displayed equation in the Laplace node's statement: its arbitrary commutative ring is our R, its square matrix is Q=B_(I,J), its size is q=r+d>0, and its retained position-column set is the singleton {q}. Its summation then has singleton row sets {a}, giving exponent a+q with no permutation of complements. The determinant definition's Leibniz formula gives det of a 1 by 1 matrix equal to its entry (the only permutation is the identity). The submatrix definition identifies the complementary submatrix entry by entry with the indicated ordered deletion. I cite these two definitions as well as the Laplace theorem and copied their actual formulas into citations.json; no proof-internal construction or stronger assertion is taken from a cited node.

Step 4 uses the submatrix definition to identify the smaller minors with those of B^-, the first n+d-1 columns. Its first n columns equal A because d>0. The induction hypothesis therefore has exactly the needed dimensions, including q-1=r+d-1. After substitution, the two finite sums are interchanged and distributed, and the inner coefficient is written explicitly; it is the evaluated defining recursion, not an unspecified transport or coefficient choice. Evaluation here is direct substitution into finite integer monomial expressions; preservation of sums/products follows by distributivity, so it hides no algebraic-geometry or determinant lemma.

Against delivery-errors B–E, I checked self-contained objects, existing definition dependencies, single-escaped TeX, precise tag/label source, actual logged search queries, and blueprint references. There is no new statement-only node to audit and no relabelled conclusion. The only non-elementary step cites the existing Laplace theorem; the remaining steps are short index arithmetic, substitution and distributivity arguments with their details written. The dependency cannot cycle through the item: the Laplace node has empty proof dependencies and its statement dependencies are the three matrix notions. Each proof step is below 2000 characters (561, 409, 546, 772).

I checked small and limiting cases explicitly: d=0 gives the delta identity; r=d=0 gives 1=1; r=0,d=1 gives L_1=X_(i,j) times the empty determinant; r=1,d=1 gives -B_(i1,j2)B_(i2,j1)+B_(i2,j2)B_(i1,j1), the usual 2 by 2 determinant. For n=0,r=0 repeated expansion ends in the empty minor. If r>n or r>p then a q=r+d selection in n+d columns or p rows cannot exist. Likewise p=0,d>0 has no row selection. The argument works over rings with zero divisors and in characteristic two, since no division, nonvanishing, or distinctness of signs is assumed.
