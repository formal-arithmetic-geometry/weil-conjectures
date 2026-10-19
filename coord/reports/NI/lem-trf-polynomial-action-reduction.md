# Worker report: lem-trf-polynomial-action-reduction

## Files written

- dag/nodes/sec-trace-formula/lem-trf-polynomial-action-reduction.json: statement split; no exact Mathlib match.
- citations.json: the two node citations in Step 1, with verbatim statement excerpts.
- report.md: this report. searches.jsonl is the search command’s journal.

## Attachments

None. Searched the item tag and the polynomial-action, stable-span, finite-over-subring concepts in WeilConjectures and checked dag/lean_names_upstream.json. No exact project declaration was found. The polynomial quotient-basis source concerns a different universal quotient construction, not arbitrary S-modules as here.

## WANTED

None. The source is present: literature/stacks-project/algebra.tex, Tag 0561, label lemma-finitely-presented-over-subring, lines 584–628, especially lines 614–620. The tag-to-label correspondence is in tags/tags.

## Problems found and corrections

The imported item has the correct statement but no proof. Its parent, lem-trf-finitely-presented-over-subring, uses exactly this conclusion in Step 4. I retained the statement literally. “Subject to relations” needs only that the displayed relations hold; additional module relations cause no problem. No hypothesis on injectivity of R→S, freeness, finite presentation, or Noetherianity is used.

The inherited four search records belong to the creation by Q93 and were retained unchanged, not asserted to be new NI searches. NI’s seven queries and actual logged results are appended to mathlib_searches; their journal is searches.jsonl. Two semantic phrasings were tried. The read candidate sources were Mathlib/Algebra/Algebra/Tower.lean:387–415 and Mathlib/Algebra/Algebra/Subalgebra/Lattice.lean:684–725. span_smul_of_span_eq_top requires generators of S as an R-module, which the x_i need not be. adjoin_eq_span concerns the algebra itself. The MonoidAlgebra.submoduleOfSMulMem hit (Module.lean:317) requires invariance under all monoid elements and constructs a monoid-algebra submodule; getting from the present generator hypotheses to that invariance is the induction being proved, so it is not a one-line specialization of this item.

## Unfinished work

None for this one-level split. No new nodes, no new Mathlib leaves, no Lean written, and no compiler run.

## Not duplicates

No new nodes. Searched the whole DAG by Tag 0561, polynomial-action, action-relations, monomial-generators and invariant-submodule concepts, and the blueprint index by “0561”, “module generators” and “polynomial action reduction”. No blueprint node states the item. The other Tag 0561 nodes concern transfer of finite presentation or applications of that transfer, not this elementary degree-reduction statement. The original item’s blueprint.same_as=[] and ancestry are retained. No off-unit theorem is used: the two cited definitions are existing Mathlib leaves.

## Review by NI

I read Tag 0561’s full statement and proof, not just the item’s description. Its middle paragraph writes z as a finite S-linear combination, writes each coefficient as a polynomial in the algebra generators, and lowers polynomial degrees with the action relations. Those are exactly the three steps delivered here. The parent has finite-presentation hypotheses for its own application, but they are not needed for this subcalculation. The item’s hypotheses are sufficient as stated. I also read the chapter record, sk-i-curve-zero unit and the ancestor’s current-blueprint update; the present item remains supporting algebra under the inherited valuation branch and changes no geometric route or unit realization.

Step 1 cites def-weil-finitely-generated-module specifically for its first sentence: every module element is a linear combination of its given generators. It is applied over S, not R. It cites def-weil-pbc-finite-type-algebra specifically for its equivalent polynomial-expression clause, using the x_i that the item specifies as generators. I opened both node statements and copied their relevant literal text into citations.json. Neither is cited for a theorem about finite presentation or for invariance of a submodule.

Step 2 uses only the hypotheses and elementary module identities. Its induction claim is simultaneous for all j, so after replacing x_i e_j the terms indexed by k are covered. The exponent sum strictly drops by one. Commutation of the R-scalars with the S-action follows from restriction of scalars along the commutative R-algebra map; no faithful action is assumed. This is a short calculation, not an uncited non-elementary invariance theorem. The monomial induction and its base are written out and remain below 2000 characters. Step 3 gives the actual coefficients c_k by finite double sums; no unspecified transport or degree cancellation is hidden.

Against B–E: there are no new nodes to be elementary duplicates, restatements, unsplit nodes with proofs, or false generalized claims. The steps carry the entire argument instead of moving it to a new lemma. All uses are exactly the union proof_deps; every cited statement supplies the claimed fact (C4); no non-elementary fact is used without a node (C1). No dependency points back to the item. All sources are Stacks Tag 0561, with no SGA citation. I checked n=0, when S is a quotient of R and only constant polynomials occur; m=0, when N=0; zero rings; and n=m=1, where x e=a e implies x^d e=a^d e by the displayed induction. Multiple generators require no compatibility conditions beyond the given S-module, so the proof does not assume matrices define a new module action. No statement dispute or source correction was necessary.
