## Files written

- dag/nodes/sec-six-functors/lem-sf-integral-point-dual-models.json: statement split in six steps; Mathlib verdict no match for the complete assertion. No new nodes and no new Mathlib leaves.
- citations.json: fourteen verbatim quotations, one for each use of a node in a proof step.
- searches.jsonl: actual searches recorded by the required command; earlier live-node search records were preserved.

## Attachments

None. Searched lean/WeilConjectures by the blueprint id and by derived completeness, point perfectness and perfect duals; inspected the relevant Point.lean declarations and the dual/perfect matches. Point evaluation and sheaf coefficient duality do not state all the ordinary-module, completeness and canonical reduction clauses of this item. No exact attachment was found.

## WANTED

None for this split. Its arguments are available in the current blueprint and Stacks source; the local-field facts are already stated by existing DAG nodes.

## Findings and corrections

The imported item had a complete statement but no proof. Its statement remains unchanged, including the meaning of D^b_fg(R) as bounded finite cohomology AND derived completeness. Its blueprint ancestry and coefficient conventions remain unchanged. The proof follows the final paragraph of Step 2 of literature/blueprint/main-20261015/blueprint/sec-six-functors/sk-thm-sf-package/thm-pod-point-perfectness.proof.md; the chapter and unit records were read. This is an ordinary module argument, not an argument about the constant discrete sheaf or the completed coefficient sheaf on a site. No SGA route is used.

The source's dual-model paragraph does not supply the completeness argument explicitly. I supplied the inverse geometric series to the multiplication-tower Roos endomorphism and used the existing perfect-completeness theorem. The coefficient-reduction assertion uses the canonical morphism in the existing perfect RHom base-change theorem, rather than merely an abstract isomorphism. The Noetherian cycles argument supplies finite generation separately from completeness. No statement dispute or route departure was needed.

## Unfinished work

None in the one-level split. Existing unsplit dependencies remain their own stage-1 work items; none has been re-created or split here.

## Not duplicates

No new nodes. Whole-DAG keyword, tag and blueprint-reference searches led to reusing lem-pod-projective-hom-evaluation-model, lem-zl-finite-projective-module-dual-pairing, lem-pc-base-change-rhom-perfect, lem-trf-noetherian-submodule-finitely-presented and lem-sf-perfect-over-derived-complete-ring. In particular the point sheaf realization lemma lem-pod-point-projective-dual-tensor-models has different objects and additional hypotheses, so I did not use it as an ordinary-module assertion.

## Review by Q76

I read the item's current blueprint proof in full, especially Step 2's final paragraph and its use of uniform finite-free finite-level models, and compared every clause with the live statement. I read the Stacks source more-algebra.tex at Tag 091R (lemma-complete-derived-complete), Tag 0A66 (lemma-RHom-out-of-projective), Tag 07VI (lemma-dual-perfect-complex and its following amplitude remark), and Tag 0A6A (lemma-base-change-RHom), including the paragraph defining its canonical map. I also read algebra.tex Tag 00FP (lemma-Noetherian-finite-type-is-finite-presentation), and the finite-projective dual passage at Tag 0FNJ. There are no new nodes requiring a separate source review.

For Step 1 I opened the coefficient definition, the full DVR statement and the metric completeness statement. They give the normalized valuation, the description of the valuation ring, the strict inequality for a uniformizer, principality of ideals, and convergence in E. For f in (t), the absolute value is at most |t|<1; uniform boundedness of every b_n in R makes the geometric series converge. I included f=0 separately and the estimate proving both that its limit belongs to R and that a kernel sequence is zero. Thus I did not assume that the definition of a valuation ring itself asserted adic completeness.

For Step 2 I read the whole statement of lem-weil-derived-limit-existence: clause (2) supplies termwise countable products specifically when products in the abelian category are exact. Modules satisfy that hypothesis by coordinatewise kernels and choice of coordinatewise lifts. The definition of derived limit supplies the precise Roos endomorphism, and the point-completeness definition requires every f in the ideal and every derived limit; the proof checks both quantifiers. The zero first vertex follows from the distinguished triangle of an invertible middle map (equivalently all its cohomology groups vanish). The step uses no assertion about sheaf products being exact.

For Step 3 I opened lem-pod-projective-hom-evaluation-model and checked that it applies to any bounded-above projective module complex and arbitrary target. P is bounded and projective and R[0] is a permitted target. Its actual differential gives the sign (-1)^(i+1) and reversed source degree. I opened lem-zl-finite-projective-module-dual-pairing and checked it explicitly asserts finite projectivity of the module dual. I also read the Mathlib dual_projective and dual_finite instances at LinearAlgebra/Dual/Lemmas.lean lines 145–152; these explain the search hits but are not an exact leaf for the whole item. The perfect-ring definition then applies directly to D, including when P is zero.

For Step 4 I opened lem-trf-noetherian-submodule-finitely-presented and checked its finite ambient module and Noetherian ring assumptions, established in Steps 1 and 3. Its statement supplies finite generation of each cycle submodule; taking a quotient preserves a finite generating family. I read lem-sf-perfect-over-derived-complete-ring: its hypothesis is completeness of R[0], not ordinary completeness of each term. Step 2 provides exactly that. Finally I checked all three conditions in def-weil-point-fg-complete-complexes; merely finite cohomology would not suffice.

For Step 5 I opened lem-pc-base-change-rhom-perfect and read its whole statement. It permits every commutative ring morphism, arbitrary second argument and perfect first argument, so R to A_n need not be flat. It explicitly identifies the canonical functor-induced morphism and gives the isomorphism in D(A_n). Substituting C and R[0], the unit and symmetry identifications produce precisely the map required by the item. I did not infer this from a degreewise cohomology assertion.

For Step 6 the same Hom-model statement applies over every A_n. A finite free term has a dual basis, with the same finite rank, and the inequalities u <= -i <= v are exactly -v <= i <= -u. I checked a single nonzero term in degree r, whose dual lies in degree -r; the zero model; n=1; and negative support intervals. Empty support gives the zero complex and causes no exception. The uniform interval is retained even though the models and bases can vary with n. This last argument is short degreewise algebra from the cited model, so it creates no new lemma.

I checked delivery-errors B–E: no new statement-only nodes, missing notions, duplicates, clause restatements or invented Mathlib searches; every non-elementary ingredient is a cited existing statement and has its exact quotation in citations.json. All sources, coefficients, boundedness and projectivity hypotheses match. Every step is below 2000 characters, and none hides a source's omitted lemma: the comparison and Hom-model theorems have been cited explicitly. The report declares the generic tools from other units without altering the unit's route. The server review_split check passed. The full delivery dry run and push follow this signed reading.
