# Q141 stage-1 delivery: lem-sfb-padic-minpoly-normed-separation

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-padic-minpoly-normed-separation.json: item, statement, split. No combined Mathlib match; existing Mathlib leaves supply the substantive algebra and analysis.
- citations.json: ten verbatim statement quotations for the ten step/node citations.
- report.md: this report. searches.jsonl contains the actual Q141 search records.

New nodes: 0. New Mathlib leaves: 0. The statement and statement dependencies are unchanged. The complete proof has five steps and 2227 text characters; no step exceeds 2000 characters.

## Attachments

None. Searched the whole project WeilConjectures/ tree for the blueprint tag and for the norm/minpoly/conjugate-distance concepts. The gap argument occurs inside PadicAlgCl.exists_isAlgebraic_mem_adjoin_simple (WeilConjectures/NumberTheory/Padics/Extension.lean:82–127), but no separate declaration states all the item's clauses for an arbitrary algebraic closure. An embedded argument inside a larger theorem is not an attachment of this item.

## WANTED

None. Stanford L19.pdf, the current blueprint, project Extension.lean, the relevant Mathlib sources, and Stacks fields.tex are all available locally.

## Findings and changes

The node had no proof. Its statement is correct, including the empty set convention, and was retained. Its cited Stanford source states the countability application but does not supply this auxiliary argument. The proof therefore remains explicitly agent supplied, expanded from the project code and supported by existing Mathlib leaves, rather than being attributed to Stanford as a complete written proof.

The existing lem-trf-spectral-norm-algebraic-extension supplies the norm for an arbitrary algebraic extension, avoiding a silent identification of an arbitrary closure with the chosen PadicAlgCl type. The existing lem-trf-irreducible-separable-derivative supplies the exact separability criterion. The existing lem-pc-separable-polynomial-distinct-roots-alg-closed supplies both root cardinality and factorization. All three are Mathlib leaves, so they are generic tools without any change to the unit route. No new norm-extension, minimal-polynomial, density or finite-minimum node was created.

The imported unit record belongs to the older sec-six-functors hierarchy, while this item's chapter and inherited arithmetic branch are in sec-six-functors-basics. I read both that unit record and the current main-20261015 direct-images proof. I retained the inherited placement and did not edit either unit or chapter. tools/blueprint_refs.py ancestor returns None for this created branch; the existing null ancestor and full via chain are preserved. Searches of blueprint references for minimal polynomial, conjugate, nonarchimedean and rational density find no equivalent blueprint item. Broad separable/spectral searches only find other notions. The item keeps same_as: [].

The existing Q95 searches are retained verbatim. New Q141 searches, including two different LeanFinder phrasings, were run through msearch.py and read. They found PadicAlgCl norm facts, general spectral norm facts and separable-root facts, but no theorem asserting the combined statement with its specified delta. Loogle found Krasner's lemma, which is a later application, not the present separation construction. The density grep confirms Padic.rat_dense at PadicNumbers.lean:815. No search was fabricated and no compiler was used.

## Not duplicates

No new nodes were created. In particular, norm extension reuses lem-trf-spectral-norm-algebraic-extension and distinct-root factorization reuses lem-pc-separable-polynomial-distinct-roots-alg-closed rather than duplicating them. The characteristic-zero step uses the more general lem-trf-irreducible-separable-derivative with an explicit derivative calculation.

## Review by Q141

I read Stanford L19.pdf p. 3, Proposition 1.1.9 first bullet, to check the countability context, and project Extension.lean:84–109 for the precise minimal-polynomial and finite-gap argument. I read the current blueprint direct-images proof paragraph (3) to keep the inherited coefficient-comparison route. I also read Mathlib SpectralNorm.lean:573–605 and 815–911, PadicNumbers.lean:815–823, Separable.lean:299–308, and Stacks fields.tex, lemma-irreducible-polynomials (Tag 09H0) and definition-separable (09H1). No new-node sources require review because there are no new nodes.

For step 1 I opened def-weil-l-adic-numbers: it explicitly gives the completion construction, completeness, characteristic zero, nonarchimedean valuation and formula for the rational norm. Nontriviality follows by evaluating at ell, whose norm is ell inverse; density follows directly from a rational Cauchy representative of a completion point. Thus I did not use the definition node as if it separately stated an unrecorded analytic theorem. The convergence criterion gives the required rational approximation in a single line, also confirmed by the exact Mathlib density statement read above.

For step 2 I opened def-weil-algebraic-closure and lem-trf-spectral-norm-algebraic-extension. The former explicitly supplies algebraicity of Omega over k. The latter explicitly supplies a genuine extending multiplicative nonarchimedean norm and the distance s(x-y). Its base hypotheses are exactly the properties verified in step 1; finite dimensionality of the whole algebraic closure and completeness of Omega are not required. Nonnegative values belong to the stated norm, not an unproved positivity claim. This gives every norm clause in the item.

For step 3 I opened the algebraic-closure, minimal-polynomial, polynomial-ring and polynomial-root definition statements. The minimal-polynomial node explicitly gives monicity, irreducibility and vanishing, so the proof does not try to extract these from an unrelated separable-extension definition. The polynomial-ring and evaluation statements support the degree-zero contradiction: the only monic constant is 1, and its evaluation is 1. Algebraicity of every x was supplied before invoking the minimal polynomial. This argument also handles x=0.

For step 4 I opened def-pc-separable-polynomial, lem-trf-irreducible-separable-derivative and lem-pc-separable-polynomial-distinct-roots-alg-closed. The derivative definition gives the coefficient n at degree n-1, nonzero since n is positive and k has characteristic zero. The criterion says precisely that an irreducible polynomial is separable iff its derivative is nonzero. The distinct-root leaf really states both exactly n roots and the product of the linear factors, not merely no repeated roots. Its field, monicity, separability and algebraically closed overfield assumptions have all been checked. In particular the much broader separably-generated extension lemma was not used as if it directly stated minimal-polynomial separability.

For step 5 no new theorem is hidden: the root set is finite from step 4, S is a subset, and each distance is strictly positive by the norm's definiteness. I wrote the finite-minimum argument explicitly by successive binary minima, preserving positivity and the lower-bound property at each adjunction. Empty S uses delta=1 and a vacuous universal bound; nonempty S gives an attained positive minimum. This is elementary finite ordering, not an omitted compactness or analytic separation theorem.

I checked the small cases x in k (degree 1 and S empty), x=0 (f=T and delta=1), a quadratic element (one other root, so delta is its single positive distance), and possible equal distances between several distinct conjugates (the distance image may have repetitions, which do not affect the minimum). No uniform lower bound over infinitely many polynomials or roots is claimed. Characteristic zero is used before the separability invocation; the argument is not asserted in inseparable positive characteristic. The extending norm is chosen once for Omega, before quantifying over x, as required.

Against delivery-errors B–E, all new-node requirements are vacuous; the item keeps all imported fields and uses valid TeX, and every citation has a verbatim statement quotation in citations.json. C1/C4 were checked by reading the cited statements as described above; the proof uses no inside-the-proof construction of another node. Every dependency is an existing Mathlib leaf or a definition, so no route replacement is made. The root-distance construction is carried out in the item itself, rather than moved to a new node restating a clause. There is no claim of a finished Lean attachment and no statement correction or unresolved mathematical dispute.

## Unfinished work

None within this stage-1 split. Formal Lean implementation is outside the authorized stage. Delivery remains subject to the required server dry run and independent maintainer review.
