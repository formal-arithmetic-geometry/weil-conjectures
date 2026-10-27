# Q124 stage-1 delivery

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-polynomial-bar-divided-monomial-normalization.json`: item, statement, split. The polynomial normalization is not an exact Mathlib statement; its general homotopy ingredient is the existing Mathlib leaf `lem-sfb-split-simplicial-nondegenerate-homotopy`.
- `citations.json`: one verbatim statement quotation for every node cited in every proof step.
- `report.md`: this report. `searches.jsonl` is the search command's unmodified log.

No new nodes, and no new Mathlib leaves. The local helper `write_split.py` writes only this sandbox and is not a project file.

## Attachments

None. I searched `lean/WeilConjectures/` for the item's exact blueprint tag and for divided-monomial, dividedMonomial, polynomial-bar, and split-simplicial terminology; there is no project declaration stating the whole item. I also searched `lean/Sheaf/` for these constructions. The general Mathlib normalization declaration is already represented in the DAG, so it is cited rather than attached or recreated.

## WANTED

None. This is an explicitly agent-formulated polynomial calculation, with a recorded agent proof origin. The general homotopy theorem already has its exact Mathlib source in the DAG.

## Findings and corrections

The statement is unchanged. The original source place refers to an older blueprint paragraph as if it included a trivial-lattice calculation. I read the current `literature/blueprint/latest/blueprint/sec-six-functors-basics/sk-thm-sf-ctf-stability/sk-thm-sf-ctf-stability-direct-images.proof.md`: paragraph (3) now invokes the open-coefficient theorem and compactification and does not give this algebra calculation. The item source and proof origin now say explicitly that this is the inherited algebraic sub-obligation below that clause, with an agent-written calculation. This is a provenance correction, not a change of unit route. I read the recorded chapter and unit, and the current unit text; none is edited, and this item is not the unit's key statement.

The item had no proof. I supplied the actual dual faces (the endpoint faces are conditional zero-block deletions, not arbitrary endpoint deletion), an operator for every monotone map, the inverse of the zero-insertion splitting, and the signed dual homotopies. Merely citing Dold–Kan would not establish these identifications. No imported field, statement clause, or previous search record was deleted.

## Searches and reuse

I read and retained all inherited search results. Fresh searches of the specific basis-identification question are recorded exactly from this sandbox's `searches.jsonl`: LeanFinder with two phrasings, Loogle, LeanSearch, and grep. All services answered. LeanFinder's general Dold–Kan summands and the second phrasing's divided-power operations do not assert this particular polynomial complex comparison. LeanSearch returned general homotopies and unrelated polynomial normalization facts. Grep located `MvPolynomial.basisMonomials` and `CategoryTheory.SimplicialObject.Splitting.homotopyEquivNondegComplex`; the first is already the polynomial definition's elementary monomial-basis content, and the second is the existing normalization leaf.

I read the normalization leaf's entire statement and Mathlib `AlgebraicTopology/DoldKan/SplitSimplicialObject.lean`, lines 148–175 and 307–312. Its nondegenerate differential is exactly inclusion, alternating differential, then projection. It supplies both homotopies, not just a quasi-isomorphism. I read Stacks `simplicial.tex`, Tag 017P, `definition-split` and `equation-splitting`; that tag defines the required decomposition and supplies no homotopy theorem. I also checked the derived-category localization statement of `def-weil-abstract-derived-category` (Stacks 05RU, `derived-definition-unbounded-derived-category`). No SGA source is used.

Whole-DAG statement searches for polynomial bar, divided monomials, and dualized homotopies found this item and its broader parents, rather than a second node with its statement. `tools/blueprint_refs.py search` was run for `polynomial`, `divided`, `zero block`, and `polynomial bar`; none states this normalization. `ancestor` returns null for this created-node chain, so the existing null ancestor and via list are retained, with an explicit place and `same_as: []`.

## Not duplicates

There are no new nodes. `lem-sfb-split-simplicial-nondegenerate-homotopy` is used for its general theorem; its statement does not construct the polynomial basis or the zero-block splitting. The parent `lem-sfb-rational-polynomial-bar-contraction` also proves the exterior-algebra contraction, which is not claimed here. No clause of the item was moved to a fresh statement-only node.

## Review by Q124

I checked the proof against delivery-errors B–E with the sources and cited node statements open. The proof is an agent expansion, and only its genuinely non-elementary step invokes the existing split-simplicial homotopy theorem. The remaining steps give coefficient formulas or explicit inverse maps and their calculations; none assumes a hidden comparison theorem. Every step is shorter than 2000 characters.

Step 1 uses the statement of `def-weil-pbc-mv-polynomial-ring`: polynomials are finite formal combinations of monomials with the stated multiplication. The coordinate bounds make each multidegree basis finite; factorials are units because the coefficients are rational. The finite double-dual inverse is written as a sum, rather than attributed to an unrelated duality theorem. This also handles the empty tuple and zero-dimensional terms.

Step 2 proves the divided-binomial identity by the displayed coefficient recurrence, then multiplies over the finite coordinate set. It proves preservation of multidegree and the zero-substitution formula directly. Step 3 transposes the resulting individual matrix coefficients; it does not assume ordinary nerve endpoint faces, which would be wrong for this dual basis.

Step 4 uses exactly the functor definition in `def-weil-pbc-simplicial-object`. Its formula applies to every order-preserving map, and composing two maps groups the same intervals. The only endpoint issue is resolved by nonnegativity of exponent vectors: a sum is zero if and only if all summands are zero. This remains true for r=0. Thus the proof establishes functoriality, rather than citing a definition for a theorem asserting simplicial identities. The face-pair cancellation then proves the differential squares to zero; the same polynomial substitution identities hold over arbitrary B, with no field hypothesis needed for that assertion.

Step 5 gives a two-sided inverse on bases, including the unique constant surjection and the all-zero tuple. Since a monotone surjection's increments are zero or one, its repeated positions are recovered uniquely. This verifies precisely the decomposition hypothesis in the normalization leaf; I am not taking a canonical splitting out of the proof of another node.

Step 6 cites `lem-sfb-split-simplicial-nondegenerate-homotopy` for exactly its stated conclusion: the projected differential is a complex and two chain maps have homotopies to both identities. The hypotheses have all been established: R is the commutative ring Q, U is the simplicial module constructed in step 4, V and j are explicit subspaces and inclusions, and every direct-sum decomposition is proved in step 5. On nonzero tuples endpoint faces vanish and internal merged blocks remain nonzero, proving the required formula for the projected differential.

Step 7 needs no general duality theorem. I checked the transpose of each chain-homotopy equation: a degree-one H gives `(H*)^n=(H_{n-1})*`, and the two transposed terms are exactly H*d and dH*. The degreewise evaluation inverse of step 1 identifies the full dual with P_m. No boundedness of U in the chain direction, exactness of infinite duals, or dual of an infinite direct sum is asserted.

Step 8 computes the polynomial inclusion and the cancellation at the first, internal, and last possible zero-block positions, with their actual signs. Hence the no-zero-block polynomial span is a subcomplex and has exactly the stated splitting differential. Step 9 uses `def-weil-abstract-derived-category` only for its explicit localization at quasi-isomorphisms. The proof first checks on cocycles that homotopic maps induce the same cohomology maps. It then separately checks the weight bound and the direct sum using finite polynomial supports.

I tested the small cases by hand. For r=1, m=1, the normalized complex consists of Q in degree one, and d(x)=x_2-(x_1+x_2)+x_1=0. For r=1, m=2, d(x^2/2)=-x_1x_2, agreeing with partial[1|1]=-[2]. For m=0 (including r=0), the unnormalized terms are Q, with differentials 0, identity, 0, identity, and the normalized complex is Q in degree zero only. For n=0, m nonzero both bases are empty; for m=0 the empty tuple is present. The tuple [0|alpha|0] has exactly one nonzero block and is recovered from the surjection [3] -> [1] with values (0,0,1,1). These tests detect the endpoint convention, factorial, sign, and surjection-index issues most likely to invalidate the argument.

Every cited node is read for its statement, and `citations.json` contains matching verbatim text for all four cited occurrences. There is no statement dispute, new unproved auxiliary statement, route change, or incomplete mathematical clause.

## Unfinished work

None within this stage-1 item. Direct delivery follows a successful server dry run; the maintainer's independent mathematical review remains the project's review step.
