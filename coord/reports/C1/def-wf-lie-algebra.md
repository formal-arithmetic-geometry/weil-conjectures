Files written:

- `dag/nodes/sec-algebraic-groups-lie-algebras/def-wf-lie-algebra.json`: existing item, classified as a Mathlib leaf.

Attachments:

- None. No sorry-free project declaration carries the full item under the blueprint tag.

WANTED:

- None.

What was checked:

- The item source `literature/blueprint/master/blueprint/sec-algebraic-groups-lie-algebras/sk-d-lie/def-wf-lie-algebra.md` explicitly identifies this bundle as existing Mathlib material. I read the corresponding Mathlib source declarations in `Mathlib/Algebra/Lie/Basic.lean`, `Ideal.lean`, `Solvable.lean`, `Quotient.lean`, and `OfAssociative.lean`.
- `LieRing` and `LieAlgebra` state the additive bracket structure, scalar compatibility, alternating/self-bracket and Jacobi/Leibniz law; `LieIdeal` is the Lie-submodule ideal abbreviation; `derivedSeriesOfIdeal` and `derivedSeries` give the derived sequence; `IsSolvable` and its `isSolvable_iff`/`mk` API give termination; the quotient file supplies the quotient Lie algebra; `LieModule` supplies Lie representations and `LieModule.toEnd` supplies the endomorphism representation. These declarations cover each clause of the item, one declaration per clause.
- I searched the project source for `(blueprint: def-wf-lie-algebra)` and found no project declaration to attach. I also checked the existing DAG for duplicate nodes and found no alternate statement node. The item has no proof steps because it is a Mathlib leaf, so `citations.json` is empty. I recorded `def-wf-algebraic-representations` as the statement dependency because the item uses the representation notion, and marked the `sk-d-lie` unit realization in the sandbox unit record for the DAG route.
- I ran LeanFinder, Loogle, grep, and LeanSearch searches in both the required broad and follow-up phrasings. LeanSearch was unavailable and is recorded as unavailable; the grep and LeanFinder results were checked against the source lines above. Small cases (the zero Lie ideal and the zeroth derived series term) are covered directly by Mathlib's definitions and do not change the meaning of the item.

## Review by C1

I checked the item statement clause by clause against the Mathlib sources listed in `mathlib_match`, including the hypotheses supplied by the typeclasses. The structure classes in `Basic.lean` provide the bracket laws, the ideal abbreviation in `Ideal.lean` gives exactly the stated ideal notion, and the solvability file defines the derived sequence and finite termination. The quotient and representation clauses are supplied by the quotient and `LieModule` APIs, with `LieModule.toEnd` matching the adjoint/endomorphism construction. Since every clause is already stated by Mathlib and there is no project proof to split, no new nodes or proof citations were needed. I also checked that the representation dependency and unit realization are present; the statement itself was retained.

What could not be finished:

- Nothing. The delivery dry run passed with the unit realization included.

## Second reading by C1

- Item statement: checked every clause against the blueprint definition and the cited Mathlib declarations in `Basic.lean` (61-99), `Ideal.lean` (46), `Solvable.lean` (57-71, 261-275), `Quotient.lean` (163), `OfAssociative.lean` (192-203, 230), and `Semisimple/Defs.lean` (33); verdict: retained as a Mathlib leaf, with the direct-definition clauses recorded explicitly in `mathlib_match`.
- Proof steps: none exist because this is a definition classified as a Mathlib leaf; verdict: no uncited proof argument or citation quote is required.
- New nodes: none; verdict: no child node was introduced, so B1-B7 and duplicate-node checks are vacuous.
- Edge cases: checked the zero Lie ideal and zeroth derived-series term against `derivedSeriesOfIdeal_zero` and the bottom solvable instance; the definitions remain valid for the zero representation and for one-dimensional/zero vector spaces.
- Changes made: removed the unrelated `def-wf-algebraic-representations` statement dependency; corrected and expanded the declaration/file/line coverage for the quotient, faithful, irreducible, and adjoint clauses; documented the second reading and the checked edge cases.
