# Worker report: lem-wf-real-semisimplification

## Files written

- `dag/nodes/sec-purity-real-sheaves/lem-wf-real-semisimplification.json`: existing statement, split into five steps; no exact Mathlib match.
- `citations.json`: thirteen verbatim statement excerpts, one for every step/node pair.
- `report.md`: this report. Search provenance is in `searches.jsonl`.

New nodes: 0. New Mathlib leaves: 0.

## Attachments

None. I searched the provided read-only slopmaster2 project for the item tag, semisimplification, semisimple, and real/characteristic-polynomial terminology. The calculation appears as a local `have hcharpoly` inside `AlgebraicGeometry.WeilGroup.isPunctuallyPure_subquotient_of_isReal`, Purity.lean around lines 735–743. That larger theorem concludes purity of a composition factor, assumes an affine smooth curve and additional hypotheses, and does not itself state this item. `IsReal.exteriorPower_of_charpoly_eq` assumes equality of characteristic polynomials rather than proving it for semisimplification. Neither is an attachment. No project declaration was found stating all clauses of the item.

## Literature and searches

WANTED: none. The argument follows the existing blueprint, so proof_origin remains `by: agent`; it is not attributed to a human-written source. I read both the old source node and the current main-20261015 statement and separate proof file, as well as the chapter and sk-r-real-linear unit. Their filtration/determinant route agrees. No SGA source is used.

I ran LeanFinder twice, first for the sheaf assertion and then for the more general representation assertion; Loogle for representation semisimplification; LeanSearch for preservation of characteristic polynomials under semisimplification; and two Mathlib grep searches. All queries and actual results are in searches.jsonl and the item. The first LeanFinder query returned Witt-vector isocrystals, the second representation characters. LeanSearch returned conjugation invariance, characters of isomorphic representations, invariant polynomials, and semisimple endomorphisms. None states this sheaf assertion or the equality for an arbitrary composition filtration. The relevant grep hits `LinearMap.charpoly_prodMap` and `LinearEquiv.charpoly_conj` were read at Mathlib/LinearAlgebra/Charpoly/ToMatrix.lean:63 and :76. They cover only ingredients. The item is consequently not a Mathlib leaf.

## Problems found and repaired

The imported single paragraph chose a composition series citing only its definition, used the exact sheaf/representation correspondence without citing its theorem, and left the direct-sum determinant comparison implicit. I added the already-existing existence theorem and exact equivalence, and computed the determinant for the direct-sum partial-sum filtration using the same existing filtration theorem. I added the definition nodes for semisimplification and iota-reality to stmt_deps. The statement itself is unchanged; no statement dispute is necessary. I removed the unnecessary punctual-weights citation: the needed local-polynomial identity is exactly the statement of p-real-operations, and reality and its coefficients are defined by def-wf-iota-real.

## Not duplicates

There are no new nodes. Searches over the entire DAG and `tools/blueprint_refs.py search` for semisimplification and composition series found the existing composition-series existence, semisimplification definition and exact sheaf-representation equivalence; I reused them. No other blueprint node states the whole assertion in another form, so same_as is empty. In particular lem-mg-semisimplification-independent is independence up to representation isomorphism, not the item. No source tags have been duplicated.

## Review by Q32

I read the main-20261015 item and proof, the old source proof, and each cited node's full statement, not just its title. The source and delivered statement both assert preservation of all local polynomials and iota-reality of the semisimplification of the same lisse Weil representation. The chapter and unit keep the finite-dimensional linear-algebra route; this delivery uses the unit's p-linear-filtration and local-polynomial route. There are no new node statements to source or test.

Step 1 uses def-wf-monodromy-data for the Weil representation, lem-mg-composition-series-exists for existence when V is nonzero, and def-mg-weil-composition-series for the Weil-stable terms and simple quotients. I checked that the existence node explicitly excludes V=0; the delivered proof handles V=0 separately using the empty direct sum and determinant 1. Thus no stronger existence statement has been silently assumed.

Step 2 uses prop-wf-weil-sheaf-representation-equivalence, whose statement explicitly says exact tensor equivalence and that subobjects, quotients and subquotients match in both directions. That is the needed assertion, not merely a definition of the fundamental representation. It supplies the lisse quotient sheaves corresponding to Q_i. The semisimplification node explicitly defines the direct sum of these quotients. Finite biproduct preservation under an equivalence follows directly from the universal properties; no extra sheaf exactness or stalk theorem is assumed here. The same base curve and coefficient representation are used on both sides.

Step 3 uses p-real-operations for its displayed identity P_x(F,T)=det(1-T rho(F_x)|V), def-mg-weil-composition-series for Weil stability, and p-linear-filtration for exactly its displayed determinant product over graded pieces. I checked finite dimensionality, a finite invariant filtration and a linear endomorphism over the same coefficient field. A local Frobenius element is a Weil-group element by p-real-operations, so it preserves every term of the composition series; there is no assumed Frobenius-stable splitting. The quotient action is the quotient representation's defining action.

Step 4 uses the semisimplification definition for S, the direct-sum clause of def-real-weil-representation-operations for the componentwise action, and p-linear-filtration again for the partial sums of S. I wrote the coordinate projection with kernel S_{j-1} that identifies the graded action with Q_j(g_x), rather than claiming an unexplained transport. p-real-operations converts this representation determinant into the sheaf's local polynomial. Both sides equal the same finite product, which proves equality. No claim that an individual composition factor is real is used. The argument applies to every choice of composition series, so no extra independence theorem is necessary.

Step 5 is elementary substitution in def-wf-iota-real: equal polynomials have equal coefficients after applying iota, and those coefficients are real for F by hypothesis. I read the definition's actual real-coefficient condition. It concerns the whole polynomial, so there is no assertion that reality passes separately to subquotients.

For edge cases I checked the zero representation (empty product 1), a rank-one representation (one quotient and identical action), a split direct sum, and a nonsplit two-dimensional extension with Frobenius matrix [[a,b],[0,d]]. The last case has local factor (1-aT)(1-dT), identical to the diagonal semisimplification even when b is nonzero or a=d. This confirms that semisimplicity of the local Frobenius, distinct eigenvalues and splitting of the original extension were never used. Pairing nonreal conjugate eigenvalues also shows why the proof must transfer the whole real polynomial, rather than declare each simple factor real. All five steps are below 2000 characters; the only comparison, the direct-sum associated graded, is the explicit coordinate projection argument from the definitions. Every non-elementary input is cited, and every step/node pair has its own verbatim quote in citations.json.

I checked delivery-errors B–E: no new unsplit claims or duplicate notions, no clause moved into a new node, no citation of a proof in place of its statement, no unrecorded search, no hidden stronger hypothesis, no change of object or coefficient category, and no route change. The concrete corrections are the existence/equivalence citations, the second filtration determinant computation and the zero case described above.

## Unfinished work

None in the requested stage-1 split. Server dry-run and delivery results are recorded below after validation.
