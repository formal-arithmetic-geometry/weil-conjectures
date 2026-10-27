## Files written

- `dag/nodes/sec-trace-formula/lem-trf-standard-cotangent-boundary-cokernel.json`: statement node, now split into six elementary calculations. Mathlib searches found no exact declaration or one-line specialization. No new nodes and no new Mathlib leaves.
- `citations.json`: verbatim statements for both node citations in step 1.
- `searches.jsonl`: the required search command's records, retained unchanged.

## Attachments

None. I searched `lean/WeilConjectures/` for the exact blueprint tag and the item id, standard cotangent/boundary terminology and simplicial polynomial terminology. No project declaration states this calculation. Imports of Mathlib's StandardSmoothCotangent are not proofs of it.

## Literature

No WANTED sources. I read `literature/stacks-project/cotangent.tex`, Tag 08RB, label `lemma-relation-with-naive-cotangent-complex`, and Tag 08UP, label `remark-explicit-comparison-map` (lines 1938--2014 of the local source). 08RB states the canonical truncation comparison; 08UP writes the downward map using the difference of the two faces and the three-term alternating next differential. The source omits verification of the explicit comparison. The six-step boundary-cokernel argument here fills that gap and is honestly recorded with `proof_origin.by = agent`; I do not treat the omitted verification as an external theorem being applied.

I also read the newest blueprint's `sec-trace-formula/sk-i-curve-zero/lem-trf-local-term-locality.md` and its proof, the chapter and unit records, and the item's ancestor chain/place. This item is a supporting algebra calculation in the previously extracted lci comparison branch, not the unit's main proposition. No chapter or unit route was altered, and no unit realization field is owned by this item.

## Corrections and unfinished work

The statement was unchanged. Its assumption that the face-difference map exists and annihilates the boundary is used as an assumption, not reproved by citing an unrelated definition. The important calculation keeps the zero polynomial index `0` distinct from the polynomial variable `X_0`: neither `t_0` nor `t_{2X_0}` may be dropped. There is no statement dispute, source error, or unfinished mathematical part.

## Searches and reuse

The sandbox initially contained no item node or report, only dispatch marker files. The repository item's earlier searches were retained. I ran the required search command for this item's statement: two LeanFinder phrasings, LeanSearch, Loogle `Ideal.Cotangent`, and the source grep `cokernel|cotangentEquiv|H1Cotangent` in `RingTheory/Extension`. All services responded successfully in this session; the earlier unavailable LeanSearch entry remains historical and unchanged. I read the returned types and the actual candidate source: `Ideal/Cotangent.lean:43--80`, `Extension/Cotangent/Basic.lean:339--344`, `Algebra/Module/Presentation/Differentials.lean:51--86,140--178`, and `Extension/Presentation/Basic.lean:520--522`. Ideal.Cotangent defines the target quotient; H1Cotangent is a kernel in the naive complex; presentation.differentials presents the differential module. None identifies this second-boundary cokernel with the target together with this inverse by a one-line specialization.

I searched the whole DAG for 08UP, 08RB, conormal and polynomial differential terminology, and searched the imported blueprint with `tools/blueprint_refs.py search` for `cotangent`, `boundary cokernel` and `08UP`; I ran the ancestor command too. The two blueprint cotangent hits are the geometric ancestor and a tangent-space/derivation node, not this algebra lemma. The existing standard-chain-projection node proves well-definedness and boundary annihilation, which are already assumptions here; citing it would be unnecessary. The naive-model ancestor uses this item and is not cited back. No new node is justified: each identity below is a substitution into the displayed boundary and the derivation laws, and quotient descent is written explicitly.

## Not duplicates

No new nodes. This delivery creates neither an elementary auxiliary node nor a restatement of a clause of the item.

## Review by Q134

I checked the statement against the explicit objects and signs of 08UP and the low-degree target of 08RB. The standard second-boundary formula is used with the stated signs, and every polynomial face in steps 2--4 is computed with the actual maps `Y_p` sent to `p` and `X_{epsilon(p)}`. The hypotheses are arbitrary commutative rings throughout. There is no finite-generation, nonzero-ring, smoothness, or regularity hypothesis hidden in the argument. There are no new statements needing separate source or hypothesis review.

Step 1 cites exactly `def-weil-pbc-kahler-differentials` and `def-weil-pbc-mv-polynomial-ring`. I opened both statements. The first explicitly states additivity, the Leibniz rule, vanishing on the base ring and the free-symbol quotient construction; these give all the derivation and generation claims used. The second explicitly describes elements as finite linear combinations of monomials; this justifies expansion and repeated Leibniz reduction to variable differentials. The relation D(f) = t_{d0 f} - t_{d1 f} follows directly from the assumed formula for the boundary, not from either definition. The matching quotes in citations.json are the full verbatim statements so all those clauses can be checked.

Step 2 uses only the relation derived in step 1: first put f = Y_p to kill the symbols t_{X_b}, then put f = Y_p - Y_{X_b}. The latter has faces p - X_b and zero, and derivative class t_p. Surjectivity needed for all b is explicit: epsilon(X_b) = b. No extra node is needed for these substitutions.

Step 3 compares the substitutions f = Y_h + Y_k and f = Y_0 + Y_0, with h,k in I. Both second faces are exactly 2X_0, and the correction is t_{2X_0} = -t_0. This proves additivity rather than presupposing that the map on polynomial indices is additive. This was the main possible gap I checked: treating p as a polynomial index does not make t_p additive automatically.

Step 4 compares Y_r Y_h with Y_r Y_0. The coefficient of t_r is zero in both derivatives because epsilon(h) = epsilon(0) = 0. Both second faces are X_{epsilon(r)} X_0. Their cancellation gives s(rh) = epsilon(r) s(h) for all r in R, not just for base-ring scalars. Thus the desired R-action really factors through B.

Step 5 uses the already proved additivity and scalar formula to kill products in I and then all finite sums of such products. It explicitly checks representatives in I/I squared, lifts b to X_b, and checks independence of the lift using I squared. This is quotient descent from the definition, not an invocation of an uncited tensor/exactness theorem.

Step 6 uses only the item's assumption rho partial2 = 0 to form the descended map. I checked both composites: rho(t_h - t_0) is [h - X_0] - [-X_0] = [h], and the other composite on t_p is t_{p-X_b} - t_0 = t_p by step 2. The classes h - X_0 and -X_0 both belong to I. Generation was proved in step 1, so equality on these generators and linearity suffices.

For small cases I checked h = 0, k = -h, r in I, the identity map A to A (whose polynomial presentation still has a nontrivial kernel), a nonsmooth quotient with nilpotents, characteristic two, and the zero target ring. The argument never divides by 2, never identifies X_0 with the zero polynomial, and never identifies A[B] with B even for the identity ring map. For r in I the scalar formula is exactly what forces products to die. For the zero target all B-modules are zero, and all formulas remain valid. No step exceeds 2000 characters; each consists of polynomial substitutions or direct quotient calculations with the previous steps. I checked delivery-errors B through E: no new-node form issues, no hidden theorem from a source proof, no relabelled clause, no circular dependency, and no omitted comparison or compatibility argument.
