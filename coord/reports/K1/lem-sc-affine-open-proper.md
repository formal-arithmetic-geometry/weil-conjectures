# lem-sc-affine-open-proper

## Files written

- `dag/nodes/sec-curve-estimates/lem-sc-affine-open-proper.json`: split statement; its proof now has four sourced steps. The Lean declaration `AlgebraicGeometry.IsConnectedCurve.isAffine_of_ne_top` at `WeilConjectures/AlgebraicGeometry/Curve/Compactification.lean:261` has `sorry`, so this is not an attachment.
- `citations.json`: verbatim passages from each cited node's statement, keyed by proof step.
- No new nodes or Mathlib leaves. Existing nodes state every non-elementary input used here.

## Attachments

None.

## Wanted

The blueprint and Stacks source trees have not been regenerated in this read-only repository. I checked the imported blueprint proof in the item and Stacks Tags 09ND and 0AYY on the Stacks site; the cited existing nodes record the other source places. The source copies listed in `literature/LIST.md` are wanted locally for a line-by-line source audit.

## Corrections

The imported proof inferred dimension zero of the boundary without a citation. I instead use the existing curve-local-rings statement to show each boundary point is closed and the Noetherian closed-points lemma to obtain finiteness. The imported citation to principal-divisor degree alone did not state `deg O(D) = deg D`; the definition `def-sc-pic0` does. The empty open is treated explicitly.

## Unfinished

None in this one-level split. The ten cited nodes retain their own statuses and proofs.

## Review by K1

I read the item's imported proof and its Lean declaration and docstring; the latter is still `sorry` and has the same mathematical statement. I checked Stacks Varieties Tag 09ND for the finite-boundary argument and Tag 0AYY for degree of an effective Cartier divisor, and checked the item against its blueprint statement as recorded in the DAG. No new node was made, so the B1-B8 new-node checks and Mathlib-leaf claims do not arise. I searched the full DAG and `blueprint_refs.py` by the boundary, divisor degree, and affine-complement concepts and found existing statements; the item's blueprint `same_as` search found no duplicate.

Step 1 uses `lem-sc-smooth-connected-curve-local-rings`, whose statement explicitly says a smooth connected curve over algebraically closed `k` is Noetherian integral and every non-generic point is closed, and `lem-sc-noetherian-closed-points-finite`, whose statement makes a closed set of such points finite. Properness supplies finite type here through `def-sc-curves`; nonempty `U` contains the generic point. The empty case is `Spec(0)` and does not use a geometric lemma. The test cases `U=empty`, `U=C` (excluded), and `U=C` minus one closed point give, respectively, an affine empty scheme, a failed hypothesis, and a one-point boundary.

Step 2 uses the exact divisor and degree formula stated by `def-sc-divisor`, the finite-sum Cartier conclusion stated by `lem-sc-point-cartier`, and the definition in `def-sc-effective-cartier-divisor`. All points of `S` are closed by step 1; `S` is finite and nonempty, so the divisor exists and its coefficient sum is positive. For `|S|=1`, the degree is one; repeated points cannot occur because `S` is a set.

Step 3 uses the isomorphism `D -> [O_C(D)]` stated by `lem-sc-divisor-class-curve`, the exact degree identity stated by `def-sc-pic0`, and `lem-sc-deg-principal-zero` only for the stated well-definedness of that degree. The proper, smooth, connected and algebraically closed hypotheses in `def-sc-pic0` are precisely the item's hypotheses. This corrects the imported mismatch between a principal-divisor theorem and the line-bundle degree identity.

Step 4 uses `lem-sc-positive-degree-ample` for its stated positive-degree implication and `lem-sc-ample-complement-affine` for its stated Cartier-divisor complement theorem. The first receives the invertible sheaf and positive degree from step 3; the second receives the proper scheme, effective Cartier divisor from step 2, and ampleness from the first. The support of the sum is `S`, so the open complement is exactly `U`. I checked that no cited node is used for an assertion found only inside its proof, that the off-unit nodes are declared as tool uses, and that no newly created statement or node cycle is introduced.
