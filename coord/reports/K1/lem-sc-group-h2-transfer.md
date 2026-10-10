Files written: `lem-sc-group-h2-transfer` (split); `lem-sc-group-h2-transfer-transfer-identity` (unsplit statement, no Mathlib match).

Attachments: none.

WANTED: none.

The imported item was unsplit even though its proof uses the non-elementary restriction-corestriction identity. I added one strictly more general helper node for all cohomological degrees; I did not create a child that merely restates the item's degree-two conclusion. The source blueprint is agent-written and is cited accordingly. The helper's Mathlib searches found only first-degree restriction and general group-cohomology map declarations, with no transfer identity.

## Review by K1

I read the item's node, the `sk-prop-h2` unit, the `sec-curve-estimates` chapter, the existing `lem-sc-group-cd-one` proof, and the previous E1 report describing the first proof paragraph. The item's statement agrees with that paragraph: finite discrete continuous ell-primary coefficients, an open subgroup of index prime to ell, degree-two vanishing on the subgroup, and the restriction-corestriction conclusion. The new helper states the transfer identity for every degree and finite discrete continuous module, so it is strictly more general and introduces all of its objects.

Step 1 cites the helper verbatim for the restriction-corestriction composite and specializes q=2. Step 2 cites no node because it is a short calculation from the continuous-cochain definition: a power of ell annihilates the coefficient module and hence the cochain complex and its cohomology; Bezout with the prime-to-ell index then proves injectivity. The hypotheses checked are that H is open (so the index is finite), H^2(H,M)=0 makes restriction zero, and the index is coprime to ell. I checked the edge cases H=G and M=0, where the argument gives the zero group immediately.

For the new helper I searched the whole DAG and source tree for transfer/corestriction statements before creating it. Its statement is only a statement, with no proof sketch, and records LeanSearch as unavailable rather than as a false no-match; LeanFinder, Loogle, and Mathlib grep returned only unrelated groupCohomology functoriality declarations. The citation quote is copied verbatim from the helper statement.
