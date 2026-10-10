# Stage 1 report: `lem-weil-pbc-smooth-localization-conormal-split`

## Files written

- `dag/nodes/sec-proper-base-change/lem-weil-pbc-smooth-localization-conormal-split.json`: changed the item from `unsplit` to `split` and added a complete three-step proof.
- No new nodes were needed.

## Attachments

None.

## Wanted literature

None. The proof uses the obtained Stacks Project sources `algebra.tex` and `smoothing.tex`.

## Findings

The statement agrees with the consequence of Algebra Definition 00T2 used in the proofs of Smoothing Ring Maps Lemmas 07C6 and 07EZ. The imported node had no proof. Its source note suggests the needed route but does not separate the presentation comparison from the splitting argument.

The split now first applies the existing Jacobi-Zariski quotient node to the presentation $P[x_0]\to A_a$ from Algebra 08JZ. Smoothness of $A_a/R$ kills $H_1$ and makes $\Omega_{A_a/R}$ finite projective. The direct-sum decomposition of 08JZ then transfers injectivity and the cokernel to the localized original conormal map $d_a$. Finally, projectivity splits the surjection to $\Omega_{A_a/R}$, giving both a left inverse to $d_a$ and the claimed direct-sum isomorphism.

Every cited fact is stated by the cited node. The last step uses only the lifting characterization in `def-weil-pbc-projective-module` and elementary direct-sum algebra. No unit-route departure is involved: all cited nodes are in `sk-thm-p1`, and the item is not the unit's key node.

## Review by E1

I checked the statement against Algebra Definition 00T2 and the proofs of Smoothing Ring Maps 07C6 and 07EZ. Step 1 uses the existing 08JZ Jacobi-Zariski quotient statement to identify the localized presentation's conormal map and uses smoothness to obtain the finite-projective differential module. Step 2 transports the direct-sum and injectivity information through localization; Step 3 applies the projective lifting property to split the surjection and writes the resulting direct-sum isomorphism. The cited nodes state these exact interfaces, and the direct-sum algebra is elementary. The item stays on `sk-thm-p1`, has no new node or duplicate, and its statement introduces the localization and conormal objects without relying on a tag for meaning. I checked the zero conormal case and a polynomial smooth algebra as edge cases. Sections A-F are satisfied after this review: one item-only commit, split metadata, no cycle, and no Lean changes.

## Unfinished work

Nothing remains for this Stage 1 item. No Lean was written or compiled.
