Files written:

- dag/nodes/sec-deligne-laumon-general/lem-zl-curve-testing-irreducibility.json: statement node, no new Mathlib leaf; updated to the main-20261015 geometric-fiber/Frobenius-stability formulation.
- citations.json: verbatim citations for every node used by every proof step.
- No new DAG nodes.

Attachments: none.

WANTED: none.

The imported statement was an older compressed formulation. I checked the source declaration and docstring in WeilConjectures/DeligneLaumon/Reduction/RealSheaves.lean (lines 68–115) and the current blueprint node and proof in literature/blueprint/main-20261015/blueprint/sec-deligne-laumon-general/sk-i-dl-general-real/lem-zl-curve-testing-irreducibility.md and its .proof.md. I corrected the statement to introduce the geometric fiber X, the finite point set S, the closed immersion i, and the Frobenius-stability equation exactly as the current blueprint and source describe. The source declaration remains sorry, so it is not an attachment.

## Not duplicates

No new nodes were created. I searched the DAG and both blueprint snapshots for the curve-testing statement, finite quotient cover construction, and the cited Stacks/Bertini tags; only the existing item and its existing dependency nodes matched.

## Review by Q131

I read the complete current item source and the old imported node, then read the full statements of def-wf-fundamental-representation, def-weil-pbc-qbar-category, lem-zl-finite-matrix-irreducibility, and lem-zl-bertini-finite-cover-curve. I also read the generic tool statements thm-galois-fundamental, cor-galois-open-subgroups, lem-galois-finite-etale-connected-object, and lem-galois-transitive; each quote used in citations.json is copied verbatim from those statements.

Step 1 checks that every geometric restriction is encoded by the geometric fundamental representation and that finite coefficient stages are available. Step 2 uses exactly the finite-matrix witness conclusion: a subgroup with the same lattice reduction image remains absolutely irreducible. Step 3 forms the finite quotient from the finitely many open normal kernels and uses the fundamental-group equivalence/open-subgroup classification to obtain the connected finite-etale Galois cover. Step 4 applies the existing Bertini-cover statement with the given dimension, cover, and finite point set; its hypotheses supply smoothness, affine structure, connectedness, and Frobenius descent. Step 5 explicitly converts connectedness of the pullback scheme into a connected Galois-category object before invoking transitivity, so the image of pi_1(C) is the whole regular quotient Q. Step 6 verifies that this gives the same reduction image required by the matrix-witness node for every sheaf. Step 7 checks that the Frobenius-stable immersion descends and that the original Weil descent datum restricts to each pullback. Step 8 separately handles the edge case d = 1 by taking the identity curve and m = 1.

I split the former paragraph-long proof so no step hides an independent comparison or identification. I tested the dimension-one and finite-point edge cases in the statement audit, and ran the required server checks: check_dag and review_split both passed.
