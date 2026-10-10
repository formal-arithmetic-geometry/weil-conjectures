1. Files written:

- `dag/nodes/sec-proper-base-change/lem-weil-pbc-field-tensor-irreducible.json` (repaired statement split; no new Mathlib leaf).
- `dag/nodes/sec-proper-base-change/lem-weil-pbc-perfect-reduced-tensor.json` (existing statement-only node retained).
- `dag/nodes/sec-proper-base-change/lem-weil-pbc-tensor-finite-type-limit.json` (statement corrected to the exact 00I3 clauses).
- `dag/nodes/sec-proper-base-change/lem-weil-pbc-flat-fibres-irreducible.json` (existing statement-only node retained).

2. Attachments:

- `lem-pc-homeo-pure-insep` is used as a generic tool from another unit; it states the purely inseparable base-change homeomorphism used in Step 1.
- `lem-weil-pbc-finite-type-over-field-prime-intersection-maximal` supplies Jacobson prime/maximal intersection and its explicit in-particular density clause.
- `lem-weil-pbc-closed-point-residue-field-base` supplies the algebraically closed closed-point residue-field isomorphism.
- `lem-weil-pbc-finite-type-noetherian-finite-presentation` supplies finite presentation of the finitely generated algebra over the Noetherian field.

3. WANTED: none.

4. Repairs: deleted the false `lem-weil-pbc-p-ring-map-homeomorphism` node, whose statement omitted the locally nilpotent kernel and power-in-image hypotheses of 0BRA; deleted duplicate Jacobson and Nullstellensatz nodes; corrected the finite-type-limit node to 00I3(1) and (2). Step 1 now applies the existing generic pure-inseparable homeomorphism to Spec(K), Spec(L), and Spec(K tensor_k L), and explicitly notes the minimal-prime bijection. Step 2 introduces R and S and explains why their reductions are fields. Step 3 uses clause (2) for a nonzero zero-divisor and observes that subalgebras of domains are domains. Step 4 checks irreducibility of Spec(R'), flatness from S' being a kbar-vector space, finite presentation from finite type over the Noetherian field, the fibre identification, Jacobson density, and irreducibility because S' is a domain. Step 5 transfers minimal primes back using Step 1.

## Review by C1

I reread `literature/stacks-project/algebra.tex`, Algebra Lemma 00I7, together with 00I3, 00I6, 00G1, 00FV, and the cited Mathlib-backed DAG statements. The item statement remains the 00I7 assertion. The finite-type-limit statement now reproduces the two alternatives of 00I3 exactly. The pinned Mathlib checkout used for searches was `/home/ubuntu/weil-conjectures-slopmaster2/.lake/packages/mathlib/Mathlib`: `RingTheory/Jacobson/Ring.lean:666` contains `isJacobsonRing_of_finiteType`, `Ring.lean:73` contains the prime-intersection characterization, and `AlgebraicGeometry/AlgClosed/Basic.lean:33,46` contains the closed-point residue-field isomorphism and its inverse compatibility. The finite-presentation node was checked against its Stacks and Mathlib search records.

For Step 1, the cited `lem-pc-homeo-pure-insep` statement says exactly that base change along a purely inseparable field extension is a homeomorphism; the minimal-prime transport is the elementary generic-point consequence. Step 2 cites the reduced-tensor statement and checks the one-prime reduction hypothesis. Step 3 cites both exact 00I3 alternatives, including the nonzero zero-divisor clause, and the domain observation is elementary. Step 4 cites the closed-point residue-field statement, the Jacobson in-particular clause, finite-type implies finite presentation, and the flat finite-presentation irreducible-fibres criterion; each cited statement contains the fact used. Step 5 cites reducedness and the same homeomorphism tool for the transfer back to K and L; nonzeroness of a tensor product of nonzero vector spaces and the definitions are elementary.

I checked small cases `K=L=k`, a rational function extension, and a purely inseparable extension. The searches recorded in the retained unsplit nodes and item were rerun against the pinned checkout; the incorrect `/home/ubuntu/weil-src-slopmaster2` path was removed. The returned points E2/C4, C5, B-searches, B2/C4, and E1/E4 are addressed above.

5. Nothing remains unfinished.
