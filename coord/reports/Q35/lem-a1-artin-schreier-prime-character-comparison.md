# Stage-1 report: lem-a1-artin-schreier-prime-character-comparison

1. Files written:

- `dag/nodes/sec-deligne-laumon-a1/lem-a1-artin-schreier-prime-character-comparison.json`: split statement; no Mathlib match.
- `dag/nodes/sec-deligne-laumon-a1/lem-a1-trace-pairing-nondegenerate.json`: statement node; Mathlib leaf (`FiniteField.trace_to_zmod_nondegenerate`, `Mathlib/FieldTheory/Finite/Trace.lean:37`).
- `dag/nodes/sec-deligne-laumon-a1/lem-a1-artin-schreier-trace-cover-map.json`: statement node; no Mathlib match.
- `citations.json`: verbatim statement quotes for every cited node in every item step.

2. Attachments: none.

3. WANTED: none. The Laumon PDF is present at `literature/laumon-transformation-de-fourier_PMIHES-1987-65.pdf`.

4. The imported item had no proof and its statement’s comparison was only described as agent-written. I audited it against Laumon (0.2), p. 135, and (1.1.3), pp. 139–140. The trace-polynomial map is the missing intermediate fact, so I made it an unsplit auxiliary node. The finite-field trace-pairing fact is exactly Mathlib’s `FiniteField.trace_to_zmod_nondegenerate`. I retained the item’s hypotheses and its naturality clause. I searched the whole DAG and blueprint for duplicates; the existing Artin–Schreier character and trace nodes concern the prime-degree construction and do not state this q-to-p comparison.

## Review by Q35

I read the item node, the parent unit `sk-p-dl-a1-middle`, its chapter record, the current main-20261015 blueprint proof for the parent, and Laumon’s displayed formulas (0.2) and (1.1.3). The first item step uses the additive-character definition and the nondegenerate trace-pairing leaf; those statements supply the fixed prime-field character and the injective trace parameterization, and the remaining finite-group character argument is elementary. The second step uses the auxiliary trace-cover statement, whose hypotheses introduce the same finite field, scheme, function, and two covers; it supplies the polynomial identity, translation equivariance, fibre surjectivity, and base-change compatibility. The third step uses that same cover statement and the Artin–Schreier definition: fibrewise pullback is injective, the character eigenspaces are one-dimensional regular-representation summands, and the polynomial construction gives the claimed naturality. I checked the edge case `r=1`, where the trace polynomial is multiplication by `b` and each fibre has one point, and checked that `b ≠ 0` is forced by nontriviality. I also corrected the proof metadata so the character-parametrization step is marked elementary rather than introducing a duplicate node for a clause of the item. Mathlib searches were run for the item and both new nodes with LeanFinder, Loogle, grep, and LeanSearch; their actual outputs are recorded in each node’s `mathlib_searches` and the sandbox search log.

5. What could not be finished: the auxiliary trace-cover comparison remains an unsplit natural-language node because it is not in Mathlib; this is the intended stage-1 boundary.
