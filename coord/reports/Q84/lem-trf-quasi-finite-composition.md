1. Files written:

- `dag/nodes/sec-trace-formula/lem-trf-quasi-finite-composition.json`: item, split, no new nodes, Mathlib candidate rejected as a nonmatching predicate.
- `citations.json`: verbatim statement excerpts for every cited node in every proof step.

2. Attachments: none. No sorry-free declaration in the read-only WeilConjectures source states this item; the only related source declarations concern other quasi-finite notions or downstream applications.

3. WANTED: none. The Stacks source and the current blueprint ancestor are present locally.

## Review by Q84

I read the imported item and the Stacks proof at Algebra Tag 00PO (algebra.tex lines 30342–30360), together with the finite-type composition lemma around lines 540–594 and the isolated-fibre criterion Tag 00PK. I also read the statement of every cited DAG node: the finite-type definition, the affine-spectrum definition, the fibre-ring prime correspondence, and the affine ring-map quasi-finite-at-a-prime definition. Step 1 explicitly reuses finite algebra generators to prove finite type of the composite. Step 2 fixes an arbitrary prime of C, verifies its contractions q and p, and uses the isolated-point definition plus the fibre-prime correspondence and Zariski topology to obtain principal-open witnesses b and c. Step 3 checks contractions carefully: a prime of C over p avoiding the image of b contracts to q, and avoiding c then forces it to be r; hence the composite has an isolated fibre point. The hypotheses that both original maps are finite type and quasi-finite at every target prime are used exactly where the item states them. I searched the DAG and blueprint for duplicate composition or isolated-fibre statements and found no statement that subsumes this item. Mathlib searches found `RingHom.QuasiFinite.comp`, but that declaration uses Mathlib's module-finite fibre predicate, so it is only a candidate and cannot close this DAG node under the project's B8 rule. I tested the argument on identity maps, field extensions, and the zero ring; the contraction argument remains valid, with empty fibres handled vacuously.

5. What could not be finished: nothing.
