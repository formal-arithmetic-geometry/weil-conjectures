# Delivery report

1. Files written:
   - `dag/nodes/sec-curve-estimates/lem-sc-zero-dim-noetherian-affine.json` — item, statement split; no Mathlib match.
   - `dag/nodes/sec-curve-estimates/lem-sc-zero-dim-noetherian-finite-discrete.json` — new statement node; no Mathlib match.
   - `dag/nodes/sec-curve-estimates/lem-sc-finite-discrete-separated-affine.json` — new statement node; no Mathlib match.

2. Attachments: none. No sorry-free declaration in the slopmaster2 source states the item exactly.

3. WANTED: none.

4. What was checked and corrected: the imported item had no proof. I checked the source route in Properties Lemmas 0AAX and 0CKV and split its argument into the finite-discrete topological conclusion, the separated finite-discrete affineness criterion, and the final definition-level ampleness check. The first step cites the existing `lem-weil-pbc-noetherian-scheme-closed-subsets-minimal` node and the new 0AAX node; the second cites the new 0CKV node; the third uses only the definitions of affine scheme, invertible module, and ampleness. Both new nodes are statement-only as required for unsplit nodes, with independent LeanSearch, LeanFinder, and Mathlib-source searches recorded. The empty scheme case is covered explicitly, and the singleton/finite-discrete cases were checked against the definition of ampleness using the global section 1.

5. What I could not finish: no independent source files were available in this checkout beyond the Stacks citation index, so the review follows the cited Stacks tags and the imported blueprint text.

## Review by M1

I read the item source references to Properties Lemmas 0AAX and 0CKV and compared each hypothesis with the item: locally Noetherian plus quasi-compact gives the Noetherian underlying space, the topological dimension bound is exactly `dim Y <= 0`, and separatedness and quasi-compactness are retained for 0CKV. The first new node states the 0AAX finite closed-point/discrete-space conclusion; the second states the final 0CKV affineness conclusion with all hypotheses introduced. The item proof's first step uses the existing Noetherian-topology node and the first new node, the second uses the second new node, and the last is elementary from the definition of ampleness (the section 1 has nonvanishing locus all of the affine scheme). I searched the DAG and blueprint before creating both nodes; no existing node stated either fact for arbitrary Noetherian schemes. I tested the empty scheme and a finite disjoint union of affine points as edge cases. The only correction was adding the existing Noetherian-topology dependency, which the initial split had used implicitly.
