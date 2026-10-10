# Stage-1 worker report

1. Files written:

- `dag/nodes/sec-picard-framework/lem-sc-finite-type-nonclosed-closure-closed-points.json` — item split into two proof steps.
- `dag/nodes/sec-picard-framework/lem-sc-positive-dimensional-locally-algebraic-closed-points.json` — statement-only unsplit node; Mathlib searches found no match.

2. Attachments: none. No sorry-free source declaration carries the item tag or its exact statement.

3. WANTED: none. The cited source text is represented by the Stacks Project tags recorded in the nodes.

4. Review

## Review by C1

I read the item record, its blueprint ancestor `lem-sc-degree-2g1-very-ample`, the Picard Framework chapter/unit records, and the surrounding proof in the already reviewed `lem-sc-point-tangent-separation-closed-immersion`. The item source is Varieties, Tags 0478 and 0A21. I searched the whole DAG and both Lean source checkouts for the item tag and for declarations about nonclosed points, closure, Jacobson schemes, and infinitely many closed points; no exact declaration or existing node was found. The existing `lem-sc-dim0-finite` and `lem-sc-dimension-locally-algebraic` nodes were read, but neither states the needed positive-dimensional infinite-closed-points conclusion, so I created `lem-sc-positive-dimensional-locally-algebraic-closed-points` as a statement-only node after recording LeanSearch, LeanFinder, and Mathlib-source searches.

Step 1 is elementary: the closure of a singleton is irreducible and closed, a nonclosed point has a strict specialization in its closure, and that strict chain gives positive Krull dimension. Step 2 cites the new node verbatim; its hypotheses match the field, locally finite-type scheme, irreducible closed subset, and positive dimension established in step 1. `citations.json` contains the exact statement quote for that citation. I checked the edge cases: for a closed point the hypothesis fails, while for the generic point of `A^1_k` the closure is all of `A^1_k` and has infinitely many closed points.

5. What was corrected: the imported proof was empty. I supplied the missing proof steps and proof dependencies, filled the blueprint split report, and added the missing non-elementary statement node rather than treating the infinite-closed-points assertion as elementary.

