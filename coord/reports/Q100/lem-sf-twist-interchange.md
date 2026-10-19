## Worker report

Files written:

- `dag/nodes/sec-six-functors/lem-sf-twist-interchange.json`: repaired the existing split while preserving its statement and route. The former 2272-character step 4 is replaced by four steps: shifted-line evaluation, the finite-level sign calculation, the completed integral tensor-shift comparison, and the final ordinary/completed tensor identification.
- `dag/nodes/sec-six-functors/lem-sf-completed-tensor-shift-right.json`: one new statement-only unsplit node isolating the reduction-tower and mapping-fiber shift comparison required by the repaired step 6. Mathlib searches found no match.
- `citations.json`: 20 verbatim step/node citations, including the new node's statement in step 6.

Attachments: none. The source checkout contains declarations tagged with this blueprint, but they are not sorry-free attachments for this natural-language item; the node remains a stage-1 split.

WANTED: none.

The returned fault was the non-elementary 2272-character step 4. I split its hidden arguments without changing the item statement: step 4 now handles evaluation at the shifted line, step 5 handles the finite-coefficient Koszul sign, step 6 cites `lem-sf-completed-tensor-shift-right` for the completed reduction-limit tensor, and step 7 handles the ordinary/completed tensor comparison identifying the twist. The new node has a self-contained statement, no proof or proof dependencies, the required blueprint ancestry, and recorded LeanSearch, Loogle/LeanFinder, and Mathlib grep searches. I checked for existing DAG and blueprint nodes before creating it; the existing shift nodes concern other pullback/tensor constructions and do not state this completed pro-etale reduction-tower comparison.

## Not duplicates

`lem-sf-completed-tensor-shift-right` vs `lem-sc-derived-pullback-tensor-shift-one`: the existing node concerns a derived pullback tensor shift in the smooth-base-change/picard route; the new node concerns the specified completed integral pro-etale tensor defined by the finite-reduction product mapping fiber, with its explicit signs and cone comparison.

## Review by Q100

I read the current item source in `literature/blueprint/main-20261015/blueprint/sec-six-functors/sk-lem-sf-twist-interchange/lem-sf-twist-interchange.proof.md`, the imported master unit and item records, and the relevant source statements for every cited node. The item statement still has the exact perfectness, coefficient-stage, twist, canonical-arrow, and shifted-dual clauses. The new node's statement was checked against Bhatt--Scholze, Definition 3.4.10 and Lemma 3.4.12(4), together with the project's integral-operation and total-tensor definitions; it introduces all rings, sites, towers, resolutions, shifts, and cone conventions it uses.

For step 1, I checked that `prop-weil-twist-preserves` supplies the rank-one invertible line, inverse twist, and constructibility preservation, while `def-coefficient-twists-detailed`, `def-sf-datum`, and `def-weil-derived-pullback-tensor-hom` supply the coefficient-stage meanings. I also checked the cited `lem-fix-constructible-tensor-completion` statement supplies the ordinary/completed comparison under the verified qcqs hypothesis for the separated finite-type scheme. Step 2 uses exactly the finite-projective hypothesis from `def-weil-site-perfect-complex`, the evaluation isomorphism from `prop-sf-dualizable-hom`, and the operation conventions from `def-weil-derived-pullback-tensor-hom`; its reassociation is the displayed formal composite. Step 3 identifies that composite with the canonical transpose by evaluating both composites and checking the same associator, symmetry, and Koszul coherence; the cited completion comparison supplies the integral identification.

The repaired step 4 uses `def-weil-finite-tor-amplitude` only for closure under shifts and `prop-sf-dualizable-hom` for evaluation at the shifted line. Step 5 is elementary from the cited total-complex differential and shift convention: multiplication by `(-1)^(ri)` gives the chain map, including negative and zero shifts. Step 6 takes precisely the natural completed-tensor shift isomorphism stated by the new node and applies it to `K^vee` and `L`; the cited operation definition verifies these are the specified ambient completed objects and explains the rational/common-stage passage. Step 7 uses the twist definition, the ordinary/completed comparison, and the dual evaluation statement to identify the result with `K^vee(m)[r]`.

I checked hypotheses and edge cases while reviewing the repaired split: `m=0`, negative `m`, `r=0`, negative `r`, `K=0`, `M=0`, and the empty scheme. The completed-tensor node was also checked for the degree convention, transition compatibility, product reindexing, and the cone map `(b,a) ↦ (b,(-1)^r a)`. Every step's `uses` agrees with its citations, every citation quote is verbatim, every cited id exists and is unmerged, and the new node has statement-only content as required. The server-side `check_dag` completed with `OK` before this report was written.
