1. Files written:

   - `dag/nodes/sec-picard-framework/lem-pc-affine-surjective-structure-map-closed-immersion.json`: statement, split proof, and Mathlib searches; no new nodes.
   - `citations.json`: verbatim statement excerpts for all proof citations.

2. Attachments: none.

3. WANTED: none.

4. Nothing was wrong with the item statement. The imported proof was empty, so I supplied the missing argument. The source route is Morphisms Tags 01QO and 01SA, with the sheaf criterion from Tags 007U and 0H7H. The existing DAG node `lem-weil-pbc-locally-surjective-iff-stalks` supplies the stalk-to-local-surjectivity fact, and `lem-weil-pbc-closed-immersion-affine-cover-criterion` supplies the affine-cover conclusion; no duplicate nodes were created.

5. No unfinished mathematical part remains.

## Review by E1

I read the item statement and its cited Stacks sources (Morphisms 01QO/01SA and Sheaves 007U/0H7H), and checked that the hypotheses are exactly an affine morphism and surjectivity of every structure-map stalk. I read both cited DAG statements in full. Step 1 uses precisely the existing node's equivalence between sheaf-local surjectivity and surjectivity on all stalks, then specializes it to the structure sheaf map. Step 2 uses precisely the affine definition to make each inverse image of an affine open affine; this is the only elementary step. Step 3 uses precisely the existing affine-cover criterion's converse, whose statement says affine inverse images plus surjective section maps imply a closed immersion. I verified that Step 1's local lifting gives surjectivity of the ring map on each affine open, and that the affine opens cover the target. I searched the whole DAG and blueprint for duplicate statements before deciding that no new node was needed, and searched Mathlib by LeanSearch, Loogle, and source grep; Mathlib has only the affine-section formulation, so the item remains a split statement rather than a Mathlib leaf. The small edge case of an empty target is covered vacuously by the affine-cover criterion.
