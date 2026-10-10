1. Files written:

   - `dag/nodes/sec-curve-estimates/lem-weil-pbc-ringed-site-injective-module-injective-presheaf.json`: statement, two proof steps, citations, and split metadata; no Mathlib leaf.
   - `dag/nodes/sec-curve-estimates/lem-weil-pbc-ringed-site-module-sheafification-exact.json`: new statement-only child; Mathlib searches found ingredients but no exact theorem for arbitrary ringed sites.

2. Attachments: none.

3. WANTED: none.

4. The imported item was unsplit. The existing `lem-weil-pbc-sheafification-exact` node is only for abelian presheaves (and the constant-ring module node is not a statement for modules over a sheaf of rings), so I created the precise ringed-site module sheafification statement instead of citing an inapplicable specialization. The generic preservation result is already the reviewed Mathlib leaf `lem-sp-right-adjoint-preserves-injectives`.

5. Nothing remains unfinished in the split; the new exactness fact is intentionally statement-only for a later worker.

## Review by K1

I read the item source, Stacks sites-cohomology Tag 03FB, and its cited adjunction argument through Homology Tag 015Z and Modules on Sites Tag 03CX. I also opened the statements of every cited DAG node. Step 1 uses the definition node's explicit assertion that module sheafification is left adjoint to inclusion and the new node's exactness assertion; together these give the exact left adjoint required by the route. Step 2 uses the existing generic node stating that the right adjoint of an exact functor between abelian categories sends injectives to injectives, plus the definitions of injectivity, the abelian sheaf-module category, and the module sheafification adjunction. The hypotheses are the arbitrary ringed site, the abelian categories of sheaves and presheaves of modules, and injectivity of I in the sheaf category; each is present in the item statement or cited statement. I checked small cases: the one-object site with identity covering reduces to the identity inclusion, and the zero module is preserved as an injective object. I searched the whole DAG and blueprint for an existing general ringed-site exactness node and found only the abelian-presheaf and constant-ring module variants, so the new child is not a duplicate.
