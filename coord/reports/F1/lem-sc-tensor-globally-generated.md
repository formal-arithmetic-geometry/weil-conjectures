1. Files written:

   - `dag/nodes/sec-curve-estimates/lem-sc-tensor-globally-generated.json`: statement, split proof, and report metadata; no Mathlib match.
   - `dag/nodes/sec-curve-estimates/lem-sc-tensor-generating-sections.json`: statement-only supporting node; no Mathlib match.

2. Attachments: none.

3. WANTED: none.

4. The item had no Lean declaration and no existing DAG or blueprint node stating tensor products of finite generating families. I added that smaller statement and cited the existing invertible-tensor node for the invertibility part. The item statement now explicitly includes `n >= 1` and finite generating families.

5. Nothing remains unfinished.

## Review by F1

I read the item source references (Varieties Lemma 09NC and the Modules tensor-product global-generation lemma 01B4) and the ancestor blueprint proof. I searched all DAG nodes, the imported blueprint, and the slopmaster2 Lean source for an exact declaration or duplicate statement; none exists. Step 1 uses the existing statement that a tensor product of invertible modules is invertible, together with the tensor-product definition and associativity for the induction. Step 2 uses the definition of a finite generating family and the new node whose statement explicitly says that all pure tensors of the chosen families generate the tensor product. The hypotheses `n >= 1`, scheme structure, module types, and finite index bounds are explicit in the item and new node. I checked the edge cases `n = 1` (the generating family is unchanged) and one-generator factors (the sole pure tensor generates). Mathlib searches for the new node used LeanSearch, LeanFinder, and source grep and found no matching theorem.
