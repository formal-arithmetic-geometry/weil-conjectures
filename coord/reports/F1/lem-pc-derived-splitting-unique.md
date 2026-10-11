1. Files written:

- `dag/nodes/sec-abelian-varieties/lem-pc-derived-splitting-unique.json`: split Tag 0BCG into three proof steps; no exact Mathlib match for the whole item.
- `dag/nodes/sec-abelian-varieties/lem-pc-derived-zero-third-split.json`: Mathlib leaf for `CategoryTheory.Pretriangulated.exists_iso_binaryBiproduct_of_distTriang`.
- `citations.json`: verbatim citations for every non-elementary dependency of every step.

2. Attachments: none.

3. WANTED: none.

4. The imported item had no proof and no Lean declaration with its blueprint tag. The existing DAG node `lem-pc-ring-precise-vanishing` states the generic bounded-projective Hom-vanishing theorem needed for both the first clause and the shifted connecting morphism. The new helper is strictly smaller than the item and states only the standard zero-third-map biproduct criterion; Mathlib search found its exact declaration. The uniqueness argument is the elementary biproduct matrix calculation after the same Hom-vanishing statement.

## Review by F1

I read the item source identified as More on Algebra, Tag 0BCG, Lemma `splitting-unique`, and checked each hypothesis against the node: the projective representative is bounded in degrees `[a,b]`, hence vanishes below `a`; shifting `K` changes the required cohomology bound from `a+1` to `a`; and the triangle's third map is exactly the connecting morphism `L -> K[1]`. Step 1 uses the cited statement of `lem-pc-ring-precise-vanishing`, which explicitly gives zero for every derived morphism from a bounded projective complex with terms zero below the threshold. Step 2 applies the same statement to `K[1]`, with the displayed cohomology shift, so it really says the connecting map is zero. Step 3 uses the new Mathlib leaf, whose statement is exactly the zero-third-morphism biproduct conclusion; the final uniqueness claim follows by writing two compatible biproduct splittings as matrices, whose difference has only an `L -> K` off-diagonal entry, and Step 1 makes that entry zero. I tested the zero complex and a split two-term projective complex: the Hom groups and connecting maps vanish and the asserted direct-sum decomposition is the evident one. The Mathlib searches for the item and helper were run with LeanFinder, Loogle, grep, and LeanSearch; LeanSearch was unavailable and recorded as such.

## Not duplicates

lem-pc-derived-zero-third-split vs lem-pc-derived-splitting-unique: the helper only treats a distinguished triangle after its third morphism has been shown zero; the item additionally proves that vanishing from cohomological bounds and proves uniqueness.

## Second reading by F1

- Step 1 checked against More on Algebra Tag 0BCG clauses (1) and the precise-vanishing node; verdict: hypotheses and Hom conclusion agree.
- Step 2 checked against Tag 0BCG clause (2), including the shift identity H^i(K[1])=H^{i+1}(K); verdict: the connecting morphism is correctly shown zero.
- Step 3 checked against Tag 0BCG clause (2) and the Mathlib declaration CategoryTheory.Pretriangulated.exists_iso_binaryBiproduct_of_distTriang; verdict: zero third map gives the required compatible biproduct isomorphism.
- Step 4 checked against Tag 0BCG clause (3) and the precise-vanishing node; verdict: the biproduct matrix argument explicitly reduces uniqueness to Hom(L,K)=0 and is elementary.
- Item statement checked hypothesis by hypothesis against More on Algebra Tag 0BCG, Lemma splitting-unique; verdict: the three source clauses are present with the same degree bounds.
- lem-pc-derived-zero-third-split checked against Mathlib Pretriangulated.lean:579-582; verdict: exact zero-third-morphism biproduct conclusion, with the required category structure stated.

Changes made: corrected the item node's created.item to the delivered item; split the former combined splitting/uniqueness step into separate splitting and elementary matrix-uniqueness steps; updated citations.json with the verbatim citation for the new step.

