1. Files written

- `dag/nodes/sec-picard-framework/lem-pc-cartier-divisor-nowhere-dense.json`: repaired item statement and three-step proof; no Mathlib match.
- `dag/nodes/sec-picard-framework/lem-pc-affine-nonzerodivisor-complement-dense.json`: existing unsplit node retained; no Mathlib match.
- `dag/nodes/sec-picard-framework/lem-pc-quasi-compact-local-on-target.json`: new unsplit statement node; no Mathlib match.
- `dag/nodes/sec-picard-framework/lem-pc-localization-preserves-nonzerodivisor.json`: new unsplit statement node; no Mathlib match.
- `citations.json`: verbatim statement quotes for every cited node in every proof step.

2. Attachments

None. The slopmaster2 source has no sorry-free declaration carrying this item's statement.

3. WANTED:

None. The cited source is present locally at `/home/ubuntu/c1-stacks-review/divisors.tex`.

4. What was wrong or incomplete

The returned version weakened the imported statement by making scheme-theoretic density conditional on quasi-compactness and referred to the Stacks tag for its meaning. I restored the imported statement and define its meaning explicitly through injectivity of `O_X -> j_* O_U`. The proof now checks quasi-compactness of the complement immersion on affine charts and invokes target-locality of quasi-compactness before applying the definition. It also no longer asserts without justification that a Cartier generator stays regular after refining an arbitrary chart: the affine refinement uses principal opens and the new localization-preserves-nonzerodivisor node. The old `created.item` metadata was corrected to this delivered item.

5. What I could not finish, and why

The two new algebraic/locality nodes are intentionally unsplit stage-1 leaves for later workers. No Lean code was written or compiled, as required by stage 1.

## Review by J1

I read the item's imported blueprint context and the full local Stacks source `/home/ubuntu/c1-stacks-review/divisors.tex`, especially Lemma `lemma-complement-effective-Cartier-divisor` (Tag 07ZU), its use of `lemma-characterize-effective-Cartier-divisor`, and the cited locality lemma. The repaired item statement now agrees with 07ZU: for any effective Cartier divisor, the complement is scheme-theoretically dense, with the predicate spelled out as injectivity of `O_X -> j_* O_U`; it also records the topological density consequence. I removed the previous convention-mismatch paragraph and WANTED entry because the source file is present.

Step 1 uses the exact statement of `def-nagata-effective-cartier-ideal` for local nonzerodivisor generators. To address the returned E1 point, I explicitly refine by principal affine opens and cite `lem-pc-localization-preserves-nonzerodivisor`, whose statement is precisely that the generator remains a nonzerodivisor in `A_g`. The complement is then the principal open `D(a)`.

Step 2 uses the existing `lem-pc-affine-nonzerodivisor-complement-dense`; its statement supplies both sheaf injectivity and topological density for `D(a)`. The affine immersion is affine and therefore quasi-compact by its explicit affine source.

Step 3 uses the new `lem-pc-quasi-compact-local-on-target`, whose statement is exactly the needed locality implication, to show that `j` is quasi-compact. It then uses the full statement of `def-nagata-scheme-theoretically-dense-open`, including its quasi-compact-open hypothesis and injectivity conclusion. Sheaf injectivity is checked on the affine cover, and density follows from the chartwise dense principal opens. The hypotheses are thus checked in the same order as the Stacks proof: affine local equation, injective localization, quasi-compactness, then the density definition.

For both new nodes I searched the whole DAG and blueprint for duplicates before writing them. I read the source locations: 07ZU for the localization calculation and `spaces-morphisms.tex`, Tag 03KG (clause (6), specialized to schemes), for quasi-compactness local on the target. LeanSearch, LeanFinder, and Mathlib-source grep searches found no exact declarations for either statement, so both remain unsplit. I tested the affine node on `A = k[t], a = t` and `A = k, a = 1`, and checked the localization statement on `A = Z, a = 2, g = 3` and on a ring with zero divisors where `a` is regular; the claimed preservation is valid. Every citation in `citations.json` is copied verbatim from the cited node statement, and all cited ids exist and are unmerged.
