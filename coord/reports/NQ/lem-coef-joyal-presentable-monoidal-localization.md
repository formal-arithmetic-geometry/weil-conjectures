# Stage-1 report: lem-coef-joyal-presentable-monoidal-localization

## Files written

- `dag/nodes/sec-six-functors/lem-coef-joyal-presentable-monoidal-localization.json`: repaired item split; statement unchanged, seven proof steps revised.
- `dag/nodes/sec-six-functors/lem-coef-joyal-generating-trivial-cofibrations.json`: new unsplit statement node for the set-generated trivial-cofibration class of the Joyal model.
- `dag/nodes/sec-six-functors/lem-coef-joyal-localization-cat-infinity.json`: new unsplit Joyal-specific coherent-localization and reflection node.
- `citations.json`: verbatim quotes for every cited step dependency.

## Attachments

None. I searched the read-only `WeilConjectures` source for the item id, the blueprint tag, and Joyal/localization declarations; no sorry-free declaration states this item exactly.

## WANTED

- `https://www.math.ias.edu/~lurie/papers/HTT.pdf`, Theorem 2.2.5.1, Corollary 2.2.5.4, Proposition 2.2.5.8 (the archived HTT PDF is unavailable in `literature/`).
- Higher Algebra, §1.3.4, Proposition 4.1.7.4 and Example 4.1.7.6 (the archived HA source is unavailable in `literature/`).

## What was wrong and what I repaired

The returned Step 4 had applied `lem-coef-simplicial-model-nerve-localization`, whose statement requires enrichment over Kan-model simplicial sets. The cartesian Joyal enrichment does not meet that hypothesis; for example, `Fun(Delta^0, Delta^1) = Delta^1`, which is not Kan. I removed that citation and added `lem-coef-joyal-localization-cat-infinity`, whose statement is specifically the hammock localization of the ordinary Joyal model followed by locally Kan replacement and coherent nerve, identified with `Cat_infty`; it explicitly applies to arbitrary simplicial sets and supplies the universal property.

The former Step 5 only argued saturation through the flawed Step 4 model and did not cover arbitrary maps. It now cites the new node's explicit reflection clause for every simplicial map, with no Kan, fibrancy, or quasicategory assumptions, and then records the Joyal functor-equivalence criterion as the equivalent test.

Step 1 previously asserted local presentability and set-generated trivial cofibrations without node dependencies. It now cites the existing Mathlib leaf `lem-coef-infinity-monomorphism-boundary-cells`, the existing local-presentability leaf `lem-coef-presheaf-local-presentability`, and the new Joyal generating-trivial-cofibration node. Step 2 now cites `lem-coef-all-cofibrant-left-proper`, so its left-properness argument has the exact all-objects-cofibrant hypothesis and conclusion. The duplicate new boundary-cell leaf was deleted; the existing node already states the relative boundary filtration and the same Mathlib declaration.

## Not duplicates

- `lem-coef-joyal-generating-trivial-cofibrations` vs `lem-coef-joyal-model-structure`: the existing node gives the Joyal classes and weak-factorization systems, while the new node isolates the additional set-generation assertion needed for combinatoriality.
- `lem-coef-joyal-localization-cat-infinity` vs `lem-coef-simplicial-model-nerve-localization`: the existing node treats simplicial model categories enriched over Kan-model simplicial sets; the new node treats the ordinary cartesian Joyal model via hammock localization and includes reflection for arbitrary simplicial maps.
- Removed `lem-coef-sset-mono-relative-cell-complex` vs `lem-coef-infinity-monomorphism-boundary-cells`: the existing node already states the full relative boundary-cell filtration for every simplicial monomorphism and has the same Mathlib declaration `SSet.relativeCellComplexOfMono`; retaining the new leaf would duplicate it.

## Review by NQ

I reread the item statement, its blueprint ancestry, HTT/HA source locations, and every cited DAG statement. Step 1 now takes exactly the Joyal model classes from `lem-coef-joyal-model-structure`, local presentability from the presheaf leaf, the boundary filtration from the existing `lem-coef-infinity-monomorphism-boundary-cells`, and set-generation from the new Joyal-specific node; the all-objects-cofibrant argument then makes tractability immediate. Step 2 uses the exact hypothesis and conclusion of `lem-coef-all-cofibrant-left-proper`, and no longer hides left properness in a cube argument. Step 3 checks the cartesian pushout-product clause and feeds the local-presentability and set-generation facts into the combinatorial-localization theorem.

For Step 4 I checked that the new Joyal-specific statement itself supplies the ordinary hammock localization, locally Kan replacement, coherent nerve, Cat-infinity identification, universal functor-category property, and universe naturality. This avoids the Kan-enrichment hypothesis that caused the return. Step 5 cites its full arbitrary-map reflection clause and separately the exact three-way Joyal functor-equivalence test, so saturation covers nonfibrant and nonquasicategorical maps. Steps 6–7 retain the existing symmetric-monoidal localization, cartesian Cat-infinity, coherent-nerve, and universe statements; each quote in `citations.json` is copied verbatim from the cited node.

I tested edge cases in the retained statement: the empty simplicial set and identity maps are cofibrant and already in the reflected weak-equivalence class; `Delta^0` is the terminal monoidal unit; products with the empty simplicial set preserve the displayed product equivalence; and the reflection clause is quantified over arbitrary maps. The new boundary leaf was removed after finding the existing exact Mathlib leaf. No Lean source, compiler, Lake, or build tool was used.

## What remains

The delivery dry run is required; the two new statements are intentionally unsplit for later stages.
