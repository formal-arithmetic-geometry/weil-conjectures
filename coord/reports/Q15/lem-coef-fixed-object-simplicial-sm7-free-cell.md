# Worker report: lem-coef-fixed-object-simplicial-sm7-free-cell

Files written:

- `lem-coef-fixed-object-simplicial-sm7-free-cell.json` — statement, split proof in five steps, and no Mathlib leaf.
- `lem-coef-kan-quillen-cartesian-pushout-product.json` — statement-only helper, Mathlib searches found no match.
- `lem-coef-fixed-object-free-arrow-weak-equivalence.json` — statement-only helper, Mathlib searches found no match.
- `citations.json` — verbatim statement excerpts for every dependency used by every proof step.

Attachments: none. I searched the slopmaster2 source under `WeilConjectures/` by the item id and by the free-arrow/fixed-object/simplicial terms; no sorry-free declaration states this item.

WANTED: Dwyer--Kan, *Simplicial maps between spaces*, Sections 1.4, 2.7 and 7.1--7.6, archival copy for the free-cell and tensor calculation.
WANTED: Hovey, *Model Categories*, the cartesian Kan--Quillen pushout-product argument for simplicial sets.

No statement correction was needed. The imported item had no proof, so I supplied the five-step free-cell argument. The two helper nodes are strictly smaller than the item: one concerns only the simplicial-set pushout product, and the other concerns only local weak equivalence preservation by a free arrow. Neither restates the item's tensor/pushout identification or its fixed-object cofibration conclusion.

## Not duplicates

- `lem-coef-kan-quillen-cartesian-pushout-product` vs `lem-coef-sset-anodyne-pushout-product`: the existing Mathlib leaf treats a monomorphism crossed with an anodyne map and concludes anodyneness; the new helper treats the boundary/horn generators crossed with a monomorphism and includes the weak-equivalence alternative.
- `lem-coef-fixed-object-free-arrow-weak-equivalence` vs `lem-coef-fixed-object-free-arrow-adjunction`: the existing node constructs the free-arrow functor and its Hom adjunction; the new helper gives the separate word-decomposition and local weak-equivalence consequence.
- `lem-coef-fixed-object-free-arrow-weak-equivalence` vs `lem-coef-fixed-object-simplicial-free-calculus`: the existing node proves invariance of coproducts with a free factor; the new helper computes the free-arrow mapping simplicial sets themselves.

## Review by Q15

I read the item node, its `stmt_deps`, the fixed-object model-structure statement, the free-arrow adjunction statement, the Kan--Quillen statement, the existing Mathlib anodyne pushout-product leaf, and the two new helper statements. I also read the blueprint ancestor `prop-coef-integral-exceptional-adjoint` and its proof paragraph 2. The source URL in the imported item and the Hovey source are not archived locally, so the report records both WANTED lines and the proof is marked agent-written.

Step 1 uses the free-arrow node's degreewise word construction and checks the tensor object degree by degree. The coproduct indexed by `X_n` has exactly the generators indexed by `X_n × Y_n`; the face and degeneracy maps apply componentwise. The loop case `u=v` retains all finite words, so it is not silently replaced by the distinct-object case. Step 2 uses only the free-arrow adjunction's universal property: compatible maps out of the two pushout legs are the same as a map from the simplicial-set pushout, giving the claimed identification of the pushout map.

Step 3 uses the new Kan--Quillen helper for monicity and the weak-equivalence cases, and the existing anodyne Mathlib leaf for the horn orientation. The helper's hypotheses exactly match the item's boundary/horn alternatives and the given monomorphism `j`; no extra Kan or cofibrancy assumption is introduced. Step 4 checks the fixed-object free-calculus statement: a monomorphism adds only the complementary generators in each degree, with faces and degeneracies preserving the selected generators, so the resulting map is one of the free extensions that the model structure declares cofibrations. Step 5 uses the new free-arrow weak-equivalence helper to obtain local weak equivalence, then combines it with Step 4 and the fixed-object model structure's local weak-equivalence class to obtain a trivial cofibration. The two small edge cases were checked explicitly: `u=v` gives the finite-word free simplicial monoid, and `u≠v` permits only length-one nonidentity words; `m=0` is covered by the boundary generator and an empty simplicial-set factor is allowed.

For each new helper I searched the whole DAG and blueprint before writing it. The Kan helper has no exact Mathlib declaration; Mathlib only returned generic cofibration, pushout, and product-of-weak-equivalence infrastructure. The free-arrow helper has no exact declaration; ordinary free-category and simplicial-category hits do not state its enriched fixed-object word formula. The exact queries and outputs are in `searches.jsonl` and are recorded in each helper's `mathlib_searches` field. The dependency closure is acyclic, and every citation quote in `citations.json` is copied verbatim from the cited node statement.
