## Worker report

Files written:
- `dag/nodes/sec-deligne-laumon-general/lem-a1-mixed-direct-summand.json`: item retained and marked `split`; no new nodes.
- `citations.json`: five verbatim citations for the non-elementary existing-node uses.
- `searches.jsonl`: the four searches run through `msearch.py` (LeanFinder, Loogle, grep and LeanSearch).
- `report.md`: this report.

New nodes: none. New Mathlib leaves: none.

Attachments: none. I searched `lean/WeilConjectures/` for the blueprint tag, the item terminology and the theorem name. The four sheaf declarations in `WeilConjectures/DeligneLaumon/Reduction/Weights.lean` are separate clauses, not one declaration stating this whole item. The complete Frobenius-module conjunction is `FrobeniusModule.mixedOfWeightsAtMost_stability` in `Sheaf/Paper/MixedWeightsStability.lean`, outside `WeilConjectures/`; it has no `sorry`, but the worker rule treats it as source provenance rather than an attachment.

WANTED: none.

No statement correction was needed. The imported statement and its six statement dependencies agree with the master and main-20261015 blueprint records. The only bookkeeping repair was to mark the item `split`, fill `blueprint.same_as` with `[]`, add the blueprint proof coverage and declare the two existing cross-unit module lemmas as tool uses. The item is project-specific, so the Mathlib searches found only unrelated filtration and semisimplicity declarations; no Mathlib leaf was created.

No work remains unfinished. No Lean, compiler, Lake/build tool, repository write, or manual git command was used.

## Not duplicates

No new node was created, so there are no new/existing node pairs. I searched the DAG and blueprint for the item id, “mixed direct summand”, “stable subquotient”, and “extension bounds”; the existing `lem-a1-extension-bounds` and `lem-a1-subquotient-extension-bounds` are the exact supporting statements cited by the proof, not duplicate replacements for this item.

## Review by Q68

I read the chapter and unit records, the current item, both blueprint versions, and the source files for every cited dependency. The source of the item is `literature/blueprint/master/blueprint/sec-deligne-laumon-general/sk-d-dl-general-weights/lem-a1-mixed-direct-summand.md`, with the corresponding proof in `literature/blueprint/main-20261015/.../lem-a1-mixed-direct-summand.proof.md`. The live declaration audit was against `WeilConjectures/DeligneLaumon/Reduction/Weights.lean:170–184` (subobjects and quotients), `:220–245` (short exact sequences and retracts), and `Sheaf/Paper/MixedWeightsStability.lean:158` (the Frobenius-module conjunction). I verified that none of these source proofs contains `sorry`; only the location of the latter prevents an attachment under the worker rule.

Step 1 uses no DAG node: it records the four existing sheaf declarations `IsMixedOfWeightsAtMost.of_mono`, `.of_epi`, `.of_shortExact`, and `.of_retract`. I checked their hypotheses and conclusions in the source and that they cover the three sheaf clauses. Step 2 uses `def-weil-frobenius-module-weights` for the finite stable-filtration notion and `lem-a1-extension-bounds` for the exact-sequence extension conclusion; the cited quotes in `citations.json` are literal parts of those statements. The zero Frobenius module has the length-zero filtration, and the equivariant linear equivalence gives an exact sequence with zero source and bijective second map, so the extension lemma transports mixedness.

Step 3 uses the exact statement of `lem-a1-subquotient-extension-bounds`. For an injective equivariant map, I checked the image is stable in both directions using equivariance and the inverse Frobenius, and that the source is equivariantly identified with the image modulo zero. Step 4 uses the same cited statement for the stable kernel and the quotient; surjectivity identifies that quotient with the target, and the quotient map is equivariant on representatives. These checks include the required hypotheses rather than relying on private helpers from the Lean proof.

Step 5 uses `lem-a1-extension-bounds` exactly for the extension clause. For a split inclusion, the equation `r.comp i = LinearMap.id` gives a left inverse and hence injectivity, so Step 3 applies. I checked the conjunction order against the Lean theorem: injective, surjective, exact-sequence, and retract clauses are all present. Edge cases include zero modules and length-zero filtrations, identity and zero maps, non-semisimple Frobenius, and a split inclusion with a projection. The proof steps remain acyclic and each non-elementary cited fact is represented by an existing node statement.

The four executed Mathlib searches are recorded verbatim in `searches.jsonl`; LeanFinder and LeanSearch returned generic filtration results, Loogle reported the project-specific identifier unknown, and the Mathlib grep returned no hits. Since the item is not a Mathlib statement, these results do not justify a leaf classification.
