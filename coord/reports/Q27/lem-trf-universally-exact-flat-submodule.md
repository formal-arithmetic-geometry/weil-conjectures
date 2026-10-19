# Q27 stage-1 report

Files written:

- `dag/nodes/sec-trace-formula/lem-trf-universally-exact-flat-submodule.json` — existing statement node, split proof, no new nodes, no Mathlib leaf.
- `citations.json` — verbatim statement quotes for every proof-step citation.

Attachments: none. The source repository has the related sorry-free declaration `Module.Flat.of_exact_of_flat_of_flat_right`, but it states the ordinary short-exact-sequence theorem with flat middle and quotient hypotheses, rather than this universally exact formulation; it is therefore not an exact attachment of this item.

WANTED: none.

The item is the submodule conclusion of Stacks Project Tag 058P (`literature/stacks-project/algebra.tex`, `lemma-ui-flat-domain`, around lines 20041–20070). I kept its statement and hypotheses unchanged. I read the existing DAG nodes `def-weil-pbc-flat-ring-map` and `def-weil-pbc-module-tensor-product`; no duplicate node states this universally exact submodule conclusion. The Mathlib searches already recorded on the item were rerun with the Q27 search command (LeanFinder, Loogle, grep, and LeanSearch); they found only general flatness/tensor criteria and no direct theorem.

## Review by Q27

I checked the item against the complete Tag 058P proof. Step 1 introduces an arbitrary injection `N → N'`, its cokernel `N''`, and the resulting 3×3 tensor diagram. The three horizontal rows are short exact because the item assumes universal exactness; the middle vertical map is injective exactly by the flat-module definition in `def-weil-pbc-flat-ring-map`. The tensor maps and their commutation are the operations specified by `def-weil-pbc-module-tensor-product`, which is why both definitions are cited and quoted in `citations.json`.

Step 2 follows the source's left-square chase: an element of `M₁ ⊗ N` killed in `M₁ ⊗ N'` maps to an element of `M₂ ⊗ N` killed by the injective middle vertical map, hence is zero; exactness of the top row then kills the original element. This proves tensor-injectivity for every injection and therefore flatness by the cited flatness definition. I verified that no step uses the proof of another DAG node, that every cited quote is verbatim, and that the existing `lem-trf-local-ui-flat-cokernel` node is a different (quotient) conclusion rather than a duplicate.

I checked small cases conceptually: split sequences reduce to a direct-summand inclusion and give a flat submodule; the zero module and zero ring satisfy the argument; the non-universally-exact sequence `0 → Z --2→ Z → Z/2 → 0` is correctly excluded. No statement error, source error, missing hypothesis, cycle, or long hidden lemma was found.

What could not be finished: nothing.
