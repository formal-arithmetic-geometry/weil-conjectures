# Stage-1 worker report

Files written:

- `dag/nodes/sec-six-functors/lem-sf-comparison-open-tensor-coherence.json` — item, statement unchanged, split with five derived-category proof steps; no new nodes and therefore no Mathlib leaves.
- `citations.json` — 20 verbatim step/node statement quotations.

Attachments: none. No existing sorry-free declaration states this item exactly.

WANTED: none.

What was wrong or incomplete in the imported node: the item had no proof or proof dependencies, although the blueprint transport paragraph uses exactly this comparison/open-tensor coherence. I supplied the missing formal argument. The item statement itself is well-typed and faithful to the finite-coefficient transport paragraph; no hypotheses were added or removed. The generic normalization lemma `lem-sf-open-tensor-normalization` is used as a tool from the compatibility unit because it fixes the adjunction-normalized open projection map.

What I could not finish: nothing.

## Review by N3

I read the item node, the `sk-thm-sf-pf-proetale` unit, its `thm-sf-pf-proetale.proof.md` blueprint proof, and the source implementations of the comparison pullback, extension-by-zero comparison, derived tensor comparison, and open projection maps in the slopmaster2 checkout. I also opened the full statements of every cited DAG node and checked that each says the fact used by its step. The Stacks sources read were `sites-cohomology.tex` Tags 0GL1 and 0E8I (open extension/tensor), plus Tag 07A4 (pullback/tensor); the blueprint finite-coefficient transport paragraph supplies the comparison context.

Step 1 uses `lem-sf-comparison-pullback-exact` for exactness and cohomology preservation of `nu^*`, `lem-cbc-proetale-extension-zero-comparison` for the natural sheaf-level comparison `nu_X^* j_!^e ≅ j_!^p nu_U^*`, `lem-weil-pbc-extension-by-zero-exact` and `lem-cbc-proetale-extension-zero` for exact degreewise extension and its adjunction, and `lem-weil-pbc-ringed-topoi-derived-tensor-pullback` for the canonical derived tensor comparison. These hypotheses are exactly the finite discrete commutative coefficient and open-immersion hypotheses in the item.

Step 2 uses `lem-pur-etale-open-derived-tensor` for the arbitrary unbounded étale open-tensor isomorphism and `lem-cbc-extension-zero-projection-formula` for the pro-étale one. It also uses the generic `lem-sf-open-tensor-normalization` tool, whose statement fixes the inverse as the open adjunction transpose and the restriction as the identity; this is the normalization required to compare the two canonical maps.

Step 3 uses `lem-weil-pbc-comparison-pullback`, which states naturality and identity/composition compatibility of the comparison pullback, and `lem-weil-pbc-ringed-topoi-derived-tensor-pullback`, whose comparison is natural in both variables. I checked that these give precisely the displayed composite `h_{K,N}` and do not identify the two sites or coefficient sheaves.

Step 4 was checked on flat-term K-flat representatives, as required by the tensor-pullback node. The degreewise maps send a local pure tensor to the extension by zero of the tensor with the restricted second factor. On objects through the open, the unit-normalized maps are identities; off the open, both extension-by-zero prescriptions are zero. Naturality with the two differentials gives chain-map equality, and the K-flat localization argument gives equality in the unbounded derived category. The cited statements supply exactness, the two canonical open maps, and the comparison e; no boundedness, constructibility, properness, or finite Tor-amplitude hypothesis entered.

Step 5 checks naturality in both variables from the naturality clauses of the comparison, extension, and tensor nodes. I tested the edge cases `K=0`, `N=0`, `U=X` (where every open map is the identity), and `U` empty (where both extension-by-zero sides are zero). No statement correction was needed, and no duplicate or new child node was introduced.
