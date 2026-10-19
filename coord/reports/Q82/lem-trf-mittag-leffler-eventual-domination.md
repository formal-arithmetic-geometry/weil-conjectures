# Stage 1 report: lem-trf-mittag-leffler-eventual-domination

Files written:

- `dag/nodes/sec-trace-formula/lem-trf-mittag-leffler-eventual-domination.json` — repaired statement split; no new nodes and no Mathlib leaves.
- `citations.json` — verbatim step-to-node citations for all seven proof steps.

Attachments: none. A grep of `/home/ubuntu/weil-src-slopmaster2/WeilConjectures` and `Comparator` found no declaration tagged `(blueprint: lem-trf-mittag-leffler-eventual-domination)` and no sorry-free declaration stating the item.

WANTED: none.

The imported item statement agrees with Stacks Algebra Tag 059E, Proposition `proposition-ML-characterization`, condition (2), and with the tensor-product formulation in Tag 059M. I found no statement error and made no change to its hypotheses or conclusion. No new node was necessary: every non-elementary input is already an existing DAG node. The Mathlib searches required for the item were run with `msearch.py`; the returned tensor/direct-limit declarations do not state this module-level characterization.

## Repair of returned delivery

The returned Step 1 was circular: it invoked `lem-trf-mittag-leffler-hom-systems` with target `M_j` while simultaneously claiming that the lemma supplied `j`. I repaired it according to Tag 059E by first taking the single target module `N = ∏_{s∈I} M_s`, applying the Hom-system lemma to obtain `j`, and only then projecting the stabilized product-valued maps to the `j`-component. Step 2 now derives `h_k : M_k → M_j` from that projected equality, so no step uses an index before it has been chosen.

## Review by Q82

I read the item node, the `sk-i-curve-zero` unit and `sec-trace-formula` chapter, the Stacks passages for Tags 059E and 059M, and the full statements of every cited node. The repaired forward direction first uses `lem-trf-mittag-leffler-hom-systems` with the product target `N = ∏_{s∈I} M_s`; that node supplies the eventual index and stabilized Hom-image equality under the tensor-product Mittag-Leffler hypothesis from `def-trf-mittag-leffler-module`. Step 2 uses only the elementary universal property of a module product to project those image sets to `M_j`; because the identity of `M_j` maps to `f_{ij}`, the cited Hom-system equality gives the factorization `h_k ∘ f_{ik} = f_{ij}` for every `k ≥ j`. This explicitly fixes the returned circularity.

For the rest of the forward direction, Step 3 uses the elementwise filtered-colimit node and tensor-colimit node to move an arbitrary kernel element to a common later stage; the tensor-product definition supplies functoriality. Step 4 then applies the resulting factorization to prove domination, with no additional non-elementary fact hidden in the elementary kernel inclusion argument.

For the reverse direction, I checked that tensoring the given finitely presented colimit with the product module is a colimit by `lem-weil-pbc-tensor-commutes-with-colimits`, so the elementwise colimit node legitimately represents an arbitrary kernel element at some finitely presented stage. Its coordinates vanish after `f_i`; the assumed domination gives coordinatewise vanishing after `f_{ij}`. The existing `lem-trf-finite-presentation-tensor-products` node states that the comparison from a finitely presented stage tensor a product to the product of stage tensors is bijective, so the single stage tensor element vanishes after `f_{ij}`. The colimit compatibility `f_i=f_j f_{ij}` then kills the original element, exactly establishing injectivity in `def-trf-mittag-leffler-module` for every family.

I checked the edge cases of an empty product family, a zero module, and a one-stage constant system: the kernel argument remains valid, and the chosen eventual index may be the original index. Every `uses` entry is present in `proof_deps`, every citation quote is verbatim in its cited statement, the repaired proof has no dependency cycle, and no proof step exceeds the long-step threshold. The split follows the two Stacks sources without SGA or hidden auxiliary claims.
