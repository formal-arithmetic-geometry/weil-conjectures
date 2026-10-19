# Worker report: lem-sf-etale-generic-perfect-hom

## Files written

- `dag/nodes/sec-six-functors/lem-sf-etale-generic-perfect-hom.json`: repaired the five-step item proof.
- `dag/nodes/sec-six-functors/lem-sf-etale-finite-projective-pullback-hom.json`: repaired statement-only finite-projective pullback/Hom node; no Mathlib match.
- `citations.json`: verbatim citations for every node used by every step.
- `searches.jsonl`: retained Mathlib search log for the new node.

## Attachments

None. The slopmaster2 source has no sorry-free declaration carrying this exact item statement.

## WANTED:

None.

## Not duplicates

- `lem-sf-etale-finite-projective-pullback-hom` vs `lem-pur-isomorphism-inverse-image-tensor-hom`: the existing node is a pro-etale scheme tensor/Hom comparison for arbitrary sheaves; this node is the small-etale finite-projective constant-module comparison with evaluation compatibility.
- `lem-sf-etale-finite-projective-pullback-hom` vs `lem-pc-perfect-tensor-hom-duality`: the existing node is a quasi-coherent perfect-complex duality statement; this node concerns ordinary constant coefficient etale module sheaves and scheme inverse image.
- `lem-sf-etale-finite-projective-pullback-hom` vs `lem-pc-perfect-rhom-tensor-comparison`: the existing node does not state inverse-image compatibility of sheaf Hom for constant etale modules.
- `lem-sf-etale-finite-projective-pullback-hom` vs `lem-sc-finite-free-internal-hom-exact`: the existing node proves exactness of Hom from finite-free terms on one ringed site and has no pullback or evaluation square.
- `lem-sf-etale-finite-projective-pullback-hom` vs `lem-sc-bounded-hom-exact-columns`: the existing node proves acyclicity of a total Hom complex from exact columns; it has no inverse-image comparison or finite-projective evaluation statement.
- `lem-sf-etale-finite-projective-pullback-hom` vs `lem-sc-finite-free-internal-hom-exact-sequence`: the existing node proves postcomposition exactness for a finite-free source and a short exact sequence; it has no scheme morphism, pullback map, or evaluation compatibility.
- `lem-sf-etale-finite-projective-pullback-hom` vs `lem-sc-hom-complex-dual-total-comparison`: the existing node identifies a formal double-complex totalization with a Hom-complex short complex; it has no sheaf pullback or finite-projective Hom isomorphism.
- `lem-sf-etale-finite-projective-pullback-hom` vs `sk-thm-sf-internal-hom-pullback`: the blueprint theorem is the general derived dualizable comparison; this node is the underived termwise finite-projective identity used to construct the item's local chain map.

## What was wrong and what changed

The return correctly identified that the prior step 2 used an arbitrary K-flat resolution, which need not be bounded below, while the cited 08JI model requires a bounded-below target. I now replace the local target by the good truncation `tau_{>=c}` of a representative of `N`, use the vanishing hypothesis to identify it quasi-isomorphically with `N`, and cite 08JI on both the chart and its inverse image. The same step now cites the existing `lem-sf-etale-hom-complex-pullback` for the chain-map assembly and the finite-projective node for its termwise isomorphism and evaluation compatibility. The unsupported duality-maps normalization has been removed from this step.

The returned C4 point in step 4 is repaired by citing `lem-weil-pbc-ringed-slice-evaluation-transpose`, whose statement contains the restriction identities for evaluation and transposes. Step 5 now states the missing argument: 08JI supplies the canonical ordinary Hom models, the existing Hom-complex pullback is defined by currying pulled-back evaluation, and the finite-projective node plus the tensor comparison make the total evaluation square commute. The perfect-duality node then identifies this evaluation-induced map with the canonical derived comparison `beta`, so the proof does not assert an arbitrary isomorphism.

The new node now declares the tensor-pullback and tensor-Hom closed-structure dependencies used to define its map. Its `unit` is corrected to the item's `sk-prop-sf-biduality-general`, its `blueprint.same_as` records `sk-thm-sf-internal-hom-pullback`, and all created metadata identifies this Q159 repair.

## Review by Q159

I read Stacks Tag 0GM7, `lemma-pullback-internal-hom`, case (1), including the finite-projective specialization, and Tag 08JI, `lemma-Rhom-complex-of-direct-summands-finite-free`. I also read the complete statements of every cited DAG node and the blueprint nodes `sk-thm-sf-internal-hom-pullback` and `sk-prop-sf-biduality-general`.

For step 1, the inverse-image proposition supplies exactness and preservation of finite-projective constant terms, while the RHom restriction node supplies the localized derived-Hom identification. For step 2, the truncation node supplies the good truncation and its cohomology preservation; 08JI applies because `E` and `g^*E` are bounded above with finite-projective terms and `tau_{>=c}N` and its pullback are bounded below. The Hom-complex pullback node supplies the canonical chain map, and the new node says its term maps are isomorphisms preserving evaluation. For step 3, the local-dual node gives dual support `[-b,-a]`; the truncation triangles, triangulated derived tensor tool, long exact cohomology, and exact inverse image give the interval `[c-b,d-a]`. For step 4, the RHom restriction node and the dedicated slice evaluation-transpose node give refinement compatibility; exact inverse image and the sheaf-cover criterion globalize both isomorphism and vanishing. For step 5, I checked that 08JI's canonical Hom model, the Hom-complex currying formula, the new node's evaluation clause, the derived tensor pullback comparison, and perfect-duality's canonical evaluation comparison identify the constructed chain map with `beta` and prove the displayed evaluation equation.

I checked the new node against Tag 0GM7's finite-projective term identity and tested the item on `P=0`, `N=0`, one-term models (`a=b`, `c=d`), the identity morphism, an empty scheme, and `A=F_2\\times F_2` with the projective summand `F_2\\times0`. The statement and all hypotheses are unchanged. No SGA citation, statement dispute, or dependency cycle remains.
