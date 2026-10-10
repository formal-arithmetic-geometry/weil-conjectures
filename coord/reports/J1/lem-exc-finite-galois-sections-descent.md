# Stage-1 split: lem-exc-finite-galois-sections-descent

## Files written

- `dag/nodes/sec-curve-estimates/lem-exc-finite-galois-sections-descent.json`: split item, three proof steps.
- `dag/nodes/sec-curve-estimates/lem-exc-finite-galois-tensor-decomposition.json`: new statement-only node; no Mathlib match.
- `citations.json`: verbatim statement quotes for every cited node at each proof step.

## Attachments

None. I searched the slopmaster2 WeilConjectures source by item tag, Galois/descent terms, and likely declarations; no sorry-free declaration states this item.

## WANTED

`literature/stacks-project/etale-cohomology.tex`, Tag 04JM, and `literature/stacks-project/pione.tex`, Tag 03SF, because the local checkout contains citation references but not the fetched Stacks TeX sources. The split follows the cited Stacks arguments and records the source locations.

## Correction

The imported item had no proof and its `created.item` pointed to a different node. I corrected the ownership metadata and supplied the missing proof. I added only the strictly smaller tensor-product decomposition statement; the sheaf descent conclusion remains the item's own statement.

## Review by J1

I read the item source reference (Stacks 04JM, `lemma-global-sections-point`) and the parent blueprint paragraph in `lem-exc-field-discrete-modules`. I also read the statements of `lem-weil-pbc-finite-separable-extension-etale`, `def-weil-pbc-etale-sheaf-of-sets`, and the new tensor-decomposition node. The new node was searched for duplicate statements across all DAG nodes and the blueprint, and no existing node or Lean declaration supplied the finite-Galois tensor decomposition.

Step 1 uses the finite-separable-etale statement for `Spec E -> Spec L`; its hypotheses are exactly that `E/L` is finite and separable. The new node states the tensor-product product decomposition and explicitly states how both projections act on sections, so it supplies the self-intersection calculation used here. Surjectivity of the one-point spectrum map is elementary.

Step 2 uses the sheaf-definition node for the equalizer condition on the etale covering and the new node for the identification of the two projection maps with the identity and all `q^*`. Thus the equalizer is precisely the Q-invariant subset; no tag is being used as an uncited theorem.

Step 3 is elementary set-theoretic unpacking of an equalizer: its inclusion is pullback, and the equalizer characterization gives both injectivity and surjectivity onto invariant sections. I tested the edge cases `E=L` (trivial group, identity bijection), a separably closed base, and the empty sheaf. The tensor statement is also correct for a quadratic Galois extension, where `E tensor_L E` has the two expected factors.

The new node is intentionally statement-only, has a self-contained statement, Stacks-tag source, three Mathlib search records, and no proof sketch. Every `citations.json` quote is copied verbatim from the cited node statement. No cited node depends on the item, and the proof dependency union matches the step uses. No part of the split remains unfinished.
