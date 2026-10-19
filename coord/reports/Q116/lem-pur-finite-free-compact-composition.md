# Report: lem-pur-finite-free-compact-composition

## Files written

- `dag/nodes/sec-smooth-purity/lem-pur-finite-free-compact-composition.json` — repaired statement split; no new nodes and no Mathlib leaves.
- `citations.json` — 53 verbatim statement quotations, covering every citation in all eight proof steps.
- `report.md` — this repair report.

## Attachments

None. I searched the read-only slopmaster2 and upstream-master sources for the item id, its compact-support coefficient-composition vocabulary, and the relevant theorem names. No sorry-free declaration states this finite-free extension item exactly.

## WANTED

None.

## What was wrong and what was repaired

The return identified four faults. I repaired all four without adding a duplicate node.

1. Steps 1, 2, 4, 5, and 6 now cite `lem-trf-open-ctf`, `cor-sf-direct-image-ctf-nonproper`, `cor-sf-direct-image-ctf-proetale`, and `lem-kun-dimension-finite-type` exactly where extension by zero, proper direct images, intermediate `P_f M`, and their finite-Tor domains are used.
2. The old Step 2 citation to pro-etale projection/restriction statements was removed from the ordinary étale argument. The step now uses `lem-pur-etale-open-derived-tensor`, whose statement gives the canonical étale `j_!` tensor comparison for an arbitrary coefficient ring, and explicitly specializes its second factor to the constant B-module sheaf. This supplies the B-linear balancing map.
3. The old “pasting” in the composition argument was replaced by two typed mate steps. They define the normalized interchange `\\gamma`, state the inverse-image coefficient square, use `lem-weil-pbc-mate-pasting`, insert the open-unit identity, and transpose under the open adjunction to obtain the B-linear square for `\\gamma`. The direct-image and open-composition squares are then pasted only after this calculation.
4. The pro-etale step now spells out `\\nu^*` commuting with scalar extension via `lem-weil-pbc-ringed-topoi-derived-tensor-pullback`; it transports proper coefficient maps using `lem-weil-pbc-comparison-direct-image-canonical-mate` and `prop-weil-pbc-comparison-direct-image`, open balancing using `lem-cbc-proetale-extension-zero-comparison` and `lem-sf-comparison-open-tensor-coherence`, and composition/refinement maps using `lem-pur-compact-support-site-coherence` and `lem-sf-proper-open-comparison-site-normalization`. It therefore proves equality of named B-linear arrows rather than merely underlying A-arrows.

The statement, hypotheses, coefficient categories, refinement equation, and composition equation were not changed. The existing Mathlib searches in `searches.jsonl` were retained because the item statement and its Mathlib status did not change; no new node was created.

The small cases checked remain `E=L` (so `A=B`), `n=1`, identity maps, a proper map, an open immersion, identity refinements, and an empty source. The maps reduce respectively to identity, proper direct image, open balancing, or the zero map, and every displayed equation has the asserted source and target.

## What could not be finished

Nothing at stage 1 before the required server checks and delivery dry run.

## Review by Q116

I reread the item, its unit `sk-thm-purity-transport`, the chapter record, and the complete `main-20261015` transport proof (Steps 1 and 3). I also opened every statement named by the eight repaired steps; the quotations in `citations.json` are copied verbatim from those statements.

Step 1 checks finite-free scalar extension, derived change of rings, extension-by-zero preservation, finite dimension, ordinary and pro-etale direct-image preservation, and etale-origin witnesses. The cited statements cover the exact finite-Tor inputs `M`, `P_{f,A}M`, and all intermediate compact-support outputs. Step 2 checks the proper transpose from `lem-coef-finite-direct-image` and the étale B-linear open tensor map from `lem-pur-etale-open-derived-tensor`; the compactification definition supplies their ordered composite. Step 3 uses the refinement node's exact coefficient square, the proper coefficient map, and compactification comparison cocycles, with the stated properness and relation `u j'=j`.

Step 4 uses the finite-direct-image composition identity and open-extension composition identity, and separately reserves the middle proper/open interchange for the next two steps; its domain citations are the same finite-Tor preservation statements verified in Step 1. Step 5 reads the normalized interchange statement, defines the exchange and mate maps with the same directions, and derives equation (1) by the cited inverse-image tensor comparison and mate-pasting theorem. Step 6 checks the open-unit identity, the two normalized mate cancellations, and injectivity of the open-adjunction transpose; it then obtains the exact B-linear `\\gamma` square and the compatible-compactification composition equation. Step 7 uses the compactification comparison naturality and cocycle to conjugate to arbitrary choices, with the proper-direct-image domain hypotheses cited again.

Step 8 checks both coefficient rings in the etale-origin pro-etale domain. The proper comparison uses the counit-mate normalization; the open comparison uses the comparison `j_!` statement and its tensor coherence; the compact-support compositor and refinement maps use their site-normalization statements. The ringed-topos tensor comparison gives the scalar-extension identification, and mate-pasting carries the normalized interchange itself. No pro-etale restriction-of-scalars statement is used in place of the required B-linear comparison.

I tested the edge cases above and corrected every returned point: the missing C1 domain citations, the invalid étale open citation (C4), the omitted proper/open mate calculation (E5), and the under-specified site transport (E5/C4). No SGA 4 or SGA 4½ source is cited, and no new node duplicates an existing DAG statement.
