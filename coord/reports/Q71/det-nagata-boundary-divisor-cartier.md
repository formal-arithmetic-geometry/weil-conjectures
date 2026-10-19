# Worker report

Files written: `dag/nodes/sec-nagata-compactification/det-nagata-boundary-divisor-cartier.json`; `citations.json`; this report. No new nodes were created. The item has no declaration tagged `(blueprint: det-nagata-boundary-divisor-cartier)` in `/home/ubuntu/weil-src-slopmaster2/WeilConjectures`.

Attachments: none.

WANTED: none.

The imported statement is retained exactly. I checked the unit record and the current blueprint proof. The item is stronger than the older Conrad density lemma because it does not assume that (U) is dense. Therefore I removed those citations: for a disconnected (T) with (U) empty on one component, their hypotheses fail. The direct affine Cartier-chart argument proves scheme-theoretic density without that extra hypothesis; the same argument applies after the further blow-up. This is a repair of the imported proof route, not a change to the mathematical statement.

## Review by Q71

I read the item node, `dag/units/sk-lem-nagata-boundary-divisor.json`, the current blueprint statement and proof, and the statements of `def-nagata-admissible-blowup`, `thm-nagata-blowup-principalizes-center`, and `lemma-nagata-cartier-total-transform-blowup`. Step 1 uses exactly the admissible-blow-up definition: finite type, unit restriction on (U), and the specified blow-up. Step 2 uses the principalization statement for the given finite-type ideal and separately checks that the support is the inverse image of (V(\mathcal I)=T\setminus U). Step 3 uses the cited non-zero-divisor generators and spells out injectivity of localization on each affine chart; this is the only local argument needed for scheme-theoretic density. Step 4 uses the total-transform statement with the further blow-up ideal, then repeats the same localization argument and identifies supports by inverse image. All hypotheses (qcqs (T), quasi-compact open (U), finite type quasi-coherent (\mathcal I), and exact vanishing locus) are tracked in the relevant steps. I tested the edge cases (U=T), (U=\varnothing), a disconnected two-point scheme with one component omitted, and a principal ideal on an affine scheme; the direct chart proof handles each, while the removed Conrad citations do not apply to the disconnected case. The Mathlib searches (LeanSearch, LeanFinder, Loogle, and source grep in two phrasings) found no exact or one-line generalization, and are recorded in the node.
