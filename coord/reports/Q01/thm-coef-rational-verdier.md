# Stage 1 report: thm-coef-rational-verdier

## Files written

- `dag/nodes/sec-six-functors/thm-coef-rational-verdier.json`: existing theorem node, audited and marked `split`; no new nodes.
- `citations.json`: verbatim statement quotes for every cited node in every proof step.

## Attachments

None. A search of `/home/ubuntu/weil-src-slopmaster2/WeilConjectures` found no declaration tagged `(blueprint: thm-coef-rational-verdier)` and no sorry-free declaration stating this theorem.

## WANTED

None. The current blueprint proof and all cited DAG statements are present locally.

## What was checked and corrected

The theorem statement was compared with `literature/blueprint/main-20261015/blueprint/sec-smooth-purity/sk-lem-sp-tower/thm-coef-rational-verdier.md` and the unit `dag/units/sk-prop-sf-biduality-general.json`. It matches the finite-extension Verdier statement: raw rationalization of the integral category, exact E-linear anti-equivalence, evaluation and biduality obtained from integral maps, and compatibility with finite scalar extensions, units, and associators. The inherited source metadata pointed at the older master snapshot; it was corrected to the main-20261015 theorem and proof files.

Step 1 uses `lem-coef-integral-residue-tor` for equality of the integral constructible and finite-Tor domains, `thm-coef-integral-verdier` for the exact integral anti-equivalence and biduality, `prop-coef-integral-dualizing` for the dualizing object's constructibility, and `def-weil-derived-pullback-tensor-hom` for the R-linear internal-Hom operation. I read each cited statement and verified that these are exactly the facts used.

Step 2 uses `def-weil-linear-scalar-localization` and `def-weil-rationalization-karoubi`; their statements give the Hom tensor localization, object set, composition, and raw rationalized triangulation used in the explicit fraction construction. Step 3 uses the same rationalization definition and the integral exact anti-equivalence to transport distinguished triangles. Step 4 uses `thm-coef-integral-verdier`, `def-weil-rationalization-karoubi`, and `prop-weil-pbc-rational-transport`; the latter explicitly extends exact linear functors and natural transformations, which is the only off-unit generic transport use and is declared in `tool_uses`.

Step 5 uses `def-weil-derived-pullback-tensor-hom`, `lem-pur-integral-operations-preserve-constructible`, and `thm-coef-integral-verdier`; I checked that the tensor preservation statement supplies the constructible source of evaluation and that integral evaluation/biduality are supplied by the integral theorem. Step 6 uses `lem-coef-integral-finite-extension`, `def-weil-rationalization-karoubi`, and the operation definitions; the cited extension lemma contains the dualizing, internal-Hom, evaluation, biduality, quotient, unit, and associator compatibilities used. Step 7 uses the same extension lemma and rationalization definition for the explicit composition and identity equations.

I ran fresh Mathlib searches with `msearch.py` (LeanFinder, Loogle, grep, and LeanSearch), recorded in the node. They found only generic category-theory localization/equivalence results, so this geometric coefficient theorem is split rather than a Mathlib leaf. I checked small cases in the proof argument (zero object, point, empty scheme, identity extension, nested extensions, and localized scalar fractions). No new node was required, no duplicate was created, and no SGA 4 source was introduced.

## Review by Q01

I reread the full item, the current blueprint theorem and proof, the unit and chapter records, and every statement cited by all seven steps. Each use is quoted verbatim in `citations.json`; hypotheses such as finite type/separatedness, invertibility of `ell`, finite extension of coefficient fields, and the raw (non-Karoubi) scalar localization were checked against the item and cited statements. The only correction was correcting stale blueprint paths and appending fresh search records while retaining all earlier recorded searches. The longest step is the finite-extension compatibility argument; it is one continuous localization of the supplied comparison diagrams, with no hidden independent lemma. The split has no missing dependencies or unverified non-elementary facts.

## What could not be finished

Nothing.
