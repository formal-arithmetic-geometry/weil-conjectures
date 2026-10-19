## Files written

- `dag/nodes/sec-zeta-weil/lem-zl-constant-sheaf-lseries.json` — the item, split into six proof steps; no new nodes.
- `citations.json` — verbatim statement quotations for every citation in every step.
- `searches.jsonl` — searches run through `msearch.py`.

## Attachments

None. I searched `/home/ubuntu/weil-src-slopmaster2/WeilConjectures` by the item id, its title and the notions `constant`, `Frobenius`, `LSeries`, and `zetaSeries`; no declaration states this item. The existing declarations around `AlgebraicGeometry.WeilSheaf.lSeries` are unrelated analytic `PowerSeries` definitions and do not identify the constant Weil stalk operators with the scheme zeta series.

## WANTED

None. The source material used here is present in the repository: the main-20261015 trace-transport unit, the main-20261015 Euler-product unit, the master definitions of the local Frobenius, coefficient datum, point counts and coefficientwise map, and Bhatt–Scholze for constant pro-etale stalks (already cited by the existing nodes).

## Not duplicates

No new nodes were created. The item uses `prop-euler-product`, which states the general closed-point product for every finite-type finite-field scheme; the item specializes its local factors to the constant rank-one Weil datum. It uses `lem-zl-constant-weil-datum`, which constructs the compatible normalized tower, while this item proves its two local Frobenius operators are identities and computes its L-series. It uses `def-weil-local-frobenius-trace` and `def-trf-frobenius-operators` only for their respective operator definitions, not as a restatement.

## What was checked and corrected

The imported item had no proof. I retained its hypotheses and dependencies and corrected one potentially misleading phrase: the finite-level operators are first assembled as an integral compatible system and then rationalized; an individual torsion module `A_n` is not tensored with `E` (which would be the wrong operation). I did not change the mathematical conclusion.

## Review by Q75

I read the item source (`literature/blueprint/main-20261015/blueprint/sec-trace-formula/sk-thm-trace-transport/_section.md`, the trace-transport setup specialized in the item's source place), the blueprint proof of `sk-thm-rationality`, and the complete statements of every cited node. I also read the source texts for `def-weil-local-frobenius-trace`, `def-trf-frobenius-operators`, `def-trf-iterated-weil-map`, `def-weil-constant-weil-structure`, `lem-zl-constant-weil-datum`, `def-weil-frobenius-point-transport`, `prop-euler-product`, `def-weil-point-counts-zeta`, `sk-def-zeta`, and `def-weil-coefficientwise-ring-hom-map`.

Step 1 uses the compatible constant datum, the iterated Weil-map definition, and the local-Frobenius definition. Those statements provide the finite-level maps, their compatibility, and the iterated composites; the identity-on-constants calculation is the one-line specialization of those definitions. Step 2 uses the local-Frobenius definition, point-transport definition, constant Weil structure, and the constant-datum lemma. I checked that the cited structure map is defined by sending each coefficient to the corresponding constant section, and that the cited datum identifies the rationalized object with the constant `E` object. This supports the explicit transport calculation and the degree return `g_Y^d \bar x = \bar x g_s^d`. Step 3 uses the separate finite-coefficient operator definition, the iterated Weil-map definition, the constant-datum lemma, and the multiplicative-iterate assertion of `prop-trf-scheme-galois-comparison`; it checks the scheme-Frobenius comparison and all finite-level identities before taking the integral realization and rationalization. Step 4 is elementary linear algebra from the rank-one degree-zero stalk stated by the constant datum: the matrix is `(1-T^d)` and its inverse is the geometric formal series. Step 5 cites clause 1 of `lem-weil-point-counts-finite` for finiteness of point sets, and uses exactly the statement of `prop-euler-product` (closed-point product and coefficientwise local finiteness), together with the two point-count/zeta definitions; I checked that their finite-field subfields, point counts, degrees, and exponential series agree. Step 6 uses clause 2 of `lem-weil-point-counts-finite` for bounded-degree finiteness, the same local-finiteness statement, and the coefficientwise ring-homomorphism definition; I checked the truncation argument modulo `T^(M+1)`, including the empty-scheme case and preservation of inverses under the coefficient map.

I searched Mathlib for the item concept with LeanSearch, LeanFinder, Loogle and source grep. The results were generic constant-sheaf categorical lemmas, Frobenius facts, and classical analytic L-series, with no declaration of this scheme/Weil local-Frobenius assertion. The unsuccessful Loogle query containing the unknown identifier `Frobenius` is recorded as invalid; the valid searches and their actual output are in `searches.jsonl`. No proof step exceeds 2000 characters, and I found no hidden independent lemma requiring a new node.

The scheme/Galois comparison is explicitly declared as a generic tool use in `split_report.tool_uses`; no unit in the zeta layer itself provides this comparison. Its statement gives the multiplicative iterates actually used. The finiteness theorem is Lean-closed and already used by the parent rationality split. I added these citations on self-review to avoid taking a theorem from a definition. The hypotheses verified are finite type over the fixed finite field for the Euler product and point finiteness, separated finite type and the specified normalized constant datum for both local operators, the prime condition `ell != p` and levels `n >= 1` for the finite coefficient comparison, and a one-dimensional degree-zero rational stalk for the determinant. No smoothness, properness, connectedness, curve hypothesis, or coefficient extension to the complex numbers was used.

## Unfinished work

None in the stage-1 split. New unsplit nodes: 0. New Mathlib leaves: 0. Server dry run and push follow this report.
