# Worker report: lem-pur-compact-product-proper-support-compatibility

## Files written

- `dag/nodes/sec-smooth-purity/lem-pur-compact-product-proper-support-compatibility.json` — existing item copied from the repository and marked `split`; no new nodes were required.
- `citations.json` — 13 verbatim statement quotes covering every proof-step citation.
- `report.md` — this report.

No Mathlib leaves or new nodes were created. The item has no finished declaration in `/home/ubuntu/weil-src-slopmaster2/WeilConjectures`; a repository-wide search found no declaration carrying the blueprint tag or the compact-support/support-compatibility statement.

## Attachments

None.

## WANTED

None. The proof uses the current DAG statements and the main-20261015 blueprint; no unavailable source was needed.

## What was wrong or incomplete in the imported item

The repository item was still `unsplit` and had no proof, proof dependencies, proof origin, or split report. Its statement and imported dependency list were retained. I supplied the missing finite-ring compactification argument, proper-support adjunction calculation, excision calculation, twist/cup identification, and etale-to-pro-etale comparison. I did not alter the mathematical statement or its hypotheses.

The item is not a Mathlib theorem. I ran the required Q07 LeanFinder, Loogle, grep, and LeanSearch searches; they returned only unrelated algebraic-geometry, etale algebra, and complex-support declarations (or zero hits), so `mathlib_match` remains null. The search records are in `searches.jsonl`.

## What I could not finish

Nothing remains unfinished in the stage-1 split. The delivery dry run is the remaining required validation step.

## Review by Q07

I read the complete item node, the current `sk-prop-an` unit and `sec-smooth-purity` chapter, and the main-20261015 proof source `literature/blueprint/main-20261015/blueprint/sec-smooth-purity/sk-prop-an/thm-pur-projective-bundle-formula.proof.md`, especially Step 1. I also opened the statements of every cited node. The item hypotheses match the source conventions: finite coefficient ring (A=A_{E,r}) with (r\ge1), separated finite-type schemes, bounded constructible finite-Tor inputs, proper closed supports where the first support maps are defined, and bounded-below etale-origin realizations for the comparison clause.

Step 1 cites `lem-pur-ordinary-kunneth-finite-ring`, whose statement says the ordinary finite-ring exterior-product map is an isomorphism, and `def-amb-etale-compact-support`, whose statement defines ordinary etale compact support as (Rr_*Dj_!). It also cites `def-weil-pbc-extension-by-zero`, which explicitly defines (j_!\) by sheafifying the zero-extension presheaf. I checked that the product compactification is proper and that the zero-extension tensor calculation is objectwise; the result is exactly the compact exterior-product map. This step checks (\ell\ne\operatorname{char}(k)) via `def-pur-conventions` and the ordinary Kunneth node's coefficient hypotheses.

Step 2 cites `def-pur-supported-exterior-product`, whose statement specifies the supported morphism and its closed-support adjunction construction, and `def-amb-etale-compact-support` for the compact-support direct image. I checked that a proper support maps as a closed subscheme into every separated proper compactification, that (j_!i_*\) is the closed pushforward, and that the two sides of the displayed (u_{Z\times W}\)-compatibility are the same adjoint after applying the tensor comparison and the three counits. The cohomology-class description follows by taking the adjunction map on (H^a).

Step 3 cites `lem-amb-closed-support-hom`, whose statement gives the cone formula for derived Hom from a closed-supported constant sheaf, and `def-amb-etale-compact-support`. I checked the excision map by applying that cone description to the two pairs ((\overline X,Z)) and ((X,Z)): (X) is an open neighbourhood of (Z), and (j_{\mathrm{ext}}K|_X\cong K), so the support cones agree. The map (j_!K\to j_{\mathrm{ext}}K) induces the stated second arrow, and the composite is the support-forgetting map under this excision identification.

Step 4 cites `def-coefficient-twists-detailed` for twist multiplication, `def-pur-supported-exterior-product` and `def-pur-supported-cup` for the two adjoint composites, `lem-pur-supported-cup-functoriality` for pullback, bilinearity, associativity, and the Koszul sign, `lem-pur-support-site-comparison` for equality of the etale and pro-etale supported products, and `lem-sf-class-compact-support-comparison` for compact-support comparison. I checked that the tensor of supported morphisms is literally the cup-product composite after identifying (A(r)\boxtimes A(s)\) with (A(r+s)), and that even degrees remove the sign. The comparison hypotheses are bounded-below and etale-origin exactly as required by the cited comparison statements.

The off-unit theorem citations are recorded in `split_report.tool_uses`: finite-ring Kunneth, the support cone calculation, support-site comparison, compact-support comparison, and cup functoriality are generic tools needed by the blueprint route. No duplicate or new node was introduced.
