# Worker report

## Files written

- `dag/nodes/sec-smooth-purity/lem-pur-integral-twist-line-inverse-image.json` — statement split into five proof steps; no new nodes; Mathlib searches recorded.
- `citations.json` — 22 verbatim statement citations, covering every node used by every step.
- `report.md` — this report and the Q88 review.

## Attachments

None. No finished declaration in `WeilConjectures/` states this item exactly; the source declarations searched were only definitions or sorry-backed constructions.

## WANTED

None.

## Not duplicates

No new nodes were created. The existing nodes `det-prop-sfb-qlbar-colimit-x-integral-limit`, `det-prop-sfb-qlbar-colimit-x-pullback`, `det-prop-sfb-cartesian-coefficients-twists`, and `lem-pur-inverse-image-compatible-free-tower` are strictly more general tools or tower statements; they do not state this item's four-clause completed-line comparison with the explicit maps `alpha`, `tau`, `rho`, `iota`, and `j`.

## What was wrong or incomplete

The imported item had no proof and the parent proof's scheme-naturality sentence cited only the broad cartesian-twist proposition, whose statement did not expose the completed inverse-limit map or the coefficient-inclusion squares. I retained the item statement and made those maps explicit in five steps. The proof uses the completed coefficient inverse-limit and pullback nodes for `alpha`, the compatible local-basis tower for `tau`, the ringed-topos tensor comparison for `rho`, and tower naturality for both field-inclusion identities. No SGA 4 or SGA 4½ source is used.

## What could not be finished

Nothing remains unfinished. This is a stage-1 natural-language split; no Lean file was written and no compiler or Lake command was run.

## Review by Q88

I read the item source `sk-prop-sfb-cartesian-coefficients-twists.proof.md`, specifically its “Roots of unity” and “The integral twist” paragraphs, and checked the chapter `sec-smooth-purity` and unit `sk-prop-sf-existence`. I also read every cited node in full. Step 1 uses the exact limit identification in `det-prop-sfb-qlbar-colimit-x-integral-limit`, its inverse-image form in `det-prop-sfb-qlbar-colimit-x-pullback`, the finite constant-section isomorphism in `prop-weil-pbc-proetale-constant-ring-map`, and the definition of the completed sheaf; these jointly give the stated projection formula for `alpha` under the hypotheses that `ell` is invertible. Step 2 applies the compatible inverse-tower statement to the roots-of-unity tower: the local compatible generators and cover come from `det-def-sp-tate-twist-locally-free`, and the transition and semilinearity checks come from `lem-pur-roots-of-unity-inverse-image-iso`; the coefficient-ring comparison required by that tower is Step 1. Step 3 uses the stated tensor pullback isomorphism, the constant-ring map, local rank-one triviality, and the definition of the twist to construct the semilinear `rho` and verify its section formula; the cartesian-twist node confirms that the resulting map is an isomorphism. Steps 4 and 5 read the naturality clause of `lem-pur-inverse-image-compatible-free-tower` literally: the maps induced by `O_E` contained in `O_F` are compatible maps of finite quotient towers, so equality after every projection gives the `alpha` square, and the tensor formula gives the `rho` square. I checked the edge cases `S` or `S'` empty, `H=Q_ell`, `E=F`, and the zero twist section; all are covered by the same limit and tensor universal properties. Each proof step is below the 2000-character review threshold, and `proof_deps` is exactly the union of the five steps' uses. The Mathlib searches were rerun with `msearch.py`; they found only generic scheme/site declarations and no complete sheaf Tate-twist result.
