## Files written

- `lem-zl-relative-curve-punctual.json`: statement node, split; no new nodes and no Mathlib leaf.

## Attachments

None. The source declaration `AlgebraicGeometry.hasWeightsAtMost_higherLowerShriek_of_isAffine_fiber` contains `sorry`, so it is not a finished attachment.

## WANTED

None.

## What was wrong or incomplete

The imported node used the older master statement and did not include the current blueprint's separated finite-type base, relative-dimension-one, separated quasi-compact morphism, affine-fibre hypotheses, or the explicit closed point degree and eigenvalue formulation. I updated it to the main-20261015 statement and followed its proof file. The imported proof was also too compressed about the finite constant extension and the direct-sum Frobenius action; the single proof step now states these arguments explicitly. No new node is required: these are elementary geometric and linear-algebra observations inside the proof, while the four substantive inputs are existing nodes.

## Review by Q125

I read the current item source and its proof at `literature/blueprint/main-20261015/blueprint/sec-deligne-laumon-general/sk-p-dl-general-relative-line/lem-zl-relative-curve-punctual.{md,proof.md}`, the unit record, the chapter record, and the Lean docstring and statement in `WeilConjectures/DeligneLaumon/Reduction/RelativeAffineLine.lean:186-201`. The Lean declaration has a `sorry`, so I did not attach it. I checked the updated statement clause by clause against the current blueprint, including the finite-type separated base, smooth separated quasi-compact relative curve, affine fibres, lisse punctually pure sheaf, nonnegative degree, closed point of degree `m`, and the bound on every eigenvalue.

The sole proof step cites `thm-cbc-qbar` for the compact-support base-change stalk identification, `lem-tw-punctual-rescaling` for preservation of weight over the residue field, `thm-a1-curve-upper` for each smooth geometrically connected curve component, and `lem-a1-weight-bound-constant-extension` for descent from the finite constant extension. I opened each cited node and verified that its statement says exactly the fact used. The finite extension splitting of the finitely many geometric components and the block-diagonal direct-sum observation are written explicitly and are elementary consequences of the hypotheses and cited statements. The fibre is empty only vacuously; otherwise every component is a smooth geometrically connected affine curve, so the curve estimate applies. The Mathlib searches (LeanFinder, LeanSearch, Loogle, and grep, including a second phrasing for component descent) found no matching theorem; the Loogle geometric-connectedness hits are only general scheme-morphism declarations and do not state the weight estimate.
