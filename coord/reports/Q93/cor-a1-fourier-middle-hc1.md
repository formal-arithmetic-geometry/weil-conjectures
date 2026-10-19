# Q93 stage-1 report: cor-a1-fourier-middle-hc1

## Files written

- `dag/nodes/sec-deligne-laumon-a1/cor-a1-fourier-middle-hc1.json`: updated and split statement; Mathlib searches found no matching declaration.
- `dag/nodes/sec-deligne-laumon-a1/prop-a1-fourier-weight-upper.json`: new unsplit statement node; Mathlib searches found no matching declaration.
- `dag/units/sk-c-dl-a1-hc1.json`: recorded the realized statement and proof step for this key unit node.
- `citations.json`: verbatim proof-step citations.

## Attachments

None. The slopmaster2 declaration is not attachable because its proof transitively rests on sorry declarations.

## WANTED

None.

## Not duplicates

- `prop-a1-fourier-weight-upper` vs `sk-p-dl-a1-fourier-weight`: the latter is a blueprint section record rather than an existing DAG node; the new node makes its proposition `v ≤ w+1` a self-contained DAG statement with all objects and hypotheses introduced.
- `prop-a1-fourier-weight-upper` vs `cor-fd-l2-plancherel-middle-extension`: the existing node asserts the older exact equality `v=w+1` under a different route, while the new node asserts the current blueprint's upper bound `v≤w+1` for the current Fourier-partner hypotheses.

## What was wrong and what changed

The imported item was based on the old master snapshot. Its statement added unramifiedness at infinity and an irreducible geometric fundamental-representation hypothesis, while the current main-20261015 statement has a nontrivial additive character, irreducibility among lisse Weil sheaves, punctual purity, and constituent nonexceptionality only. Its old Step 1 consequently invoked the unramified-at-infinity lemma even though that hypothesis is absent. Its old Step 2 also used the stale exact-weight claim `v=w+1`; the current Fourier-weight unit and the upstream source declaration prove only `v≤w+1`. I replaced those steps with the current route: Fourier middle-extension shape, generic partner purity plus the new upper-weight node, boundary semicontinuity, and Frobenius-equivariant stationary phase.

## Review by Q93

I read the current item statement and proof in `literature/blueprint/main-20261015/blueprint/sec-deligne-laumon-a1/sk-c-dl-a1-hc1/cor-a1-fourier-middle-hc1.md` and its `.proof.md`, the unit record `dag/units/sk-c-dl-a1-hc1.json`, and the source declaration comments and theorem signature in `WeilConjectures/DeligneLaumon/AffineLine/DegreeOne.lean`. The theorem signature confirms the four hypotheses used by the corrected statement: nontrivial character, irreducible lisse sheaf, nonexceptionality, and punctual purity; there is no unramified-at-infinity parameter.

For Step 1 I read `prop-a1-fourier-middle-extension.json`. Its statement supplies exactly the dense dual open, nonzero irreducible lisse partner, and middle-extension Fourier isomorphism used in the step. I therefore removed the prior citation to `lem-a1-unramified-nonexceptional`, whose hypothesis was unavailable. For Step 2 I read `thm-fd-generic-fourier-sheaf-pure.json`, which supplies punctual purity of the partner of some real weight `v`, and I added `prop-a1-fourier-weight-upper.json`, whose statement is the current section proposition `v≤w+1`; both hypotheses match the corrected item. This new node was searched with LeanSearch, LeanFinder, Loogle, and Mathlib grep, all with no relevant Mathlib declaration.

For Step 3 I read `lem-wf-boundary-semicontinuity.json` and `def-wf-middle-extension.json`. The former explicitly transfers an eigenvalue bound on the dense lisse open to the middle-extension stalks on all of the curve, and the latter defines the middle extension as `j_*𝓕`; taking `β=w+1` is the stated specialization. For Step 4 I read `cor-fd-origin-stationary-phase.json`; its statement gives the Frobenius-equivariant identification of `H_c^1` with the origin stalk under the middle-extension transform. I also read `def-weil-punctual-weights.json` for the final translation from the inequality `|ι(α)|²≤q^{w+1}` to the phrase “weights at most `w+1`”. The `citations.json` quotes are copied verbatim from these node statements.

I checked that every non-elementary fact in the four steps is represented by a cited node, that each cited node states the exact fact taken from it, that the new node is strictly smaller than the item, and that no proof step is a restatement of the target. I did not write Lean or run a compiler, Lake, or build tool.

## What could not be finished

Nothing remains for this stage-1 split; the required dry run is the remaining delivery check.
