Files written:

- `dag/nodes/sec-curve-estimates/lem-sc-brauer-zero.json` — repaired proof split and dependencies.
- `dag/nodes/sec-curve-estimates/lem-sc-open-curve-gm-direct-image-cohomology.json` — statement-only missing affine comparison; no Mathlib match.
- `citations.json` — verbatim statements used by each proof step.

Attachments:

- `AlgebraicGeometry.IsCurve.subsingleton_cohomologicalBrauerGroup_of_connectedSpace` belongs to `lem-sc-brauer-zero`; it is sorry-free, with the remaining open dependency recorded by the audit.

WANTED:

- None.

What was wrong and what changed:

- Removed `lem-sc-field-brauer-cohomology-equivalence`: the proper case needs only `lem-sc-brauer-injectivity` and `lem-sc-tsen`, and no central-simple-algebra comparison.
- Added `lem-sc-open-curve-gm-direct-image-cohomology` for the non-elementary open-immersion comparison used in the affine case.
- Replaced the inline closed-pushforward stalk argument with the finite direct-image exactness, finite pushforward cohomology, and algebraically closed point-cohomology citations.

What I could not finish:

- The new open-curve comparison remains statement-only as required by stage 1.

## Review by E1

I read the blueprint proof for `lem-sc-brauer-zero`, Stacks Tag 03RM (including the 03RE proof area), and the Lean declaration in `WeilConjectures/AlgebraicGeometry/Curve/Brauer.lean`. I opened every cited DAG node and copied its statement into `citations.json`. Step 1 uses exactly the compactification statement and the affineness statement for the complement. Step 2 uses the injection stated by `lem-sc-brauer-injectivity` and the cohomological Brauer vanishing stated by `lem-sc-tsen`; the removed field-comparison node was not needed. Step 3 uses the compactification, zero-dimensional finiteness, proper-affine finiteness, and divisor exact sequence. The new open-curve node states the required isomorphism through degree 2. For each boundary point, the closed immersion is finite, so `lemma-weil-pbc-finite-direct-image-exact` supplies exactness and `lem-weil-pbc-finite-pushforward-cohomology` supplies the cohomology identification; `lem-sc-point-z-cohomology` then gives positive-degree vanishing because the residue field is the algebraically closed field k. I checked the hypotheses on the basic cases `A^1_k`, `G_m`, and a proper smooth projective curve, and checked the point case `Spec k`. I searched the DAG, blueprint index, Lean source, and Mathlib source before creating the new node; no duplicate or Mathlib theorem was found. The returned issues were repaired exactly: the superfluous field-comparison node was deleted, the missing open-curve comparison was added, and the unsupported inline pushforward argument was replaced by the required citations.
