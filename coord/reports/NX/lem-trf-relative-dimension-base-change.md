# Stage-1 report: lem-trf-relative-dimension-base-change

## Files written

- `dag/nodes/sec-trace-formula/lem-trf-relative-dimension-base-change.json`: split statement with four proof steps; no Mathlib match.
- `citations.json`: verbatim excerpts for every cited node and proof step.

## Attachments

None. I searched the slopmaster2 source for the item id, title, and relative-dimension/base-change notions; no sorry-free project declaration states this item exactly.

## WANTED

None. The Stacks source is present locally at `literature/stacks-project/morphisms.tex`.

## Not duplicates

None: no new nodes were created. The existing Tag 02FY node `lem-sc-fibre-dimension-after-base-change` is a strictly more general local-dimension/fibre-identification input, while this item is the pure-component-dimension consequence of it.

## What was wrong or corrected

The imported item had an empty proof and no proof dependencies, although its source Tag 02NK says the result is immediate from Tag 02FY. I expanded that shortcut into explicit fibre, local-dimension, and component-dimension steps. I retained the exact hypotheses and conclusion. The statement's integer $d\ge0$ is used as the natural number parameter in the existing dimension lemmas. No statement error was found.

## Review by NX

I read the item against `literature/stacks-project/morphisms.tex`, especially Tag 02NK (lines 5582–5591), Tag 02NJ (the definition immediately above), and Tag 02FY (lines 5425–5450), and checked the existing DAG statements cited in every step. Step 1 uses `lem-weil-pbc-lft-base-change` for local finite type after base change, `def-pc-scheme-fibre` for the scheme-theoretic fibre, and `lem-sc-fibre-dimension-after-base-change` for both the residue-field fibre identification and equality of local dimensions. Step 2 applies the same base-change lemma to the fibre over `Spec κ(s)`, uses `def-weil-pure-dimension` for the component hypothesis, and uses `lem-sbc-equidimensional-open-local-dimension` to obtain local dimension $d$ at every point. Step 3 applies the Tag 02FY equality to each point of each nonempty new fibre and combines it with Step 2. Step 4 verifies that each new fibre is locally Noetherian via `pqf-lem-locnoeth-lft` (a locally finite-type scheme over the field `κ(s')`), then uses `lem-sbc-constant-local-dimension-components` to turn constant local dimension into component dimension and `def-weil-pure-dimension` to conclude purity; empty fibres are vacuous. I checked the edge cases $d=0$, empty fibres, identity base change, and a field-extension base change. All cited statements say exactly the facts used, and every citation quote in `citations.json` is copied verbatim from its node. The Mathlib searches for the item were run with LeanFinder, LeanSearch, Loogle, and Mathlib grep; they found only smooth/locally-finite-type stability results and no general pure-fibre-dimension theorem.
