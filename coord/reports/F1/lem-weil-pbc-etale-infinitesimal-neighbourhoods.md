# Worker report: `lem-weil-pbc-etale-infinitesimal-neighbourhoods`

## Files written

- `dag/nodes/sec-proper-base-change/lem-weil-pbc-etale-infinitesimal-neighbourhoods.json`: split into four Stacks 0A43(2) proof steps.
- `dag/nodes/sec-proper-base-change/lem-weil-pbc-etale-artinian-point-criterion.json`: new unsplit support statement; Mathlib verdict: no match.
- `dag/nodes/sec-proper-base-change/def-weil-essentially-finite-type.json`: new unsplit definition statement; Mathlib verdict: no match.
- `dag/nodes/sec-proper-base-change/def-weil-etale-at-a-point.json`: new unsplit definition statement; Mathlib verdict: no match.
- `dag/nodes/sec-proper-base-change/lem-weil-pbc-etale-locality.json`: new unsplit statement; Mathlib verdict: no direct scheme-level match.
- `dag/nodes/sec-proper-base-change/lem-weil-pbc-etale-locus-open.json`: new unsplit statement; Mathlib verdict: no direct scheme-level match.

## Attachments

None.

## WANTED

None. The cited Stacks sources are present in `literature/stacks-project/`.

## Findings

The source is More on Morphisms, Lemma 0A43(2). Its proof uses the local Artinian lifting criterion: for a point over the closed subscheme, every small extension factors through some infinitesimal neighbourhood because the Artinian maximal ideal is nilpotent; etaleness of every neighbourhood supplies the lift, and etale is smooth of relative dimension zero. The final open neighbourhood is supplied by the etale-locus openness result. The imported statement was retained unchanged. No Lean was written or compiled.

## Checks

Mathlib searches used LeanSearch, LeanFinder/Loogle, and a source grep for the item and every new node; no Mathlib theorem states the infinitesimal-neighbourhood criterion. The support nodes are unsplit and carry complete source locations and searches.

## Review by F1

I checked the four proof steps against `more-morphisms.tex`, Lemma 0A43(2), lines 5230--5255 and its cited pointwise lifting lemma at lines 3575--3610. The localization step preserves finite type and local Noetherian hypotheses; the ideal-sheaf stalk calculation gives exactly `A/I^(n+1)` and `B/I^(n+1)B`; the Artinian criterion is cited at the point where every quotient hypothesis is available; and the last step uses the finite-type etale-locus openness result to assemble the pointwise conclusions into the required open `W`. I also checked each cited node exists on this branch, that all new nodes inherit chapter `sec-proper-base-change` and unit `sk-thm-p1`, and that every unsplit support node has LeanSearch, LeanFinder or Loogle, and grep records.
