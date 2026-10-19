# Report: lem-per-snc-boundary-parameter-criterion

1. Files written:

- `dag/nodes/sec-deligne-laumon-a1/lem-per-snc-boundary-parameter-criterion.json`: split statement with four proof steps; no new nodes.
- `citations.json`: verbatim statement excerpts for every cited node at every step.
- `report.md`: this report.

All Mathlib searches for the item were run with `msearch.py`. The searches found no Mathlib declaration of the scheme-theoretic strict-normal-crossings criterion.

2. Attachments:

None.

3. WANTED:

None. The proof follows the local algebra in Stacks Tags 0BI9 and 0BIA, with the cited Stacks algebra lemmas already represented in the DAG.

4. What I checked and changed:

The imported node had the exact intended statement but no proof split. I retained its hypotheses, including regular Noetherian X, a closed subscheme H, the empty-product case, and the concluding reduced/Cartier/intersection clauses. I did not add or remove hypotheses.

## Not duplicates

- `lem-per-snc-boundary-parameter-criterion` vs `lem-per-regular-boundary-divisorial-chart`: the existing node starts with a strict normal crossings boundary and constructs its divisorial log chart; this item proves the iff characterization of that boundary by ordinary local product equations.
- `lem-per-snc-boundary-parameter-criterion` vs `lem-trf-nc-coordinate-max-stratum`: the existing node assumes a fixed list of coordinate functions on a regular locally Noetherian scheme and computes branch strata; this item characterizes the global boundary predicate and supplies both directions.
- `lem-per-snc-boundary-parameter-criterion` vs `lem-trf-etale-component-coordinate-identification`: the existing node identifies already-known reduced regular components after an etale coordinate equation; this item proves the component and intersection conditions from the local equation and proves the reverse local equation from them.

## Review by Q82

I read the item and the fixed ancestor/unit route in the blueprint, and read Stacks `etale.tex` at Tags 0BI9 and 0BIA, including the proof that regular component intersections give local parameter equations. For the forward direction, Step 1 uses exactly the boundary definition's regular component and codimension hypotheses, then the existing regular-local quotient-parameter statement and the regular-sequence/dimension statement to obtain one local equation for each component. Step 2 checks the cotangent-space kernel dimension against the intersection codimension, uses Nakayama to extend the actual component equations to one parameter system, and then uses the existing regular-local UFD statement to identify the reduced Cartier equation with the square-free product. For the converse, Step 3 checks nonzerodivisor, domain, prime-factor, regular-quotient, codimension, and finite-component clauses from the local product condition; every cited node says the precise fact used. Step 4 records the empty-product convention and the stated reduced/Cartier/intersection consequences. I read each cited node file and copied every citation quote verbatim into `citations.json`. I also ran fresh LeanFinder, Loogle, and Mathlib grep searches; their results were recorded as no match. No Lean source or compiler was used.
