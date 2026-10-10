Files written:

- `dag/nodes/sec-curve-estimates/lem-exc-coinduced-functions-open-stabilizer.json` — statement, 2-step proof, status `split`.

Attachments: none.

WANTED: none.

What was wrong or incomplete: the imported item had an empty proof. I supplied the compactness/fibre argument and the finite-index core construction for an open normal subgroup. The repository's blueprint source files are not present locally; the item's imported blueprint metadata supplies the ancestor and proof place.

What I could not finish: no Lean declaration or Mathlib theorem exactly states the item.

## Review by J1

I read the item's source metadata for Stacks Tag 04JP (`definition-G-module-continuous`) and the existing coinduced embedding node that cites this item. Tag 04JP supplies the continuity/open-stabilizer context; the finite compactness and open-normal-basis details are explicitly identified as agent-supplied in the node source. The item statement introduces only a profinite group, a discrete space, and a continuous map, and has no statement dependencies.

Step 1 is the direct argument: discreteness makes each fibre open, compactness gives a finite cover by right coset neighbourhoods, and intersecting the finitely many open subgroups gives an open subgroup `V` with `f(xv)=f(x)`. I checked the containment `xV ⊆ x_i V_{x_i}` when `x ∈ x_i V_{x_i}` and tested the construction on the trivial group, a finite discrete group, and a constant map. Step 2 explicitly forms the finite-index core, the intersection of finitely many conjugates of `V`, which is open, normal, and contained in `V`; this preserves the equality from step 1.

I searched all DAG nodes and blueprint references for open-normal subgroup/core statements, searched the refreshed Lean checkout for the item id, tags, and relevant names, and searched Mathlib by LeanSearch, LeanFinder, and source grep. No exact declaration was found. Both proof steps are elementary calculations from continuity, compactness, and the finite-index core construction, so the citation manifest is empty.
