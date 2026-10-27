## Files written

- `dag/nodes/sec-trace-formula/lem-trf-geometric-fibre-affine-chart-test.json`: the item, split into four proof steps; no new nodes.
- `citations.json`: nine verbatim statement quotations, one for each cited node at each step.

## Attachments

None. I found no complete sorry-free project declaration with this item’s exact arbitrary-base-change, arbitrary-field-extension, projection-compatible chart statement.

## WANTED

None. The Stacks sources used by the split are present in `literature/stacks-project/`.

## What I checked and corrected

The imported node had the correct hypotheses and conclusion but no proof. I retained its arbitrary morphisms, arbitrary field extension, possible empty cover, and absence of finiteness, flatness, or nonemptiness assumptions. I supplied the two pullback pastings needed to identify the base-changed fibre with the scalar extension of the original fibre, then the open-fibre-product and affine-fibre-product steps for the charts, and finally the affine and open-cover reducedness tests. I did not create a node for any clause of the item: every result used already exists in the DAG. The Mathlib searches were run for this item on 2026-10-23 with LeanSearch, LeanFinder, Loogle, and Mathlib grep; the records and their actual hits are in the item’s `mathlib_searches` and `searches.jsonl`. They found only separate general fibre, tensor-chart, or reducedness declarations, with no single exact assembly.

## Review by Q37

I read the item’s source, Stacks More on Morphisms Tag 0576, and the affine-chart sources in Schemes Tags 01JR, 01I4, and 01J2. I also read the current DAG statements of `lem-weil-pbc-fibre-of-base-change`, `lem-weil-pbc-cartesian-square-pasting`, `lem-weil-pbc-open-fibre-product`, `lem-weil-pbc-fibre-product-affine-spectra`, `lem-weil-pbc-algebra-tensor-pushout-universal-property`, `lem-trf-reduced-scheme-open-cover`, `lem-weil-pbc-affine-scheme-reduced-iff`, `def-pc-fibre-product`, and `def-pc-reduced-scheme`; each citation says exactly the fact used in its step. Step 1 uses the existing fibre-of-base-change cartesian square and checks that the residue-field map is the one induced by (g). Step 2 uses cartesian-square pasting twice and the fibre-product universal property to retain both projections and the map to (X). Step 3 uses the open-fibre-product identification, the affine tensor-product spectrum theorem, and the tensor product’s ring structure to obtain (a\mapsto a\otimes1), (h\mapsto1\otimes h), and pure-tensor multiplication. Step 4 uses the open-cover reducedness equivalence and the affine reducedness equivalence; it explicitly checks the empty cover, empty fibre, and zero-ring cases. I checked that no step assumes flatness, finite presentation, algebraicity, or nonemptiness. The only correction was replacing the imported empty proof with this explicit assembly; no statement or dependency hypothesis was changed.
