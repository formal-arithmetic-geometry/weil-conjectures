# Stage 1 report

## Files written

- `dag/nodes/sec-trace-formula/lem-trf-etale-source-smoothness.json`: repaired item split with four proof steps.
- `dag/nodes/sec-trace-formula/lem-trf-smooth-composition.json`: new Mathlib leaf for generic composition of smooth morphisms.
- `citations.json`: verbatim statement citations for every dependency used by every proof step.
- `searches.jsonl`: the four fresh msearch records for the new Mathlib leaf, in addition to the retained item searches.

## Attachments

None.

## WANTED:

None.

## What was wrong or corrected

The returned version used `lem-trf-etale-smooth-composition`, whose statement was exactly the forward clause of the parent item (D1). I deleted that parent-clause leaf and replaced it with the strictly more general Mathlib composition statement. Its Mathlib declaration and source are now `AlgebraicGeometry.smooth_comp` in `Mathlib/AlgebraicGeometry/Morphisms/Smooth.lean`, line 109; the LeanSearch, LeanFinder, Loogle, and grep records were rerun with the required item identifier and copied into the leaf. The item and leaf carry the full blueprint `via` ancestry with the item itself at the front (B9), and the item has the corrected Q110 creation record. The reverse and pointwise steps now cite both the existing open-image factorization node and the existing open-restriction node (C1). The old incorrect Mathlib names and source description were removed (B6), and the missing LeanSearch record was supplied (B7).

## What remains unfinished

Nothing for stage 1.

## Review by Q110

I read the retained item source in `literature/stacks-project/descent.tex`, the Stacks statements for Tags 036U, 05B5, 01UA and 01V6, the blueprint ancestor `lem-trf-local-term-locality` and its proof branch, and every existing DAG node cited by the repaired proof. I checked the no-separatedness, no-quasi-compactness, and no-Noetherian hypotheses against the item statement and checked the pointwise meaning as smoothness on an open neighbourhood.

Step 1 uses `lem-weil-pbc-etale-smooth-zero-dimensional-fibres` for the fact that each etale source map is smooth and `lem-trf-smooth-composition` for composition; both statements say exactly those facts. Step 2 uses `def-weil-etale-morphism` for flatness and local finite presentation, `lem-weil-pbc-flat-lfp-open` for openness of each image, `lem-weil-pbc-morphism-factors-through-open-subscheme` for the factor through the image and its surjectivity, `lem-weil-pbc-smooth-restrict-open-subschemes` for the open-restriction construction, and `lem-sbc-smooth-flat-surjective-source-descent` for descent. I verified that the restriction preserves flatness and local finite presentation directly from their local definitions, while the cited nodes supply the non-elementary openness, factorization, restriction notation, and descent assertions.

Step 3 uses `lem-weil-pbc-smooth-local-on-source`; its statement is exactly the open-cover gluing equivalence. Step 4 checks both directions on neighbourhoods: the open-restriction node identifies the restricted morphisms, the etale-smooth and composition nodes handle the forward direction, and the flat-lfp openness, factorization, and flat-surjective descent nodes handle the reverse direction. I checked that the restricted image contains `h(u)` and that the restricted source map is surjective, flat, and locally finitely presented. I copied every cited node's statement verbatim into `citations.json` and tested the edge cases of an identity cover, an empty scheme/family, a single open immersion, and a disjoint union cover.

## Not duplicates

- `lem-trf-smooth-composition` vs `lem-trf-etale-smooth-composition`: the deleted leaf specialized to an etale first morphism and restated the parent forward clause; the repaired leaf states generic composition of two smooth morphisms and is independent of the parent item.
- `lem-trf-smooth-composition` vs `lem-weil-pbc-smooth-restrict-open-subschemes`: the repaired leaf is composition for arbitrary smooth morphisms, while the existing node concerns restriction to open subschemes and its induced smoothness clauses.
