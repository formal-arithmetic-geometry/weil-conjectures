# Stage 1 report: `lem-weil-pbc-horseshoe-morphism-lift`

## Files written

- `dag/nodes/sec-proper-base-change/lem-weil-pbc-horseshoe-morphism-lift.json`: marked `split` with four sourced proof steps.
- `dag/nodes/sec-proper-base-change/lem-weil-pbc-acyclic-map-to-injective-nullhomotopy.json`: Mathlib leaf; bounded-below injective complexes are K-injective and maps from acyclic complexes are null-homotopic.
- `coord/reports/F1/lem-weil-pbc-horseshoe-morphism-lift.md`: this report.

## Attachments

None. The statement has no Lean declaration on either audited branch.

## WANTED

- Weibel, *An Introduction to Homological Algebra*, Lemma 2.2.8 and Theorem 2.4.6, for the classical horseshoe/naturality presentation cited by the imported node. The proof is recorded as agent-written from the explicit construction and Stacks Tags 0136 and 013R.

## What was wrong or incomplete

The imported item had an empty proof despite its source describing the compatible middle lift. I wrote the degreewise splitting construction, factored the chain and augmentation defects through the outer terms, removed the defect by the bounded-below injective null-homotopy leaf, and checked the corrected middle map against both rows and the augmentation. The only notation correction found during review was replacing the ill-typed `alpha' beta` with the valid horseshoe identity `beta alpha = 0`.

## What could not be finished, and why

The Weibel book is not present in the literature checkout, so the proof remains marked agent-written; the Stacks sources supply the splitting and null-homotopy ingredients. No Lean was written or compiled.

## Review by F1

I checked the four steps against the imported route and the cited Stacks ingredients. Step 1 uses the existing Tag 0136 Mathlib leaf for row splittings. Step 2 spells out the exactness factorization and augmentation calculation. Step 3 uses the new Mathlib leaf, whose search records cover LeanSearch, LeanFinder, Loogle, and source grep, for Tag 013R. Step 4 verifies the chain-map, row, and augmentation identities. `python3 tools/check_dag.py` and `python3 tools/review_split.py lem-weil-pbc-horseshoe-morphism-lift` pass; no Lean was built.
