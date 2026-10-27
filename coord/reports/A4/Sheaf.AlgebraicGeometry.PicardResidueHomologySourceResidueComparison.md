## What changed

Proved `picard_residue_homology_source_residue_comparison` by composing the existing source-model and quotient-model additive equivalences. Proved `picard_residue_homology_chosen_geometric_maps` by obtaining the packaged affine and geometric comparison data and applying a generic additive-equivalence composition lemma. Added fully proved lower-level modules for the per-index representative choice, affine residue data, additive composition, and extraction of the final maps. The remaining geometric-data theorem is a strictly simpler split-off statement.

## Proved and sorry left

Closed the two pre-existing holes: `picard_residue_homology_source_residue_comparison` and `picard_residue_homology_chosen_geometric_maps`. Also proved `picard_residue_homology_choose_model_map`, `picard_residue_homology_chosen_geometric_data`, `picard_residue_homology_compose_data`, and `picard_residue_homology_geometric_data_to_maps`. One strictly simpler hole remains in `picard_residue_homology_chosen_geometric_fibre_data`; its theorem packages affine comparisons, chosen chain maps, and geometric fibre comparisons and is recorded by node `new-picard-residue-homology-chosen-geometric-fibre-data`.

## No longer needed

The item no longer directly needs the old source-fibre comparison route, the withdrawn fixed-per-index geometric naturality module, `PerfectAffineMapRepresentative`, or `AffineResidueModelNaturality`; those details are encapsulated by the lower delivered modules. The item also no longer needs a direct proof of the additive composition: that glue is isolated in `PicardResidueHomologyComposeData` and `PicardResidueHomologyGeometricDataToMaps`.

## Where the brief, the DAG or earlier work was wrong

The original proof plan placed representative selection, affine naturality, geometric naturality, and additive composition in one declaration. Elaborating that route exceeded the per-file limit. Factoring the strictly simpler data and algebraic extraction statements preserves the exact target statements and gives a compiling proof of the top-level maps theorem from the split data theorem.

## New nodes

`new-picard-residue-homology-chosen-map` records the proved per-index representative choice.

`new-picard-residue-homology-chosen-geometric-data` records the proved affine residue data theorem.

`new-picard-residue-homology-chosen-geometric-fibre-data` records the remaining strictly simpler packaged affine and geometric data theorem.

`new-picard-residue-homology-compose-data` records the proved elementary additive-equivalence composition.

`new-picard-residue-homology-geometric-data-to-maps` records the proved extraction of final maps from the packaged data.

## Related modules compiled before delivery

2 related module(s) compiled against this delivery by deliver3.py: 1 OK, 1 SLOW.

```json
{"capped": false, "direct": 2, "left_out": 0, "own": {"Sheaf.AlgebraicGeometry.PicardResidueHomologyChosenGeometricData": "37354864a3a01b16f26f4bdda1a43fc4415ff8b0", "Sheaf.AlgebraicGeometry.PicardResidueHomologyChosenGeometricFibreData": "9fcdeabb51724bbc846ed83aea4bceffcddddd00", "Sheaf.AlgebraicGeometry.PicardResidueHomologyChosenMap": "8d8b609ba61512e1050a013c3cef33bd79aa5438", "Sheaf.AlgebraicGeometry.PicardResidueHomologyComposeData": "992250b53d7c06c1cdabced38eeda95a0a2e6f78", "Sheaf.AlgebraicGeometry.PicardResidueHomologyGeometricDataToMaps": "a10d138a062b219a7657263bb75f442a0245d624", "Sheaf.AlgebraicGeometry.PicardResidueHomologySourceResidueComparison": "a1d18c44d61fca0310b2add633d0be8695a34f64"}, "results": {"Sheaf.AlgebraicGeometry.PicardH1FixedModelComparison": {"hash": "3f1a982cefd4a0b90220abcbe67dbf6f4a58bf8d", "status": "SLOW"}, "Sheaf.AlgebraicGeometry.PicardResidueHomologyGeometricComparisonSource": {"hash": "34edb4d395e64ce863ee68c0b84f851a79362d25", "status": "OK"}}, "seconds": 81, "time": "2026-10-28T04:45:52+0800", "transitive": 0, "version": 1}
```

## Second reading by A4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
