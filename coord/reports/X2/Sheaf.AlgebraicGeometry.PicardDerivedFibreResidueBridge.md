## What changed

The target bridge now delegates its finite-family model-selection interface to
`picard_derived_fibre_residue_model_data` and its fixed-model comparison interface
to `picard_derived_fibre_residue_bridge_core`. The target proof is complete and
assembles the two strictly lower interfaces. Two new modules were added under
`lean/Sheaf/AlgebraicGeometry/`.

## Proved and sorry left

Proved: `AlgebraicGeometry.Scheme.picard_derived_fibre_residue_model_data` and
`AlgebraicGeometry.Scheme.picard_derived_fibre_residue_bridge`.

Sorry left: `AlgebraicGeometry.Scheme.picard_derived_fibre_residue_bridge_core`
(node `new-picard-derived-fibre-residue-bridge-core`). This is the strict
fixed-model residue naturality part of the argument; the model-selection split is
closed in this delivery.

## No longer needed

The target and model-data proof no longer import
`Sheaf.AlgebraicGeometry.PicardH1CommonMinimalModel`; the model-data module uses
the narrower public perfect direct-image and finite-free residue-model APIs and
contains local restriction helpers. The target also no longer directly imports
`Sheaf.AlgebraicGeometry.AffineResidueModelNaturality`,
`Sheaf.AlgebraicGeometry.PerfectAffineMapRepresentative`,
`Sheaf.AlgebraicGeometry.PicardResidueHomologyGeometricComparison`,
`Sheaf.AlgebraicGeometry.PicardResidueHomologyGeometricComparisonSource`, or
`Sheaf.AlgebraicGeometry.PicardResidueHomologyGeometricComparisonTargets`; the
fixed-core interface owns the relevant proof dependencies without the source
cycle.

## Where the brief, the DAG or earlier work was wrong

The original proof plan treated common model selection and fixed-model geometric
naturality as if they were available from the target hypotheses. The existing
common minimal-model theorem additionally requires universal structure-sheaf
adjunction isomorphisms and finite locally free descent witnesses, which are not
arguments of this target. The fixed-model naturality theorem is likewise a
separate geometric obligation. They are therefore recorded as two strictly
smaller intermediate nodes rather than asserted as existing dependencies.

## New nodes

`new-picard-derived-fibre-residue-model-data` records only simultaneous affine,
strictly-perfect representatives and localization isomorphisms; its theorem is
proved here from perfect direct-image base change and finite-free residue models.

`new-picard-derived-fibre-residue-bridge-core` records only the fixed-model
comparison equivalences, chain representatives, and the two naturality equations.

## Second reading by X2

1. I compared the delivered target module with the repository version. The
   theorem signature of `picard_derived_fibre_residue_bridge` is unchanged byte
   for byte; only its proof, proof-only imports, and the two new intermediate
   modules were added. Verdict: pass.

2. I compiled all three delivered modules with `lcompile.py --all`. The model
   selection theorem is fully proved. The bridge theorem is assembled from the
   two strict lower interfaces, and the remaining named `sorry` is only
   `picard_derived_fibre_residue_bridge_core`, with its matching DAG node and
   complete source/proof docstring. No forbidden declarations or hollow
   definitions occur. Verdict: pass, with that one documented split-off hole.

3. I checked both new statements against their Lean declarations and the
   edge case `n = 0`. The model-data statement supplies exactly the common
   affine and strictly-perfect data used by the target; the core statement
   supplies exactly the fixed-model comparisons and naturality equations.
   Neither adds hypotheses or weakens a conclusion. Verdict: pass.

4. I checked the proof route and pruning. The target uses the model-data and
   fixed-core interfaces; the old common-minimal-model dependency and the
   direct residue comparison imports are no longer required by the target.
   Proof-only imports are plain imports in the new modules, and the unit route
   remains represented by the target bridge node. Verdict: pass.

5. I checked the DAG records. The target node's `proof`, `proof_deps`, and
   `proof_origin` match the assembled proof; the model-data and core nodes have
   matching Lean declarations, sources, proof dependencies, and split/proved
   statuses. Verdict: pass.

Changed during second reading: made proof-only imports non-public, added direct
public imports for declarations used by the core statement, and expanded the
core theorem's docstring to include its complete proof route.
