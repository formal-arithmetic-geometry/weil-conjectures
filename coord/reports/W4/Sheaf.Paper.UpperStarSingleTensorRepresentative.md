## What changed

Replaced the proof hole in
`AlgebraicGeometry.Etale.upperStar_single_tensor_representative` with a complete
counit diagram calculation. Its statement is unchanged. The ordinary tensor/single
comparison and its transport to the specified natural iso are proved generically.
The proved generic `tensor_single_cochain_counit` combines them with the cochain
tensor counit square, the single-coefficient representative equation, and
naturality. Its regular predicate avoids repeated concrete cochain structure
conversions in the final specialization.

`Sheaf.Paper.UpperStarTensorCochainRepresentative` proves the cochain square from
the existing homotopy-category square. Its `LaxSquareHδ` packaging avoids repeated
kernel expansion. The ordinary comparison is converted to the cochain oplax map
at the generic category level, before specialization to sheaves.
`Sheaf.Paper.UpperStarSingleCoefficientRepresentative` proves the geometric
representative equation using the canonical single-coefficient iso. The canonical
tensor-single comparisons stay folded and enter the diagram through their proved
defining equations.

After profiling and local optimization, split existing declarations to bound
individual compile times. `Sheaf.Paper.UpperStarSingleTensorDefinitions` contains
the three original definitions, with signatures and bodies verbatim.
`Sheaf.Paper.ScalarCoefficientSinglePullbackIso` contains the existing scalar
coefficient equality, with signature and `rfl` proof verbatim. The item retains
its original public imports and publicly imports the new modules, preserving all
original names and public availability. No existing statement or construction
changes. See `coord/changes/w4-upper-star-single-file-split.md`.

Updated the item's DAG proof and Lean attachments, and added the five nodes below.
No existing module besides the item is changed. Both direct importers,
`ScalarTensorRepresentativeCalculus` and `ScalarSheafTensorPullbackComplex`, compile
unchanged against the delivery. Their temporary copies were removed. All six final modules compile without
profiling; the slowest check took 22.1 s.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.Etale.upperStar_single_tensor_representative`
(node `lem-pur-upper-star-single-tensor-representative`).

The existing `scalarCoefficientSinglePullbackIso_eq` remains proved by `rfl`.
The new `AlgebraicGeometry.Etale.upperStar_tensor_cochain_representative`,
`AlgebraicGeometry.Etale.upperStar_single_coefficient_representative`,
`AlgebraicGeometry.Etale.tensor_single_cochain_counit`, and all private helpers
are proved. No holes added or split off; no `sorry` remains in
the six delivered modules.

## No longer needed

None. All original mathematical ingredients remain needed. No unit step, module,
node or upstream declaration is withdrawn. The moved declarations remain public.
The proved source-library lemmas
`CochainComplex.mapBifunctorComparison_δNatTrans_single₂` and
`CochainComplex.mapBifunctorSingle₂Iso_inv_naturality₂` close the ordinary
single-complex calculation without adding a new obligation.

## Where the brief, the DAG or earlier work was wrong

The initial source was quarantined together with its scalar-data dependencies.
Their original contents returned to the live repository during this session, so
the sandbox copies of those dependencies were removed. The mathematical argument
follows the original plan and Stacks Tags 07A4 and 0FPH. No flatness hypothesis on
the complex or coefficient is required: this is the counit equation. The zero
complex, zero coefficient and identity coefficient iso obey the same counit and
naturality equations. No target or mathematical definition changes.

The file organization changes only to keep compile times below the required
limit. The new definition node and equality node record existing constructions
and a previously proved equality at their new file locations. A separately
compiled generic diagram lemma keeps the final specialization below the file limit.

## New nodes

`lem-pur-upper-star-tensor-cochain-representative`, realized by
`AlgebraicGeometry.Etale.upperStar_tensor_cochain_representative` in
`Sheaf.Paper.UpperStarTensorCochainRepresentative`, records the proved transport
of the homotopy-category tensor counit square to cochain representatives.

`lem-pur-upper-star-single-coefficient-representative`, realized by
`AlgebraicGeometry.Etale.upperStar_single_coefficient_representative` in
`Sheaf.Paper.UpperStarSingleCoefficientRepresentative`, records the proved
identification of the geometric representative on a single coefficient.

`def-pur-upper-star-single-tensor-comparisons`, realized by the three unchanged
canonical definitions in `Sheaf.Paper.UpperStarSingleTensorDefinitions`, records
only their relocation.

`lem-pur-scalar-coefficient-single-pullback-iso`, realized by the unchanged
`AlgebraicGeometry.Etale.scalarCoefficientSinglePullbackIso_eq` in
`Sheaf.Paper.ScalarCoefficientSinglePullbackIso`, records its relocation.
`lem-pur-tensor-single-cochain-counit`, realized by
`AlgebraicGeometry.Etale.tensor_single_cochain_counit` and its regular predicate
`TensorSingleCounitSquare` in `Sheaf.Algebra.Homology.TensorSingleCounit`, records
the fully proved generic assembly of the single-coefficient counit square. It
introduces no missing proof.

All five nodes add zero holes and preserve the unit route.

## Second reading by W4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
