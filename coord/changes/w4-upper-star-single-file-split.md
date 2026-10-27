# Split the tensor-single comparison declarations into smaller modules

Item: `Sheaf.Paper.UpperStarSingleTensorRepresentative`, group W4.

Profiling found 10.7–26.1 seconds of kernel checking in the existing
`upperStarSingleCoefficientIso` definition. Its target theorem statement alone
checks in about five seconds, while the unsplit proof exceeded 120 seconds.
After optimizing the tensor square's packaging and the local diagram calculation,
this delivery splits the existing declarations to keep each file within 60 seconds.
The complete unsplit theorem proof still took about 100 seconds in the kernel.
The ordinary comparison and diagram calculation now occur at the generic category
level in the proved `Sheaf.Algebra.Homology.TensorSingleCounit`; the item specializes
its named square. This module adds no proof holes.

The following declarations move from the item to
`Sheaf.Paper.UpperStarSingleTensorDefinitions`, with signatures and bodies verbatim:

- `AlgebraicGeometry.Etale.tensorSingleRepresentative`
- `AlgebraicGeometry.Etale.upperStarSingleCoefficientIso`
- `AlgebraicGeometry.Etale.upperStarTensorSingleIso`

The already proved `AlgebraicGeometry.Etale.scalarCoefficientSinglePullbackIso_eq`
moves, with its signature and `rfl` proof verbatim, to
`Sheaf.Paper.ScalarCoefficientSinglePullbackIso`.

The item retains its three original public imports and publicly imports both new
modules. Every original public declaration remains available to its importers,
with the same universe parameters, type, body, and visibility. No global instance
or attribute changes. Local proof attributes do not affect importers. No adopted
source-library module changes. The DAG attachments record the new locations.

Both direct importers were compiled unchanged against the complete sandbox:
`Sheaf.Paper.ScalarTensorRepresentativeCalculus` (30.9 s) and
`Sheaf.Paper.ScalarSheafTensorPullbackComplex` (18.6 s). Both passed. Their temporary
sandbox copies were removed after confirming byte equality with the shared source;
no consumer adaptation is delivered. The final theorem compiled in 21.6 s, with
15 s in the kernel; the generic helper module compiled in 18.0 s.
