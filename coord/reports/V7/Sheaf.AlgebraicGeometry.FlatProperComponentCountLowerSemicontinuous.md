## What changed

Proved `AlgebraicGeometry.Scheme.Hom.geometricComponentCount_lowerSemicontinuous` in
`lean/Sheaf/AlgebraicGeometry/FlatProperComponentCountLowerSemicontinuous.lean`.
The proof defines the count by `Nat.card`, proves geometric-fibre finiteness from properness
and Noetherianity, uses geometric-component-count base-change invariance, counts a finite
clopen partition with `ConnectedComponents.equivOfIsClopenOfIsConnected`, and obtains the
neighbourhood inequality from flat locally-finitely-presented openness and étale openness.
The difficult Stein-factor/étale partition is isolated in the new module
`lean/Sheaf/AlgebraicGeometry/EtaleGeometricFiberClopenPartition.lean`.

## Proved and sorry left

The target declaration `AlgebraicGeometry.Scheme.Hom.geometricComponentCount_lowerSemicontinuous`
is proved with no `sorry`. One new intermediate theorem remains sorry:
`AlgebraicGeometry.Scheme.Hom.exists_etale_geometricFiber_clopen_partition` in
`lem-weil-pbc-etale-geometric-fibre-clopen-partition`.

## No longer needed

The target proof does not directly use the original Stein-factorization, finite-Stein-fibre,
integral-splitting, faithful-flat-spectrum, field-extension-faithful-flat, or explicit
radicial dependencies; those are used only by the new partition theorem or by Mathlib's
instances. The target node's proof dependencies were pruned to the partition theorem and
geometric component-count base change. The removed direct imports are recorded by the
module diff.

## Where the brief, the DAG or earlier work was wrong

The DAG proof plan expands the Stein-factor and purely inseparable residue-field argument
inline. That glue is substantially larger than the lower-semicontinuity argument, so it is
represented as one strictly smaller intermediate theorem. The target statement and all
existing declarations are unchanged.

## New nodes

`lem-weil-pbc-etale-geometric-fibre-clopen-partition` is added. It states the finite étale
clopen partition with connected nonempty geometric-fibre traces needed to identify the
special-fibre component count. Its source is Tag 0BUI, using the Stein factorization and
integral-fibre étale-splitting inputs; its Lean declaration is in
`Sheaf.AlgebraicGeometry.EtaleGeometricFiberClopenPartition`.

## Second reading by V7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
