## What changed

Repaired the return of c790a5b6004: added all six omitted consumers to the change record's
Users table, inspected their uses, and refreshed the combined downstream inventory and
claim holders. The six modules are Sheaf.Paper.CoefficientProjectionSquare,
Sheaf.Paper.CompactificationRefinementLocalizing, Sheaf.Paper.ContinuousAlgClProperFiniteness,
Sheaf.Paper.IntegralExtensionByZero, Sheaf.Paper.IntegralOpenExtensionReduction, and
Sheaf.Paper.InternalScalarTensorComparison. They retain the same local irreducibility
attributes; CompactificationRefinementLocalizing also retains its local flat-resolution
instance. No consumer adaptation is necessary.

The retained source-item proofs fill both instance holes in the current readable source.
Closedness transports the existing concrete equalizer adjunction along the relative-tensor
coequalizer comparison and symmetry. Functorial flat resolutions use the supplied ambient
resolution, free modules, and the free-forget counit, with flatness proved using the split
free-tensor coequalizer. The only added proof imports are InternalHom and TensorRegular
under WeilConjectures.CategoryTheory.Monoidal.Mod. All new helpers are private and proved.

The companion Sheaf.UpstreamExtra.WeilConjectures.CategoryTheory.ModuleObjects.GrothendieckAbelian
retains its public relativeTensor_isLeftAdjoint theorem, both public imports, and all proof
bodies. Its edits only wrap the opening comment and omit the unused MonoidalPreadditive C
assumption from private flat_free. Existing source signatures and public imports are preserved.

Change record: coord/changes/F4-module-object-closed-flat-proofs.md.

## Proved and sorry left

Against current readable source: 2 existing holes, 2 holes closed, 0 added, 0 split off,
and 0 holes left in either submitted module.

Closed CategoryTheory.Mod.monoidalClosed by the equalizer adjunction and the tensor
comparison. Closed CategoryTheory.Mod.hasFunctorialFlatResolution by the free-flat
construction (nodes lem-weil-pbc-module-functorial-flat-resolution and
lem-sfb-modobj-flat-resolutions). The existing companion theorem
CategoryTheory.Mod.relativeTensor_isLeftAdjoint is retained with its complete proof
(node lem-weil-pbc-module-relative-tensor-adjoint). No named declaration remains sorry.

## No longer needed

None. No current import, declaration, node or module is removed. The existing equalizer
internal-hom and free-flat construction remain the route of the upstream proofs. The
companion's special-adjoint proof is retained. No new nodes are needed.

## Where the brief, the DAG or earlier work was wrong

The return identified six newly present consumers missing from the old Users table.
All six are now recorded with their current holder and effect; the full downstream table
was refreshed as well. Their references occur in local attributes and remain valid.

The retained report described a previous source state with zero holes after the D2 landing.
The currently readable source again contains two instance holes. This report and the change
record now describe the actual current comparison and do not treat the packet as a no-op.
The earlier packet's public-theorem removal, additional public imports and global notation
changes remain discarded. No target statement or public signature changes.

## Second reading by F4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
