# Sheaf.RingTheory.BoundedProjectiveResolutionDimension

## Reason

Carry out the human's retirement hand-off in
coord/changes/retire-sheaf-twins-20261020.md. The remaining Sheaf file is only a
public reexport of the proved official twin; it adds no declaration or definition.
All current active consumers already import the official twin directly. Retire
this redundant import path without changing any mathematical statement or proof.

## Old

```lean
module

public import WeilConjectures.RingTheory.BoundedProjectiveResolutionDimension

@[expose] public section
```

The omitted copyright and module documentation contain no Lean declarations.

## New

The Sheaf copy is withdrawn through deleted.txt. The delivery protocol writes an
empty module stub pending maintainer pruning. The retained API is supplied by
WeilConjectures.RingTheory.BoundedProjectiveResolutionDimension:
ModuleCat.hasProjectiveResolutionLE_iff_hasProjectiveDimensionLE,
ModuleCat.exists_hasProjectiveResolutionLE_iff,
ModuleCat.projectiveDimension_eq_of_hasProjectiveResolutionLE, and
Ring.hasGlobalDimensionLE_iff. No upstream source is changed.

The existing DAG node lem-weil-pbc-projective-resolution-ext-degree already
points at this official module and declaration. Its lean.note now records this
retirement; its statement, proof, dependencies, unit and declaration stay intact.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.RingTheory.BoundedProjectiveResolutionDimension | C1 | Retire the public reexport. |
| Sheaf.AlgebraicGeometry.AffinePolynomialResolutionOfStalkwise | absent; official twin active | Official twin already imports the upstream bridge; checked unchanged. |
| Sheaf.RingTheory.ProjectiveResolutionExtAllDegrees | absent; official twin active | Official twin already imports the upstream bridge; checked unchanged. |
| Sheaf.RingTheory.ProjectiveResolutionExtCharacterization | absent; official twin active | Official twin already imports the upstream bridge; checked unchanged. |
| Sheaf.RingTheory.AuslanderBuchsbaum | quarantined; separate rework | Preserve archive and node. When restored, replace its private import of the retired path by import WeilConjectures.RingTheory.BoundedProjectiveResolutionDimension. The bridge name and type are identical. |
| Sheaf.RingTheory.UniformPerfectQuotientBound | quarantined; separate rework | Preserve archive and node. When restored, use the same private-import replacement. The bridge name and type are identical. |
| Sheaf.Algebra.ProjectiveDimensionWellDefined | unchanged | Already imports the upstream bridge; checked unchanged. |
| Sheaf.RingTheory.ProjectiveDimensionSESKernel | unchanged | Already imports the upstream bridge; checked unchanged. |

There are no active direct importers of the Sheaf copy. The two quarantine
archives remain immutable historical inputs for their rework assignments; they
are not compiled library modules. This delivery neither withdraws their nodes
nor substitutes a weaker theorem for their outstanding repairs. In particular,
AuslanderBuchsbaum also has pre-existing failures from the retired natural-number
projectiveDimension API and public depth helpers, independent of this reexport.
No target statement or definition changes. No proof is replaced by sorry.

## Status

landed 20261020T155629-L-3268905 2026-10-20 (merge of deliver/C1/Sheaf.RingTheory.BoundedProjectiveResolutionDimension)
