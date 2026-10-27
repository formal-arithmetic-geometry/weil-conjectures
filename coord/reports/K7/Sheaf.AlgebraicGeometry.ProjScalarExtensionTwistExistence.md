## What changed

Constructed the comparison morphism in `ProjScalarExtensionTwistExistence` explicitly,
using the ordinary localization ring map on the values of locally homogeneous fractions.
Proved that it preserves homogeneous degree, locally-fraction sections, restrictions and
scalar multiplication. Transposed this concrete map through the section-normalized tensor
adjunction and proved its pointwise formula on the actual section `1 tensor s`.

Identified the given scheme map with Mathlib's `Proj.map` on its standard cover, then
proved the original theorem from the one-chart bijectivity calculation in the new
`ProjScalarExtensionTwistChart` module. Local bijectivity supplies the isomorphism;
applying a ring hom to `b*s=a` proves the required normalization on arbitrary opens.
The item statement and all existing public definitions and signatures are unchanged.
No data is chosen from an unproved existence theorem: the map is the explicit adjoint
of the constructed section map; the remaining theorem supplies only bijectivity.

Validation: both delivered Lean modules compile with no warnings through `lcompile.py`.
The item takes 12.9 seconds, and the new chart statement takes 3.6 seconds.
The original theorem signature was compared byte for byte and is unchanged.
Import-direction checks found no cycles through the added existing proof imports.

## Proved and sorry left

Closed the original hole in `AlgebraicGeometry.Proj.scalarExtension_twist_exists`
(node `lem-sfb-proj-scalar-extension-twist-existence`) by a genuine decomposition.
The new theorem `AlgebraicGeometry.Proj.scalarExtension_twistMap_basicOpen_bijective`
(node `lem-sfb-proj-scalar-extension-twist-chart`) is the only sorry added and the
only sorry left in the delivered files. Thus one upper hole is closed, one strictly
smaller local hole is added, and the net hole change is zero. This is a decomposition,
not a claim of a complete proof without admitted dependencies.

The private helpers `twistFiberMap`, `twistFiberMap_mk`, `twistSectionMap`,
`twistSectionMap_smul`, `twistPushforwardMap`, `twistPullbackMap` and
`twistPullbackMap_section` are fully constructed or proved. They do not depend
on the new chart theorem. The remaining chart theorem assumes a
particular morphism with its section formula and concerns only bijectivity on one
standard chart in one degree; the construction of that morphism, its global
compatibility, and the original normalization are proved in the item.

## No longer needed

Removed the item's direct proof imports of:

- `Sheaf.RingTheory.HomogeneousLocalizationScalarExtension`
- `Sheaf.Algebra.Module.GradedLocalizationScalarExtension`
- `Mathlib.AlgebraicGeometry.Modules.Tilde`
- `WeilConjectures.Topology.GlueSheavesOfModules`
- `WeilConjectures.AlgebraicGeometry.ModulePullbackAffineSections`
- `WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Tilde`
- `WeilConjectures.AlgebraicGeometry.ProjGradedModuleSheafExists`

The algebraic localization, affine sections, quasi-coherence and tilde inputs remain
needed by the new chart subargument and are imported there. In particular their nodes
are retained below the new node, rather than falsely reported as globally pruned.
`lem-weil-pbc-glue-sheaves-of-modules` and its module are no longer used by this
argument: the maps are defined pointwise on every open. No overlap-gluing theorem
is needed. `lem-weil-pbc-proj-basic-open-intersection` is also no longer a proof
step: restrictions commute definitionally in the explicit section map. The Mathlib
standard chart cover supplies all local-to-global input. The scalar-extension
Proj existence theorem `lem-nagata-affine-proj-scalar-extension` is not invoked:
the given map is identified with `Proj.map` directly by `hchart`. Its module remains
a public dependency of the unchanged data module, and its node remains a statement
dependency; neither is withdrawn. No existing module or declaration is deleted.

## Where the brief, the DAG or earlier work was wrong

The original plan requires constructing affine comparison maps and gluing them on
overlaps. The existing twist is already a sheaf of pointwise homogeneous fractions,
so applying the localization map gives a shorter global construction. The new route
keeps the same generality, including negative degrees, arbitrary gradings, non-flat
coefficient extensions, nilpotent chart denominators and empty opens.

The general graded-module sheaf theorem does not directly assert quasi-coherence of
the specific concrete `Proj.twist`. The one-chart proof therefore explicitly includes
the identification via the existing single-twist fraction theorem and basis-extension
uniqueness. That bridge and the chart's algebra-to-sheaf comparison remain part of the
named local obligation, rather than being silently treated as existing instances.
The unit route and existing target statements are unchanged. The existing
`lem-sc-proj-single-twist-basic-open-fractions` is used as a generic chart tool,
not as an alternate route through its unit; its concrete fraction description
is needed to connect the existing twist to the affine graded-module construction.

## New nodes

`lem-sfb-proj-scalar-extension-twist-chart`, in
`dag/nodes/sec-six-functors-basics/lem-sfb-proj-scalar-extension-twist-chart.json`,
records the fixed-degree, fixed-chart bijectivity step of Stacks 01N2(3).
Its hypotheses prescribe a given morphism by its pointwise localization formula;
it asserts no existence of a comparison. The docstring and node give the complete
chart proof using homogeneous localization scalar extension, affine pullback sections,
and the tilde adjunction. The cases of negative degree, empty charts, nilpotents and
non-flat coefficient extensions are included. Three actual Mathlib searches found
no replacement. The parent node's proof and proof dependencies now match the explicit
section construction and its use of this one local statement.

## Related modules compiled before delivery

1 related module(s) compiled against this delivery by deliver3.py: 1 OK.

```json
{"capped": false, "direct": 1, "left_out": 0, "own": {"Sheaf.AlgebraicGeometry.ProjScalarExtensionTwistChart": "22a2bcab3f4da91135061e6f36a08f0975f0f5ae", "Sheaf.AlgebraicGeometry.ProjScalarExtensionTwistExistence": "693af4a4e71c412036c3f4e4840aa6bc158a41c9"}, "results": {"Sheaf.AlgebraicGeometry.ProjScalarExtensionTwistComparison": {"hash": "b5a123a2f140b7f1f2f0298259ab97e4e6c9edb3", "status": "OK"}}, "seconds": 15, "time": "2026-10-28T03:31:39+0800", "transitive": 0, "version": 1}
```

## Second reading by K7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
