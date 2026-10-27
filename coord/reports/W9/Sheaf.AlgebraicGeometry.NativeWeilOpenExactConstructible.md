## What changed

Proved `AlgebraicGeometry.ProEtaleWeilSheaf.extensionByZero_exact_constructible` in
`Sheaf.AlgebraicGeometry.NativeWeilOpenExactConstructible` by assembling the existing
native extension-by-zero instances and
`WeilSheaf.isAdicConstructibleSheaf_extensionByZero` from
`WeilConjectures.WeilSheaf.OpenImmersion`, publicly available through the unchanged
`WeilConjectures.WeilSheaf.LowerShriek` import. The theorem signature is unchanged.
Updated the node proof to this direct assembly. No source-library file was changed.
The item compiled cleanly via lcompile.py in 6.9 seconds.

## Proved and sorry left

Closed one hole: `AlgebraicGeometry.ProEtaleWeilSheaf.extensionByZero_exact_constructible`
(node `lem-sf-native-weil-open-exact-constructible`). No sorry remains in the item;
zero holes added, zero statements split off. The underlying source instances and
constructibility proof already exist and have no textual sorry.

## No longer needed

Removed proof imports:
- `Sheaf.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization`
- `Sheaf.CategoryTheory.RingedSheafSliceAdjunction`
- `WeilConjectures.AlgebraicGeometry.ConstructibleStratificationAssembly`
- `Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact`
- `Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated`
- `Mathlib.AlgebraicGeometry.AffineScheme`
- `Mathlib.Topology.Constructible`
- `Mathlib.CategoryTheory.Endofunctor.Algebra`

The direct proof needs none of the former auxiliary proof nodes:
`lem-weil-proetale-weakly-etale-localization`,
`lem-weil-pbc-open-immersion-base-change`, `lem-pc-quasi-compact-base-change`,
`lem-weil-pbc-ringed-sheaf-slice-adjunction`,
`def-weil-endofunctor-fixed-pair-category`,
`lem-sf-native-weil-constructible-abelian`, `def-weil-sheaf-of-modules-category`,
`lem-sf-exact-conservative-square-finite-preservation`,
`lem-sf-native-adic-open-restrictions`, and
`lem-sf-native-adic-affine-open-zero-stratification`.
Removed the three obsolete tool-use approvals for weakly-etale localization,
ringed-sheaf-slice adjunction and constructible-stratification assembly.
This removes only direct dependencies of the item: no claim is made that modules
still used elsewhere are globally unnecessary. All upstream declarations and
public imports remain intact. The source proof retains the intended affine
open/closed stratification route; the unit route is unchanged.

## Where the brief, the DAG or earlier work was wrong

The planned reconstruction duplicates results already proved in
`WeilConjectures.WeilSheaf.OpenImmersion`. Its three native instances and the
constructibility theorem give precisely the four clauses of this item.
LeanFinder and Loogle did not find a closer Mathlib theorem; local source search
found the exact existing API. No mathematical statement needed repair.

## Second reading by W9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
