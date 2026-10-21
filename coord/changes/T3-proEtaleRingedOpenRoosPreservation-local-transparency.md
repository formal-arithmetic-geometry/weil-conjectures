# AlgebraicGeometry.Scheme.proEtaleRingedExtensionByZero

## Reason

The first delivery compile, including the declaration axiom probe, exceeded the
60-second limit. Profiling showed repeated instance synthesis and reduction of the
extension-by-zero functor, whose definition is a composite with module
sheafification. The proof now caches its categorical structures and introduces a
local reduction barrier before the product/Roos theorem. With these changes the
compile with the axiom probe passed in the second delivery attempt.

The static command check conservatively classifies this local attribute as an
interface change. The attribute is local to the namespace scope of
`Sheaf.AlgebraicGeometry.ProEtaleRingedOpenRoosPreservation`; it is not exported to
importers. The source definition, its public signature, and all public imports
remain verbatim. No definition of the adopted source library changes.

## Old

The existing definition in
`Sheaf.AlgebraicGeometry.ProEtaleRingedOpenClosed` is unchanged:

```lean
noncomputable def proEtaleRingedExtensionByZero {X : Scheme.{u}} (U : X.ProEt)
    (A : Sheaf (ProEt.topology X) CommRingCat.{u + 1}) :=
  SheafOfModules.extensionByZeroPresheaf.{u + 1} (proEtaleModuleCoefficients A) U ⋙
    PresheafOfModules.sheafification (𝟙 (proEtaleModuleCoefficients A).obj)
```

There was no local transparency attribute in
`Sheaf.AlgebraicGeometry.ProEtaleRingedOpenRoosPreservation`.

## New

The same definition and signature remain in
`Sheaf.AlgebraicGeometry.ProEtaleRingedOpenClosed`:

```lean
noncomputable def proEtaleRingedExtensionByZero {X : Scheme.{u}} (U : X.ProEt)
    (A : Sheaf (ProEt.topology X) CommRingCat.{u + 1}) :=
  SheafOfModules.extensionByZeroPresheaf.{u + 1} (proEtaleModuleCoefficients A) U ⋙
    PresheafOfModules.sheafification (𝟙 (proEtaleModuleCoefficients A).obj)
```

Only the item module adds this locally scoped command immediately before its
product/Roos theorem:

```lean
attribute [local irreducible] proEtaleRingedExtensionByZero
```

The proof uses the exactness, adjunction, and product APIs of this functor rather
than allowing inference to unfold its sheafification composite. The derived
extension abbreviation and the statement being proved are unchanged.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.ProEtaleRingedOpenRoosPreservation | T3 | Local proof reduction barrier and cached structures; public declarations unchanged. |

`tools/downstream.py` for the item module, both without a name filter and with
`--uses proEtaleRingedOpenDerived`, lists no downstream modules. The underlying
extension-by-zero definition itself is not edited, and its other consumers see
no changed attribute or data. No consumer adaptation or target re-review is needed.

## Status

landed 20261021T120539-L-3908365 2026-10-21 (merge of deliver/T3/Sheaf.AlgebraicGeometry.ProEtaleRingedOpenRoosPreservation)
