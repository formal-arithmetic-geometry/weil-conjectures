# AlgebraicGeometry.affineSpectrum_counit_compatibility

## Reason

The current Sheaf module duplicates an adopted source module. Its complete theorem
statement and proof are byte-identical to the upstream declaration, which the actual
parent already imports. Preserve one declaration of this notion by retiring the Sheaf
copy and updating the DAG attachment. The previous rework defect was repaired by M8.

## Old

`lem-pc-affine-spectrum-counit-compatibility` points to module
`Sheaf.AlgebraicGeometry.AffineSpectrumCounitCompatibility`, file
`lean/Sheaf/AlgebraicGeometry/AffineSpectrumCounitCompatibility.lean`, declaration:

```lean
theorem affineSpectrum_counit_compatibility
    {X S : Scheme.{u}} [IsAffine X] [IsAffine S]
    (f : X ⟶ S) (K : schemeDerivedCategory X) :
  (derivedPullback f).map ((affineSpectrumDerivedDirectImageIso f).hom.app K) ≫
      (affineSpectrumForwardPullbackIso f).hom.app
        ((schemeDerivedDirectImage (Spec.map f.appTop)).obj
          ((derivedPullback X.isoSpec.inv).obj K)) ≫
      (derivedPullback X.toSpecΓ).map
        ((canonicalSchemeDerivedAdjunction (Spec.map f.appTop)).counit.app
          ((derivedPullback X.isoSpec.inv).obj K)) ≫
      affineSpectrumUnitInv X K =
    (canonicalSchemeDerivedAdjunction f).counit.app K
```

The section assumptions are universes `u w` and
`[∀ Y : Scheme.{u}, HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]`.

## New

The theorem and section assumptions above are unchanged in the existing module
`WeilConjectures.AlgebraicGeometry.AffineSpectrumCounitCompatibility` at
`lean/WeilConjectures/AlgebraicGeometry/AffineSpectrumCounitCompatibility.lean`.
Point the node there and withdraw only the Sheaf duplicate using `deleted.txt`.
The adopted source file is unmodified. The quarantine archive remains unmodified.
All mathematical statement and proof dependencies are retained.

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.AffineSpectrumCounitCompatibility | S8 | Retire the duplicate after checking the exact replacement. |
| WeilConjectures.AlgebraicGeometry.AffineSpectrumCounitCompatibility | unclaimed | Existing complete theorem retained without any edit. |
| WeilConjectures.AlgebraicGeometry.AffineSpectrumMateCompatibility | unclaimed | Already imports and uses the preserved upstream theorem; no edit needed. |

`tools/downstream.py` finds zero downstream modules of the Sheaf module. Direct searches
of both library roots and the quarantine tree find no importer of it. The parent DAG
node `lem-pc-affine-spectrum-mate-compatibility` retains its uses of the same counit node
in proof steps 2 and 3; its existing upstream attachment resolves to the preserved theorem.
No forced adaptations are required. No unit route is bypassed.

Validation: the old live Sheaf module compiles cleanly in 12.1 seconds. An example with
the exact old statement, importing only the upstream module and applying its theorem,
compiles cleanly in 2.0 seconds. Its axiom report contains only `propext`,
`Classical.choice`, and `Quot.sound`. The declaration through the end of its proof is
byte-identical in the two current source files.

## Status

landed 20261020T153022-L-2864432 2026-10-20 (merge of deliver/S8/Sheaf.AlgebraicGeometry.AffineSpectrumCounitCompatibility)
