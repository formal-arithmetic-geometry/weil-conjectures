# AlgebraicGeometry.SupportedConstantNormalization.exchange

## Reason

Inline the existing concrete construction to replace the public import of
`Sheaf.AlgebraicGeometry.OrdinarySupportedKummerBoundary` by the two operation modules
`WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs` and
`WeilConjectures.SixFunctors.BaseChange.Square`. The broad Kummer import brings in all
of Mathlib through the raw higher-direct-image interface. The former private imports
of the two narrow modules are removed as duplicates.

The new body is definitionally equal to the old body: it spells out the definition
of `Etale.supportedConstantUnit`, respectively `Etale.supportedConstantExchange`.
The source declarations remain untouched. Every existing declaration signature,
attribute and theorem proof in this dependency is preserved. The dependency is
unclaimed in the current claim records. Its six existing theorem holes are unchanged.

Targets that use these definitions require the usual renewed statement review.
Definitional equality preserves their meaning; no hypothesis or conclusion changes.

## Old

```lean
def exchange (pro : Bool) {Z' Z X' X : Scheme.{u}}
    {g : Z' ⟶ Z} {i' : Z' ⟶ X'} {i : Z ⟶ X} {h : X' ⟶ X}
    (sq : ChosenCartesianSquare g i' i h) :
    (pull A pro h).obj (supported A pro i) ⟶ supported A pro i' :=
  match pro with
  | false => Etale.supportedConstantExchange A i i' h g sq.toCommSq
  | true => (adj A true i').homEquiv _ _
      ((square A true sq).hom.app (supported A true i) ≫
        (pull A true g).map ((adj A true i).counit.app (constant A true Z)) ≫
        (unitIso A true g).hom)
```

## New

```lean
def exchange (pro : Bool) {Z' Z X' X : Scheme.{u}}
    {g : Z' ⟶ Z} {i' : Z' ⟶ X'} {i : Z ⟶ X} {h : X' ⟶ X}
    (sq : ChosenCartesianSquare g i' i h) :
    (pull A pro h).obj (supported A pro i) ⟶ supported A pro i' :=
  match pro with
  | false => (Etale.baseChangeMap (ModuleCat.{u + 1} A) sq.toCommSq).app
      (constant A false Z) ≫ (Etale.lowerStar (ModuleCat.{u + 1} A) i').map
        ((Scheme.upperStarConstantSheafIso (ModuleCat.{u + 1} A) g).app
          (ModuleCat.of A A)).hom
  | true => (adj A true i').homEquiv _ _
      ((square A true sq).hom.app (supported A true i) ≫
        (pull A true g).map ((adj A true i).counit.app (constant A true Z)) ≫
        (unitIso A true g).hom)
```

## Users

`tools/downstream.py` with each qualified declaration reports zero downstream modules
and only internal uses in the dependency. A whole-library direct-import search also
finds no existing importer. The assigned module is the new consumer in this packet.

| module | group holding it | effect |
| --- | --- | --- |
| `Sheaf.AlgebraicGeometry.SupportedConstantExchangeNormalization` | unclaimed | Equivalent concrete body and narrower imports; all six existing holes retained. |
| `Sheaf.Paper.SupportedHomPullback` | B8 | Uses the same canonical maps to construct the transports; no signature or statement change. |
| `Sheaf.Paper.AffineDiagonalTensorCoordinates` | unclaimed | No adaptation: the changed types and constructions remain definitionally equal. |
| `Sheaf.Paper.AffineSpaceZeroSectionPurity` | unclaimed | No adaptation: the changed types and constructions remain definitionally equal. |
| `Sheaf.Paper.ProjectionPurityAgreement` | unclaimed | No adaptation: the changed types and constructions remain definitionally equal. |

## Status

landed 20261022T025316-L-1272250 2026-10-22 (merge of deliver/B8/Sheaf.Paper.SupportedHomPullback)
