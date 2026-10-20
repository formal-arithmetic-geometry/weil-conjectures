# AlgebraicGeometry.Etale.nonempty_strictLocalBaseChange_continuityPresentation

## Reason

Repair return C-ed57b: restore the original small-spectrum statement, its declaration,
and its node attachment. The returned forwarding module instead exposed the theorem
on `strictLocalization`; those schemes are not definitionally equal.

The duplicate `smallStrictHenselizationColimitIso`, `smallStrictHenselizationCocone`
and `isColimitSmallStrictHenselizationCocone` have already been removed from
`Sheaf.AlgebraicGeometry.StrictHenselization` by the reviewed W4 landing
`9c024ef6813f3086cb759e63324375d6ccd29569`.
Its users now reuse `WeilConjectures.AlgebraicGeometry.StrictHenselizationExtension`;
the complete census and changes are in `coord/changes/W4-strict-henselization-retirement.md`.
This packet preserves that merge and the quarantine archives. It does not restore a twin.

The original proof cannot simply import the three canonical-model upstream helpers:
those helpers have been migrated to `strictLocalization`, and their public interfaces
also collide with the original-model Sheaf interfaces (for example
`strictHenselizationStructuralMap_eq`). Restore their already-stated proof chain in
`Sheaf.AlgebraicGeometry.StrictLocalSmallModel`, adapting the proved upstream calculations
to the original scheme, cone and structural morphism. The restored helper theorem names
carry `smallModel_`. All helpers are completely proved; no source-library file changes.

## Old

The original, quarantined signature was:

```lean
theorem nonempty_strictLocalBaseChange_continuityPresentation
    {X S : Scheme.{v}} (f : X ⟶ S) [QuasiCompact f] [QuasiSeparated f]
    {Ω : Type v} [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ S)
    (K : DerivedCategory.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{v + 1}))
    (n : ℤ) :
    Nonempty (GlobalCohomologyContinuityPresentation X K n
      ((Sheaf.Γ (Scheme.strictHenselizationScheme s).smallEtaleTopology
        AddCommGrpCat.{v + 1}).map
        ((DerivedCategory.Plus.homologyFunctor _ n).map
          ((mateEquiv (upperStarLowerStarAdjunction AddCommGrpCat.{v + 1} f).derivedPlus
            (upperStarLowerStarAdjunction AddCommGrpCat.{v + 1}
              (pullback.snd f (Scheme.strictHenselizationStructuralMap s))).derivedPlus
            (TwoSquare.mk _ _ _ _ (pullbackSquareComparison AddCommGrpCat.{v + 1}
              (IsPullback.of_hasPullback f
                (Scheme.strictHenselizationStructuralMap s)).toCommSq).hom))
                |>.natTrans.app K))))
```

The returned packet replaced it by a declaration-free public re-export of
`WeilConjectures.AlgebraicGeometry.StrictLocalMateContinuityPresentation` and repointed
the node to its theorem on `strictLocalization` and `strictLocalizationToBase`.

## New

```lean
theorem nonempty_strictLocalBaseChange_continuityPresentation
    {X S : Scheme.{v}} (f : X ⟶ S) [QuasiCompact f] [QuasiSeparated f]
    {Ω : Type v} [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ S)
    (K : DerivedCategory.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{v + 1}))
    (n : ℤ) :
    Nonempty (GlobalCohomologyContinuityPresentation X K n
      ((Sheaf.Γ (Scheme.strictHenselizationScheme s).smallEtaleTopology
        AddCommGrpCat.{v + 1}).map
        ((DerivedCategory.Plus.homologyFunctor _ n).map
          ((mateEquiv (upperStarLowerStarAdjunction AddCommGrpCat.{v + 1} f).derivedPlus
            (upperStarLowerStarAdjunction AddCommGrpCat.{v + 1}
              (pullback.snd f (Scheme.strictHenselizationStructuralMap s))).derivedPlus
            (TwoSquare.mk _ _ _ _ (pullbackSquareComparison AddCommGrpCat.{v + 1}
              (IsPullback.of_hasPullback f
                (Scheme.strictHenselizationStructuralMap s)).toCommSq).hom))
                |>.natTrans.app K))))
```

The signature above is restored verbatim, with its complete assembly proof and its
original public imports. Its three proof imports now select the original-model
neighbourhood geometry, source-colimit and projection-formula realizations.
The node again has `existing: false`, the Sheaf module/file, and the original statement.
The existing mathematical nodes for the helper results point to their fully proved
small-model realizations; their mathematical statements and dependency routes remain.

Each helper is the counterpart of the identically named upstream module under
`WeilConjectures.AlgebraicGeometry`, with four explicit substitutions:
`strictLocalization` to `strictHenselizationScheme`, `strictLocalizationToBase` to
`strictHenselizationStructuralMap`, `strictHenselizationAffineCone` to
`strictHenselizationCone`, and `strictHenselizationAffineProperties` to
`strictHenselization_properties`. Geometry reuses the existing proved
`strictHenselizationBaseChangeCone_exists`. Generic termwise sections reuse the existing
`Sheaf.AlgebraicGeometry.EtaleInjectiveSectionsComparison`. The sources, proof docstrings,
integer degrees, coefficient universes and all hypotheses are preserved.

No target, existing definition, upstream declaration, attribute or public import changes.
The original theorem still constructs source legs, their colimit and the projection
restriction equations without using continuity or invertibility of the mate.

## Users

The live module is quarantined, so `tools/downstream.py` does not index it. A direct
source census finds its one archived importer below. No consumer signature is changed.
The unchanged archived consumer is compiled with its original imports and statement.

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.StrictLocalBaseChangeGlobalHomology | unclaimed; quarantined | Its original `strictHenselizationScheme` theorem and entire assembly proof receive precisely the original presentation again. No adaptation or withdrawal is requested. |
| Sheaf.AlgebraicGeometry.StrictHenselization | W4 retirement already landed | Remains withdrawn; the conflicting twins are not restored. Its live users already import the upstream extension. The archived importer can import this empty compatibility module without a name clash. |
| Sheaf.AlgebraicGeometry.StrictLocalSmallModel.* | new, E3 | Fully proved counterparts of the already-stated helper chain; no existing source or Sheaf module is edited. |

No forced adaptations are submitted. No quarantine path is deleted or listed in deleted.txt.
The original strict-local target definitions and the unit's realized route remain unchanged.

## Status

landed 20261020T174747-L-792517 2026-10-20 (merge of deliver/E3/Sheaf.AlgebraicGeometry.StrictLocalMateContinuityPresentation)
