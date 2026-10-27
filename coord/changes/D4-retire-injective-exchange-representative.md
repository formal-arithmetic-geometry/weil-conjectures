# AlgebraicGeometry.Etale.injectiveExchange_representative

## Reason

Complete the explicit zero-hole retirement assignment for
`Sheaf.AlgebraicGeometry.InjectiveExchangeRepresentative` in
`coord/retire-items.tsv` (consumer count 1 in that historical inventory).
The module has no live library importers, no DAG Lean attachments, and no sorry.
Withdraw its 376-line implementation, including its private comparison helpers.
The adopted source module remains unchanged.

This is not justified merely by the absence of live importers. The inventory's
one consumer, `Sheaf.AlgebraicGeometry.StrictLocalDerivedExchangeLeray`, is an
archived, independently retired duplicate. Its retirement was explicitly reviewed
by C-4f264 and completed by maintenance in
`coord/changes/C2-strict-local-derived-exchange-maintenance-20261021.md`.
That record preserves the review instruction, closes the original rework row,
and requires keeping the quarantine archive as historical evidence. The current
rework table has no row for that old consumer. It must not be restored or edited
as part of this retirement. No live source imports it.

The current mathematical DAG follows a distinct, retained route:
`lem-weil-pbc-strict-local-derived-exchange-leray` uses
`lem-weil-pbc-injective-exchange-representative`. Their Lean attachments are
`Sheaf.AlgebraicGeometry.StrictLocalSmallModel.StrictLocalDerivedExchangeLeray`
and `Sheaf.AlgebraicGeometry.StrictLocalSmallModel.InjectiveExchangeRepresentative`,
respectively. The latter is realized by
`AlgebraicGeometry.Etale.smallModel_injectiveExchange_representative`.
Those quarantine sources and current rework assignments are preserved verbatim,
as are their complete proofs, all node dependencies and the unit route.
Neither node is attached to the retired module. No node field changes are needed.

The adopted upstream theorem uses `Scheme.strictLocalizationToBase`, whereas the
retired theorem uses `Scheme.strictHenselizationStructuralMap`. They are not claimed
to be definitionally the same statement. The original-model mathematical obligation
remains attached to its independently named small-model provider; it is not replaced
by the canonical-model theorem. No target, definition, public upstream signature,
attribute, import or theorem proof changes.

## Old

Withdrawn public signature, verbatim:

```lean
theorem injectiveExchange_representative {X S : Scheme.{v}} (f : X ⟶ S)
    {Ω : Type v} [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ S)
    (K : DerivedCategory.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{v + 1}))
    (J : CochainComplex.Plus (InjectiveObject
      (Sheaf X.smallEtaleTopology AddCommGrpCat.{v + 1})))
    (q : K.obj ≅ DerivedCategory.Q.obj
      (((InjectiveObject.ι _).mapHomologicalComplex (.up ℤ)).obj J.obj)) :
    let M := ((InjectiveObject.ι _).mapHomologicalComplex (.up ℤ)).obj J.obj
    let L := ((lowerStar AddCommGrpCat.{v + 1} f).mapHomologicalComplex (.up ℤ)).obj M
    let U := upperStar AddCommGrpCat.{v + 1} (Scheme.strictHenselizationStructuralMap s)
    let P := upperStar AddCommGrpCat.{v + 1}
      (pullback.fst f (Scheme.strictHenselizationStructuralMap s))
    let F := lowerStar AddCommGrpCat.{v + 1}
      (pullback.snd f (Scheme.strictHenselizationStructuralMap s))
    let D := (P.mapHomologicalComplex (.up ℤ)).obj M
    let T := P.mapDerivedCategoryPlus.obj K
    let a : (U.mapHomologicalComplex (.up ℤ)).obj L ⟶
        (F.mapHomologicalComplex (.up ℤ)).obj D :=
      (NatTrans.mapHomologicalComplex
      (baseChangeMap AddCommGrpCat.{v + 1}
        (IsPullback.of_hasPullback f (Scheme.strictHenselizationStructuralMap s)).toCommSq)
      (.up ℤ)).app M
    U.mapDerivedCategoryFactors.inv.app L ≫
      U.mapDerivedCategory.map (sourceInjectiveDirectImageIso f K J q).inv ≫
      DerivedCategory.Plus.ι.map
        ((mateEquiv (upperStarLowerStarAdjunction AddCommGrpCat.{v + 1} f).derivedPlus
          (upperStarLowerStarAdjunction AddCommGrpCat.{v + 1}
            (pullback.snd f (Scheme.strictHenselizationStructuralMap s))).derivedPlus
          (TwoSquare.mk _ _ _ _ (pullbackSquareComparison AddCommGrpCat.{v + 1}
            (IsPullback.of_hasPullback f
              (Scheme.strictHenselizationStructuralMap s)).toCommSq).hom)).natTrans.app K) =
    DerivedCategory.Q.map a ≫
      (DerivedCategory.quotientCompQhIso _).inv.app
        ((F.mapHomologicalComplex (.up ℤ)).obj D) ≫
      F.rightDerivedFunctorUnit.app ((HomotopyCategory.quotient _ _).obj D) ≫
      F.rightDerivedFunctor.map ((DerivedCategory.quotientCompQhIso _).hom.app D) ≫
      F.rightDerivedFunctor.map
        (P.mapDerivedCategoryFactors.inv.app M ≫ P.mapDerivedCategory.map q.inv) ≫
      F.rightDerivedFunctorPlusCompatibility.inv.app T
```

## New

No declaration remains in the retired module. `deleted.txt` lists only its existing
library path, `lean/Sheaf/AlgebraicGeometry/InjectiveExchangeRepresentative.lean`.
The delivery tool installs the standard withdrawn module stub.

The adopted canonical theorem
`AlgebraicGeometry.Etale.injectiveExchange_representative` in
`WeilConjectures.AlgebraicGeometry.InjectiveExchangeRepresentative` and its consumer
`AlgebraicGeometry.Etale.strictLocalDerivedExchange_leray` in
`WeilConjectures.AlgebraicGeometry.StrictLocalDerivedExchangeLeray` are untouched.
The original-model DAG provider and its small-model parent are also untouched.

## Users

`tools/downstream.py Sheaf.AlgebraicGeometry.InjectiveExchangeRepresentative
--uses injectiveExchange_representative` reports zero downstream library modules;
the only textual declaration use in the Sheaf library is its own declaration.
A separate scan of all active and quarantined Lean sources finds only the old
archived Leray consumer importing this module.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.InjectiveExchangeRepresentative | D4 | Retire the unused implementation; zero original holes. |
| Sheaf.AlgebraicGeometry.StrictLocalDerivedExchangeLeray | retired; historical quarantine archive | No edit. Its independent retirement and closed rework row are recorded by C2 maintenance; archive preserved verbatim. |
| Sheaf.AlgebraicGeometry.StrictLocalSmallModel.InjectiveExchangeRepresentative | existing rework assignment; not adapted | Preserve its source archive, Lean attachment, proof and dependencies. It supplies the original-model DAG obligation. |
| Sheaf.AlgebraicGeometry.StrictLocalSmallModel.StrictLocalDerivedExchangeLeray | existing rework assignment; not adapted | Preserve its source archive, Lean attachment and dependency on the original-model representative theorem. |
| WeilConjectures.AlgebraicGeometry.InjectiveExchangeRepresentative | not adapted | Adopted canonical theorem preserved verbatim. |
| WeilConjectures.AlgebraicGeometry.StrictLocalDerivedExchangeLeray | not adapted | Adopted canonical consumer preserved verbatim; already imports the adopted representative module. |

## Status

landed 20261022T143039-L-936759 2026-10-22 (merge of deliver/D4/Sheaf.AlgebraicGeometry.InjectiveExchangeRepresentative)
