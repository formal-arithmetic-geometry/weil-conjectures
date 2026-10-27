# AlgebraicGeometry.Etale.injectiveExchange_target_transport

## Reason

Retire the zero-hole duplicate `Sheaf.AlgebraicGeometry.InjectiveExchangeTargetTransport`
listed in `coord/retire-items.tsv`. Its only active direct importer is the unclaimed
`Sheaf.AlgebraicGeometry.InjectiveExchangeRepresentative`.

The retirement table's "same statements" description predates the adopted theorem's
change from `Scheme.strictHenselizationStructuralMap` to `Scheme.strictLocalizationToBase`.
An import-only substitution with the upstream twin fails at the consumer's theorem
application (original line 160): the supplied equality concerns the canonical strict
localization, whereas the expected equality concerns the small coordinate-ring colimit
model. Changing the consumer's geometric object would change its statement.

Eliminate the redundant transport wrapper by moving its three fully proved private
calculations into the consumer: `assemble_transport`, `exchange_localization_prefix`,
and `target_unit_representative_transport`. Their declarations and proofs are copied
verbatim from the retired item. The consumer already has all the required exact
localization and derived-unit APIs through its original imports. Its existing proof
already sets up M, H, q′, R, U, P, F and the square, so it can combine the two comparison
calculations directly with `assemble_transport`, then use that equality in its original
`assemble_exchange` argument. The moved calculations remain private, with complete
proofs; no new public theorem, definition, proof dependency or module is introduced.
The combined source shrinks from 491 to 376 lines.

The separately proved small-model DAG realization remains in the library, unchanged.
The direct comparison proof removes the obsolete wrapper without adding any import.

No source-library file, declaration, signature, attribute, public import or proof changes.
No target statement or definition changes. The consumer's entire original public
signature, public imports and docstrings are preserved verbatim. Its only import change
is deletion of the private import of the retired item.

## Old

Withdrawn transport theorem signature, verbatim:

```lean
theorem injectiveExchange_target_transport {X S : Scheme.{v}} (f : X ⟶ S)
    {Ω : Type v} [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ S)
    (K : DerivedCategory.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{v + 1}))
    (J : CochainComplex.Plus (InjectiveObject
      (Sheaf X.smallEtaleTopology AddCommGrpCat.{v + 1})))
    (q : K.obj ≅ DerivedCategory.Q.obj
      (((InjectiveObject.ι _).mapHomologicalComplex (.up ℤ)).obj J.obj)) :
    let M₁ := ((InjectiveObject.ι _).mapHomologicalComplex (.up ℤ)).obj J.obj
    let M : CochainComplex.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{v + 1}) :=
      ⟨M₁, ((InjectiveObject.ι _).mapCochainComplexPlus.obj J).property⟩
    let H := (HomotopyCategory.Plus.quotient _).obj M
    let q' : K ≅ DerivedCategory.Plus.Qh.obj H :=
      DerivedCategory.Plus.ι.preimageIso (Y := DerivedCategory.Plus.Q.obj M)
        (q ≪≫ (DerivedCategory.quotientCompQhIso _).symm.app M.obj)
    let R := lowerStar AddCommGrpCat.{v + 1} f
    let U := upperStar AddCommGrpCat.{v + 1} (Scheme.strictHenselizationStructuralMap s)
    let P := upperStar AddCommGrpCat.{v + 1}
      (pullback.fst f (Scheme.strictHenselizationStructuralMap s))
    let F := lowerStar AddCommGrpCat.{v + 1}
      (pullback.snd f (Scheme.strictHenselizationStructuralMap s))
    let M₀ := ((InjectiveObject.ι _).mapHomologicalComplex (.up ℤ)).obj J.obj
    let L := (R.mapHomologicalComplex (.up ℤ)).obj M₀
    let D := (P.mapHomologicalComplex (.up ℤ)).obj M₀
    let T := P.mapDerivedCategoryPlus.obj K
    let sq := (IsPullback.of_hasPullback f
      (Scheme.strictHenselizationStructuralMap s)).toCommSq
    let a : (U.mapHomologicalComplex (.up ℤ)).obj L ⟶
        (F.mapHomologicalComplex (.up ℤ)).obj D :=
      (NatTrans.mapHomologicalComplex
      (baseChangeMap AddCommGrpCat.{v + 1} sq) (.up ℤ)).app M₀
    U.mapDerivedCategoryFactors.inv.app
      ((R.mapHomologicalComplex (.up ℤ)).obj M.obj) ≫
      DerivedCategory.Plus.ι.map
        (U.mapDerivedCategoryPlusFactorsh.hom.app (R.mapHomotopyCategoryPlus.obj H) ≫
          DerivedCategory.Plus.Qh.map
            ((NatTrans.mapHomotopyCategoryPlus
              (baseChangeMap AddCommGrpCat.{v + 1} sq)).app H) ≫
          F.rightDerivedFunctorPlusUnit.app (P.mapHomotopyCategoryPlus.obj H) ≫
          F.rightDerivedFunctorPlus.map
            (P.mapDerivedCategoryPlusFactorsh.inv.app H ≫
              P.mapDerivedCategoryPlus.map q'.inv)) =
    DerivedCategory.Q.map a ≫
      (DerivedCategory.quotientCompQhIso _).inv.app
        ((F.mapHomologicalComplex (.up ℤ)).obj D) ≫
      F.rightDerivedFunctorUnit.app ((HomotopyCategory.quotient _ _).obj D) ≫
      F.rightDerivedFunctor.map ((DerivedCategory.quotientCompQhIso _).hom.app D) ≫
      F.rightDerivedFunctor.map
        (P.mapDerivedCategoryFactors.inv.app M₀ ≫ P.mapDerivedCategory.map q.inv) ≫
      F.rightDerivedFunctorPlusCompatibility.inv.app T
```

Consumer's old private import and proof call:

```lean
import Sheaf.AlgebraicGeometry.InjectiveExchangeTargetTransport
    (injectiveExchange_target_transport f s K J q)
```

## New

The old item is withdrawn through `deleted.txt`. There is no exported replacement
or alias: the canonical upstream theorem and the independently named small-model
realization both remain where they already were.

The consumer's preserved public signature is:

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

Its proof privately proves the exact exchange prefix and target-unit suffix, composes
those equations by functoriality and associativity, and supplies the resulting `htarget`
to its existing `assemble_exchange` call. Neither target unit nor pullback of an
injective complex is assumed invertible. The private helper proofs are those of the
withdrawn module; the local assembly reuses the consumer's existing objects and square.

## Users

`tools/downstream.py Sheaf.AlgebraicGeometry.InjectiveExchangeTargetTransport
--uses injectiveExchange_target_transport` reports exactly the consumer below
(and the item's own declaration). A source scan also checked quarantined files.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.InjectiveExchangeRepresentative | unclaimed | Remove the private import; inline the proved comparison calculations and assemble them inside the original proof. Public signature, public imports, and docstrings unchanged. |

The quarantined `Sheaf.AlgebraicGeometry.StrictLocalDerivedExchangeLeray` imports
that consumer, not the retired item. It continues to have exactly the same public
`injectiveExchange_representative` theorem available; its archived source is untouched.
There are no additional active transitive consumers. No source or quarantined module
continues to import the withdrawn item after the delivered consumer edit.

No DAG node currently attaches to the retired item. The node
`lem-weil-pbc-injective-exchange-target-transport` already attaches to the retained
`Sheaf.AlgebraicGeometry.StrictLocalSmallModel.InjectiveExchangeTargetTransport`.
Its only parent, `lem-weil-pbc-injective-exchange-representative`, already attaches to
`Sheaf.AlgebraicGeometry.StrictLocalSmallModel.InjectiveExchangeRepresentative`.
Those two fully proved realizations and every statement/proof dependency are retained
verbatim. This is retirement of a redundant implementation, not withdrawal of either
mathematical node. `dag/units/sk-prop-h2.json` realizes neither node as its statement
or a proof step; no unit or chapter route changes.

## Status

landed 20261022T113920-L-398450 2026-10-22 (merge of deliver/E3/Sheaf.AlgebraicGeometry.InjectiveExchangeTargetTransport)
