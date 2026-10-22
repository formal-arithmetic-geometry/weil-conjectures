# AlgebraicGeometry.Etale.isIso_unit_constantSheaf_generic_unit

## Reason

Retire the duplicate assigned in coord/retire-items.tsv under the human's instruction in
coord/changes/retire-sheaf-twins-20261020.md. The adopted module proves the exact same public
theorem. Its private helpers use the full strictLocalizationToBase presentation; the copy's
small-model helpers are private and have no external callers. The two public signatures
were compared verbatim and agree, including universes and all hypotheses.

## Old

In Sheaf.AlgebraicGeometry.NormalConstantGenericUnit:

```lean
theorem isIso_unit_constantSheaf_generic_unit
    (Λ : Type (u + 1)) [CommRing Λ] {Y : Scheme.{u}} [IsIntegral Y]
    (hY : ∀ y : Y, IsIntegrallyClosed (Y.presheaf.stalk y))
    (M : ModuleCat.{u + 1} Λ) :
    IsIso ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ)
        (Y.fromSpecStalk (genericPoint Y))).unit.app
          ((constantSheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj M))
```

## New

The unchanged adopted declaration in WeilConjectures.AlgebraicGeometry.NormalConstantGenericUnit:

```lean
theorem isIso_unit_constantSheaf_generic_unit
    (Λ : Type (u + 1)) [CommRing Λ] {Y : Scheme.{u}} [IsIntegral Y]
    (hY : ∀ y : Y, IsIntegrallyClosed (Y.presheaf.stalk y))
    (M : ModuleCat.{u + 1} Λ) :
    IsIso ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ)
        (Y.fromSpecStalk (genericPoint Y))).unit.app
          ((constantSheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj M))
```

Withdraw the Sheaf module using deleted.txt. Preserve the node and point its Lean attachment
at the adopted theorem. Update its proof description to the adopted argument: use the full
chart ring and strict fibre directly, with no small/full transport. This preserves normality,
integrality, arbitrary coefficient modules, the zero coefficient ring, and the unit route.
No definition or target statement changes, so no target statement re-review is required.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.NormalConstantGenericUnit | D2 | Withdraw the duplicate. |
| WeilConjectures.AlgebraicGeometry.NormalConstantOpenUnit | not edited | Already imports the adopted theorem; statement unchanged. |
| WeilConjectures.AlgebraicGeometry.ConstructibleModuleIntegralStalkEmbeddingNoetherian | not edited | Already imports the adopted theorem; statement unchanged. |
| WeilConjectures.ConstructibleSheaf.FinitePushforward | not edited | Already imports the adopted theorem and its open conjunct. |

The current tools/downstream.py --uses check reports zero modules downstream of the Sheaf
copy. A search of lean/ and quarantine/ found no importer of that copy. The retirement TSV's
two named Sheaf consumers have already been retired, and their nodes point at the adopted
modules above. No rework row names the copy or those two consumers.

All three parent nodes retain their dependency on the mathematical generic-unit node:
lem-weil-pbc-normal-constant-generic, lem-weil-pbc-normal-constant-generic-open-unit, and
new-lem-weil-pbc-noetherian-integral-stalk-embedding. They require no change because the
node still supplies exactly the original declaration. The sk-thm-p1 realized route is kept.

## Status

landed 20261022T022948-L-766640 2026-10-22 (merge of deliver/D2/Sheaf.AlgebraicGeometry.NormalConstantGenericUnit)
