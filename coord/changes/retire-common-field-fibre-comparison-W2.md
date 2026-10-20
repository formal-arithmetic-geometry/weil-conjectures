# AlgebraicGeometry.exists_common_field_fibre_comparison

## Reason

Retire the unused Sheaf copy in favour of the stronger, completely proved upstream theorem,
following the 2026-10-20 retirement instruction in
`coord/changes/retire-sheaf-twins-20261020.md`. The current source graph has no importers of
`Sheaf.AlgebraicGeometry.CommonFieldFibreComparison`. The former consumer,
`Sheaf.AlgebraicGeometry.GeometricGenericCoverSpread`, has already been retired; its upstream
replacement imports the upstream comparison module and uses its stronger conclusion.

## Old

In `lean/Sheaf/AlgebraicGeometry/CommonFieldFibreComparison.lean`:

```lean
theorem exists_common_field_fibre_comparison {X S T : Scheme.{u}}
    (f : X ⟶ S) (g : T ⟶ S) (t : T) (s : S) (ht : g t = s)
    (K : Type u) [Field K]
    (y : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of (S.residueField s))) :
    ∃ (E : Type u) (_ : Field E)
      (z : Spec (CommRingCat.of E) ⟶ Spec (CommRingCat.of (T.residueField t)))
      (p : pullback ((pullback.snd f g).fiberToSpecResidueField t) z ⟶
        pullback (f.fiberToSpecResidueField s) y), Surjective p
```

## New

Withdraw the Sheaf module and attach `lem-sbc-common-field-fibre-comparison` to the existing
upstream declaration in `WeilConjectures.AlgebraicGeometry.CommonFieldFibreComparison`:

```lean
theorem exists_common_field_fibre_comparison {X S T : Scheme.{u}}
    (f : X ⟶ S) (g : T ⟶ S) (t : T) (s : S) (ht : g t = s)
    (K : Type u) [Field K]
    (y : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of (S.residueField s))) :
    ∃ (E : Type u) (_ : Field E)
      (z : Spec (CommRingCat.of E) ⟶ Spec (CommRingCat.of (T.residueField t)))
      (k : Spec (CommRingCat.of E) ⟶ Spec (CommRingCat.of K))
      (heq : (z ≫ T.fromSpecResidueField t) ≫ g = (k ≫ y) ≫ S.fromSpecResidueField s),
      Surjective k ∧ Surjective ((commonFieldFibreIso f g t s z k y heq).hom ≫
        pullback.fst (pullback.snd (f.fiberToSpecResidueField s) y) k)
```

The upstream file is unchanged. Its stronger conclusion implies the original one: retain
`E`, its field instance and `z`, choose
`p := (commonFieldFibreIso f g t s z k y heq).hom ≫
pullback.fst (pullback.snd (f.fiberToSpecResidueField s) y) k`, and use the final conjunct.
A scratch proof with the exact old signature compiles and has only the permitted axioms.
The node's natural-language statement and its proof plan remain unchanged.

## Users

`python3 tools/downstream.py Sheaf.AlgebraicGeometry.CommonFieldFibreComparison --uses
AlgebraicGeometry.exists_common_field_fibre_comparison` reports zero downstream modules.
A search of both Lean roots confirms that the only other occurrence of the theorem is its
upstream definition and the already adapted upstream `GeometricGenericCoverSpread` proof.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.CommonFieldFibreComparison | W2 | Withdraw unused duplicate. |
| WeilConjectures.AlgebraicGeometry.CommonFieldFibreComparison | unmodified | Existing theorem supplies the node. |
| WeilConjectures.AlgebraicGeometry.GeometricGenericCoverSpread | unmodified | Already uses upstream witnesses; compiled unchanged. |

No target statement or definition changes; no target statement review is reopened.

## Status

landed 20261020T135435-L-1823728 2026-10-20 (merge of deliver/W2/Sheaf.AlgebraicGeometry.CommonFieldFibreComparison)
