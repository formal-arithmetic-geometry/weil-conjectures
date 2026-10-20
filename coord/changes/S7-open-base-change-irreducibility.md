# AlgebraicGeometry.singleComplexOpen_baseChange_calculation

## Reason

Return C-32aed passed the mathematics but refused landing from the stale base
`d92f73d8e`. Rechecked the current rework entry and quarantined source for this
retry; deliver3.py builds the new packet on the current fetched `sheaf-dag`.
The archive remains untouched, and the existing upstream proof still matches
it apart from the copyright header and the corrected irreducibility command.

Restore the module listed in coord/rework.tsv using its already proved upstream
twin. The quarantined Sheaf copy rejects a redundant local irreducibility
attribute for `derivedPullback`. The upstream twin has the identical public
statement and complete calculation and already omits that attribute. Re-export
it to preserve the module interface and avoid duplicate declarations.

## Old

The quarantined file publicly imports
`WeilConjectures.AlgebraicGeometry.SingleComplexOpenBaseChangeComparisons` and
`WeilConjectures.AlgebraicGeometry.SchemeDerivedBaseChangeMap`, privately imports
`WeilConjectures.AlgebraicGeometry.SingleComplexOpenCounitCompatibility` and
`WeilConjectures.AlgebraicGeometry.SingleComplexOpenPullbackCube`, and redeclares
`AlgebraicGeometry.singleComplexOpen_baseChange_calculation` with the verbatim
signature recorded in node `lem-pc-n3-open-base-change-calculation`. It contains
five private helper proofs and the rejected command:

```lean
attribute [local irreducible] derivedPullback singleComplexOpenDirectImageIso
```

The previous public signature, preserved by the re-export, is:

```lean
theorem singleComplexOpen_baseChange_calculation
    [∀ Y : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    {X X' S S' : Scheme.{u}}
    (f : X ⟶ S) (f' : X' ⟶ S') (g : S' ⟶ S) (g' : X' ⟶ X)
    (sq : IsPullback g' f' f g)
    (K : schemeDerivedCategory X)
    (V : S.Opens) (V' : S'.Opens) (hV' : V' ≤ g ⁻¹ᵁ V)
    (j : (f' ⁻¹ᵁ V').toScheme ⟶ (f ⁻¹ᵁ V).toScheme)
    (hj : j ≫ (f ⁻¹ᵁ V).ι = (f' ⁻¹ᵁ V').ι ≫ g')
    (sq₀ : IsPullback j (f' ∣_ V') (f ∣_ V) (g.resLE V V' hV')) :
    let K₀ := (schemeOpenRestriction X (f ⁻¹ᵁ V)).mapDerivedCategory.obj K
    let R := (schemeOpenRestriction S' V').mapDerivedCategory
    let δ := singleComplexRestrictedCoefficient g' K ((derivedPullback g').obj K) (𝟙 _)
      (f ⁻¹ᵁ V) (f' ⁻¹ᵁ V') j hj
    R.map (schemeDerivedBaseChangeMap f f' g g' sq.w K) =
      (singleComplexOpenBaseChangeSourceIso f g K V V' hV').hom ≫
        schemeDerivedBaseChangeMap
          (f ∣_ V) (f' ∣_ V') (g.resLE V V' hV') j sq₀.w K₀ ≫
        (schemeDerivedDirectImage (f' ∣_ V')).map δ ≫
        (singleComplexOpenDirectImageIso f' V').inv.app ((derivedPullback g').obj K)
```

## New

```lean
module

public import WeilConjectures.AlgebraicGeometry.SingleComplexOpenBaseChangeCalculation
```

The same theorem and all previously public imports remain visible through this
upstream module. No statement or definition changes. The DAG attachment points
to the existing upstream declaration, whose proof route is identical. No
upstream file or target meaning changes, and no new sorry is introduced.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.SingleComplexOpenBaseChangeCalculation | S7 | Restored as a re-export of its proved upstream twin. |

No lean/ module currently imports the quarantined Sheaf path (direct import
scan). tools/downstream.py reports it unknown. Existing current consumers import
the upstream twin, which is unchanged. No adaptation is needed.

## Status

landed 20261020T151232-L-2651895 2026-10-20 (merge of deliver/S7/Sheaf.AlgebraicGeometry.SingleComplexOpenBaseChangeCalculation)
