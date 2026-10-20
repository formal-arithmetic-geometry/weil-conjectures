# AlgebraicGeometry.affine_koszul_geometric_properties

## Reason

Retire the duplicate Sheaf module under the human-approved retirement of upstream twins
(recorded in coord/changes/retire-sheaf-twins-20261020.md and coord/retire-items.tsv).
The upstream theorem has exactly the same signature and a complete proof. The stale
retirement inventory reports two missing helpers, but both were private in the Sheaf
copy; upstream supplies public versions named exists_tilde_exteriorPower_iso_free and
isZero_exteriorPower_finsupp_of_lt. There is no public API loss.

## Old

Module: Sheaf.AlgebraicGeometry.AffineKoszulGeometricProperties.
DAG attachment: lem-pc-affine-koszul-geometric-properties.

```lean
theorem affine_koszul_geometric_properties
    (A : Type u) [CommRing A] (r : ℕ) (f : Fin r → A)
    [HasDerivedCategory.{w}
      (SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace))]
    [∀ V : (Spec (.of A)).Opens, HasDerivedCategory.{w}
      (SheafOfModules.{u} ((moduleRings (Spec (.of A)).toRingedSpace).over V))] :
    let Q := DerivedCategory.Q.obj
      ((@Functor.mapHomologicalComplex ℤ (ModuleCat.{u} A)
        (SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace))
        _ _ _ _ (tilde.functor (.of A))
        ⟨fun _ _ ↦ tilde.map_zero⟩ (ComplexShape.up ℤ)).obj
        ((ExteriorAlgebra.koszulComplex A r f).extend ComplexShape.embeddingDownNat))
    Scheme.IsPerfect (Spec (.of A)) Q ∧
      ∀ (n : ℤ) (x : PrimeSpectrum A), (∃ i, f i ∉ x.asIdeal) →
        Subsingleton (↑(TopCat.Presheaf.stalk ((DerivedCategory.homologyFunctor
          (SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace)) n).obj
            Q).val.presheaf x))
```

## New

The same declaration and signature in
WeilConjectures.AlgebraicGeometry.AffineKoszulGeometricProperties:

```lean
theorem affine_koszul_geometric_properties
    (A : Type u) [CommRing A] (r : ℕ) (f : Fin r → A)
    [HasDerivedCategory.{w}
      (SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace))]
    [∀ V : (Spec (.of A)).Opens, HasDerivedCategory.{w}
      (SheafOfModules.{u} ((moduleRings (Spec (.of A)).toRingedSpace).over V))] :
    let Q := DerivedCategory.Q.obj
      ((@Functor.mapHomologicalComplex ℤ (ModuleCat.{u} A)
        (SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace))
        _ _ _ _ (tilde.functor (.of A))
        ⟨fun _ _ ↦ tilde.map_zero⟩ (ComplexShape.up ℤ)).obj
        ((ExteriorAlgebra.koszulComplex A r f).extend ComplexShape.embeddingDownNat))
    Scheme.IsPerfect (Spec (.of A)) Q ∧
      ∀ (n : ℤ) (x : PrimeSpectrum A), (∃ i, f i ∉ x.asIdeal) →
        Subsingleton (↑(TopCat.Presheaf.stalk ((DerivedCategory.homologyFunctor
          (SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace)) n).obj
            Q).val.presheaf x))
```

The DAG attachment points to the upstream module and its file. The Sheaf file is
withdrawn using deleted.txt. Proof steps, proof dependencies and unit route stay intact.
No source-library file or target statement changes.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.AffineKoszulGeometricProperties | N3 | Duplicate withdrawn. |
| WeilConjectures.AlgebraicGeometry.SupportedPerfectDetectorAffineConstruction | unchanged | Already imports the upstream theorem; compiles in the verification environment. |
| WeilConjectures.AlgebraicGeometry.AffinePerfectKoszulPrincipalUnitPerfect | unchanged | Already imports the upstream helpers; compiles in the verification environment. |

There are zero live or quarantined Lean importers of the Sheaf module.
The former consumer named by the retirement inventory has already been retired to
WeilConjectures.AlgebraicGeometry.SupportedPerfectDetectorAffineConstruction.
The one DAG attachment is redirected; its parent keeps the same node dependency.
No consumer adaptation is necessary. The existing unit record realizes no step with
this node, and the mathematical statement is preserved, not pruned.

Verification: an example with the original signature is proved by the upstream theorem,
while importing both official consumer modules. lcompile.py accepts it in 3.8 seconds.
#print axioms reports only propext, Classical.choice and Quot.sound.

## Status

landed 20261020T153751-L-2989221 2026-10-20 (merge of deliver/N3/Sheaf.AlgebraicGeometry.AffineKoszulGeometricProperties)
