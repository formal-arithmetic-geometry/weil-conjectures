# AlgebraicGeometry.affine_perfect_open_represent_cohomology_core

## Reason

Apply the human-approved retirement of upstream twins in
coord/changes/retire-sheaf-twins-20261020.md and this item's DIFFERENT row in
coord/retire-items.tsv. The copy has zero proof holes. The official library already
proves its structural conjunction, with only the unused E argument removed.
There are no live or quarantined Lean importers of the copy. The two inventory
consumers have already moved upstream and use the official API without E.
The remaining work is withdrawing the duplicate and redirecting its DAG attachment.

## Old

Module: Sheaf.AlgebraicGeometry.AffinePerfectOpenRepresentCohomologyCore.

```lean
theorem affine_perfect_open_represent_cohomology_core
    (A : Type uMain) [CommRing A] (r : ℕ) (f : Fin r → A)
    [HasDerivedCategory.{wMain}
      (SheafOfModules.{uMain} (moduleRings (Spec (.of A)).toRingedSpace))]
    [∀ V : (Spec (.of A)).Opens, HasDerivedCategory.{wMain}
      (SheafOfModules.{uMain} ((moduleRings (Spec (.of A)).toRingedSpace).over V))]
    [HasDerivedCategory.{wMain}
      (SheafOfModules.{uMain} (moduleRings (koszulOpen A r f).toScheme.toRingedSpace))]
    (E : schemeDerivedQCohCategory (Spec (.of A))) :
    (∀ e : ℕ, ∃ δ : koszulOpenKoszulObject A r f e ⟶
      (koszulOpenObject A r f e)⟦(1 : ℤ)⟧,
      Triangle.mk (koszulOpenUnit A r f e) (koszulOpenKoszulUnit A r f e) δ ∈
        distTriang (schemeDerivedCategory (Spec (.of A)))) ∧
    (∀ e : ℕ, Scheme.IsPerfect (Spec (.of A)) (koszulOpenObject A r f e)) ∧
    (∀ (a b : ℕ) (h : a ≤ b),
      koszulOpenMap A r f a b h ≫ koszulOpenUnit A r f a = koszulOpenUnit A r f b)
```

## New

Module: WeilConjectures.AlgebraicGeometry.AffinePerfectOpenRepresentCohomologyCore.
This existing source declaration is unchanged:

```lean
theorem affine_perfect_open_represent_cohomology_core
    (A : Type uMain) [CommRing A] (r : ℕ) (f : Fin r → A)
    [HasDerivedCategory.{wMain}
      (SheafOfModules.{uMain} (moduleRings (Spec (.of A)).toRingedSpace))]
    [∀ V : (Spec (.of A)).Opens, HasDerivedCategory.{wMain}
      (SheafOfModules.{uMain} ((moduleRings (Spec (.of A)).toRingedSpace).over V))]
    [HasDerivedCategory.{wMain}
      (SheafOfModules.{uMain} (moduleRings (koszulOpen A r f).toScheme.toRingedSpace))] :
    (∀ e : ℕ, ∃ δ : koszulOpenKoszulObject A r f e ⟶
      (koszulOpenObject A r f e)⟦(1 : ℤ)⟧,
      Triangle.mk (koszulOpenUnit A r f e) (koszulOpenKoszulUnit A r f e) δ ∈
        distTriang (schemeDerivedCategory (Spec (.of A)))) ∧
    (∀ e : ℕ, Scheme.IsPerfect (Spec (.of A)) (koszulOpenObject A r f e)) ∧
    (∀ (a b : ℕ) (h : a ≤ b),
      koszulOpenMap A r f a b h ≫ koszulOpenUnit A r f a = koszulOpenUnit A r f b)
```

The old statement follows by `exact affine_perfect_open_represent_cohomology_core A r f`
for any E. A scratch theorem with the verbatim old signature verifies this.
No mathematical hypothesis is added and all three conclusions stay identical.
The Sheaf copy is withdrawn using deleted.txt; its node now points to the official
module and records that module's verbatim signature. Its statement, proof steps,
proof dependencies and unit route are unchanged. No source file or target changes.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.AffinePerfectOpenRepresentCohomologyCore | C4 | Withdraw duplicate. |
| WeilConjectures.AlgebraicGeometry.AffinePerfectOpenRepresentCohomology | unchanged | Already uses official theorem without E. |
| WeilConjectures.AlgebraicGeometry.AffinePerfectOpenRepresentCohomologyColimit | unchanged | Already uses official theorem without E. |

tools/downstream.py reports zero downstream modules and only the old file itself
mentions the declaration in that closure. Source searches in lean/ and quarantine/
also find no importer of the Sheaf copy.
The DAG parent lem-sc-affine-perfect-open-represent-cohomology-colimit retains its
edge to the same core node, now realized upstream. The inventory's former Sheaf
consumers are absent, and neither is quarantined. Their official counterparts
already import the official core. No consumer adaptation is needed.
The sk-thm-picard-duality unit has no realized node for this item; its route is kept.
The private helpers boundary_zero and chain_augmentation_compatibility belong only
to the deleted proof; the official proof supplies its own private helpers.

## Status

landed 20261020T160105-L-3325388 2026-10-20 (merge of deliver/C4/Sheaf.AlgebraicGeometry.AffinePerfectOpenRepresentCohomologyCore)
