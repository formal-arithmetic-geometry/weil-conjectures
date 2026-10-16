# SheafOfModules.tensorToRestrict and SheafOfModules.tensorHomEquiv

## Reason

The upstream sync replaced these private constructions by holed definitions and commented
out their inverse. Construct the data explicitly using the public module scalar-extension
Hom equivalence and sheafification Hom equivalence. Restore the inverse and prove its
naturality. A proved local helper derives the restriction formula from the public
`exists_changeOfRingsMap` specification, avoiding private declarations of the retired
TensorProduct wrapper. The site adjunction is then proved by `leftAdjointOfEquiv`.

## Old

```lean
private noncomputable def tensorToRestrict
    (M : SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj A))
    (N : SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj B))
    (f : changeOfRingsPresheaf α M ⟶ N.val) :
    M ⟶ (restrictScalars ((sheafCompose J (forget₂ CommRingCat RingCat)).map α)).obj N := by
  sorry

private noncomputable def tensorHomEquiv
    (M : SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj A))
    (N : SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj B)) :
    (changeOfRings α M ⟶ N) ≃
      (M ⟶ (restrictScalars ((sheafCompose J (forget₂ CommRingCat RingCat)).map α)).obj N) := by
  sorry
```

`tensorFromRestrict` was commented out after the sync.

## New

```lean
private noncomputable def tensorToRestrict
    (M : SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj A))
    (N : SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj B))
    (f : changeOfRingsPresheaf α M ⟶ N.val) :
    M ⟶ (restrictScalars ((sheafCompose J (forget₂ CommRingCat RingCat)).map α)).obj N where
  val :=
    { app := fun U ↦ ModuleCat.ExtendRestrictScalarsAdj.HomEquiv.toRestrictScalars
        (α.hom.app U).hom (f.app U)
      naturality := by
        intro U V i
        ext m
        change f.app V ((1 : B.obj.obj V) ⊗ₜ[A.obj.obj V, (α.hom.app V).hom]
            M.val.map i m) =
          N.val.map i (f.app U ((1 : B.obj.obj U) ⊗ₜ[A.obj.obj U, (α.hom.app U).hom] m))
        have h := PresheafOfModules.naturality_apply f i
          ((1 : B.obj.obj U) ⊗ₜ[A.obj.obj U, (α.hom.app U).hom] m)
        change f.app V (changeOfRingsMap α M i _) = N.val.map i (f.app U _) at h
        rw [scalarExtensionMap_tmul, map_one] at h
        exact h }

private noncomputable def tensorHomEquiv
    (M : SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj A))
    (N : SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj B)) :
    (changeOfRings α M ⟶ N) ≃
      (M ⟶ (restrictScalars ((sheafCompose J (forget₂ CommRingCat RingCat)).map α)).obj N) :=
  (PresheafOfModules.sheafificationHomEquiv (𝟙 _)).trans
    { toFun := tensorToRestrict α M N
      invFun := tensorFromRestrict α M N
      left_inv := by
        intro f
        ext U x
        exact ConcreteCategory.congr_hom
          ((ModuleCat.ExtendRestrictScalarsAdj.homEquiv
            (α.hom.app U).hom).symm_apply_apply (f.app U)) x
      right_inv := by
        intro g
        ext U x
        exact ConcreteCategory.congr_hom
          ((ModuleCat.ExtendRestrictScalarsAdj.homEquiv
            (α.hom.app U).hom).apply_symm_apply (g.val.app U)) x }
```

`tensorFromRestrict` is restored as a private explicit construction; it is proved
sectionwise from `HomEquiv.fromExtendScalars`, and its naturality is checked on generators.
All public declarations keep their signatures, visibility, and mathematical meaning.
The two repaired definitions occur only in proofs and have no external users.

## Users

The two `tools/downstream.py --uses` checks each found only the item module.
The import closure has 22 downstream modules, but none can access these private helpers.
The direct public consumer, `ContinuousModuleEncodingLattices`, uses the unchanged
`continuousModuleEncoding_scalar_extension` theorem; no consumer adaptation is needed.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.ContinuousModuleEncodingScalarExtension | M2 | Explicit private data replaces both holes; the site adjunction is proved. |

## Status

landed 20261016T221618-L-1617414 2026-10-16 (merge of deliver/M2/Sheaf.Paper.ContinuousModuleEncodingScalarExtension)
