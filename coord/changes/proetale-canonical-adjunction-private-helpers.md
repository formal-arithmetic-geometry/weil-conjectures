# AlgebraicGeometry.Scheme.proEtaleRingModuleAdjunction_existsUnique

## Reason

The delivery adds only proved private helpers and completes the existing normalization
proof. The static interface checker flags the added top-level universe and variable
commands. This record documents their actual scope: `v` and `w` parameterize only the
private arbitrary-site tensor helpers. Namespace-local variables and the local notation
are confined to those helpers. The existing theorem still has exactly its original
universe and binders. No existing public declaration, instance, notation or import
changes; downstream modules need no adaptation.

The new helpers construct both tensor transpose maps and both AsSmall transport maps
explicitly. They do not choose arbitrary witnesses from an existence theorem and do
not introduce any new proof holes.

## Old

The original public theorem signature, verbatim:

```lean
theorem proEtaleRingModuleAdjunction_existsUnique :
    ∃! adj : proEtaleRingModulePullback f R S c ⊣ proEtaleRingModuleDirectImage f R S c,
      ∀ (M : proEtaleRingModules Y R) (N : proEtaleRingModules X S)
        (h : (proEtaleRingModulePullback f R S c).obj M ⟶ N),
      ∃ g : (SheafOfModules.pullback.{u + 1} (proEtaleModelRingUnit f R)).obj
          ((proEtaleModuleToModel ((sheafCompose (ProEt.topology Y)
            (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R)).obj M) ⟶
          (proEtaleModuleToModel ((sheafCompose (ProEt.topology X)
            (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
              ((proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj R))).obj
                ((SheafOfModules.restrictScalars.{u + 1}
                  ((sheafCompose (ProEt.topology X)
                    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map c.hom)).obj N),
        (∀ (W : (proEtaleSiteModel X)ᵒᵖ)
          (m : ((SheafOfModules.pullback.{u + 1} (proEtaleModelRingUnit f R)).obj
            ((proEtaleModuleToModel ((sheafCompose (ProEt.topology Y)
              (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R)).obj M)).val.obj W),
          g.val.app W m = h.val.app (AsSmall.down.op.obj W)
            (((PresheafOfModules.sheafificationAdjunction.{u + 1}
              (𝟙 ((sheafCompose (ProEt.topology X)
                (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj S).obj)).unit.app
                  (SheafOfModules.changeOfRingsPresheaf.{u, u + 1, u + 1}
                    (J := ProEt.topology X) c.hom
                    ((proEtaleModuleInverseImage f R).obj M))).app
                      (AsSmall.down.op.obj W)
                        ((1 : S.obj.obj (AsSmall.down.op.obj W)) ⊗ₜ[_,
                          (c.hom.hom.app (AsSmall.down.op.obj W)).hom]
                            (@id (((proEtaleModuleInverseImage f R).obj M).val.obj
                              (AsSmall.down.op.obj W)) m)))) ∧
        ∀ (W : Y.ProEtᵒᵖ) (m : M.val.obj W),
          (adj.homEquiv M N h).val.app W m =
            (((SheafOfModules.pullbackPushforwardAdjunction
              (proEtaleModelRingUnit f R)).homEquiv _ _ g).val.app
                (AsSmall.up.op.obj W)) m
```

Original universe declaration: `universe u`.

## New

The public theorem signature is identical, verbatim:

```lean
theorem proEtaleRingModuleAdjunction_existsUnique :
    ∃! adj : proEtaleRingModulePullback f R S c ⊣ proEtaleRingModuleDirectImage f R S c,
      ∀ (M : proEtaleRingModules Y R) (N : proEtaleRingModules X S)
        (h : (proEtaleRingModulePullback f R S c).obj M ⟶ N),
      ∃ g : (SheafOfModules.pullback.{u + 1} (proEtaleModelRingUnit f R)).obj
          ((proEtaleModuleToModel ((sheafCompose (ProEt.topology Y)
            (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R)).obj M) ⟶
          (proEtaleModuleToModel ((sheafCompose (ProEt.topology X)
            (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
              ((proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj R))).obj
                ((SheafOfModules.restrictScalars.{u + 1}
                  ((sheafCompose (ProEt.topology X)
                    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map c.hom)).obj N),
        (∀ (W : (proEtaleSiteModel X)ᵒᵖ)
          (m : ((SheafOfModules.pullback.{u + 1} (proEtaleModelRingUnit f R)).obj
            ((proEtaleModuleToModel ((sheafCompose (ProEt.topology Y)
              (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R)).obj M)).val.obj W),
          g.val.app W m = h.val.app (AsSmall.down.op.obj W)
            (((PresheafOfModules.sheafificationAdjunction.{u + 1}
              (𝟙 ((sheafCompose (ProEt.topology X)
                (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj S).obj)).unit.app
                  (SheafOfModules.changeOfRingsPresheaf.{u, u + 1, u + 1}
                    (J := ProEt.topology X) c.hom
                    ((proEtaleModuleInverseImage f R).obj M))).app
                      (AsSmall.down.op.obj W)
                        ((1 : S.obj.obj (AsSmall.down.op.obj W)) ⊗ₜ[_,
                          (c.hom.hom.app (AsSmall.down.op.obj W)).hom]
                            (@id (((proEtaleModuleInverseImage f R).obj M).val.obj
                              (AsSmall.down.op.obj W)) m)))) ∧
        ∀ (W : Y.ProEtᵒᵖ) (m : M.val.obj W),
          (adj.homEquiv M N h).val.app W m =
            (((SheafOfModules.pullbackPushforwardAdjunction
              (proEtaleModelRingUnit f R)).homEquiv _ _ g).val.app
                (AsSmall.up.op.obj W)) m
```

The file now declares `universe u v w`, with `v` and `w` used only by private helpers.
All existing public definitions are retained verbatim. Their selected adjunction is
now justified by the completed unique-normalization proof. No target statement or
notion changes meaning, so no target statement review is reopened.

## Users

The table includes every transitive importer returned by `tools/downstream.py`.
Groups are the local claim snapshot; no consumer is edited in this delivery.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.NoetherianStratumDetection | unclaimed | No adaptation; all existing signatures, definitions and imports unchanged. |
| Sheaf.AlgebraicGeometry.ProEtaleBoundedBelowCoproducts | C2 | No adaptation; all existing signatures, definitions and imports unchanged. |
| Sheaf.AlgebraicGeometry.ProEtaleOpenClosedDetection | unclaimed | No adaptation; all existing signatures, definitions and imports unchanged. |
| Sheaf.AlgebraicGeometry.ProEtaleRingSheafChangeAdjunction | unclaimed | No adaptation; all existing signatures, definitions and imports unchanged. |
| Sheaf.Paper.CondensedFinitePresentationDescent | unclaimed | No adaptation; all existing signatures, definitions and imports unchanged. |
| Sheaf.Paper.CondensedOpenClosedRecollement | unclaimed | No adaptation; all existing signatures, definitions and imports unchanged. |
| Sheaf.Paper.CondensedQbarBaseChangeCompatibility | unclaimed | No adaptation; all existing signatures, definitions and imports unchanged. |
| Sheaf.Paper.CondensedQcqsPushforwardContinuity | unclaimed | No adaptation; all existing signatures, definitions and imports unchanged. |
| Sheaf.Paper.CondensedSheafExtContinuity | unclaimed | No adaptation; all existing signatures, definitions and imports unchanged. |
| Sheaf.Paper.FiniteCtfTriangulated | unclaimed | No adaptation; all existing signatures, definitions and imports unchanged. |
| Sheaf.Paper.FiniteTensorConstructibleCohomology | unclaimed | No adaptation; all existing signatures, definitions and imports unchanged. |
| Sheaf.Paper.FiniteTorsionConstructibility | unclaimed | No adaptation; all existing signatures, definitions and imports unchanged. |
| Sheaf.Paper.IntrinsicFiniteTorsionConstructibility | unclaimed | No adaptation; all existing signatures, definitions and imports unchanged. |
| Sheaf.Paper.ProEtaleBoundedConstructibleTriangulated | unclaimed | No adaptation; all existing signatures, definitions and imports unchanged. |
| Sheaf.Paper.ProEtaleResidueTorTest | unclaimed | No adaptation; all existing signatures, definitions and imports unchanged. |
| TargetsCheck | unclaimed | No adaptation; all existing signatures, definitions and imports unchanged. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.CompactSupport | unclaimed | No adaptation; all existing signatures, definitions and imports unchanged. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.Proper | A2 | No adaptation; all existing signatures, definitions and imports unchanged. |

## Status

landed 20261015T161929-L-300828 2026-10-15 (merge of deliver/G3/Sheaf.AlgebraicGeometry.ProEtaleOperationsCanonicalAdjunction)
