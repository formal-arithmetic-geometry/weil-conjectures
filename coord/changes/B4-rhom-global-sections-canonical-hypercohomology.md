# CategoryTheory.ringedSiteZerothHypercohomology

## Reason

The sync to upstream 5f7b33eac added the source-library definition
CategoryTheory.ringedSiteZerothHypercohomology. Its signature and complete body are
byte-identical to the declaration still in the local Sheaf module. Loading both modules
fails with a duplicate-declaration error. The assigned RhomGlobalSectionsOfUniverses
item was quarantined for precisely this error (coord/rework.tsv).

Replace the legacy module's duplicate declaration with a public import of the canonical
upstream declaration, preserving all six original public infrastructure imports. The
legacy module continues to export the same declaration under the same name and with
the same signature and body. Also import the canonical module directly from the
independent-universe companion; its complete definition is unchanged. This handles
both the assigned item and QbarCohomologyFiniteLevelComparison, which imports both
the companion and LocallyFreeDerivedHom (the other direct legacy consumer).

Both auxiliary modules are unclaimed. No source-library file is edited, no mathematical
definition changes, no target meaning changes, and no public API is withdrawn.
The restored item is byte-identical to its quarantine archive; its proof and DAG
attachment/dependencies are preserved.

## Old

Legacy module public imports and declaration:

```lean
public import Sheaf.CategoryTheory.RingedSiteKInjectiveResolutions
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.KInjective
public import Mathlib.CategoryTheory.Preadditive.Yoneda.Basic
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence

noncomputable def ringedSiteZerothHypercohomology
    {C : Type u} [SmallCategory C]
    (J : GrothendieckTopology C) (R : Sheaf J CommRingCat.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))] :
    DerivedCategory (SheafOfModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) ⥤ AddCommGrpCat.{u} :=
  haveI : IsGrothendieckAbelian.{u} (SheafOfModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) :=
    SheafOfModules.isGrothendieckAbelian _
  letI := HasDerivedCategory.standard AddCommGrpCat.{u}
  (preadditiveCoyoneda.obj (op (SheafOfModules.unit
    ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)))).rightDerivedFunctor ⋙
      DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0
```

Companion public import and declaration:

```lean
public import Sheaf.Algebra.Homology.RingedSiteZerothHypercohomology

noncomputable def ringedSiteZerothHypercohomologyOfUniverses
    {C : Type c} [Category.{v} C] (J : GrothendieckTopology C)
    [HasSheafify J AddCommGrpCat.{max c v r}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{max c v r}]
    (R : Sheaf J CommRingCat.{max c v r})
    [HasDerivedCategory.{w} (SheafOfModules.{max c v r}
      ((sheafCompose J
        (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R))] :
    DerivedCategory (SheafOfModules.{max c v r}
      ((sheafCompose J
        (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R)) ⥤
      AddCommGrpCat.{max c v r} :=
  letI : IsGrothendieckAbelian.{max c v r} (SheafOfModules.{max c v r}
      ((sheafCompose J
        (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R)) :=
    (SheafOfModules.grothendieckAbelian_and_functorial_kInjective_resolutionsOfUniverses.{c, v, r}
      J R).1
  letI := HasDerivedCategory.standard AddCommGrpCat.{max c v r}
  let Γ : SheafOfModules.{max c v r}
      ((sheafCompose J
        (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R) ⥤ AddCommGrpCat.{max c v r} :=
    preadditiveCoyoneda.obj (op (SheafOfModules.unit
      ((sheafCompose J
        (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R)))
  Γ.rightDerivedFunctor ⋙ DerivedCategory.homologyFunctor AddCommGrpCat.{max c v r} 0
```

## New

The legacy module retains the following public imports, including the new canonical
provider, and declares no duplicate definition. The upstream definition imported here
is byte-identical to the old legacy definition above.

```lean
public import Sheaf.CategoryTheory.RingedSiteKInjectiveResolutions
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.KInjective
public import Mathlib.CategoryTheory.Preadditive.Yoneda.Basic
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence

public import WeilConjectures.Algebra.Homology.RingedSiteZerothHypercohomology
```

The companion imports the canonical provider and retains its definition verbatim:

```lean
public import WeilConjectures.Algebra.Homology.RingedSiteZerothHypercohomology

noncomputable def ringedSiteZerothHypercohomologyOfUniverses
    {C : Type c} [Category.{v} C] (J : GrothendieckTopology C)
    [HasSheafify J AddCommGrpCat.{max c v r}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{max c v r}]
    (R : Sheaf J CommRingCat.{max c v r})
    [HasDerivedCategory.{w} (SheafOfModules.{max c v r}
      ((sheafCompose J
        (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R))] :
    DerivedCategory (SheafOfModules.{max c v r}
      ((sheafCompose J
        (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R)) ⥤
      AddCommGrpCat.{max c v r} :=
  letI : IsGrothendieckAbelian.{max c v r} (SheafOfModules.{max c v r}
      ((sheafCompose J
        (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R)) :=
    (SheafOfModules.grothendieckAbelian_and_functorial_kInjective_resolutionsOfUniverses.{c, v, r}
      J R).1
  letI := HasDerivedCategory.standard AddCommGrpCat.{max c v r}
  let Γ : SheafOfModules.{max c v r}
      ((sheafCompose J
        (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R) ⥤ AddCommGrpCat.{max c v r} :=
    preadditiveCoyoneda.obj (op (SheafOfModules.unit
      ((sheafCompose J
        (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R)))
  Γ.rightDerivedFunctor ⋙ DerivedCategory.homologyFunctor AddCommGrpCat.{max c v r} 0
```

## Users

Both downstream.py --uses scans were run, for the legacy module and for the companion.
The first eleven rows below are the union of their live transitive consumers; the
remaining rows add the restored item, every quarantined direct companion consumer,
and the repaired legacy provider itself.
Import searches found that QbarCohomologyFiniteLevelComparison is the only importer of
LocallyFreeDerivedHom. Thus re-exporting the source definition from the legacy module
is necessary to preserve its combined import context. No consumer signature changes.
The canonical source dependency has the same public infrastructure as the legacy
module; its K-injective resolution import is the source module re-exported by the
legacy module's existing Sheaf compatibility import.

| module | group holding it | effect |
|---|---|---|
| Sheaf.Algebra.Homology.DerivedInternalHomSectionsModel | unclaimed | Same public declarations; no adaptation. |
| Sheaf.Algebra.Homology.LocallyFreeDerivedHom | unclaimed | Same public declarations; no adaptation. |
| Sheaf.Algebra.Homology.RhomHypercohomologyBridgeOfUniverses | unclaimed | Same public declarations; no adaptation. |
| Sheaf.Algebra.Homology.RingedSiteZerothHypercohomologyOfUniverses | unclaimed | Unchanged definition; import canonical upstream dependency directly. |
| Sheaf.AlgebraicGeometry.DerivedBasisBbdDescent | unclaimed | Same public declarations; no adaptation. |
| Sheaf.AlgebraicGeometry.DerivedBasisIncreasingUnion | unclaimed | Same public declarations; no adaptation. |
| Sheaf.AlgebraicGeometry.DerivedBasisLocalHomGlue | unclaimed | Same public declarations; no adaptation. |
| Sheaf.AlgebraicGeometry.SupportedProductLocalization | unclaimed | Same public declarations; no adaptation. |
| Sheaf.CategoryTheory.DerivedCoyonedaEvaluation | unclaimed | Same public declarations; no adaptation. |
| Sheaf.Paper.ExternalRHomConePairing | unclaimed | Same public declarations; no adaptation. |
| Sheaf.TraceFormula.DerivedBasisLocalExtSheaf | unclaimed | Same public declarations; no adaptation. |
| Sheaf.Algebra.Homology.RhomGlobalSectionsOfUniverses | B4 | Restore quarantined proof verbatim; duplicate-import error resolved. |
| Sheaf.Paper.QbarCohomologyFiniteLevelComparison | unclaimed | Imports legacy and companion; both now expose the same upstream definition. |
| Sheaf.SixFunctors.IntegralExtHomContinuity | unclaimed | Same public declarations; no adaptation. |
| Sheaf.Paper.IntegralStratumHomFormula | unclaimed | Same public declarations; no adaptation. |
| Sheaf.Algebra.Homology.RingedSiteZerothHypercohomology | unclaimed | Repaired provider: re-export the identical canonical definition; retain original public imports. |

All three delivered modules compile together with lcompile.py. The unchanged
DerivedInternalHomSectionsModel, RhomHypercohomologyBridgeOfUniverses, and
LocallyFreeDerivedHom also compile against the repair. A combined-import probe of
the latter with the restored item and independent-universe companion passes.
The definitions have only the three allowed axioms; the theorem retains its existing
unfinished dependencies. Every compile was below 60 seconds without warnings.

The complete three-module dry run passed compilation and server preflight (CODEX).

## Status

landed 20261020T145448-L-2397739 2026-10-20 (merge of deliver/B4/Sheaf.Algebra.Homology.RhomGlobalSectionsOfUniverses)
