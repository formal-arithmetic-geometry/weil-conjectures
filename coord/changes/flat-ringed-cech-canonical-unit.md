# CategoryTheory.flat_ringedCech_baseChange_data_quasiIso

## Reason

STATEMENT-DISPUTED (resolved by this repair): augmentation compatibility alone does
not imply a quasi-isomorphism. For the identity coefficient map and zero ideal, take
the nonzero ring complex K=R[0], L=K direct-sum K, delta the first projection, and u
the first inclusion. The required augmentation equation holds, but H^0(u) is not
surjective. The empty-list local extended Cech description is K=R[0].

Stacks Algebraization Tag 099I instead takes K prime = K tensor_R B. The replacement
states the canonical unit theorem and proves it using the quotient criterion, ordered
Koszul torsion, and exact filtered colimits. This is a correction of a false intermediate
statement, not a proof of its old universal assertion. The parent existential theorem
retains its exact signature. No Challenge declaration or source-library signature changes.

## Old

```lean
theorem flat_ringedCech_baseChange_data_quasiIso
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    {R B : Sheaf J CommRingCat.{u}} (φ : R ⟶ B) (I : RingedSiteIdeal R)
    [HasDerivedCategory.{w} (SheafOfModules.{u} (siteModuleRings R))]
    [∀ U : C, HasDerivedCategory.{w}
      (SheafOfModules.{u} (siteModuleRings (R.over U)))]
    (hI : SheafOfModules.IsFiniteType.{u, u, u} I.module)
    (hflat : SheafOfModules.IsFlat
      ((SheafOfModules.restrictScalars.{u}
        ((sheafCompose J (forget₂ CommRingCat RingCat)).map φ)).obj
          (SheafOfModules.unit (siteModuleRings B))))
    (hquot : I.IsQuotientIso φ)
    (K : ringedSiteComplex R) (ε : K ⟶ ringedSiteRingComplex R)
    (hK : HasLocalExtendedCechDescription R I.module I.inclusion K ε) :
    let r := SheafOfModules.restrictScalars.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).map φ)
    let rc := r.mapHomologicalComplex (.up ℤ)
    let σ : ringedSiteRingComplex R ⟶ rc.obj (ringedSiteRingComplex B) :=
      (HomologicalComplex.single _ (.up ℤ) 0).map
          (SheafOfModules.LocalizationCech.unitMap φ) ≫
        (HomologicalComplex.singleMapHomologicalComplex r (.up ℤ) 0).inv.app
          (SheafOfModules.unit (siteModuleRings B))
    ∀ (L : ringedSiteComplex B) (δ : L ⟶ ringedSiteRingComplex B)
      (u : K ⟶ rc.obj L), u ≫ rc.map δ = ε ≫ σ → QuasiIso u
```

## New

```lean
theorem flat_ringedCech_baseChange_data_quasiIso
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    {R B : Sheaf J CommRingCat.{u}} (φ : R ⟶ B) (I : RingedSiteIdeal R)
    [HasDerivedCategory.{w} (SheafOfModules.{u} (siteModuleRings R))]
    [∀ U : C, HasDerivedCategory.{w}
      (SheafOfModules.{u} (siteModuleRings (R.over U)))]
    (hI : SheafOfModules.IsFiniteType.{u, u, u} I.module)
    (hflat : SheafOfModules.IsFlat
      ((SheafOfModules.restrictScalars.{u}
        ((sheafCompose J (forget₂ CommRingCat RingCat)).map φ)).obj
          (SheafOfModules.unit (siteModuleRings B))))
    (hquot : I.IsQuotientIso φ)
    (K : ringedSiteComplex R) (ε : K ⟶ ringedSiteRingComplex R)
    (hK : HasLocalExtendedCechDescription R I.module I.inclusion K ε) :
    QuasiIso ((ringedScalarExtensionComplexAdjunction φ).unit.app K)
```

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.FlatRingedCechBaseChangeQuasiIso | R2 | Replace false intermediate assertion with the canonical-unit theorem, fully proved. |
| Sheaf.Paper.FlatRingedCechBaseChange | unclaimed | Keep every binder and the existential conclusion; choose actual scalar extension and its adjoint augmentation. |

`tools/downstream.py ... --uses CategoryTheory.flat_ringedCech_baseChange_data_quasiIso`
reports these two textual users and the parent as the only downstream module. The only
DAG citer is lem-weil-pbc-flat-ringed-cech-base-change; its proof is adapted in this packet.
The public definition ringedScalarExtensionComplexAdjunction is the existing scalar
adjunction prolonged termwise, with its additivity instance proved from Mathlib. It
introduces no alternative notion or arbitrary chosen object. The three new comparison
modules contain only proved theorems and explicit constructions.

## Status

landed 20261020T153020-L-2864097 2026-10-20 (merge of deliver/R2/Sheaf.Paper.FlatRingedCechBaseChangeQuasiIso)
