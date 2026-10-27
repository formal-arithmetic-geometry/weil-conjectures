# AlgebraicGeometry.Etale.projectiveLine_strictLocal_stalkExchangeComparison_smallModel

## Reason

The restored small-colimit-model comparison and its adopted canonical-model counterpart
use the same fully qualified theorem name but have different hypotheses:
strictHenselizationScheme versus strictLocalization. Importing both modules fails with:

```
import WeilConjectures.AlgebraicGeometry.ProjectiveLineStrictLocalStalkExchangeComparison
failed, environment already contains
'AlgebraicGeometry.Etale.projectiveLine_strictLocal_stalkExchangeComparison'
from Sheaf.AlgebraicGeometry.ProjectiveLineStrictLocalStalkExchangeComparison
```

The proof dependency ProjectiveLineOriginalStalkTotalCohomologyExchange has the same
collision with its canonical counterpart. Rename both Sheaf theorems with the existing
_smallModel convention (already used by the abelian comparison), and rename the sole
caller in the item's proof. All binders, universes, instances, hypotheses, conclusions,
visibility, docstrings, imports and proofs are otherwise byte-identical. The dependency
module is unclaimed. No adopted source-library file is changed. Both nodes retain their
attachments and dependencies; only their Lean names and statement text are refreshed.
The unit route and all mathematical meanings are unchanged. No target is changed.

## Old

```lean
theorem Etale.projectiveLine_strictLocal_stalkExchangeComparison
    (Λ : Type (u + 1)) [CommRing Λ]
    {S T X' : Scheme.{u}} {g : T ⟶ S} {f' : X' ⟶ T} {g' : X' ⟶ ProjectiveLine S}
    (sq : IsPullback g' f' (ProjectiveLine S ↘ S) g)
    {k k' Ω : Type u} [Field k] [IsSepClosed k] [Field k'] [IsSepClosed k']
    [Field Ω] [IsAlgClosed Ω]
    (σ : Spec (.of k) ⟶ S) (τ : Spec (.of k') ⟶ T)
    (ι : Spec (.of k') ⟶ Spec (.of k)) (hι : ι ≫ σ = τ ≫ g)
    (ν : Spec (.of Ω) ⟶ Spec (.of k'))
    {A B : Type u} [CommRing A] [HenselianLocalRing A]
    [CommRing B] [HenselianLocalRing B]
    [IsSepClosed (IsLocalRing.ResidueField A)] [IsSepClosed (IsLocalRing.ResidueField B)]
    (eA : Spec (.of A) ≅ strictHenselizationScheme (ν ≫ ι ≫ σ))
    (eB : Spec (.of B) ≅ strictHenselizationScheme (ν ≫ τ))
    (φ : A →+* B) [IsLocalHom φ]
    (ρA : Spec (.of k) ⟶ Spec (.of (IsLocalRing.ResidueField A)))
    (ρB : Spec (.of k') ⟶ Spec (.of (IsLocalRing.ResidueField B)))
    (hφ : Spec.map (CommRingCat.ofHom φ) ≫ eA.hom ≫
        strictHenselizationStructuralMap (ν ≫ ι ≫ σ) =
      eB.hom ≫ strictHenselizationStructuralMap (ν ≫ τ) ≫ g)
    (hρA : ρA ≫ Spec.map (CommRingCat.ofHom (IsLocalRing.residue A)) ≫
      eA.hom ≫ strictHenselizationStructuralMap (ν ≫ ι ≫ σ) = σ)
    (hρB : ρB ≫ Spec.map (CommRingCat.ofHom (IsLocalRing.residue B)) ≫
      eB.hom ≫ strictHenselizationStructuralMap (ν ≫ τ) = τ)
    (hρ : ρB ≫ Spec.map (CommRingCat.ofHom (IsLocalRing.ResidueField.map φ)) = ι ≫ ρA)
    (F : Sheaf (ProjectiveLine S).smallEtaleTopology (ModuleCat.{u + 1} Λ))
    [IsTorsionModuleSheaf F] (q : ℕ) :
    let F₀ := (ProjectiveSpace.map _
      (eA.hom ≫ strictHenselizationStructuralMap (ν ≫ ι ≫ σ)))^*[
      ModuleCat.{u + 1} Λ].obj F
    let t₀ := pointSmallEtale (Spec.map (CommRingCat.ofHom (IsLocalRing.residue B)))
    let g₀ := Spec.map (CommRingCat.ofHom φ)
    ∃ (a₁ : ((pointSmallEtale τ).sheafFiber (A := ModuleCat.{u + 1} Λ)).obj
                  ((Etale.baseChangeSourceFunctor Λ g (ProjectiveLine S ↘ S) q).obj F) ≃+
                (t₀.sheafFiber (A := ModuleCat.{u + 1} Λ)).obj
                  ((Etale.baseChangeSourceFunctor Λ g₀
                    (ProjectiveLine (Spec (.of A)) ↘ Spec (.of A)) q).obj F₀))
                (a₂ : ((pointSmallEtale τ).sheafFiber (A := ModuleCat.{u + 1} Λ)).obj
                  ((Etale.baseChangeTargetFunctor Λ g' f' q).obj F) ≃+
                (t₀.sheafFiber (A := ModuleCat.{u + 1} Λ)).obj
                  ((Etale.baseChangeTargetFunctor Λ (ProjectiveSpace.map _ g₀)
                    (ProjectiveLine (Spec (.of B)) ↘ Spec (.of B)) q).obj F₀)),
                (∀ x, a₂ ((((pointSmallEtale τ).sheafFiber
                    (A := ModuleCat.{u + 1} Λ)).map
                    (Etale.baseChangeHomologyMap Λ sq q F)).hom x) =
                  ((t₀.sheafFiber (A := ModuleCat.{u + 1} Λ)).map
                    (Etale.baseChangeHomologyMap Λ
                      (ProjectiveSpace.isPullback_map _ g₀) q F₀)).hom (a₁ x))

theorem Etale.projectiveLine_originalStalk_totalCohomologyExchange
    (Λ : Type (u + 1)) [CommRing Λ]
    {S T X' : Scheme.{u}} {g : T ⟶ S} {f' : X' ⟶ T} {g' : X' ⟶ ProjectiveLine S}
    (sq : IsPullback g' f' (ProjectiveLine S ↘ S) g)
    {k k' Ω : Type u} [Field k] [IsSepClosed k] [Field k'] [IsSepClosed k']
    [Field Ω] [IsAlgClosed Ω]
    (σ : Spec (.of k) ⟶ S) (τ : Spec (.of k') ⟶ T)
    (ι : Spec (.of k') ⟶ Spec (.of k)) (hι : ι ≫ σ = τ ≫ g)
    (ν : Spec (.of Ω) ⟶ Spec (.of k'))
    {A B : Type u} [CommRing A] [HenselianLocalRing A]
    [CommRing B] [HenselianLocalRing B]
    [IsSepClosed (IsLocalRing.ResidueField A)] [IsSepClosed (IsLocalRing.ResidueField B)]
    (eA : Spec (.of A) ≅ strictHenselizationScheme (ν ≫ ι ≫ σ))
    (eB : Spec (.of B) ≅ strictHenselizationScheme (ν ≫ τ))
    (φ : A →+* B) [IsLocalHom φ]
    (ρA : Spec (.of k) ⟶ Spec (.of (IsLocalRing.ResidueField A)))
    (ρB : Spec (.of k') ⟶ Spec (.of (IsLocalRing.ResidueField B)))
    (hφ : Spec.map (CommRingCat.ofHom φ) ≫ eA.hom ≫
        strictHenselizationStructuralMap (ν ≫ ι ≫ σ) =
      eB.hom ≫ strictHenselizationStructuralMap (ν ≫ τ) ≫ g)
    (hρA : ρA ≫ Spec.map (CommRingCat.ofHom (IsLocalRing.residue A)) ≫
      eA.hom ≫ strictHenselizationStructuralMap (ν ≫ ι ≫ σ) = σ)
    (hρB : ρB ≫ Spec.map (CommRingCat.ofHom (IsLocalRing.residue B)) ≫
      eB.hom ≫ strictHenselizationStructuralMap (ν ≫ τ) = τ)
    (hρ : ρB ≫ Spec.map (CommRingCat.ofHom (IsLocalRing.ResidueField.map φ)) = ι ≫ ρA)
    (F : Sheaf (ProjectiveLine S).smallEtaleTopology (ModuleCat.{u + 1} Λ))
    [IsTorsionModuleSheaf F] (q : ℕ) :
    let F₀ := (ProjectiveSpace.map _
      (eA.hom ≫ strictHenselizationStructuralMap (ν ≫ ι ≫ σ)))^*[
      ModuleCat.{u + 1} Λ].obj F
    let G₀ := (sheafCompose _
      (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj F₀
    let g₀ := Spec.map (CommRingCat.ofHom φ)
    ∃ (c₁ : ((pointSmallEtale τ).sheafFiber (A := ModuleCat.{u + 1} Λ)).obj
          ((Etale.baseChangeSourceFunctor Λ g (ProjectiveLine S ↘ S) q).obj F) ≃+
        Sheaf.H G₀ q)
      (c₂ : ((pointSmallEtale τ).sheafFiber (A := ModuleCat.{u + 1} Λ)).obj
          ((Etale.baseChangeTargetFunctor Λ g' f' q).obj F) ≃+
        Sheaf.H ((ProjectiveSpace.map _ g₀)^*[AddCommGrpCat.{u + 1}].obj G₀) q),
      ∀ x, c₂ ((((pointSmallEtale τ).sheafFiber
          (A := ModuleCat.{u + 1} Λ)).map
          (Etale.baseChangeHomologyMap Λ sq q F)).hom x) =
        Etale.cohomologyMap (ProjectiveSpace.map _ g₀) G₀ q (c₁ x)
```

## New

```lean
theorem Etale.projectiveLine_strictLocal_stalkExchangeComparison_smallModel
    (Λ : Type (u + 1)) [CommRing Λ]
    {S T X' : Scheme.{u}} {g : T ⟶ S} {f' : X' ⟶ T} {g' : X' ⟶ ProjectiveLine S}
    (sq : IsPullback g' f' (ProjectiveLine S ↘ S) g)
    {k k' Ω : Type u} [Field k] [IsSepClosed k] [Field k'] [IsSepClosed k']
    [Field Ω] [IsAlgClosed Ω]
    (σ : Spec (.of k) ⟶ S) (τ : Spec (.of k') ⟶ T)
    (ι : Spec (.of k') ⟶ Spec (.of k)) (hι : ι ≫ σ = τ ≫ g)
    (ν : Spec (.of Ω) ⟶ Spec (.of k'))
    {A B : Type u} [CommRing A] [HenselianLocalRing A]
    [CommRing B] [HenselianLocalRing B]
    [IsSepClosed (IsLocalRing.ResidueField A)] [IsSepClosed (IsLocalRing.ResidueField B)]
    (eA : Spec (.of A) ≅ strictHenselizationScheme (ν ≫ ι ≫ σ))
    (eB : Spec (.of B) ≅ strictHenselizationScheme (ν ≫ τ))
    (φ : A →+* B) [IsLocalHom φ]
    (ρA : Spec (.of k) ⟶ Spec (.of (IsLocalRing.ResidueField A)))
    (ρB : Spec (.of k') ⟶ Spec (.of (IsLocalRing.ResidueField B)))
    (hφ : Spec.map (CommRingCat.ofHom φ) ≫ eA.hom ≫
        strictHenselizationStructuralMap (ν ≫ ι ≫ σ) =
      eB.hom ≫ strictHenselizationStructuralMap (ν ≫ τ) ≫ g)
    (hρA : ρA ≫ Spec.map (CommRingCat.ofHom (IsLocalRing.residue A)) ≫
      eA.hom ≫ strictHenselizationStructuralMap (ν ≫ ι ≫ σ) = σ)
    (hρB : ρB ≫ Spec.map (CommRingCat.ofHom (IsLocalRing.residue B)) ≫
      eB.hom ≫ strictHenselizationStructuralMap (ν ≫ τ) = τ)
    (hρ : ρB ≫ Spec.map (CommRingCat.ofHom (IsLocalRing.ResidueField.map φ)) = ι ≫ ρA)
    (F : Sheaf (ProjectiveLine S).smallEtaleTopology (ModuleCat.{u + 1} Λ))
    [IsTorsionModuleSheaf F] (q : ℕ) :
    let F₀ := (ProjectiveSpace.map _
      (eA.hom ≫ strictHenselizationStructuralMap (ν ≫ ι ≫ σ)))^*[
      ModuleCat.{u + 1} Λ].obj F
    let t₀ := pointSmallEtale (Spec.map (CommRingCat.ofHom (IsLocalRing.residue B)))
    let g₀ := Spec.map (CommRingCat.ofHom φ)
    ∃ (a₁ : ((pointSmallEtale τ).sheafFiber (A := ModuleCat.{u + 1} Λ)).obj
                  ((Etale.baseChangeSourceFunctor Λ g (ProjectiveLine S ↘ S) q).obj F) ≃+
                (t₀.sheafFiber (A := ModuleCat.{u + 1} Λ)).obj
                  ((Etale.baseChangeSourceFunctor Λ g₀
                    (ProjectiveLine (Spec (.of A)) ↘ Spec (.of A)) q).obj F₀))
                (a₂ : ((pointSmallEtale τ).sheafFiber (A := ModuleCat.{u + 1} Λ)).obj
                  ((Etale.baseChangeTargetFunctor Λ g' f' q).obj F) ≃+
                (t₀.sheafFiber (A := ModuleCat.{u + 1} Λ)).obj
                  ((Etale.baseChangeTargetFunctor Λ (ProjectiveSpace.map _ g₀)
                    (ProjectiveLine (Spec (.of B)) ↘ Spec (.of B)) q).obj F₀)),
                (∀ x, a₂ ((((pointSmallEtale τ).sheafFiber
                    (A := ModuleCat.{u + 1} Λ)).map
                    (Etale.baseChangeHomologyMap Λ sq q F)).hom x) =
                  ((t₀.sheafFiber (A := ModuleCat.{u + 1} Λ)).map
                    (Etale.baseChangeHomologyMap Λ
                      (ProjectiveSpace.isPullback_map _ g₀) q F₀)).hom (a₁ x))

theorem Etale.projectiveLine_originalStalk_totalCohomologyExchange_smallModel
    (Λ : Type (u + 1)) [CommRing Λ]
    {S T X' : Scheme.{u}} {g : T ⟶ S} {f' : X' ⟶ T} {g' : X' ⟶ ProjectiveLine S}
    (sq : IsPullback g' f' (ProjectiveLine S ↘ S) g)
    {k k' Ω : Type u} [Field k] [IsSepClosed k] [Field k'] [IsSepClosed k']
    [Field Ω] [IsAlgClosed Ω]
    (σ : Spec (.of k) ⟶ S) (τ : Spec (.of k') ⟶ T)
    (ι : Spec (.of k') ⟶ Spec (.of k)) (hι : ι ≫ σ = τ ≫ g)
    (ν : Spec (.of Ω) ⟶ Spec (.of k'))
    {A B : Type u} [CommRing A] [HenselianLocalRing A]
    [CommRing B] [HenselianLocalRing B]
    [IsSepClosed (IsLocalRing.ResidueField A)] [IsSepClosed (IsLocalRing.ResidueField B)]
    (eA : Spec (.of A) ≅ strictHenselizationScheme (ν ≫ ι ≫ σ))
    (eB : Spec (.of B) ≅ strictHenselizationScheme (ν ≫ τ))
    (φ : A →+* B) [IsLocalHom φ]
    (ρA : Spec (.of k) ⟶ Spec (.of (IsLocalRing.ResidueField A)))
    (ρB : Spec (.of k') ⟶ Spec (.of (IsLocalRing.ResidueField B)))
    (hφ : Spec.map (CommRingCat.ofHom φ) ≫ eA.hom ≫
        strictHenselizationStructuralMap (ν ≫ ι ≫ σ) =
      eB.hom ≫ strictHenselizationStructuralMap (ν ≫ τ) ≫ g)
    (hρA : ρA ≫ Spec.map (CommRingCat.ofHom (IsLocalRing.residue A)) ≫
      eA.hom ≫ strictHenselizationStructuralMap (ν ≫ ι ≫ σ) = σ)
    (hρB : ρB ≫ Spec.map (CommRingCat.ofHom (IsLocalRing.residue B)) ≫
      eB.hom ≫ strictHenselizationStructuralMap (ν ≫ τ) = τ)
    (hρ : ρB ≫ Spec.map (CommRingCat.ofHom (IsLocalRing.ResidueField.map φ)) = ι ≫ ρA)
    (F : Sheaf (ProjectiveLine S).smallEtaleTopology (ModuleCat.{u + 1} Λ))
    [IsTorsionModuleSheaf F] (q : ℕ) :
    let F₀ := (ProjectiveSpace.map _
      (eA.hom ≫ strictHenselizationStructuralMap (ν ≫ ι ≫ σ)))^*[
      ModuleCat.{u + 1} Λ].obj F
    let G₀ := (sheafCompose _
      (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj F₀
    let g₀ := Spec.map (CommRingCat.ofHom φ)
    ∃ (c₁ : ((pointSmallEtale τ).sheafFiber (A := ModuleCat.{u + 1} Λ)).obj
          ((Etale.baseChangeSourceFunctor Λ g (ProjectiveLine S ↘ S) q).obj F) ≃+
        Sheaf.H G₀ q)
      (c₂ : ((pointSmallEtale τ).sheafFiber (A := ModuleCat.{u + 1} Λ)).obj
          ((Etale.baseChangeTargetFunctor Λ g' f' q).obj F) ≃+
        Sheaf.H ((ProjectiveSpace.map _ g₀)^*[AddCommGrpCat.{u + 1}].obj G₀) q),
      ∀ x, c₂ ((((pointSmallEtale τ).sheafFiber
          (A := ModuleCat.{u + 1} Λ)).map
          (Etale.baseChangeHomologyMap Λ sq q F)).hom x) =
        Etale.cohomologyMap (ProjectiveSpace.map _ g₀) G₀ q (c₁ x)
```

The sole caller changes from
Etale.projectiveLine_originalStalk_totalCohomologyExchange to
Etale.projectiveLine_originalStalk_totalCohomologyExchange_smallModel.

## Users

Source-only downstream.py --uses --allow-missing reports zero downstream modules of
the item, and one downstream module of its dependency: the item itself. Its declaration
use lists contain only the defining modules and that same caller. A separate search of
lean and quarantine finds only the historical archived item as an additional importer
of the dependency; the quarantine archives remain untouched. No public import changes.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.ProjectiveLineStrictLocalStalkExchangeComparison | A3 | Rename the small-model declaration and its dependency application; preserve the full mathematical type and proof. |
| Sheaf.AlgebraicGeometry.ProjectiveLineOriginalStalkTotalCohomologyExchange | unclaimed | Rename the small-model declaration only; preserve the complete proof and type. |

## Status

landed 20261022T032511-L-2032677 2026-10-22 (merge of deliver/A3/Sheaf.AlgebraicGeometry.ProjectiveLineStrictLocalStalkExchangeComparison)
