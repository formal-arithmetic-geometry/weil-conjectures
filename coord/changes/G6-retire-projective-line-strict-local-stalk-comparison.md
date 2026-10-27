# AlgebraicGeometry.Etale.projectiveLine_strictLocal_stalkExchangeComparison_smallModel

## Reason

Complete the explicit retirement assignment in coord/retire-items.tsv. The current
Sheaf module has zero holes, and its former parent already imports and applies the
adopted canonical-model comparison. Retain the mathematical DAG node on that existing
source declaration, preserving the parent dependency and every realized unit step.
The module is present in lean; this is not deletion of an absent quarantine path.

## Old

Withdrawn small-model wrapper signature, verbatim:

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
```

## New

Existing adopted source declaration, unchanged:

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
    (eA : Spec (.of A) ≅ strictLocalization (ν ≫ ι ≫ σ))
    (eB : Spec (.of B) ≅ strictLocalization (ν ≫ τ))
    (φ : A →+* B) [IsLocalHom φ]
    (ρA : Spec (.of k) ⟶ Spec (.of (IsLocalRing.ResidueField A)))
    (ρB : Spec (.of k') ⟶ Spec (.of (IsLocalRing.ResidueField B)))
    (hφ : Spec.map (CommRingCat.ofHom φ) ≫ eA.hom ≫
        strictLocalizationToBase (ν ≫ ι ≫ σ) =
      eB.hom ≫ strictLocalizationToBase (ν ≫ τ) ≫ g)
    (hρA : ρA ≫ Spec.map (CommRingCat.ofHom (IsLocalRing.residue A)) ≫
      eA.hom ≫ strictLocalizationToBase (ν ≫ ι ≫ σ) = σ)
    (hρB : ρB ≫ Spec.map (CommRingCat.ofHom (IsLocalRing.residue B)) ≫
      eB.hom ≫ strictLocalizationToBase (ν ≫ τ) = τ)
    (hρ : ρB ≫ Spec.map (CommRingCat.ofHom (IsLocalRing.ResidueField.map φ)) = ι ≫ ρA)
    (F : Sheaf (ProjectiveLine S).smallEtaleTopology (ModuleCat.{u + 1} Λ))
    [IsTorsionModuleSheaf F] (q : ℕ) :
    let F₀ := (ProjectiveSpace.map _
      (eA.hom ≫ strictLocalizationToBase (ν ≫ ι ≫ σ)))^*[
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
```

The only difference in geometric inputs is the strict-henselization presentation.
Compose eA and eB with Spec of the inverse smallStrictHenselizationColimitIso.
The proved smallStrictHenselizationColimitIso_toBase identities transport hphi,
hrhoA and hrhoB by associativity, while hrho is unchanged. Apply the adopted
comparison, reduce its let bindings, and rewrite the source structural-map identity.
This gives exactly the old small-model conclusion. A sandbox adapter performing
this transport compiled through lcompile.py on the server in 21.2 seconds, exit 0.
It is not retained as a new wrapper. Withdraw the item with deleted.txt instead.

The sole actual DAG parent is lem-weil-pbc-p1-strict-local-model-comparison.
Its current Lean implementation already imports the adopted module, receives
canonical presentations from projectiveLine_compatibleStrictHenselizationResidues,
and applies projectiveLine_strictLocal_stalkExchangeComparison directly. No parent
adaptation is needed. Provenance-only blueprint.from mentions are retained.
No public import, signature, attribute, definition, or proof in WeilConjectures changes.

## Users

Source-only downstream.py reports zero importers and no uses beyond the wrapper's
own declaration. A full textual search of lean/Sheaf, lean/WeilConjectures and
quarantine finds no importer or user of the smallModel name. All current rework
archives were included. The retirement table's former Sheaf model-comparison
consumer is absent; its adopted source implementation already uses the replacement.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.ProjectiveLineStrictLocalStalkExchangeComparison | G6 | Withdraw the redundant wrapper with zero holes. |
| WeilConjectures.AlgebraicGeometry.ProjectiveLineStrictLocalStalkExchangeComparison | unclaimed; untouched | Existing replacement declaration and full proof retained verbatim. |
| WeilConjectures.AlgebraicGeometry.ProjectiveLineStrictLocalModelComparison | unclaimed; untouched | Sole mathematical parent already calls the adopted comparison with canonical inputs. |

The node's lean attachment, proof, proof_deps and proof_origin now describe the
adopted implementation. Its statement, stmt_deps, parent dependencies, and the
sk-thm-p1 unit realization remain unchanged. The structural small/full comparison
node is no longer a direct dependency of this node, since the adopted inputs are
canonical; its statement and other consumers are retained.

## Status

landed 20261025T123010-L-1823089 2026-10-25 (merge of deliver/G6/Sheaf.AlgebraicGeometry.ProjectiveLineStrictLocalStalkExchangeComparison)
