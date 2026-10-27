# AlgebraicGeometry.Etale.projectiveLine_originalStalk_totalCohomologyExchange_smallModel

## Reason

Complete the explicit retirement assignment in coord/retire-items.tsv. The item has
zero holes. Its small-colimit presentation theorem repeats the adopted canonical
strictLocalization theorem, with an explicit isomorphism transport. Move that
transport to its only consumer and withdraw the wrapper. No definition or target
statement changes, and no source-library declaration, signature, attribute, public
import or proof is edited.

The retirement row is reconciled with the current sources: the wrapper was restored
by D2, renamed by A3, and its abelian-wrapper application was already migrated by M9.
This packet starts from that current proof, not from a quarantine archive.

## Old

Withdrawn wrapper signature, verbatim:

```lean
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

The only direct consumer privately imports the Sheaf wrapper and applies its
smallModel theorem to the original small-colimit presentations.

## New

The existing adopted theorem, left entirely unchanged, has this signature:

```lean
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

Remove the wrapper with deleted.txt. The sole consumer privately imports the adopted
module and Sheaf.AlgebraicGeometry.StrictHenselizationClosedFiberComparison.
Construct eA′ and eB′ by composing the original presentations with Spec of the inverse
smallStrictHenselizationColimitIso. Prove hA,hB using
smallStrictHenselizationColimitIso_toBase. Rewrite the structural and residue equations
with these identities, apply the adopted theorem, reduce its let-bindings and rewrite
hA in the result. This recovers exactly the old two cohomology groups and equation.
The consumer's existing composition with inverse strict-local equivalences is retained.
Its entire theorem signature and all public imports remain byte-identical.
Only the structural identity is used from the comparison module; its closed-fibre
consequence is never applied.

Reattach lem-weil-pbc-p1-original-stalk-total-cohomology-exchange to the adopted theorem
with its verbatim Lean signature and its actual unchanged proof dependencies. Its
abstract mathematical statement remains unchanged. Record the presentation transport
in the parent node's proof and proof dependencies. No DAG node or unit route is deleted.

## Users

Repository searches for the module and smallModel declaration, and tools/downstream.py
with --uses, find exactly this caller. The only DAG parent is
lem-weil-pbc-p1-strict-local-stalk-exchange-comparison, updated in this delivery.
The unit sk-thm-p1 does not realize this adapter as a separate statement or step;
all its realized statements and steps remain intact. The canonical theorem preserves
the original total-space cohomology argument and its dependencies.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.ProjectiveLineOriginalStalkTotalCohomologyExchange | Z9 | Withdraw duplicate small-model wrapper; reattach its node to adopted theorem. |
| Sheaf.AlgebraicGeometry.ProjectiveLineStrictLocalStalkExchangeComparison | unclaimed | Migrate private import and inline the presentation transport; exact public statement preserved. |
| WeilConjectures.AlgebraicGeometry.ProjectiveLineOriginalStalkTotalCohomologyExchange | unclaimed; untouched | Adopted replacement theorem and full proof are preserved verbatim. |

The migrated consumer proof compiled alone through lcompile.py in 43.6 seconds
with exit code 0. Textual comparison verifies the exact original consumer signature
and public imports, zero holes, and lines at most 100 characters.

## Status

landed 20261025T102125-L-3779258 2026-10-25 (merge of deliver/Z9/Sheaf.AlgebraicGeometry.ProjectiveLineOriginalStalkTotalCohomologyExchange)
