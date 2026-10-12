# AlgebraicGeometry.Etale.projectiveLine_strictLocal_modelComparison

## Reason

Add independent geometric and stalk interfaces for the strict-local model reduction, and a proved residue-cohomology interface. Existing signatures and public imports are unchanged; all new imports in the assigned module are proof-only. No target meaning is changed.

## Old

The three auxiliary declarations did not exist. The existing theorem had the same signature and a whole-proof sorry.

## New

Three new declarations, one per new module:

```lean
theorem Etale.projectiveLine_compatibleStrictHenselizationResidues {S T : Scheme.{u}} {g : T ⟶ S} {k k' Ω : Type u} [Field k] [IsSepClosed k] [Field k'] [IsSepClosed k'] [Field Ω] [IsAlgClosed Ω] (σ : Spec (.of k) ⟶ S) (τ : Spec (.of k') ⟶ T) (ι : Spec (.of k') ⟶ Spec (.of k)) (hι : ι ≫ σ = τ ≫ g) (hσ : ∃ (s : S) (ψ : S.residueField s ⟶ .of k), ψ.hom.IsIntegral ∧ Spec.map ψ ≫ S.fromSpecResidueField s = σ) (hτ : ∃ (t : T) (ψ : T.residueField t ⟶ .of k'), ψ.hom.IsIntegral ∧ Spec.map ψ ≫ T.fromSpecResidueField t = τ) (ν : Spec (.of Ω) ⟶ Spec (.of k')) : let s := ν ≫ ι ≫ σ let t := ν ≫ τ ∃ (A B : Type u) (cA : CommRing A) (cB : CommRing B), letI := cA letI := cB ∃ (hA : HenselianLocalRing A) (hB : HenselianLocalRing B), letI := hA letI := hB ∃ (sA : IsSepClosed (IsLocalRing.ResidueField A)) (sB : IsSepClosed (IsLocalRing.ResidueField B)), letI := sA letI := sB ∃ (φ : A →+* B) (hφ : IsLocalHom φ), letI := hφ ∃ (eA : Spec (.of A) ≅ strictHenselizationScheme s) (eB : Spec (.of B) ≅ strictHenselizationScheme t) (ρA : Spec (.of k) ⟶ Spec (.of (IsLocalRing.ResidueField A))) (ρB : Spec (.of k') ⟶ Spec (.of (IsLocalRing.ResidueField B))), IsUniversalHomeomorphism ρA ∧ IsUniversalHomeomorphism ρB ∧ Spec.map (CommRingCat.ofHom φ) ≫ eA.hom ≫ strictHenselizationStructuralMap s = eB.hom ≫ strictHenselizationStructuralMap t ≫ g ∧ ρA ≫ Spec.map (CommRingCat.ofHom (IsLocalRing.residue A)) ≫ eA.hom ≫ strictHenselizationStructuralMap s = σ ∧ ρB ≫ Spec.map (CommRingCat.ofHom (IsLocalRing.residue B)) ≫ eB.hom ≫ strictHenselizationStructuralMap t = τ ∧ ρB ≫ Spec.map (CommRingCat.ofHom (IsLocalRing.ResidueField.map φ)) = ι ≫ ρA
```

```lean
theorem Etale.projectiveLine_strictLocal_stalkExchangeComparison (Λ : Type (u + 1)) [CommRing Λ] {S T X' : Scheme.{u}} {g : T ⟶ S} {f' : X' ⟶ T} {g' : X' ⟶ ProjectiveLine S} (sq : IsPullback g' f' (ProjectiveLine S ↘ S) g) {k k' Ω : Type u} [Field k] [IsSepClosed k] [Field k'] [IsSepClosed k'] [Field Ω] [IsAlgClosed Ω] (σ : Spec (.of k) ⟶ S) (τ : Spec (.of k') ⟶ T) (ι : Spec (.of k') ⟶ Spec (.of k)) (hι : ι ≫ σ = τ ≫ g) (ν : Spec (.of Ω) ⟶ Spec (.of k')) {A B : Type u} [CommRing A] [HenselianLocalRing A] [CommRing B] [HenselianLocalRing B] [IsSepClosed (IsLocalRing.ResidueField A)] [IsSepClosed (IsLocalRing.ResidueField B)] (eA : Spec (.of A) ≅ strictHenselizationScheme (ν ≫ ι ≫ σ)) (eB : Spec (.of B) ≅ strictHenselizationScheme (ν ≫ τ)) (φ : A →+* B) [IsLocalHom φ] (ρA : Spec (.of k) ⟶ Spec (.of (IsLocalRing.ResidueField A))) (ρB : Spec (.of k') ⟶ Spec (.of (IsLocalRing.ResidueField B))) (hφ : Spec.map (CommRingCat.ofHom φ) ≫ eA.hom ≫ strictHenselizationStructuralMap (ν ≫ ι ≫ σ) = eB.hom ≫ strictHenselizationStructuralMap (ν ≫ τ) ≫ g) (hρA : ρA ≫ Spec.map (CommRingCat.ofHom (IsLocalRing.residue A)) ≫ eA.hom ≫ strictHenselizationStructuralMap (ν ≫ ι ≫ σ) = σ) (hρB : ρB ≫ Spec.map (CommRingCat.ofHom (IsLocalRing.residue B)) ≫ eB.hom ≫ strictHenselizationStructuralMap (ν ≫ τ) = τ) (hρ : ρB ≫ Spec.map (CommRingCat.ofHom (IsLocalRing.ResidueField.map φ)) = ι ≫ ρA) (F : Sheaf (ProjectiveLine S).smallEtaleTopology (ModuleCat.{u + 1} Λ)) [IsTorsionSheaf F] (q : ℕ) : let F₀ := (ProjectiveSpace.map _ (eA.hom ≫ strictHenselizationStructuralMap (ν ≫ ι ≫ σ)))^*[ ModuleCat.{u + 1} Λ].obj F let t₀ := pointSmallEtale (Spec.map (CommRingCat.ofHom (IsLocalRing.residue B))) let g₀ := Spec.map (CommRingCat.ofHom φ) ∃ (a₁ : ((pointSmallEtale τ).sheafFiber (A := ModuleCat.{u + 1} Λ)).obj ((Etale.baseChangeSourceFunctor Λ g (ProjectiveLine S ↘ S) q).obj F) ≃+ (t₀.sheafFiber (A := ModuleCat.{u + 1} Λ)).obj ((Etale.baseChangeSourceFunctor Λ g₀ (ProjectiveLine (Spec (.of A)) ↘ Spec (.of A)) q).obj F₀)) (a₂ : ((pointSmallEtale τ).sheafFiber (A := ModuleCat.{u + 1} Λ)).obj ((Etale.baseChangeTargetFunctor Λ g' f' q).obj F) ≃+ (t₀.sheafFiber (A := ModuleCat.{u + 1} Λ)).obj ((Etale.baseChangeTargetFunctor Λ (ProjectiveSpace.map _ g₀) (ProjectiveLine (Spec (.of B)) ↘ Spec (.of B)) q).obj F₀)), (∀ x, a₂ ((((pointSmallEtale τ).sheafFiber (A := ModuleCat.{u + 1} Λ)).map (Etale.baseChangeHomologyMap Λ sq q F)).hom x) = ((t₀.sheafFiber (A := ModuleCat.{u + 1} Λ)).map (Etale.baseChangeHomologyMap Λ (ProjectiveSpace.isPullback_map _ g₀) q F₀)).hom (a₁ x))
```

```lean
theorem Etale.projectiveLine_residueCohomologyComparison (Λ : Type (u + 1)) [CommRing Λ] {S : Scheme.{u}} {A B : Type u} [CommRing A] [IsLocalRing A] [CommRing B] [IsLocalRing B] {k k' : Type u} [Field k] [Field k'] (jA : Spec (.of A) ⟶ S) (φ : A →+* B) [IsLocalHom φ] (σ : Spec (.of k) ⟶ S) (ι : Spec (.of k') ⟶ Spec (.of k)) (ρA : Spec (.of k) ⟶ Spec (.of (IsLocalRing.ResidueField A))) (ρB : Spec (.of k') ⟶ Spec (.of (IsLocalRing.ResidueField B))) [IsUniversalHomeomorphism ρA] [IsUniversalHomeomorphism ρB] (hρA : ρA ≫ Spec.map (CommRingCat.ofHom (IsLocalRing.residue A)) ≫ jA = σ) (hρ : ρB ≫ Spec.map (CommRingCat.ofHom (IsLocalRing.ResidueField.map φ)) = ι ≫ ρA) (F : Sheaf (ProjectiveLine S).smallEtaleTopology (ModuleCat.{u + 1} Λ)) (q : ℕ) : let F₀ := (ProjectiveSpace.map _ jA)^*[ModuleCat.{u + 1} Λ].obj F let rA := Spec.map (CommRingCat.ofHom (IsLocalRing.residue A)) let i₀ := Spec.map (CommRingCat.ofHom (IsLocalRing.ResidueField.map φ)) let G₀ := (sheafCompose _ (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj ((ProjectiveSpace.map _ rA)^*[ModuleCat.{u + 1} Λ].obj F₀) let G := (sheafCompose _ (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj ((ProjectiveSpace.map _ σ)^*[ModuleCat.{u + 1} Λ].obj F) ∃ (b₁ : Sheaf.H G₀ q ≃+ Sheaf.H G q) (b₂ : Sheaf.H ((ProjectiveSpace.map _ i₀)^*[AddCommGrpCat.{u + 1}].obj G₀) q ≃+ Sheaf.H ((ProjectiveSpace.map _ ι)^*[AddCommGrpCat.{u + 1}].obj G) q), (∀ y, b₂ (Etale.cohomologyMap (ProjectiveSpace.map _ i₀) G₀ q y) = Etale.cohomologyMap (ProjectiveSpace.map _ ι) G q (b₁ y))
```

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.ProjectiveLineStrictLocalModelComparison | Q1 | Uses all three new theorems in its proof; existing signature unchanged. |
| Sheaf.AlgebraicGeometry.ProjectiveLineGeometricStalkReduction | none | Existing caller of the assigned theorem; unchanged signature and no adaptation. |

No pre-existing module uses the new declarations. No existing definition or statement changes.

## Status

landed 20261012T042416-L-1819410 2026-10-12 (merge of deliver/Q1/Sheaf.AlgebraicGeometry.ProjectiveLineStrictLocalModelComparison)
