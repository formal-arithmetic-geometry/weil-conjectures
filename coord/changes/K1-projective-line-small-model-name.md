# AlgebraicGeometry.Etale.projectiveLine_abelian_originalStalk_totalExchange_smallModel

## Reason

The restored small-colimit-model theorem and the adopted canonical-model theorem
have the same fully qualified declaration name but different input types. Rename
only the Sheaf declaration with the suffix `_smallModel`. All binders, instances,
hypotheses, universes and the conclusion remain verbatim. Preserve the complete
small/full-model transport and the existing localization/strict-local proof.
No source-library declaration, public import or proof is edited.

D2 has now restored the sole small-model caller on current sheaf-dag. Change only
its proof application to the new name; its statement, visibility, imports and
remaining proof stay byte-identical to the current source. Both DAG attachments
remain on the small-model modules. No node is withdrawn and no unit route is bypassed.

Repair of return C-72890 (head 72890e8e148): retain this change record as the delivery
file `coord/changes/K1-projective-line-small-model-name.md`. The former landing
passed only the basename to `--apply-fixes`, which was not a delivery path. The
worker changes no landing tools; deliver3.py rebuilds this packet on current sheaf-dag.

## Old

```lean
theorem Etale.projectiveLine_abelian_originalStalk_totalExchange
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
    (G : Sheaf (ProjectiveLine S).smallEtaleTopology AddCommGrpCat.{u + 1}) (q : ℕ) :
    let G₀ := (ProjectiveSpace.map _
      (eA.hom ≫ strictHenselizationStructuralMap (ν ≫ ι ≫ σ)))^*[
      AddCommGrpCat.{u + 1}].obj G
    let g₀ := Spec.map (CommRingCat.ofHom φ)
    let K := (DerivedCategory.Plus.singleFunctor _ 0).obj G
    let C₁ := (DerivedCategory.Plus.homologyFunctor _ (q : ℤ)).obj
      ((R+((ProjectiveLine S ↘ S)_*[AddCommGrpCat.{u + 1}]) ⋙
        D+((g)^*[AddCommGrpCat.{u + 1}])).obj K)
    let C₂ := (DerivedCategory.Plus.homologyFunctor _ (q : ℤ)).obj
      ((D+((g')^*[AddCommGrpCat.{u + 1}]) ⋙
        R+((f')_*[AddCommGrpCat.{u + 1}])).obj K)
    let e := (DerivedCategory.Plus.homologyFunctor _ (q : ℤ)).map
      ((Etale.derivedBaseChangeMapPlus AddCommGrpCat.{u + 1} sq.toCommSq).app K)
    ∃ (a₁ : ((pointSmallEtale τ).sheafFiber
          (A := AddCommGrpCat.{u + 1})).obj C₁ ≃+ Sheaf.H G₀ q)
      (a₂ : ((pointSmallEtale τ).sheafFiber
          (A := AddCommGrpCat.{u + 1})).obj C₂ ≃+
        Sheaf.H ((ProjectiveSpace.map _ g₀)^*[AddCommGrpCat.{u + 1}].obj G₀) q),
      ∀ x, a₂ ((((pointSmallEtale τ).sheafFiber
          (A := AddCommGrpCat.{u + 1})).map e).hom x) =
        Etale.cohomologyMap (ProjectiveSpace.map _ g₀) G₀ q (a₁ x)
```

The caller's old proof application is:

```lean
  obtain ⟨a₁, a₂, ha⟩ := Etale.projectiveLine_abelian_originalStalk_totalExchange
    sq σ τ ι hι ν eA eB φ ρA ρB hφ hρA hρB hρ G q
```

## New

```lean
theorem Etale.projectiveLine_abelian_originalStalk_totalExchange_smallModel
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
    (G : Sheaf (ProjectiveLine S).smallEtaleTopology AddCommGrpCat.{u + 1}) (q : ℕ) :
    let G₀ := (ProjectiveSpace.map _
      (eA.hom ≫ strictHenselizationStructuralMap (ν ≫ ι ≫ σ)))^*[
      AddCommGrpCat.{u + 1}].obj G
    let g₀ := Spec.map (CommRingCat.ofHom φ)
    let K := (DerivedCategory.Plus.singleFunctor _ 0).obj G
    let C₁ := (DerivedCategory.Plus.homologyFunctor _ (q : ℤ)).obj
      ((R+((ProjectiveLine S ↘ S)_*[AddCommGrpCat.{u + 1}]) ⋙
        D+((g)^*[AddCommGrpCat.{u + 1}])).obj K)
    let C₂ := (DerivedCategory.Plus.homologyFunctor _ (q : ℤ)).obj
      ((D+((g')^*[AddCommGrpCat.{u + 1}]) ⋙
        R+((f')_*[AddCommGrpCat.{u + 1}])).obj K)
    let e := (DerivedCategory.Plus.homologyFunctor _ (q : ℤ)).map
      ((Etale.derivedBaseChangeMapPlus AddCommGrpCat.{u + 1} sq.toCommSq).app K)
    ∃ (a₁ : ((pointSmallEtale τ).sheafFiber
          (A := AddCommGrpCat.{u + 1})).obj C₁ ≃+ Sheaf.H G₀ q)
      (a₂ : ((pointSmallEtale τ).sheafFiber
          (A := AddCommGrpCat.{u + 1})).obj C₂ ≃+
        Sheaf.H ((ProjectiveSpace.map _ g₀)^*[AddCommGrpCat.{u + 1}].obj G₀) q),
      ∀ x, a₂ ((((pointSmallEtale τ).sheafFiber
          (A := AddCommGrpCat.{u + 1})).map e).hom x) =
        Etale.cohomologyMap (ProjectiveSpace.map _ g₀) G₀ q (a₁ x)
```

The caller's corresponding application is now:

```lean
  obtain ⟨a₁, a₂, ha⟩ := Etale.projectiveLine_abelian_originalStalk_totalExchange_smallModel
    sq σ τ ι hι ν eA eB φ ρA ρB hφ hρA hρB hρ G q
```

## Users

Current sheaf-dag contains D2’s restored caller and its corrected structural-map
import. The caller is held by D2, so its only adaptation is the forced theorem
application rename at line 112. The declaration’s full signature stays identical.
The adopted counterpart continues to use its canonical theorem, unchanged.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.ProjectiveLineAbelianOriginalStalkTotalExchange | K1 | Rename its small-model theorem only; preserve its full type and proof. |
| Sheaf.AlgebraicGeometry.ProjectiveLineOriginalStalkTotalCohomologyExchange | D2 | Change only the forced theorem application at line 112; preserve all signatures and imports. |
| Sheaf.AlgebraicGeometry.ProjectiveLineStrictLocalStalkExchangeComparison | unclaimed, quarantined rework | Preserved caller interface; no adaptation required. |
| WeilConjectures.AlgebraicGeometry.ProjectiveLineOriginalStalkTotalCohomologyExchange | source library, unchanged | Continues to use the canonical theorem with canonical-model inputs. |

## Status

landed 20261022T022044-L-433026 2026-10-22 (merge of deliver/K1/Sheaf.AlgebraicGeometry.ProjectiveLineAbelianOriginalStalkTotalExchange)
