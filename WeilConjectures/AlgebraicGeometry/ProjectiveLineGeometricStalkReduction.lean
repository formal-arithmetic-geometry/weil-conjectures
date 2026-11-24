/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine.StrictHenselian
public import WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Defs
import WeilConjectures.AlgebraicGeometry.ProjectiveLineStrictLocalModelComparison

/-!
# Reduction of the geometric-stalk exchange to the strict-local exchange

## References

* Stacks Project, Tag 095T (proof of Theorem 59.91.11).
-/

@[expose] public section

universe u
set_option autoImplicit false
set_option linter.style.haveILetI false

open CategoryTheory Limits

namespace AlgebraicGeometry

open Scheme Etale

/-- It suffices to identify the exchange for local maps of strictly henselian local rings.
The premise is precisely the existing strict-local exchange statement, for every pair
of strictly henselian bases and every degree. The conclusion applies it to the strict
henselizations of the two arbitrary bases (Stacks, Tag 095T). -/
theorem Etale.geometricStalk_projectiveLine_of_strictLocal
    (Λ : Type (u + 1)) [CommRing Λ]
    (hLocal : ∀ (A B : Type u) [CommRing A] [HenselianLocalRing A]
      [IsSepClosed (IsLocalRing.ResidueField A)] [CommRing B] [HenselianLocalRing B]
      [IsSepClosed (IsLocalRing.ResidueField B)] (φ : A →+* B) [IsLocalHom φ]
      (F : Sheaf (ProjectiveLine (Spec (.of A))).smallEtaleTopology
        (ModuleCat.{u + 1} Λ)) [IsTorsionModuleSheaf F] (q : ℕ),
      ∃ (e₁ : ((pointSmallEtale (Spec.map (CommRingCat.ofHom (IsLocalRing.residue B)))).sheafFiber
          (A := ModuleCat.{u + 1} Λ)).obj
          ((Etale.baseChangeSourceFunctor Λ (Spec.map (CommRingCat.ofHom φ))
            (ProjectiveLine (Spec (.of A)) ↘ Spec (.of A)) q).obj F) ≃+
        Sheaf.H ((sheafCompose _ (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj
          ((ProjectiveSpace.map _ (Spec.map (CommRingCat.ofHom
            (IsLocalRing.residue A))))^*[ModuleCat.{u + 1} Λ].obj F)) q)
      (e₂ : ((pointSmallEtale (Spec.map (CommRingCat.ofHom (IsLocalRing.residue B)))).sheafFiber
          (A := ModuleCat.{u + 1} Λ)).obj
          ((Etale.baseChangeTargetFunctor Λ (ProjectiveSpace.map _ (Spec.map (CommRingCat.ofHom φ)))
            (ProjectiveLine (Spec (.of B)) ↘ Spec (.of B)) q).obj F) ≃+
        Sheaf.H ((ProjectiveSpace.map _ (Spec.map (CommRingCat.ofHom
            (IsLocalRing.ResidueField.map φ))))^*[AddCommGrpCat.{u + 1}].obj
          ((sheafCompose _ (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj
            ((ProjectiveSpace.map _ (Spec.map (CommRingCat.ofHom
              (IsLocalRing.residue A))))^*[ModuleCat.{u + 1} Λ].obj F))) q),
      ∀ x, e₂ ((((pointSmallEtale (Spec.map (CommRingCat.ofHom (IsLocalRing.residue B)))).sheafFiber
          (A := ModuleCat.{u + 1} Λ)).map (Etale.baseChangeHomologyMap Λ
            (ProjectiveSpace.isPullback_map _ (Spec.map (CommRingCat.ofHom φ))) q F)).hom x) =
        Etale.cohomologyMap (ProjectiveSpace.map _ (Spec.map (CommRingCat.ofHom
            (IsLocalRing.ResidueField.map φ))))
          ((sheafCompose _ (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj
            ((ProjectiveSpace.map _ (Spec.map (CommRingCat.ofHom
              (IsLocalRing.residue A))))^*[ModuleCat.{u + 1} Λ].obj F)) q (e₁ x))
    {S T X' : Scheme.{u}} {g : T ⟶ S} {f' : X' ⟶ T} {g' : X' ⟶ ProjectiveLine S}
    (sq : IsPullback g' f' (ProjectiveLine S ↘ S) g)
    {k k' : Type u} [Field k] [IsSepClosed k] [Field k'] [IsSepClosed k']
    (σ : Spec (.of k) ⟶ S) (τ : Spec (.of k') ⟶ T) (ι : Spec (.of k') ⟶ Spec (.of k))
    (hι : ι ≫ σ = τ ≫ g)
    (hσ : ∃ (s : S) (φ : S.residueField s ⟶ .of k),
      φ.hom.IsIntegral ∧ Spec.map φ ≫ S.fromSpecResidueField s = σ)
    (hτ : ∃ (t : T) (φ : T.residueField t ⟶ .of k'),
      φ.hom.IsIntegral ∧ Spec.map φ ≫ T.fromSpecResidueField t = τ)
    (F : Sheaf (ProjectiveLine S).smallEtaleTopology (ModuleCat.{u + 1} Λ))
    [IsTorsionModuleSheaf F] (q : ℕ) :
    ∃ (e₁ : ((pointSmallEtale τ).sheafFiber (A := ModuleCat.{u + 1} Λ)).obj
          ((Etale.baseChangeSourceFunctor Λ g (ProjectiveLine S ↘ S) q).obj F) ≃+
        Sheaf.H ((sheafCompose _ (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj
          ((ProjectiveSpace.map _ σ)^*[ModuleCat.{u + 1} Λ].obj F)) q)
      (e₂ : ((pointSmallEtale τ).sheafFiber (A := ModuleCat.{u + 1} Λ)).obj
          ((Etale.baseChangeTargetFunctor Λ g' f' q).obj F) ≃+
        Sheaf.H ((ProjectiveSpace.map _ ι)^*[AddCommGrpCat.{u + 1}].obj
          ((sheafCompose _ (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj
            ((ProjectiveSpace.map _ σ)^*[ModuleCat.{u + 1} Λ].obj F))) q),
      ∀ x, e₂ ((((pointSmallEtale τ).sheafFiber (A := ModuleCat.{u + 1} Λ)).map
          (Etale.baseChangeHomologyMap Λ sq q F)).hom x) =
        Etale.cohomologyMap (ProjectiveSpace.map _ ι)
          ((sheafCompose _ (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj
            ((ProjectiveSpace.map _ σ)^*[ModuleCat.{u + 1} Λ].obj F)) q (e₁ x) := by
  obtain ⟨A, B, cA, cB, hmodel⟩ :=
    Etale.projectiveLine_strictLocal_modelComparison Λ sq σ τ ι hι hσ hτ F q
  letI := cA
  letI := cB
  obtain ⟨hA, hB, hmodel⟩ := hmodel
  letI := hA
  letI := hB
  obtain ⟨sA, sB, hmodel⟩ := hmodel
  letI := sA
  letI := sB
  obtain ⟨φ, hφ, hmodel⟩ := hmodel
  letI := hφ
  obtain ⟨F₀, hF₀, a₁, a₂, b₁, b₂, ha, hb⟩ := hmodel
  letI := hF₀
  obtain ⟨e₁, e₂, he⟩ := hLocal A B φ F₀ q
  refine ⟨(a₁.trans e₁).trans b₁, (a₂.trans e₂).trans b₂, ?_⟩
  intro x
  change b₂ (e₂ (a₂ _)) = _
  rw [ha, he, hb]
  rfl

end AlgebraicGeometry
