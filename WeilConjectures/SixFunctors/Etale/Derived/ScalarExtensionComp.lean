/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.DerivedBaseChange
public import WeilConjectures.CategoryTheory.DerivedCategory.RationalizationMapComp
public import WeilConjectures.SixFunctors.Etale.Derived.ScalarExtension
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.RestrictScalars

/-!
# Composition of scalar extensions

Let `E ⊆ L ⊆ M` be finite extensions of `ℚ_ℓ` inside `ℚ̄_ℓ`, and let `Y` be a scheme. The scalar
extensions `- ⊗_E L : D_comp(Y_ét, E) ⥤ D_comp(Y_ét, L)` of blueprint
`def-weil-rationalization-karoubi`
(`AlgebraicGeometry.Etale.derivedCompleteRationalScalarExtension`)
are compatible with the composition of finite extensions and with the identity extension
(blueprint `lem-weil-scalar-extension-composition`):

```
  (K ⊗_E L) ⊗_L M ≅ K ⊗_E M,     K ⊗_E E ≅ K,
```

naturally in `K`.

As in the blueprint, the comparison is first constructed on the integral representatives: the
derived base changes `- ⊗ᴸ_{𝒪_E} 𝒪_L` are left adjoint to the restrictions of scalars, and
restriction of scalars along `𝒪_E ⟶ 𝒪_L ⟶ 𝒪_M` is restriction of scalars along `𝒪_E ⟶ 𝒪_M`
(`CategoryTheory.Sheaf.derivedRestrictScalarsCompIso`), so the uniqueness of left adjoints gives
the associativity isomorphism
`(K ⊗ᴸ_{𝒪_E} 𝒪_L) ⊗ᴸ_{𝒪_L} 𝒪_M ≅ K ⊗ᴸ_{𝒪_E} 𝒪_M`
(`AlgebraicGeometry.Etale.derivedBaseChangeCompIso`). It descends to the rationalizations
(`CategoryTheory.Rationalization.mapOfRingHomCompIso`).

## Main definitions

- `AlgebraicGeometry.Etale.derivedCompleteRationalScalarExtensionCompIso`: the isomorphism
  `(- ⊗_E L) ⊗_L M ≅ - ⊗_E M` (`lem-weil-scalar-extension-composition`).
- `AlgebraicGeometry.Etale.derivedCompleteRationalScalarExtensionIdIso`: the isomorphism
  `- ⊗_E E ≅ 𝟭` (`lem-weil-scalar-extension-composition`, compatibility with the identity).
-/

@[expose] public section

universe w u

open CategoryTheory Limits

attribute [local instance] AlgebraicGeometry.Scheme.Etale.essentiallySmall

namespace PadicAlgCl

variable (l : ℕ) [Fact l.Prime] (E L M : Type w) [Field E] [Field L] [Field M]
  [Algebra E (PadicAlgCl l)] [Algebra L (PadicAlgCl l)] [Algebra M (PadicAlgCl l)]
  [Algebra E L] [Algebra L M] [Algebra E M] [IsScalarTower E L (PadicAlgCl l)]
  [IsScalarTower L M (PadicAlgCl l)] [IsScalarTower E M (PadicAlgCl l)]

/-- The inclusions of rings of integers compose: `𝒪_E ⟶ 𝒪_L ⟶ 𝒪_M` is `𝒪_E ⟶ 𝒪_M`. -/
lemma integersMap_comp :
    (integersMap l L M).comp (integersMap l E L) = integersMap l E M := by
  ext x
  apply (algebraMap M (PadicAlgCl l)).injective
  change algebraMap M (PadicAlgCl l) (algebraMap L M (algebraMap E L x)) =
    algebraMap M (PadicAlgCl l) (algebraMap E M x)
  rw [← IsScalarTower.algebraMap_apply L M (PadicAlgCl l),
    ← IsScalarTower.algebraMap_apply E L (PadicAlgCl l),
    ← IsScalarTower.algebraMap_apply E M (PadicAlgCl l)]

/-- The inclusion of the ring of integers of `E` into itself is the identity. -/
lemma integersMap_self : integersMap l E E = RingHom.id _ := by
  ext x
  rfl

variable [Small.{u + 1} E] [Small.{u + 1} L] [Small.{u + 1} M]

/-- The inclusions `Shrink 𝒪_E ⟶ Shrink 𝒪_L ⟶ Shrink 𝒪_M` compose to `Shrink 𝒪_E ⟶ Shrink 𝒪_M`. -/
lemma integersShrinkMap_comp :
    integersShrinkMap.{w, u} l E M =
      (integersShrinkMap.{w, u} l L M).comp (integersShrinkMap.{w, u} l E L) := by
  ext x
  simp [integersShrinkMap, ← integersMap_comp l E L M]

lemma integersShrinkMap_self : integersShrinkMap.{w, u} l E E = RingHom.id _ := by
  ext x
  simp [integersShrinkMap, integersMap_self]

end PadicAlgCl

namespace CategoryTheory.Sheaf

variable {C : Type*} [Category C] (J : GrothendieckTopology C) {R : Type w} [CommRing R]
  (f : R →+* R) (hf : f = RingHom.id R)

/-- Restriction of scalars of sheaves of modules along the identity is the identity, computed
objectwise by `ModuleCat.restrictScalarsId'`. -/
noncomputable def restrictScalarsIdIso : restrictScalars J f ≅ 𝟭 _ :=
  NatIso.ofComponents
    (fun F ↦ (fullyFaithfulSheafToPresheaf J _).preimageIso
      (Functor.isoWhiskerLeft F.obj (ModuleCat.restrictScalarsId' f hf) ≪≫ F.obj.rightUnitor))
    (fun {F G} φ ↦ (fullyFaithfulSheafToPresheaf J _).map_injective (by
      ext U : 2
      exact (ModuleCat.restrictScalarsId' f hf).hom.naturality (φ.hom.app U)))

end CategoryTheory.Sheaf

namespace CategoryTheory.Sheaf

section Assoc

variable {C : Type (u + 1)} [Category.{u} C] [EssentiallySmall.{u + 1} C]
  (J : GrothendieckTopology C)
  {A₀ A₁ A₂ A₃ : Type (u + 1)} [CommRing A₀] [CommRing A₁] [CommRing A₂] [CommRing A₃]
  {f₁ : A₀ →+* A₁} {f₂ : A₁ →+* A₂} {f₃ : A₂ →+* A₃} {f₁₂ : A₀ →+* A₂} {f₂₃ : A₁ →+* A₃}
  {f₁₂₃ : A₀ →+* A₃} (h₁₂ : f₁₂ = f₂.comp f₁) (h₂₃ : f₂₃ = f₃.comp f₂)
  (h₁₃ : f₁₂₃ = f₂₃.comp f₁) (h₀₃ : f₁₂₃ = f₃.comp f₁₂)

/-- The composition isomorphisms of the restrictions of scalars of sheaves of modules satisfy
the associativity (cocycle) condition. -/
lemma restrictScalarsCompIso_assoc :
    Functor.isoWhiskerLeft (restrictScalars J f₃) (restrictScalarsCompIso J f₁ f₂ f₁₂ h₁₂) ≪≫
        restrictScalarsCompIso J f₁₂ f₃ f₁₂₃ h₀₃ =
      (Functor.associator _ _ _).symm ≪≫
        Functor.isoWhiskerRight (restrictScalarsCompIso J f₂ f₃ f₂₃ h₂₃) (restrictScalars J f₁) ≪≫
          restrictScalarsCompIso J f₁ f₂₃ f₁₂₃ h₁₃ := by
  ext F : 2
  apply (fullyFaithfulSheafToPresheaf J _).map_injective
  ext U x
  rfl

/-- The composition isomorphisms of the derived restrictions of scalars satisfy the
associativity (cocycle) condition. -/
lemma derivedRestrictScalarsCompIso_assoc :
    Functor.isoWhiskerLeft (derivedRestrictScalars J f₃) (derivedRestrictScalarsCompIso J h₁₂) ≪≫
        derivedRestrictScalarsCompIso J h₀₃ =
      (Functor.associator _ _ _).symm ≪≫
        Functor.isoWhiskerRight (derivedRestrictScalarsCompIso J h₂₃)
          (derivedRestrictScalars J f₁) ≪≫ derivedRestrictScalarsCompIso J h₁₃ := by
  have e₄ : Functor.isoWhiskerLeft (restrictScalars J f₃)
        (restrictScalarsCompIso J f₁ f₂ f₁₂ h₁₂) ≪≫ restrictScalarsCompIso J f₁₂ f₃ f₁₂₃ h₀₃ =
      Functor.isoWhiskerRight (restrictScalarsCompIso J f₂ f₃ f₂₃ h₂₃) (restrictScalars J f₁) ≪≫
        restrictScalarsCompIso J f₁ f₂₃ f₁₂₃ h₁₃ := by
    ext F : 2
    apply (fullyFaithfulSheafToPresheaf J _).map_injective
    ext U x
    rfl
  ext K
  have e₁ := NatTrans.congr_app (Functor.mapDerivedCategoryNatIso_isoWhiskerLeft
    (restrictScalars J f₃) (restrictScalarsCompIso J f₁ f₂ f₁₂ h₁₂)) K
  have e₂ := NatTrans.congr_app (Functor.mapDerivedCategoryNatIso_isoWhiskerRight
    (restrictScalarsCompIso J f₂ f₃ f₂₃ h₂₃) (restrictScalars J f₁)) K
  have e₃ := NatTrans.congr_app (Functor.mapDerivedCategoryCompIso_assoc (restrictScalars J f₃)
    (restrictScalars J f₂) (restrictScalars J f₁)) K
  have e₅ := NatTrans.congr_app (congrArg Iso.hom (congrArg Functor.mapDerivedCategoryNatIso e₄)) K
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app] at e₁ e₂ e₃
  rw [Functor.mapDerivedCategoryNatIso_trans, Functor.mapDerivedCategoryNatIso_trans,
    NatTrans.comp_app, NatTrans.comp_app] at e₅
  simp only [derivedRestrictScalarsCompIso, Iso.trans_hom, Iso.symm_hom,
    Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom, NatTrans.comp_app,
    Functor.whiskerLeft_app, Functor.whiskerRight_app, Functor.associator_inv_app,
    Functor.map_comp, Category.assoc, Category.id_comp]
  rw [← cancel_epi ((Functor.mapDerivedCategoryCompIso (restrictScalars J f₂)
      (restrictScalars J f₁)).hom.app ((restrictScalars J f₃).mapDerivedCategory.obj K)),
    ← cancel_epi ((Functor.mapDerivedCategoryCompIso (restrictScalars J f₃)
      (restrictScalars J f₂ ⋙ restrictScalars J f₁)).hom.app K)]
  simp only [Iso.hom_inv_id_app_assoc]
  rw [← reassoc_of% e₁, Iso.hom_inv_id_app_assoc, reassoc_of% e₃]
  erw [Category.id_comp]
  rw [← Functor.map_comp_assoc, Iso.hom_inv_id_app, Functor.map_id, Category.id_comp,
    ← reassoc_of% e₂, Iso.hom_inv_id_app_assoc]
  exact e₅

end Assoc

end CategoryTheory.Sheaf

namespace AlgebraicGeometry

open Scheme

namespace Etale

set_option hygiene false in
/-- The derived category `D(X_ét, Λ)` of étale sheaves of `Λ`-modules on `X`. -/
local notation "𝐃(" X ", " Λ ")" =>
  _root_.DerivedCategory (Sheaf (Scheme.smallEtaleTopology X) (ModuleCat.{u + 1} Λ))

section Integral

variable {Λ Λ' Λ'' : Type (u + 1)} [CommRing Λ] [CommRing Λ'] [CommRing Λ''] (X : Scheme.{u})

/-- Restriction of scalars along the identity is the identity. -/
noncomputable def derivedRestrictScalarsIdIso (φ : Λ →+* Λ) (hφ : φ = RingHom.id Λ) :
    derivedRestrictScalars φ X ≅ 𝟭 _ :=
  Functor.mapDerivedCategoryNatIso (Sheaf.restrictScalarsIdIso X.smallEtaleTopology φ hφ) ≪≫
    Functor.mapDerivedCategoryIdIso _

variable (φ₁ : Λ →+* Λ') (φ₂ : Λ' →+* Λ'') (φ : Λ →+* Λ'')
  (h₁ : ∀ K : 𝐃(X, Λ), ∃ (K' : 𝐃(X, Λ')) (η : K ⟶ (derivedRestrictScalars φ₁ X).obj K'),
    IsDerivedBaseChange η)
  (h₂ : ∀ K : 𝐃(X, Λ'), ∃ (K' : 𝐃(X, Λ'')) (η : K ⟶ (derivedRestrictScalars φ₂ X).obj K'),
    IsDerivedBaseChange η)
  (h : ∀ K : 𝐃(X, Λ), ∃ (K' : 𝐃(X, Λ'')) (η : K ⟶ (derivedRestrictScalars φ X).obj K'),
    IsDerivedBaseChange η)

/-- Derived base changes compose: `(K ⊗ᴸ_Λ Λ') ⊗ᴸ_{Λ'} Λ'' ≅ K ⊗ᴸ_Λ Λ''` for `φ = φ₂ ∘ φ₁`, by
uniqueness of the left adjoints of the restrictions of scalars. -/
noncomputable def derivedBaseChangeCompIso (hφ : φ = φ₂.comp φ₁) :
    derivedBaseChange φ₁ X h₁ ⋙ derivedBaseChange φ₂ X h₂ ≅ derivedBaseChange φ X h :=
  Adjunction.leftAdjointCompIso (derivedBaseChangeAdjunction φ₁ X h₁)
    (derivedBaseChangeAdjunction φ₂ X h₂) (derivedBaseChangeAdjunction φ X h)
    (Sheaf.derivedRestrictScalarsCompIso X.smallEtaleTopology hφ)

/-- Derived base change along the identity is the identity. -/
noncomputable def derivedBaseChangeIdIso (ψ : Λ →+* Λ) (hψ : ψ = RingHom.id Λ)
    (h₀ : ∀ K : 𝐃(X, Λ), ∃ (K' : 𝐃(X, Λ)) (η : K ⟶ (derivedRestrictScalars ψ X).obj K'),
      IsDerivedBaseChange η) :
    derivedBaseChange ψ X h₀ ≅ 𝟭 _ :=
  ((derivedBaseChangeAdjunction ψ X h₀).ofNatIsoRight
    (derivedRestrictScalarsIdIso X ψ hψ)).leftAdjointUniq Adjunction.id

section Assoc

variable {Λ₀ Λ₁ Λ₂ Λ₃ : Type (u + 1)} [CommRing Λ₀] [CommRing Λ₁] [CommRing Λ₂] [CommRing Λ₃]
  {ρ₁ : Λ₀ →+* Λ₁} {ρ₂ : Λ₁ →+* Λ₂} {ρ₃ : Λ₂ →+* Λ₃} {ρ₁₂ : Λ₀ →+* Λ₂} {ρ₂₃ : Λ₁ →+* Λ₃}
  {ρ₁₂₃ : Λ₀ →+* Λ₃}
  (k₁ : ∀ K : 𝐃(X, Λ₀), ∃ (K' : 𝐃(X, Λ₁)) (η : K ⟶ (derivedRestrictScalars ρ₁ X).obj K'),
    IsDerivedBaseChange η)
  (k₂ : ∀ K : 𝐃(X, Λ₁), ∃ (K' : 𝐃(X, Λ₂)) (η : K ⟶ (derivedRestrictScalars ρ₂ X).obj K'),
    IsDerivedBaseChange η)
  (k₃ : ∀ K : 𝐃(X, Λ₂), ∃ (K' : 𝐃(X, Λ₃)) (η : K ⟶ (derivedRestrictScalars ρ₃ X).obj K'),
    IsDerivedBaseChange η)
  (k₁₂ : ∀ K : 𝐃(X, Λ₀), ∃ (K' : 𝐃(X, Λ₂)) (η : K ⟶ (derivedRestrictScalars ρ₁₂ X).obj K'),
    IsDerivedBaseChange η)
  (k₂₃ : ∀ K : 𝐃(X, Λ₁), ∃ (K' : 𝐃(X, Λ₃)) (η : K ⟶ (derivedRestrictScalars ρ₂₃ X).obj K'),
    IsDerivedBaseChange η)
  (k₁₂₃ : ∀ K : 𝐃(X, Λ₀), ∃ (K' : 𝐃(X, Λ₃)) (η : K ⟶ (derivedRestrictScalars ρ₁₂₃ X).obj K'),
    IsDerivedBaseChange η)
  (hρ₁₂ : ρ₁₂ = ρ₂.comp ρ₁) (hρ₂₃ : ρ₂₃ = ρ₃.comp ρ₂) (hρ₁₃ : ρ₁₂₃ = ρ₂₃.comp ρ₁)
  (hρ₀₃ : ρ₁₂₃ = ρ₃.comp ρ₁₂)

/-- The composition isomorphisms of the derived base changes satisfy the associativity
(cocycle) condition: the two identifications of `((K ⊗ᴸ Λ₁) ⊗ᴸ Λ₂) ⊗ᴸ Λ₃` with `K ⊗ᴸ Λ₃`
agree. -/
lemma derivedBaseChangeCompIso_assoc :
    Functor.isoWhiskerLeft (derivedBaseChange ρ₁ X k₁)
        (derivedBaseChangeCompIso X ρ₂ ρ₃ ρ₂₃ k₂ k₃ k₂₃ hρ₂₃) ≪≫
      derivedBaseChangeCompIso X ρ₁ ρ₂₃ ρ₁₂₃ k₁ k₂₃ k₁₂₃ hρ₁₃ =
    (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (derivedBaseChangeCompIso X ρ₁ ρ₂ ρ₁₂ k₁ k₂ k₁₂ hρ₁₂)
        (derivedBaseChange ρ₃ X k₃) ≪≫
      derivedBaseChangeCompIso X ρ₁₂ ρ₃ ρ₁₂₃ k₁₂ k₃ k₁₂₃ hρ₀₃ :=
  Adjunction.leftAdjointCompIso_assoc _ _ _ _ _ _ _ _ _ _
    (Sheaf.derivedRestrictScalarsCompIso_assoc _ hρ₁₂ hρ₂₃ hρ₁₃ hρ₀₃)

end Assoc

end Integral

section Rational

variable (l : ℕ) [Fact l.Prime] (E L M : Type w) [Field E] [Field L] [Field M]
  [Algebra E (PadicAlgCl l)] [Algebra L (PadicAlgCl l)] [Algebra M (PadicAlgCl l)]
  [Algebra E L] [Algebra L M] [Algebra E M] [IsScalarTower E L (PadicAlgCl l)]
  [IsScalarTower L M (PadicAlgCl l)] [IsScalarTower E M (PadicAlgCl l)]
  [Algebra ℚ_[l] E] [IsScalarTower ℚ_[l] E (PadicAlgCl l)] [FiniteDimensional ℚ_[l] E]
  [Algebra ℚ_[l] L] [IsScalarTower ℚ_[l] L (PadicAlgCl l)] [FiniteDimensional ℚ_[l] L]
  [Algebra ℚ_[l] M] [IsScalarTower ℚ_[l] M (PadicAlgCl l)] [FiniteDimensional ℚ_[l] M]
  [Small.{u + 1} E] [Small.{u + 1} L] [Small.{u + 1} M] (Y : Scheme.{u})

/-- The inclusion `D_comp(Y_ét, 𝒪_E) ⥤ D(Y_ét, 𝒪_E)` is fully faithful. -/
noncomputable def fullyFaithfulDerivedCompleteIntegralι (E : Type w) [Field E]
    [Algebra E (PadicAlgCl l)] [Small.{u + 1} E] :
    (DerivedCategoryDerivedCompleteIntegral.ι Y.smallEtaleTopology l E).FullyFaithful :=
  ObjectProperty.fullyFaithfulι _

set_option maxHeartbeats 1600000 in
-- the naturality check unfolds the derived base change functors
/-- The composite of the integral scalar extensions `D_comp(Y_ét, 𝒪_E) ⥤ D_comp(Y_ét, 𝒪_L) ⥤
D_comp(Y_ét, 𝒪_M)` is the integral scalar extension `D_comp(Y_ét, 𝒪_E) ⥤ D_comp(Y_ét, 𝒪_M)`. -/
noncomputable def derivedCompleteIntegralScalarExtensionCompIso :
    derivedCompleteIntegralScalarExtension (Y := Y) l E L ⋙
        derivedCompleteIntegralScalarExtension l L M ≅
      derivedCompleteIntegralScalarExtension l E M :=
  let e := derivedBaseChangeCompIso Y _ _ _ exists_isDerivedBaseChange_integersShrinkMap
    exists_isDerivedBaseChange_integersShrinkMap exists_isDerivedBaseChange_integersShrinkMap
    (PadicAlgCl.integersShrinkMap_comp l E L M)
  NatIso.ofComponents
    (fun K ↦ (fullyFaithfulDerivedCompleteIntegralι l Y M).preimageIso
      (e.app ((DerivedCategoryDerivedCompleteIntegral.ι _ l E).obj K)))
    (fun f ↦ (fullyFaithfulDerivedCompleteIntegralι l Y M).map_injective (by
      simp only [Functor.map_comp, Functor.FullyFaithful.preimageIso_hom,
        Functor.FullyFaithful.map_preimage]
      exact e.hom.naturality ((DerivedCategoryDerivedCompleteIntegral.ι _ l E).map f)))

/-- The integral scalar extension along `𝒪_E ⟶ 𝒪_E` is the identity. -/
noncomputable def derivedCompleteIntegralScalarExtensionIdIso :
    derivedCompleteIntegralScalarExtension (Y := Y) l E E ≅ 𝟭 _ :=
  have := (fullyFaithfulDerivedCompleteIntegralι l Y E).full
  have := (fullyFaithfulDerivedCompleteIntegralι l Y E).faithful
  Functor.fullyFaithfulCancelRight
    (DerivedCategoryDerivedCompleteIntegral.ι Y.smallEtaleTopology l E)
    (Functor.isoWhiskerLeft (DerivedCategoryDerivedCompleteIntegral.ι Y.smallEtaleTopology l E)
      (derivedBaseChangeIdIso Y _ (PadicAlgCl.integersShrinkMap_self l E)
        exists_isDerivedBaseChange_integersShrinkMap))

/-- Blueprint `lem-weil-scalar-extension-composition`: Composition of scalar extensions.

For finite extensions `E ⊆ L ⊆ M` of `ℚ_ℓ` inside `ℚ̄_ℓ` and a scheme `Y`, there is a canonical
isomorphism `(K ⊗_E L) ⊗_L M ≅ K ⊗_E M` in `D_comp(Y_ét, M)`, natural in `K ∈ D_comp(Y_ét, E)`:
the scalar extension functors of `def-weil-rationalization-karoubi` compose. It is induced on the
rationalizations by the associativity isomorphism
`(K ⊗ᴸ_{𝒪_E} 𝒪_L) ⊗ᴸ_{𝒪_L} 𝒪_M ≅ K ⊗ᴸ_{𝒪_E} 𝒪_M` of the integral derived base changes. -/
noncomputable def derivedCompleteRationalScalarExtensionCompIso :
    derivedCompleteRationalScalarExtension (Y := Y) l E L ⋙
        derivedCompleteRationalScalarExtension l L M ≅
      derivedCompleteRationalScalarExtension l E M :=
  Rationalization.mapOfRingHomCompIso _ _ _ _ _ _ _ _ _ _ _ _
    (derivedCompleteIntegralScalarExtensionCompIso l E L M Y)

/-- Blueprint `lem-weil-scalar-extension-composition` (compatibility with the identity
extension): the scalar extension `- ⊗_E E : D_comp(Y_ét, E) ⥤ D_comp(Y_ét, E)` is isomorphic to
the identity. -/
noncomputable def derivedCompleteRationalScalarExtensionIdIso :
    derivedCompleteRationalScalarExtension (Y := Y) l E E ≅ 𝟭 _ :=
  Rationalization.mapOfRingHomIdIso _ _ _ _ (derivedCompleteIntegralScalarExtensionIdIso l E Y)

/-- The composition isomorphism `(K ⊗_E L) ⊗_L M ≅ K ⊗_E M` on the rationalization of an
integral object `K` is the rationalization of the integral associativity isomorphism, read
through the identifications `derivedCompleteRationalScalarExtensionFromIntegralIso`. -/
lemma derivedCompleteRationalScalarExtensionCompIso_hom_app_fromIntegral
    (K : DerivedCategoryDerivedCompleteIntegral Y.smallEtaleTopology l E) :
    (derivedCompleteRationalScalarExtensionCompIso l E L M Y).hom.app
        ((DerivedCategoryDerivedCompleteRational.fromIntegral _ l E).obj K) =
      (derivedCompleteRationalScalarExtension l L M).map
          (derivedCompleteRationalScalarExtensionFromIntegralIso l E L K).hom ≫
        (derivedCompleteRationalScalarExtensionFromIntegralIso l L M _).hom ≫
        (DerivedCategoryDerivedCompleteRational.fromIntegral _ l M).map
          ((derivedCompleteIntegralScalarExtensionCompIso l E L M Y).hom.app K) ≫
        (derivedCompleteRationalScalarExtensionFromIntegralIso l E M K).inv := by
  rw [derivedCompleteRationalScalarExtensionCompIso, Rationalization.mapOfRingHomCompIso_hom_app]
  simp [Rationalization.mapOfRingHomCompFac, derivedCompleteRationalScalarExtensionFromIntegralIso]

end Rational

end Etale

end AlgebraicGeometry
