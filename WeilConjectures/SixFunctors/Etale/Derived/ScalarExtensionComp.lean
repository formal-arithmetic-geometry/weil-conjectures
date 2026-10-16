/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.DerivedBaseChange
public import WeilConjectures.CategoryTheory.DerivedCategory.RationalizationMapComp
public import WeilConjectures.SixFunctors.Etale.Derived.ScalarExtension

/-!
# Composition of scalar extensions

Let `E ⊆ L ⊆ M` be finite extensions of `ℚ_ℓ` inside `ℚ̄_ℓ`, and let `Y` be a scheme. The scalar
extensions `- ⊗_E L : D_comp(Y_ét, E) ⥤ D_comp(Y_ét, L)` of blueprint
`def-weil-rationalization-karoubi` (`AlgebraicGeometry.Etale.derivedCompleteRationalScalarExtension`)
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
  (((derivedBaseChangeAdjunction φ₁ X h₁).comp (derivedBaseChangeAdjunction φ₂ X h₂)).ofNatIsoRight
    (Sheaf.derivedRestrictScalarsCompIso X.smallEtaleTopology hφ)).leftAdjointUniq
      (derivedBaseChangeAdjunction φ X h)

/-- Derived base change along the identity is the identity. -/
noncomputable def derivedBaseChangeIdIso (ψ : Λ →+* Λ) (hψ : ψ = RingHom.id Λ)
    (h₀ : ∀ K : 𝐃(X, Λ), ∃ (K' : 𝐃(X, Λ)) (η : K ⟶ (derivedRestrictScalars ψ X).obj K'),
      IsDerivedBaseChange η) :
    derivedBaseChange ψ X h₀ ≅ 𝟭 _ :=
  ((derivedBaseChangeAdjunction ψ X h₀).ofNatIsoRight
    (derivedRestrictScalarsIdIso X ψ hψ)).leftAdjointUniq Adjunction.id

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

/-- The composite of the integral scalar extensions `D_comp(Y_ét, 𝒪_E) ⥤ D_comp(Y_ét, 𝒪_L) ⥤
D_comp(Y_ét, 𝒪_M)` is the integral scalar extension `D_comp(Y_ét, 𝒪_E) ⥤ D_comp(Y_ét, 𝒪_M)`. -/
noncomputable def derivedCompleteIntegralScalarExtensionCompIso :
    derivedCompleteIntegralScalarExtension (Y := Y) l E L ⋙
        derivedCompleteIntegralScalarExtension l L M ≅
      derivedCompleteIntegralScalarExtension l E M :=
  Functor.fullyFaithfulCancelRight
    (_root_.DerivedCategory.derivedCompleteIntegral Y.smallEtaleTopology l M).ι
    (Functor.isoWhiskerLeft
      (_root_.DerivedCategory.derivedCompleteIntegral Y.smallEtaleTopology l E).ι
      (derivedBaseChangeCompIso Y _ _ _ _ _ _ (PadicAlgCl.integersShrinkMap_comp l E L M)))

/-- The integral scalar extension along `𝒪_E ⟶ 𝒪_E` is the identity. -/
noncomputable def derivedCompleteIntegralScalarExtensionIdIso :
    derivedCompleteIntegralScalarExtension (Y := Y) l E E ≅ 𝟭 _ :=
  Functor.fullyFaithfulCancelRight
    (_root_.DerivedCategory.derivedCompleteIntegral Y.smallEtaleTopology l E).ι
    (Functor.isoWhiskerLeft
      (_root_.DerivedCategory.derivedCompleteIntegral Y.smallEtaleTopology l E).ι
      (derivedBaseChangeIdIso Y _ (PadicAlgCl.integersShrinkMap_self l E) _))

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
