/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.PoincareDuality.Biduality.Constructible
public import WeilConjectures.CategoryTheory.Monoidal.Closed.DualFullyFaithful

/-!
# The Verdier dual is fully faithful on bounded constructible complexes

By constructible Verdier biduality (`ProEtale.CondensedRing.isIso_verdierBiduality`), the Verdier
dual `𝔻_X = RHom(-, ω_X)` is fully faithful on `Dᵇc(X)⟦ℚ̲̄_ℓ⟧`: for bounded constructible `T` and
`A`, the map `f ↦ 𝔻_X f` from `T ⟶ A` to `𝔻_X A ⟶ 𝔻_X T` is bijective
(`ProEtale.CondensedRing.bijective_derivedHom_map_dualizingComplex`). It is stated for the
morphisms of the ambient derived category and the derived hom `RHom(X)⟦ℚ̲̄_ℓ⟧`.
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory MonoidalClosed Opposite

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

attribute [local instance] boundedConstructibleBraiding

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)]

variable {X : Over (Spec (.of k))} [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
  [IsSeparated X.hom]

/-- **The Verdier dual is fully faithful on bounded constructible complexes**: for bounded
constructible `T` and `A`, `f ↦ RHom(f, ω_X)` is a bijection from `T ⟶ A` to
`RHom(A, ω_X) ⟶ RHom(T, ω_X)`. -/
theorem bijective_derivedHom_map_dualizingComplex
    (T A : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    Function.Bijective (fun f : T.obj ⟶ A.obj ↦
      ((derivedHom (Profinite.padicAlgClRingObj ℓ) X.left).map f.op).app
        ((ObjectProperty.ι _).obj (dualizingComplex ℓ X))) := by
  have : IsIso (toIhomIhom (dualizingComplex ℓ X) A) := by
    have h := isIso_verdierBiduality ℓ A
    rwa [verdierBiduality, Verdier.bidualityMap_eq_toIhomIhom] at h
  have e : (fun f : T.obj ⟶ A.obj ↦
      ((derivedHom (Profinite.padicAlgClRingObj ℓ) X.left).map f.op).app
        ((ObjectProperty.ι _).obj (dualizingComplex ℓ X))) =
      (fun g ↦ (ObjectProperty.ι _).map g) ∘
        (fun f : T ⟶ A ↦ (pre f).app (dualizingComplex ℓ X)) ∘
        (ObjectProperty.fullyFaithfulι _).homEquiv.symm := by
    ext f
    rfl
  rw [e]
  exact ((ObjectProperty.fullyFaithfulι _).map_bijective _ _).comp
    ((bijective_pre_app_of_isIso (dualizingComplex ℓ X) T A).comp
      (ObjectProperty.fullyFaithfulι _).homEquiv.symm.bijective)

end AlgebraicGeometry.ProEtale.CondensedRing
