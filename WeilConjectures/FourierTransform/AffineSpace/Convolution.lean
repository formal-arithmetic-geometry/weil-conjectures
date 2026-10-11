/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import WeilConjectures.AlgebraicGeometry.AffineSpace.Subtraction
public import WeilConjectures.FourierTransform.AffineSpace.Unit

/-!
# Convolution of Fourier kernels

-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

open AlgebraicGeometry.AffineSpace

section ArtinSchreier

variable (Λ : Type (u + 1)) [CommRing Λ] {p : ℕ} [Fact p.Prime] [Invertible (p : Λ)]

/-- An Artin–Schreier sheaf is flat, having a tensor inverse. -/
lemma flat_artinSchreierSheafZMod (X : Scheme.{u}) [CharP Γ(X, ⊤) p] (Ψ : AddChar (ZMod p) Λ)
    (f : Γ(X, ⊤)) : ObjectProperty.flat (artinSchreierSheafZMod X Ψ f) := by
  let := X.overSpecZModOfCharP p
  obtain ⟨e⟩ := nonempty_iso_artinSchreierSheafOf_neg X
    (Ψ.compAddMonoidHom AddEquiv.ulift.toAddMonoidHom) f
  exact ObjectProperty.flat_of_tensorIso e

/-- The derived tensor product of two Artin–Schreier sheaves of the same character, placed in
degree zero, is the Artin–Schreier sheaf of the sum: `ℒ_{ψ(f)} ⊗ᴸ ℒ_{ψ(g)} ≅ ℒ_{ψ(f + g)}`. -/
lemma nonempty_iso_singleFunctor_artinSchreierSheafZMod_tensor (X : Scheme.{u})
    [CharP Γ(X, ⊤) p] (Ψ : AddChar (ZMod p) Λ) (f g : Γ(X, ⊤)) :
    Nonempty ((DerivedCategory.singleFunctor _ 0).obj (artinSchreierSheafZMod X Ψ f) ⊗
        (DerivedCategory.singleFunctor _ 0).obj (artinSchreierSheafZMod X Ψ g) ≅
      (DerivedCategory.singleFunctor (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) 0).obj
        (artinSchreierSheafZMod X Ψ (f + g))) := by
  let := X.overSpecZModOfCharP p
  obtain ⟨e⟩ := nonempty_iso_artinSchreierSheafOf_add X
    (Ψ.compAddMonoidHom AddEquiv.ulift.toAddMonoidHom) f g
  exact ⟨singleFunctorObjTensorIso _ _ (flat_artinSchreierSheafZMod Λ X Ψ f) ≪≫
    (DerivedCategory.singleFunctor _ 0).mapIso e⟩

/-- The integrand of a convolution of two Artin–Schreier kernels. For morphisms
`g₁ g₂ g₃ : X ⟶ Y`, a function `b` on `Y`, and an identification `ℒ_{ψ'(g₂^* b)} ≅ ℒ_{ψ(c)}`
with `g₁^* b + c = g₃^* b`, one has `g₁^* ℒ_{ψ(b)} ⊗ᴸ g₂^* ℒ_{ψ'(b)} ≅ g₃^* ℒ_{ψ(b)}`. -/
lemma nonempty_iso_derivedTensorRight_artinSchreierSheafZMod {X Y : Scheme.{u}}
    [CharP Γ(X, ⊤) p] [CharP Γ(Y, ⊤) p] (g₁ g₂ g₃ : X ⟶ Y) (Ψ Ψ' : AddChar (ZMod p) Λ)
    (b : Γ(Y, ⊤)) (c : Γ(X, ⊤))
    (e : artinSchreierSheafZMod X Ψ' (g₂.appTop b) ≅ artinSchreierSheafZMod X Ψ c)
    (hb : g₁.appTop b + c = g₃.appTop b) :
    Nonempty ((derivedTensorRight (ModuleCat.{u + 1} Λ) X
        ((D((g₂)^*[ModuleCat.{u + 1} Λ])).obj
          ((DerivedCategory.singleFunctor _ 0).obj (artinSchreierSheafZMod Y Ψ' b)))).obj
        ((D((g₁)^*[ModuleCat.{u + 1} Λ])).obj
          ((DerivedCategory.singleFunctor _ 0).obj (artinSchreierSheafZMod Y Ψ b))) ≅
      (L((g₃)^*[ModuleCat.{u + 1} Λ])).obj
        ((DerivedCategory.singleFunctor _ 0).obj (artinSchreierSheafZMod Y Ψ b))) := by
  let A := ModuleCat.{u + 1} Λ
  obtain ⟨t⟩ := nonempty_iso_singleFunctor_artinSchreierSheafZMod_tensor Λ X Ψ (g₁.appTop b) c
  obtain ⟨e₃⟩ := nonempty_iso_leftDerivedUpperStar_singleFunctor Λ g₃ _ _
    (artinSchreierSheafZModPullbackIso g₃ Ψ b)
  exact ⟨tensorIso
      ((((g₁)^*[A]).mapDerivedCategorySingleFunctor 0).app _ ≪≫
        (DerivedCategory.singleFunctor _ 0).mapIso (artinSchreierSheafZModPullbackIso g₁ Ψ b))
      ((((g₂)^*[A]).mapDerivedCategorySingleFunctor 0).app _ ≪≫
        (DerivedCategory.singleFunctor _ 0).mapIso
          (artinSchreierSheafZModPullbackIso g₂ Ψ' b ≪≫ e)) ≪≫ t ≪≫
    eqToIso (by rw [hb]) ≪≫ e₃.symm⟩

end ArtinSchreier

end AlgebraicGeometry.Etale
