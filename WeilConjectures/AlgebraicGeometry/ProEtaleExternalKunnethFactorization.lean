/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProEtaleExternalKunnethTargetIso

/-! # Factoring the specified two-morphism external Künneth arrow

Source: sk-lem-sf-kunneth-star, Two morphisms
(blueprint: lem-sf-external-kunneth-factorization).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
namespace AlgebraicGeometry.ProEtale
variable (A : Type (u + 1)) [CommRing A] [Finite A]

/-- The two-morphism arrow is the composite of the two specified identity-factor arrows,
with the constructed factor-interchange and direct-image composition isomorphisms.
This is a statement about the actual morphisms, without any Künneth invertibility hypothesis.
Source: sk-lem-sf-kunneth-star, Two morphisms
(blueprint: lem-sf-external-kunneth-factorization).

Proof: Write U = X₁ × Y₂ and U' = Y₂ × X₁. The inverse product symmetry U' to U gives
J = R(swap)_*. Pullback-composition and tensor symmetry identify the external product
of M₁ and Rf₂*M₂ on U with J of the reversed external product on U'. This is e.
Let W' = X₂ × X₁. Compose R(f₂ × id)*, R(swap)* and R(f₁ × id)* using the canonical
direct-image compositor. The composite scheme map is swap from W' to X₁ × X₂
followed by f₁ × f₂; pullback-composition, the inverse equivalence for this scheme
isomorphism, and tensor symmetry give e'. To identify the arrows, transpose the
composite along the composite pullback adjunction. Naturality of the composition
comparisons moves both counits to their respective tensor factors. The monoidal
composition comparison and involutivity of the symmetry cancel the intervening
swaps. The transpose is precisely the tensor of the two pulled-back counits,
which defines externalKunnethMap. Injectivity of the adjunction Hom equivalence
proves the displayed equation. No ctf or cohomological hypothesis or finite-type
hypothesis on the schemes is needed for this formal calculation. -/
theorem externalKunnethMap_factorization
    {B X₁ X₂ Y₁ Y₂ : Scheme.{u}}
    (b₁ : Y₁ ⟶ B) (b₂ : Y₂ ⟶ B) (f₁ : X₁ ⟶ Y₁) (f₂ : X₂ ⟶ Y₂)
    (M₁ : DerivedCategory (Sheaf (Scheme.ProEt.topology X₁) (ModuleCat.{u + 1} A)))
    (M₂ : DerivedCategory (Sheaf (Scheme.ProEt.topology X₂) (ModuleCat.{u + 1} A))) :
    let R₂ := (lowerStar (ModuleCat.{u + 1} A) f₂).rightDerivedFunctor.obj M₂
    let J := (lowerStar (ModuleCat.{u + 1} A)
      (pullbackSymmetry (f₁ ≫ b₁) b₂).inv).rightDerivedFunctor
    let H := (lowerStar (ModuleCat.{u + 1} A)
      (pullback.mapOverBaseRight f₁ b₁ b₂)).rightDerivedFunctor
    externalKunnethMap A
          ⟨(pullback.mapOverBase_fst f₁ f₂ b₁ b₂).symm⟩
          ⟨(pullback.mapOverBase_snd f₁ f₂ b₁ b₂).symm⟩ M₁ M₂ =
        externalKunnethIdentityMap A
            ⟨(pullback.mapOverBaseRight_fst f₁ b₁ b₂).symm⟩
            (pullback.mapOverBaseRight_snd f₁ b₁ b₂) M₁ R₂ ≫
          H.map ((externalKunnethSwapIso A (f₁ ≫ b₁) b₂ M₁ R₂).hom ≫
            J.map (externalKunnethIdentityMap A
            ⟨(pullback.mapOverBaseRight_fst f₂ b₂ (f₁ ≫ b₁)).symm⟩
            (pullback.mapOverBaseRight_snd f₂ b₂ (f₁ ≫ b₁)) M₂ M₁)) ≫
          (externalKunnethTargetIso A b₁ b₂ f₁ f₂ M₁ M₂).hom := by
  sorry

end AlgebraicGeometry.ProEtale
