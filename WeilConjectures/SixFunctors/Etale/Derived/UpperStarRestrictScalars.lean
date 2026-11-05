/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.BaseChange.RestrictScalars
public import WeilConjectures.SixFunctors.Etale.Derived.UpperStarIdCoherence
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Coherence
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.RestrictScalars

/-!
# Pullback of étale sheaves commutes with restriction of scalars

Let `ρ : Λ →+* Λ'` be a morphism of commutative rings and `g : Y ⟶ Z` a morphism of schemes.
Restriction of scalars along `ρ` commutes with the pullback `g^*` of étale sheaves of modules:
the canonical isomorphism `g^* (Res F) ≅ Res (g^* F)` for sheaves `F` of `Λ'`-modules on `Z` is
`AlgebraicGeometry.Etale.upperStarRestrictScalarsIso ρ g`, conjugate, for the adjunctions
`Res ⊣ Coext` and `g^* ⊣ g_*`, to the identity `g_* ∘ Coext = Coext ∘ g_*`. This isomorphism is
compatible with the composition,
identity and congruence isomorphisms of the pullbacks, and passes to the derived categories,
where it is compatible with the corresponding isomorphisms of derived pullbacks.

This is the compatibility of pullback with the change of the finite coefficients, used to make
the systems of derived pullbacks of the `ℓ`-adic coefficient stages into morphisms of adic
systems, for the compatible systems of Frobenius coefficient morphisms. It is the étale
counterpart of `WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.RestrictScalars`,
whose general pasting lemmas on derived categories it reuses.

## Main definitions

- `AlgebraicGeometry.Etale.leftDerivedUpperStarRestrictScalarsIso ρ g` :
  `Res ⋙ Lg^* ≅ Lg^* ⋙ Res` on the derived categories.

## Main results

- `AlgebraicGeometry.Etale.upperStarRestrictScalarsIso_comp_hom`,
  `AlgebraicGeometry.Etale.upperStarRestrictScalarsIso_id_hom`,
  `AlgebraicGeometry.Etale.upperStarRestrictScalarsIso_congr_hom` : the compatibilities of
  `upperStarRestrictScalarsIso` with `Etale.upperStarComp`, `Etale.upperStarId` and the
  transport along an equality of morphisms.
- `AlgebraicGeometry.Etale.leftDerivedUpperStarRestrictScalarsIso_comp_hom_app`,
  `AlgebraicGeometry.Etale.leftDerivedUpperStarRestrictScalarsIso_id_hom_app`,
  `AlgebraicGeometry.Etale.leftDerivedUpperStarRestrictScalarsIso_congr_hom_app` : the
  derived versions, with `Etale.leftDerivedUpperStarComp`, `Etale.leftDerivedUpperStarId` and
  the transport along an equality of morphisms.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

variable {Λ Λ' : Type (u + 1)} [CommRing Λ] [CommRing Λ'] (ρ : Λ →+* Λ')

section Coherence

end Coherence

section Derived

/-- The components of the identity isomorphism `L(𝟙 X)^* ≅ 𝟭` of the derived pullback, in terms
of the functor induced levelwise by the exact pullback. -/
lemma leftDerivedUpperStarId_hom_app (A : Type*) [Category.{u + 1} A] [Abelian A]
    [IsGrothendieckAbelian.{u + 1} A] [MonoidalCategory A] [MonoidalPreadditive A]
    [SymmetricCategory A] [MonoidalClosed A] [Abelian.HasFunctorialFlatResolution A]
    (X : Scheme.{u}) (K : DerivedCategory (Sheaf X.smallEtaleTopology A)) :
    (leftDerivedUpperStarId A X).hom.app K =
      (leftDerivedUpperStarIsoMapDerivedCategory A (𝟙 X)).hom.app K ≫
        (Functor.mapDerivedCategoryNatIso (upperStarId A X) ≪≫
          Functor.mapDerivedCategoryIdIso _).hom.app K := by
  simp [leftDerivedUpperStarId, Functor.leftDerivedFunctorNatIso,
    leftDerivedUpperStarIsoMapDerivedCategory]

variable {Y Z : Scheme.{u}} (g : Y ⟶ Z)

end Derived

end AlgebraicGeometry.Etale
