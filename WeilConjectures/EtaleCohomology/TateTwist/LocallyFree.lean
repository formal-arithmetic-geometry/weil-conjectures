/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.EtaleCohomology.TateTwist.Basic
public import WeilConjectures.SixFunctors.Etale.Derived.TensorRightUnitor

/-!
# The Tate twists are locally free of rank one

Let `Λ` be a commutative ring of positive characteristic `n` and `X` a scheme on which `n` is
invertible. This file collects the statements of blueprint `det-def-sp-tate-twist-locally-free`
for the étale Tate twists `Λ_X(m) = (μₙ ⊗ Λ)^{⊗ m}` of `WeilConjectures.EtaleCohomology.TateTwist.Basic`:

1. on the étale cover `X' = X ×_{ℤ[1/n]} ℤ[1/n][ζ] ⟶ X` adjoining a primitive `n`-th root of
   unity `ζ`, the map `ℤ/n ⟶ μₙ`, `a ↦ ζ^a`, is an isomorphism
   (`AlgebraicGeometry.Etale.exists_etale_surjective_isIso_constantZModToRootsOfUnitySheaf`);
2. every `Λ_X(m)` becomes the constant sheaf `Λ` on that cover, it is ⊗-invertible, with
   `Λ_X(d) ⊗ᴸ Λ_X(-d) ≅ Λ_X`, and the twist `K ↦ K(d)` is an autoequivalence of `D(X_ét, Λ)`
   with inverse `K ↦ K(-d)` (`AlgebraicGeometry.Etale.tateTwistEquivalence`).

The autoequivalence only uses the twist datum `AlgebraicGeometry.Etale.HasTateTwist`, and is
stated for an arbitrary one.

## Main definitions

- `AlgebraicGeometry.Etale.derivedTensorRightCompIso`: `(- ⊗ᴸ M) ⊗ᴸ N ≅ - ⊗ᴸ (M ⊗ᴸ N)`.
- `AlgebraicGeometry.Etale.tateTwistCompTateTwistIso`: `(K(a))(b) ≅ K` for `a + b = 0`.
- `AlgebraicGeometry.Etale.tateTwistEquivalence`: `K ↦ K(d)` as an autoequivalence.

## Main statements

- `AlgebraicGeometry.Etale.tateTwistObject_locallyFree`: blueprint
  `det-def-sp-tate-twist-locally-free`.
-/

@[expose] public section

universe u' u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

section General

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A] (X : Scheme.{u})

/-- Tensoring on the right with `M` and then with `N` is tensoring with `M ⊗ᴸ N`:
`(K ⊗ᴸ M) ⊗ᴸ N ≅ K ⊗ᴸ (M ⊗ᴸ N)`, naturally in `K`, through the associator. -/
noncomputable def derivedTensorRightCompIso
    (M N : _root_.DerivedCategory (Sheaf X.smallEtaleTopology A)) :
    (derivedTensor A X).flip.obj M ⋙ (derivedTensor A X).flip.obj N ≅
      (derivedTensor A X).flip.obj (((derivedTensor A X).obj M).obj N) :=
  (tensorRightTensor M N).symm

end General

variable (Λ : Type (u + 1)) [CommRing Λ]

section Equivalence

variable [HasTateTwist Λ] (X : Scheme.{u}) [HasInvertibleExponent Λ X]

/-- `Λ_X(a) ⊗ᴸ Λ_X(b) ≅ Λ_X(a + b) = Λ_X(0) ≅ Λ_X` for `a + b = 0`. -/
noncomputable def tateObjectTensorIsoOfAddEqZero {a b : ℤ} (h : a + b = 0) :
    ((derivedTensor (ModuleCat.{u + 1} Λ) X).obj (tateObject Λ X a)).obj (tateObject Λ X b) ≅
      constantComplex Λ X :=
  HasTateTwist.twistObjectAddIso X a b ≪≫ eqToIso (by rw [h]) ≪≫
    HasTateTwist.twistObjectZeroIso X

/-- `(K(a))(b) ≅ K` for `a + b = 0`, naturally in `K`: the associator, then
`Λ_X(a) ⊗ᴸ Λ_X(b) ≅ Λ_X`, then the right unitor. -/
noncomputable def tateTwistCompTateTwistIso {a b : ℤ} (h : a + b = 0) :
    tateTwist Λ X a ⋙ tateTwist Λ X b ≅ 𝟭 _ :=
  derivedTensorRightCompIso (ModuleCat.{u + 1} Λ) X _ _ ≪≫
    (derivedTensor (ModuleCat.{u + 1} Λ) X).flip.mapIso
      (tateObjectTensorIsoOfAddEqZero Λ X h) ≪≫
    derivedTensorRightUnitorNatIso (ModuleCat.{u + 1} Λ) X

/-- The twist `K ↦ K(d)` is an autoequivalence of `D(X_ét, Λ)`, with inverse `K ↦ K(-d)`. -/
noncomputable def tateTwistEquivalence (d : ℤ) :
    DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) ≌
      DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :=
  .mk (tateTwist Λ X d) (tateTwist Λ X (-d)) (tateTwistCompTateTwistIso Λ X (add_neg_cancel d)).symm
    (tateTwistCompTateTwistIso Λ X (neg_add_cancel d))

@[simp]
lemma tateTwistEquivalence_functor (d : ℤ) :
    (tateTwistEquivalence Λ X d).functor = tateTwist Λ X d :=
  rfl

@[simp]
lemma tateTwistEquivalence_inverse (d : ℤ) :
    (tateTwistEquivalence Λ X d).inverse = tateTwist Λ X (-d) :=
  rfl

instance (d : ℤ) : (tateTwist Λ X d).IsEquivalence :=
  (tateTwistEquivalence Λ X d).isEquivalence_functor

end Equivalence

section Cover

variable [NeZero (ringChar Λ)] (X : Scheme.{u}) [HasInvertibleExponent Λ X]

/-- The primitive `n`-th root of unity `ζ` on the cover `X ×_{ℤ[1/n]} ℤ[1/n][ζ]` of `X`. -/
noncomputable def tateCoverOfZeta :
    Γ(pullback (toInvertibleExponentBase (Λ := Λ) X) (tateCover Λ), ⊤)ˣ :=
  Units.map (pullback.snd (toInvertibleExponentBase (Λ := Λ) X) (tateCover Λ)).appTop.hom
    (tateCoverZeta Λ)

lemma tateCoverOfZeta_pow : tateCoverOfZeta Λ X ^ ringChar Λ = 1 := by
  rw [tateCoverOfZeta, ← map_pow, tateCoverZeta_pow, map_one]

lemma isUnit_tateCoverOfZeta_pow_sub {i j : ℕ} (hi : i < ringChar Λ) (hj : j < ringChar Λ)
    (hij : i ≠ j) :
    IsUnit (((tateCoverOfZeta Λ X : _) : Γ(pullback (toInvertibleExponentBase (Λ := Λ) X)
        (tateCover Λ), ⊤)) ^ i -
      ((tateCoverOfZeta Λ X : _) : Γ(pullback (toInvertibleExponentBase (Λ := Λ) X)
        (tateCover Λ), ⊤)) ^ j) := by
  simpa [tateCoverOfZeta, ← map_pow, ← map_sub] using
    (isUnit_tateCoverZeta_pow_sub Λ hi hj hij).map
      (pullback.snd (toInvertibleExponentBase (Λ := Λ) X) (tateCover Λ)).appTop.hom

/-- On the étale cover `X' = X ×_{ℤ[1/n]} ℤ[1/n][ζ]` of `X`, the primitive `n`-th root of unity
`ζ` generates `μₙ`: the map `ℤ/n ⟶ μₙ`, `a ↦ ζ^a`, is an isomorphism, and every twist
`Λ_X(m)` becomes the constant sheaf `Λ`. -/
theorem exists_etale_surjective_isIso_constantZModToRootsOfUnitySheaf :
    ∃ (X' : Scheme.{u}) (π : X' ⟶ X), Etale π ∧ Function.Surjective π.base ∧
      ∃ (ζ : Γ(X', ⊤)ˣ) (hζ : ζ ^ ringChar Λ = 1),
        IsIso (X'.constantZModToRootsOfUnitySheaf (ringChar Λ) ζ hζ) ∧
        ∀ m : ℤ, Nonempty ((π)^*[ModuleCat.{u + 1} Λ].obj (tateTwistSheaf Λ X m) ≅ 𝟙_ _) :=
  ⟨_, tateCoverOf Λ X, inferInstance, surjective_tateCoverOf Λ X, tateCoverOfZeta Λ X,
    tateCoverOfZeta_pow Λ X,
    isIso_constantZModToRootsOfUnitySheaf_of_isUnit_sub _ _ _
      fun _ hi _ hj hij ↦ isUnit_tateCoverOfZeta_pow_sub Λ X hi hj hij,
    fun m ↦ ⟨upperStarTateCoverOfTateTwistSheafIso Λ X m⟩⟩

/-- Blueprint `det-def-sp-tate-twist-locally-free`: Tate twists are well defined and locally free
of rank one

For a ring `Λ` of positive characteristic `n` and a scheme `X` on which `n` is invertible:

1. there is a surjective étale cover `π : X' ⟶ X` and an `n`-th root of unity `ζ` on `X'` such
   that `ℤ/n ⟶ μₙ`, `a ↦ ζ^a`, is an isomorphism on `X'`;
2. every twist sheaf `Λ_X(m) = (μₙ ⊗ Λ)^{⊗ m}` becomes the constant sheaf `Λ` on `X'`, the
   twisting objects are ⊗-invertible with `Λ_X(d) ⊗ᴸ Λ_X(-d) ≅ Λ_X`, and `K ↦ K(d)` is an
   autoequivalence of `D(X_ét, Λ)`, with inverse `K ↦ K(-d)`
   (`AlgebraicGeometry.Etale.tateTwistEquivalence`).

The blueprint works with a pro-étale cover carrying a compatible system `(ζ_r)_r` of roots of
unity of all levels, which is needed for the integral and rational coefficients; for the finite
coefficient ring `Λ` the étale cover adjoining a single primitive `n`-th root suffices. The
independence of the level (clause (2) of the blueprint) is built into the construction: the twist
is defined with the characteristic `n` of `Λ` itself. -/
theorem tateTwistObject_locallyFree :
    (∃ (X' : Scheme.{u}) (π : X' ⟶ X), Etale π ∧ Function.Surjective π.base ∧
      ∃ (ζ : Γ(X', ⊤)ˣ) (hζ : ζ ^ ringChar Λ = 1),
        IsIso (X'.constantZModToRootsOfUnitySheaf (ringChar Λ) ζ hζ) ∧
        ∀ m : ℤ, Nonempty ((π)^*[ModuleCat.{u + 1} Λ].obj (tateTwistSheaf Λ X m) ≅ 𝟙_ _)) ∧
    ∀ d : ℤ, DerivedCategory.isInvertible Λ X (tateTwistObject Λ X d) ∧
      Nonempty (((derivedTensor (ModuleCat.{u + 1} Λ) X).obj (tateTwistObject Λ X d)).obj
        (tateTwistObject Λ X (-d)) ≅ constantComplex Λ X) ∧
      (tateTwist Λ X d).IsEquivalence ∧
      Nonempty (tateTwist Λ X d ⋙ tateTwist Λ X (-d) ≅ 𝟭 _) :=
  ⟨exists_etale_surjective_isIso_constantZModToRootsOfUnitySheaf Λ X, fun d ↦
    ⟨isInvertible_tateTwistObject Λ X d,
      ⟨tateObjectTensorIsoOfAddEqZero Λ X (add_neg_cancel d)⟩, inferInstance,
      ⟨tateTwistCompTateTwistIso Λ X (add_neg_cancel d)⟩⟩⟩

end Cover

end Etale

end AlgebraicGeometry
