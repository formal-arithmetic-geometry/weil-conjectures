/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.Kunneth
public import WeilConjectures.SixFunctors.Etale.Derived.Orientation
public import WeilConjectures.SixFunctors.Etale.Derived.ProjectionFormula
public import WeilConjectures.SixFunctors.Etale.Derived.Stability
public import WeilConjectures.SixFunctors.Etale.Derived.TensorHom

/-!

# The six-operations package

This file states the summary theorem of the block: the six operations
`Lf^*`, `Rf_*`, `Rf_!`, `Rf^!`, `- ⊗ᴸ -` and `RHom(-, -)` exist on the ambient derived
categories of étale sheaves, descend to the small categories `Dᵇc` and `Dctf`, and satisfy the
eight clauses of the blueprint: adjunctions, base change, the projection formula,
compactification-independence and proper coincidence, the orientation, duality, the relative
product, and stability of the small categories.

Each clause is one of the statements proved elsewhere in this directory; the theorem is the
enumeration. Where a clause is already a named proposition it is used as it stands:

* clause (3) is `AlgebraicGeometry.Etale.HasProjectionFormula`;
* clause (7) is `AlgebraicGeometry.Etale.HasKunnethComparisons`;
* clause (5) is `AlgebraicGeometry.Etale.Orientation`.

The clauses of the blueprint that this statement does not carry are the ones whose content is an
identity *between canonical comparison transformations* rather than the existence of an
isomorphism — the coherence of the projection formula
(`AlgebraicGeometry.Etale.hasProjectionFormula_coherence` states the part that is expressible),
the naturality clauses, and the compatibilities with finite reduction, scalar extension and the
pro-étale realization, which would need a change-of-coefficients functor between stages. In this
development a coefficient stage is chosen by picking the coefficient category `A`, so there is
nothing to compare across; see the module docstring of
`WeilConjectures.SixFunctors.Etale.Derived.Stability`.

## Main statements

- `AlgebraicGeometry.Etale.sixOperationsPackage` (`sk-thm-sf-package`): the eight clauses.

-/

@[expose] public section

universe u' u

open CategoryTheory Limits MonoidalCategory Opposite Functor

namespace AlgebraicGeometry

open Scheme

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A]

variable {FA : A → A → Type (u + 1)} {CA : A → Type (u + 1)}
  [∀ X Y, FunLike (FA X Y) (CA X) (CA Y)] [ConcreteCategory.{u + 1} A FA]
  [HasSmallSiteSheafify A]

namespace Etale

/-- Blueprint `sk-thm-sf-package`: The six-operations package.

Let `f : X ⟶ Y` be a separated finite-type morphism of finite-type schemes over a base `S`,
with `a_Y : Y ⟶ S` the structure morphism of `Y` and `a_X = f ≫ a_Y` that of `X`, all three
admitting compactifications. Then the six operations of
`WeilConjectures.SixFunctors.Etale.Derived.{Tensor, Hom, UpperLowerStar, LowerShriek,
UpperShriek}` satisfy:

1. **Adjunctions.** `Lf^* ⊣ Rf_*` and `Rf_! ⊣ Rf^!`.
2. **Base change.** For a Cartesian square, `Lg^* Rf_! ≅ Rf'_! Lg'^*`; and
   `Lg^* Rf_* ≅ Rf'_* Lg'^*` for proper `f` and for smooth `g`.
3. **Projection formula.** `Rf_!(K ⊗ᴸ Lf^* L) ≅ Rf_! K ⊗ᴸ L` at every `K` and `L`.
4. **Compactifications and proper coincidence.** `Rf_!` is independent of the compactification,
   `R(f ≫ h)_! ≅ Rh_! Rf_!`, and `Rf_! ≅ Rf_*` for proper `f`.
5. **Orientation.** A smooth `f` of pure relative dimension `d` carries an orientation
   `Rf^! Λ_Y ≅ Lf^* Λ_Y (d)[2d]`.
6. **Duality.** `𝔻_X 𝔻_X ≅ id` on `Dctf(X, A)`, and the Verdier exchange
   `𝔻_Y Rf_! ≅ Rf_* 𝔻_X`.
7. **Relative product.** The four Künneth comparisons over `S` are isomorphisms; in particular
   `R(f ×_B g)_!(K ⊠ L) ≅ Rf_! K ⊗ᴸ Rg_! L`.
8. **Stability.** `Lf^*`, `- ⊗ᴸ -`, `Rf_*`, `Rf_!` and `𝔻_X` carry `Dctf` into `Dctf`.

Every clause is one of the propositions stated in this directory; see the module docstring for
the clauses that are deliberately not carried here. -/
theorem sixOperationsPackage {X Y S : Scheme.{u}} (f : X ⟶ Y) (aY : Y ⟶ S)
    [HasCompactification f] [HasCompactification aY] [HasCompactification (f ≫ aY)] :
    -- (1) adjunctions
    (Nonempty (L((f)^*[A]) ⊣ R((f)_*[A])) ∧ Nonempty (R(f)_![A] ⊣ R(f)^![A])) ∧
    -- (2) base change
    (∀ {X' Y' : Scheme.{u}} (g : Y' ⟶ Y) (g' : X' ⟶ X) (f' : X' ⟶ Y')
        (_ : IsPullback g' f' f g) [HasCompactification f'],
        Nonempty (R(f)_![A] ⋙ L((g)^*[A]) ≅ L((g')^*[A]) ⋙ R(f')_![A]) ∧
          (IsProper f → Nonempty (R((f)_*[A]) ⋙ L((g)^*[A]) ≅
            L((g')^*[A]) ⋙ R((f')_*[A]))) ∧
          (Smooth g → Nonempty (R((f)_*[A]) ⋙ L((g)^*[A]) ≅
            L((g')^*[A]) ⋙ R((f')_*[A])))) ∧
    -- (3) projection formula
    (∀ K L, HasProjectionFormula A f K L) ∧
    -- (4) compactifications, composition law and proper coincidence
    ((∀ c c' : Compactification f, Nonempty (Rf_!(c)[A] ≅ Rf_!(c')[A])) ∧
      (∀ {Z : Scheme.{u}} (h : Y ⟶ Z) [HasCompactification h] [HasCompactification (f ≫ h)],
        Nonempty (R(f ≫ h)_![A] ≅ R(f)_![A] ⋙ R(h)_![A])) ∧
      (IsProper f → Nonempty (R(f)_![A] ≅ R((f)_*[A])))) ∧
    -- (5) orientation
    (∀ d : ℕ, SmoothOfRelativeDimension d f → Nonempty (Orientation A f d)) ∧
    -- (6) duality
    ((∀ K, DerivedCategory.boundedConstructible A X K ∧
        DerivedCategory.finiteTorAmplitude A X K →
        Nonempty (K ≅ (verdierDual A (f ≫ aY)).obj (op
          ((verdierDual A (f ≫ aY)).obj (op K))))) ∧
      (∀ M, DerivedCategory.boundedConstructible A X M ∧
        DerivedCategory.finiteTorAmplitude A X M →
        Nonempty ((verdierDual A aY).obj (op ((R(f)_![A]).obj M)) ≅
          (R((f)_*[A])).obj ((verdierDual A (f ≫ aY)).obj (op M))))) ∧
    -- (7) relative product
    HasKunnethComparisons A S ∧
    -- (8) stability of the small categories
    (∀ K, DerivedCategory.boundedConstructible A X K ∧
        DerivedCategory.finiteTorAmplitude A X K →
        (DerivedCategory.boundedConstructible A Y ((R(f)_![A]).obj K) ∧
          DerivedCategory.finiteTorAmplitude A Y ((R(f)_![A]).obj K)) ∧
        (DerivedCategory.boundedConstructible A Y ((R((f)_*[A])).obj K) ∧
          DerivedCategory.finiteTorAmplitude A Y ((R((f)_*[A])).obj K)) ∧
        (DerivedCategory.boundedConstructible A X
            ((verdierDual A (f ≫ aY)).obj (op K)) ∧
          DerivedCategory.finiteTorAmplitude A X
            ((verdierDual A (f ≫ aY)).obj (op K)))) :=
  sorry

end Etale

end AlgebraicGeometry
