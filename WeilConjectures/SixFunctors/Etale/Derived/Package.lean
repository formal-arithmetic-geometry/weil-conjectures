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

## Main definitions

- `AlgebraicGeometry.Etale.SixOperationsPackage` (`sk-thm-sf-package`): the eight clauses,
  one named field each.

## Main statements

- `AlgebraicGeometry.Etale.sixOperationsPackage` (`sk-thm-sf-package`): the eight clauses
  hold.

## Implementation notes

Each clause is one of the statements of this directory, and `sixOperationsPackage` is the
assembly: the clauses that are already available are *proved* here, and only the genuinely
open ones carry a `sorry`. Proved outright are the two adjunctions
(`AlgebraicGeometry.Etale.derivedUpperStarLowerStarAdjunction` and
`AlgebraicGeometry.Etale.rightDerivedUpperShriekAdjunction`), the composition law for `Rf_!`,
the duality clause, the relative product clause and the whole of the stability clause. Left
sorried are the base-change square, the projection formula, the independence of the
compactification, the proper coincidence `Rf_! ≅ Rf_*` and the orientation.

The clauses of the blueprint that this statement does not carry are the ones whose content is
an identity *between canonical comparison transformations* rather than the existence of an
isomorphism: the naturality clauses, and the compatibilities with finite reduction, scalar
extension and the pro-étale realization, which would need a change-of-coefficients functor
between stages. In this development a coefficient stage is chosen by picking the coefficient
category `A`, so there is nothing to compare across; see the module docstring of
`WeilConjectures.SixFunctors.Etale.Derived.Stability`.

Three further components of the blueprint's duality clause (6) are not collected here, since
they need data that the package's `f` does not carry: `𝔻_X K ≅ K^∨(d)[2d]` for perfect `K`
needs an orientation and is
`AlgebraicGeometry.Etale.Orientation.nonempty_iso_verdierDual_coefficientDual`, and global
duality and the derived Poincaré pairing need `X` smooth proper geometrically connected and
are the two statements of `WeilConjectures.SixFunctors.Etale.Derived.GlobalDuality`.

-/

@[expose] public section

universe u' u

open CategoryTheory Limits MonoidalCategory Opposite

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A]

variable {FA : A → A → Type (u + 1)} {CA : A → Type (u + 1)}
  [∀ X Y, FunLike (FA X Y) (CA X) (CA Y)] [ConcreteCategory.{u + 1} A FA]
  [HasSmallSiteSheafify A]
  [Etale.UpperStarPreservesFlat A] [(CategoryTheory.forget A).ReflectsIsomorphisms]
  [PreservesFilteredColimitsOfSize.{u + 1, u + 1} (CategoryTheory.forget A)]
  [∀ X : Scheme.{u}, X.smallEtaleTopology.HasSheafCompose (CategoryTheory.forget A)]

namespace Etale

variable {X Y S : Scheme.{u}} (f : X ⟶ Y) (aY : Y ⟶ S) [HasCompactification f]
  [QuasiCompact f] [HasCompactification aY] [HasCompactification (f ≫ aY)]

/-- Blueprint `sk-thm-sf-package`: The six-operations package.

Let `f : X ⟶ Y` be a separated finite-type morphism of schemes over a base `S`, with
`a_Y : Y ⟶ S` the structure morphism of `Y` and `a_X = f ≫ a_Y` that of `X`, all three
admitting compactifications. The eight clauses of the blueprint, one group of fields each:

1. **Adjunctions.** `Lf^* ⊣ Rf_*` and `Rf_! ⊣ Rf^!`.
2. **Base change.** For a Cartesian square

   ```
     X' --g'--> X
     |          |
     f'         f
     v          v
     Y' --g---> Y
   ```

   one has `Lg^* Rf_! ≅ Rf'_! Lg'^*`; and `Lg^* Rf_* ≅ Rf'_* Lg'^*` for proper `f` and for
   smooth `g`.
3. **Projection formula.** `Rf_!(K ⊗ᴸ Lf^* L) ≅ Rf_! K ⊗ᴸ L` at every `K` and `L`.
4. **Compactifications and proper coincidence.** `Rf_!` is independent of the compactification,
   `R(f ≫ h)_! ≅ Rh_! Rf_!`, and `Rf_! ≅ Rf_*` for proper `f`.
5. **Orientation.** A smooth `f` of pure relative dimension `d` carries an orientation
   `Rf^! Λ_Y ≅ Lf^* Λ_Y (d)[2d]`.
6. **Duality.** `𝔻_X 𝔻_X ≅ id` on `Dctf(X, A)`, and the Verdier exchange
   `𝔻_Y Rf_! ≅ Rf_* 𝔻_X`.
7. **Relative product.** The four Künneth comparisons over `S` are isomorphisms.
8. **Stability.** `Lf^*`, `- ⊗ᴸ -`, `Rf_*`, `Rf_!`, `Rf^!` and `𝔻_X` carry `Dctf` into
   `Dctf`.

See the module docstring for the clauses that are deliberately not carried here. -/
structure SixOperationsPackage : Prop where
  /-- (1) The adjunction `Lf^* ⊣ Rf_*`. -/
  upperStarLowerStarAdjunction : Nonempty (L((f)^*[A]) ⊣ R((f)_*[A]))
  /-- (1) The adjunction `Rf_! ⊣ Rf^!`. -/
  lowerShriekUpperShriekAdjunction : Nonempty (R(f)_![A] ⊣ R(f)^![A])
  /-- (2) Base change for `Rf_!`. -/
  baseChangeLowerShriek : ∀ {X' Y' : Scheme.{u}} (g : Y' ⟶ Y) (g' : X' ⟶ X) (f' : X' ⟶ Y'),
    IsPullback g' f' f g → ∀ [HasCompactification f'],
      Nonempty (R(f)_![A] ⋙ L((g)^*[A]) ≅ L((g')^*[A]) ⋙ R(f')_![A])
  /-- (2) Proper base change for `Rf_*`. -/
  baseChangeLowerStarOfProper :
    ∀ {X' Y' : Scheme.{u}} (g : Y' ⟶ Y) (g' : X' ⟶ X) (f' : X' ⟶ Y'),
      IsPullback g' f' f g → IsProper f →
      Nonempty (R((f)_*[A]) ⋙ L((g)^*[A]) ≅ L((g')^*[A]) ⋙ R((f')_*[A]))
  /-- (2) Smooth base change for `Rf_*`. -/
  baseChangeLowerStarOfSmooth :
    ∀ {X' Y' : Scheme.{u}} (g : Y' ⟶ Y) (g' : X' ⟶ X) (f' : X' ⟶ Y'),
      IsPullback g' f' f g → Smooth g →
      Nonempty (R((f)_*[A]) ⋙ L((g)^*[A]) ≅ L((g')^*[A]) ⋙ R((f')_*[A]))
  /-- (3) The projection formula. -/
  projectionFormula : ∀ K L, HasProjectionFormula A f K L
  /-- (4) `Rf_!` is independent of the chosen compactification. -/
  lowerShriekCompactificationIndependent :
    ∀ c c' : Compactification f, Nonempty (Rf_!(c)[A] ≅ Rf_!(c')[A])
  /-- (4) The composition law `R(f ≫ h)_! ≅ Rf_! ⋙ Rh_!`. -/
  lowerShriekComp : ∀ {Z : Scheme.{u}} (h : Y ⟶ Z) [HasCompactification h]
    [HasCompactification (f ≫ h)], Nonempty (R(f ≫ h)_![A] ≅ R(f)_![A] ⋙ R(h)_![A])
  /-- (4) Proper coincidence `Rf_! ≅ Rf_*`. -/
  lowerShriekIsoLowerStarOfProper : IsProper f → Nonempty (R(f)_![A] ≅ R((f)_*[A]))
  /-- (5) A smooth morphism of pure relative dimension carries an orientation. -/
  orientation : ∀ d : ℕ, SmoothOfRelativeDimension d f → Nonempty (Orientation A f d)
  /-- (6) Verdier biduality on `Dctf(X, A)`. -/
  biduality : ∀ K, DerivedCategory.constructibleFiniteTor A X K →
    Nonempty (K ≅ (verdierDual A (f ≫ aY)).obj (op ((verdierDual A (f ≫ aY)).obj (op K))))
  /-- (6) The Verdier exchange `𝔻_Y Rf_! ≅ Rf_* 𝔻_X`. -/
  verdierExchange : ∀ M, DerivedCategory.constructibleFiniteTor A X M →
    Nonempty ((verdierDual A aY).obj (op ((R(f)_![A]).obj M)) ≅
      (R((f)_*[A])).obj ((verdierDual A (f ≫ aY)).obj (op M)))
  /-- (7) The four Künneth comparisons over `S` are isomorphisms. -/
  kunneth : HasKunnethComparisons A S
  /-- (8) `Lf^*` carries `Dctf` into `Dctf`. -/
  ctfLeftDerivedUpperStar : ∀ K, DerivedCategory.constructibleFiniteTor A Y K →
    DerivedCategory.constructibleFiniteTor A X ((L((f)^*[A])).obj K)
  /-- (8) `- ⊗ᴸ -` carries `Dctf` into `Dctf`. -/
  ctfTensor : ∀ K M, DerivedCategory.constructibleFiniteTor A X K →
    DerivedCategory.constructibleFiniteTor A X M →
    DerivedCategory.constructibleFiniteTor A X (((-⊗ᴸ-(X)[A]).obj K).obj M)
  /-- (8) `Rf_*` carries `Dctf` into `Dctf`. -/
  ctfRightDerivedLowerStar : ∀ K, DerivedCategory.constructibleFiniteTor A X K →
    DerivedCategory.constructibleFiniteTor A Y ((R((f)_*[A])).obj K)
  /-- (8) `Rf_!` carries `Dctf` into `Dctf`. -/
  ctfRightDerivedLowerShriek : ∀ K, DerivedCategory.constructibleFiniteTor A X K →
    DerivedCategory.constructibleFiniteTor A Y ((R(f)_![A]).obj K)
  /-- (8) `Rf^!` carries `Dctf` into `Dctf`. -/
  ctfRightDerivedUpperShriek : ∀ K, DerivedCategory.constructibleFiniteTor A Y K →
    DerivedCategory.constructibleFiniteTor A X ((R(f)^![A]).obj K)
  /-- (8) `𝔻_X` carries `Dctf` into `Dctf`. -/
  ctfVerdierDual : ∀ K, DerivedCategory.constructibleFiniteTor A X K →
    DerivedCategory.constructibleFiniteTor A X ((verdierDual A (f ≫ aY)).obj (op K))

/-- Blueprint `sk-thm-sf-package`: The six-operations package.

The eight clauses of `AlgebraicGeometry.Etale.SixOperationsPackage` hold when `Y` is
Noetherian, which the stability of `Dctf` under `Rf^!` needs. Every clause is one
of the propositions of this directory, and the proof is the assembly; the clauses that are
still open carry a `sorry`, see the module docstring. -/
theorem sixOperationsPackage [IsNoetherian Y] : SixOperationsPackage A f aY where
  upperStarLowerStarAdjunction := ⟨derivedUpperStarLowerStarAdjunction A f⟩
  lowerShriekUpperShriekAdjunction := ⟨rightDerivedUpperShriekAdjunction A f⟩
  baseChangeLowerShriek _ _ _ _ := sorry
  baseChangeLowerStarOfProper _ _ _ _ _ := sorry
  baseChangeLowerStarOfSmooth _ _ _ _ _ := sorry
  projectionFormula _ _ := sorry
  lowerShriekCompactificationIndependent _ _ := sorry
  lowerShriekComp h := nonempty_iso_rightDerivedLowerShriek_comp A f h
  lowerShriekIsoLowerStarOfProper _ := sorry
  orientation _ _ := sorry
  biduality _ hK := nonempty_iso_verdierDual_verdierDual A (f ≫ aY) hK
  verdierExchange _ hM := nonempty_iso_verdierDual_rightDerivedLowerShriek A f aY hM
  kunneth := hasKunnethComparisons A S
  ctfLeftDerivedUpperStar _ hK := constructibleFiniteTor_leftDerivedUpperStar A f hK
  ctfTensor _ _ hK hM := constructibleFiniteTor_tensor A X hK hM
  ctfRightDerivedLowerStar _ hK := constructibleFiniteTor_rightDerivedLowerStar A f hK
  ctfRightDerivedLowerShriek _ hK := constructibleFiniteTor_rightDerivedLowerShriek A f hK
  ctfRightDerivedUpperShriek _ hK := constructibleFiniteTor_rightDerivedUpperShriek A f hK
  ctfVerdierDual _ hK := constructibleFiniteTor_verdierDual A (f ≫ aY) hK

end Etale

end AlgebraicGeometry
