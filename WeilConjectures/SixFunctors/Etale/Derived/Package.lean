/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.EtaleCohomology.Purity.Smooth.KummerClass
public import WeilConjectures.SixFunctors.Etale.Derived.Composition
public import WeilConjectures.SixFunctors.Etale.Derived.Kunneth
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekIndependenceUnbounded
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

The package is stated in the setting of `sk-def-sf-setting`: the coefficients are
`ModuleCat Λ` for a finite ring `Λ` (with a normalized Tate twist datum, for the orientation
clause) whose exponent is invertible on the base field `k`, and `Y` is separated of finite
type over `k`. For a general coefficient category the clauses are false: for `Λ = 𝔽_p` over
`𝔽̄_p`, `Rf_*` of the constant sheaf along `𝔸¹ ⟶ Spec 𝔽̄_p` is not constructible
(Artin–Schreier).

Each clause is one of the statements of this directory, and `sixOperationsPackage` is the
assembly: the clauses are proved from the corresponding statements, and only smooth base change
and the orientation, whose statements live in other chapters, carry a `sorry` here.

The clauses of the blueprint that this statement does not carry are the ones whose content is
an identity *between canonical comparison transformations* rather than the existence of an
isomorphism: the naturality clauses, and the compatibilities with finite reduction, scalar
extension and the pro-étale realization, which would need a change-of-coefficients functor
between stages; see the module docstring of
`WeilConjectures.SixFunctors.Etale.Derived.Stability`.

Three further components of the blueprint's duality clause (6) are not collected here, since
they need data that the package's `f` does not carry: `𝔻_X K ≅ K^∨(d)[2d]` for perfect `K`
needs an orientation and is
`AlgebraicGeometry.Etale.Orientation.nonempty_iso_verdierDual_coefficientDual`, and global
duality and the derived Poincaré pairing need `X` smooth proper geometrically connected and
are the two statements of `WeilConjectures.SixFunctors.Etale.Derived.GlobalDuality`.

-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory Opposite

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ] [HasTateTwist Λ] (k : Type u) [Field k]

variable {X Y : Scheme.{u}} (f : X ⟶ Y) (aY : Y ⟶ Spec (.of k)) [HasCompactification f]
  [QuasiCompact f] [IsSeparated aY] [LocallyOfFiniteType aY] [QuasiCompact aY]
  [HasCompactification aY] [HasCompactification (f ≫ aY)]

/-- Blueprint `sk-thm-sf-package`: The six-operations package.

Let `k` be a field, `Λ` a finite ring with a Tate twist datum, `Y` separated of finite type over
`k` with structure morphism `a_Y`, and `f : X ⟶ Y` separated of finite type, with
`a_X = f ≫ a_Y`. The twist `Λ_X(d)` of the orientation clause is that of the ambient Tate twist
datum; the clause is only true for a normalized datum
(`AlgebraicGeometry.Etale.HasTateTwist.IsNormalized`), which `sixOperationsPackage` assumes.
The eight clauses of the blueprint, one group of fields each:
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
   `Rf^! Λ_Y ≅ Lf^* Λ_Y ⊗ Λ_X(d)[2d]`.
6. **Duality.** `𝔻_X 𝔻_X ≅ id` on `Dctf(X, Λ)`, and the Verdier exchange
   `𝔻_Y Rf_! ≅ Rf_* 𝔻_X`.
7. **Relative product.** The four Künneth comparisons over `k` are isomorphisms.
8. **Stability.** `Lf^*`, `- ⊗ᴸ -`, `Rf_*`, `Rf_!`, `Rf^!` and `𝔻_X` carry `Dctf` into
   `Dctf`.
See the module docstring for the clauses that are deliberately not carried here. -/
structure SixOperationsPackage : Prop where
  /-- (1) The adjunction `Lf^* ⊣ Rf_*`. -/
  upperStarLowerStarAdjunction :
    Nonempty (L((f)^*[ModuleCat.{u + 1} Λ]) ⊣ R((f)_*[ModuleCat.{u + 1} Λ]))
  /-- (1) The adjunction `Rf_! ⊣ Rf^!`. -/
  lowerShriekUpperShriekAdjunction :
    Nonempty (R(f)_![ModuleCat.{u + 1} Λ] ⊣ R(f)^![ModuleCat.{u + 1} Λ])
  /-- (2) Base change for `Rf_!`. -/
  baseChangeLowerShriek : ∀ {X' Y' : Scheme.{u}} (g : Y' ⟶ Y) (g' : X' ⟶ X) (f' : X' ⟶ Y'),
    IsPullback g' f' f g → ∀ [HasCompactification f'],
      Nonempty (R(f)_![ModuleCat.{u + 1} Λ] ⋙ L((g)^*[ModuleCat.{u + 1} Λ]) ≅
        L((g')^*[ModuleCat.{u + 1} Λ]) ⋙ R(f')_![ModuleCat.{u + 1} Λ])
  /-- (2) Proper base change for `Rf_*`. -/
  baseChangeLowerStarOfProper :
    ∀ {X' Y' : Scheme.{u}} (g : Y' ⟶ Y) (g' : X' ⟶ X) (f' : X' ⟶ Y'),
      IsPullback g' f' f g → IsProper f →
      Nonempty (R((f)_*[ModuleCat.{u + 1} Λ]) ⋙ L((g)^*[ModuleCat.{u + 1} Λ]) ≅
        L((g')^*[ModuleCat.{u + 1} Λ]) ⋙ R((f')_*[ModuleCat.{u + 1} Λ]))
  /-- (2) Smooth base change for `Rf_*`. -/
  baseChangeLowerStarOfSmooth :
    ∀ {X' Y' : Scheme.{u}} (g : Y' ⟶ Y) (g' : X' ⟶ X) (f' : X' ⟶ Y'),
      IsPullback g' f' f g → Smooth g →
      Nonempty (R((f)_*[ModuleCat.{u + 1} Λ]) ⋙ L((g)^*[ModuleCat.{u + 1} Λ]) ≅
        L((g')^*[ModuleCat.{u + 1} Λ]) ⋙ R((f')_*[ModuleCat.{u + 1} Λ]))
  /-- (3) The projection formula. -/
  projectionFormula : ∀ K L, HasProjectionFormula (ModuleCat.{u + 1} Λ) f K L
  /-- (4) `Rf_!` is independent of the chosen compactification. -/
  lowerShriekCompactificationIndependent : ∀ c c' : Compactification f,
    Nonempty (Rf_!(c)[ModuleCat.{u + 1} Λ] ≅ Rf_!(c')[ModuleCat.{u + 1} Λ])
  /-- (4) The composition law `R(f ≫ h)_! ≅ Rf_! ⋙ Rh_!`. -/
  lowerShriekComp : ∀ {Z : Scheme.{u}} (h : Y ⟶ Z) [HasCompactification h]
    [HasCompactification (f ≫ h)],
    Nonempty (R(f ≫ h)_![ModuleCat.{u + 1} Λ] ≅
      R(f)_![ModuleCat.{u + 1} Λ] ⋙ R(h)_![ModuleCat.{u + 1} Λ])
  /-- (4) Proper coincidence `Rf_! ≅ Rf_*`. -/
  lowerShriekIsoLowerStarOfProper :
    IsProper f → Nonempty (R(f)_![ModuleCat.{u + 1} Λ] ≅ R((f)_*[ModuleCat.{u + 1} Λ]))
  /-- (5) A smooth morphism of pure relative dimension carries an orientation. -/
  orientation : ∀ d : ℕ, SmoothOfRelativeDimension d f → Nonempty (Orientation Λ f d)
  /-- (6) Verdier biduality on `Dctf(X, Λ)`. -/
  biduality : ∀ K, DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} Λ) X K →
    Nonempty (K ≅ (verdierDual (ModuleCat.{u + 1} Λ) (f ≫ aY)).obj
      (op ((verdierDual (ModuleCat.{u + 1} Λ) (f ≫ aY)).obj (op K))))
  /-- (6) The Verdier exchange `𝔻_Y Rf_! ≅ Rf_* 𝔻_X`. -/
  verdierExchange : ∀ M,
    Nonempty ((verdierDual (ModuleCat.{u + 1} Λ) aY).obj
        (op ((R(f)_![ModuleCat.{u + 1} Λ]).obj M)) ≅
      (R((f)_*[ModuleCat.{u + 1} Λ])).obj
        ((verdierDual (ModuleCat.{u + 1} Λ) (f ≫ aY)).obj (op M)))
  /-- (7) The four Künneth comparisons over `k` are isomorphisms. -/
  kunneth : HasKunnethComparisons (ModuleCat.{u + 1} Λ) (Spec (.of k))
  /-- (8) `Lf^*` carries `Dctf` into `Dctf`. -/
  ctfLeftDerivedUpperStar : ∀ K,
    DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} Λ) Y K →
      DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} Λ) X
        ((L((f)^*[ModuleCat.{u + 1} Λ])).obj K)
  /-- (8) `- ⊗ᴸ -` carries `Dctf` into `Dctf`. -/
  ctfTensor : ∀ K M, DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} Λ) X K →
    DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} Λ) X M →
    DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} Λ) X
      (((-⊗ᴸ-(X)[ModuleCat.{u + 1} Λ]).obj K).obj M)
  /-- (8) `Rf_*` carries `Dctf` into `Dctf`. -/
  ctfRightDerivedLowerStar : ∀ K,
    DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} Λ) X K →
      DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} Λ) Y
        ((R((f)_*[ModuleCat.{u + 1} Λ])).obj K)
  /-- (8) `Rf_!` carries `Dctf` into `Dctf`. -/
  ctfRightDerivedLowerShriek : ∀ K,
    DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} Λ) X K →
      DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} Λ) Y
        ((R(f)_![ModuleCat.{u + 1} Λ]).obj K)
  /-- (8) `Rf^!` carries `Dctf` into `Dctf`. -/
  ctfRightDerivedUpperShriek : ∀ K,
    DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} Λ) Y K →
      DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} Λ) X
        ((R(f)^![ModuleCat.{u + 1} Λ]).obj K)
  /-- (8) `𝔻_X` carries `Dctf` into `Dctf`. -/
  ctfVerdierDual : ∀ K,
    DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} Λ) X K →
      DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} Λ) X
        ((verdierDual (ModuleCat.{u + 1} Λ) (f ≫ aY)).obj (op K))

/-- Blueprint `sk-thm-sf-package`: The six-operations package.

The eight clauses of `AlgebraicGeometry.Etale.SixOperationsPackage` hold for a finite `Λ` whose
exponent is invertible on `k`. Every clause is one of the propositions of this directory, and
the proof is the assembly. Smooth base change on the unbounded derived categories and the
orientation, which is smooth purity, are not available in this directory and are left open
here. The Tate twist datum is assumed normalized: for the untwisted datum `Λ_X(m) = Λ_X` the
orientation clause fails over `ℚ`, where `Rf^! Λ ≅ μ_n[2] ≇ Λ[2]` for `𝔸¹_ℚ ⟶ Spec ℚ`. -/
theorem sixOperationsPackage [HasTateTwist.IsNormalized Λ] [HasInvertibleExponent Λ (Spec (.of k))]
    [IsSeparated f] :
    SixOperationsPackage Λ k f aY where
  upperStarLowerStarAdjunction := ⟨derivedUpperStarLowerStarAdjunction _ f⟩
  lowerShriekUpperShriekAdjunction := ⟨rightDerivedUpperShriekAdjunction _ f⟩
  baseChangeLowerShriek g g' f' sq _ :=
    have : QuasiCompact f' := MorphismProperty.of_isPullback (P := @QuasiCompact) sq inferInstance
    have := isIso_rightDerivedLowerShriekBaseChangeMap Λ sq
    ⟨asIso (rightDerivedLowerShriekBaseChangeMap Λ sq)⟩
  baseChangeLowerStarOfProper g g' f' sq _ :=
    have := isIso_derivedBaseChangeMap_of_isProper_of_isAddTorsion_ring Λ isAddTorsion_of_finite sq
    ⟨asIso (derivedBaseChangeMap _ sq.toCommSq)⟩
  baseChangeLowerStarOfSmooth _ _ _ _ _ := sorry
  projectionFormula K L := hasProjectionFormula_of_finite Λ f K L
  lowerShriekCompactificationIndependent c c' :=
    ⟨rightDerivedLowerShriekOfCompactificationIso Λ c c'⟩
  lowerShriekComp h := nonempty_iso_rightDerivedLowerShriek_comp Λ f h
  lowerShriekIsoLowerStarOfProper _ :=
    nonempty_iso_rightDerivedLowerShriek_rightDerivedLowerStar _ f
  orientation _ hd :=
    have := hd
    have : HasInvertibleExponent Λ X := HasInvertibleExponent.of_hom (f ≫ aY)
    Orientation.nonempty (Λ := Λ) f aY
  biduality _ hK := nonempty_iso_verdierDual_verdierDual Λ (f ≫ aY) hK
  verdierExchange M := nonempty_iso_verdierDual_rightDerivedLowerShriek Λ f aY M
  kunneth := hasKunnethComparisons Λ k
  ctfLeftDerivedUpperStar _ hK := constructibleFiniteTor_leftDerivedUpperStar _ f hK
  ctfTensor _ _ hK hM := constructibleFiniteTor_tensor _ X hK hM
  ctfRightDerivedLowerStar _ hK :=
    have : HasInvertibleExponent Λ Y := HasInvertibleExponent.of_hom aY
    constructibleFiniteTor_rightDerivedLowerStar Λ (f ≫ aY) aY f rfl hK
  ctfRightDerivedLowerShriek _ hK :=
    have : HasInvertibleExponent Λ Y := HasInvertibleExponent.of_hom aY
    constructibleFiniteTor_rightDerivedLowerShriek Λ aY f hK
  ctfRightDerivedUpperShriek _ hK :=
    have : HasInvertibleExponent Λ Y := HasInvertibleExponent.of_hom aY
    constructibleFiniteTor_rightDerivedUpperShriek Λ aY f hK
  ctfVerdierDual _ hK := constructibleFiniteTor_verdierDual Λ (f ≫ aY) hK

end Etale

end AlgebraicGeometry
