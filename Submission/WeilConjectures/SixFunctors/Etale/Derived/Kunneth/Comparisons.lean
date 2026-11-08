/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Submission.WeilConjectures.AlgebraicGeometry.InvertibleExponent
public import Submission.WeilConjectures.Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Submission.WeilConjectures.SixFunctors.Etale.Derived.Composition
public import Submission.WeilConjectures.SixFunctors.Etale.Derived.Dualizing
public import Submission.WeilConjectures.SixFunctors.Etale.Derived.Exchange
public import Submission.WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.MapDerivedCategory
public import Submission.WeilConjectures.SixFunctors.Etale.Derived.LowerShriekIndependenceUnbounded
public import Submission.WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Comp
public import Submission.WeilConjectures.SixFunctors.Etale.Derived.ProjectionFormula
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.CategoryTheory.ObjectProperty.Retract
public import Mathlib.CategoryTheory.Triangulated.Subcategory
public import Mathlib.Topology.KrullDimension
public import Submission.WeilConjectures.SixFunctors.Etale.Derived.Stability.Basic
public import Submission.WeilConjectures.SixFunctors.Etale.Derived.Stability.ClosedImmersion
public import Submission.WeilConjectures.SixFunctors.Etale.Derived.Stability.DirectImage
public import Submission.WeilConjectures.SixFunctors.Etale.Derived.Stability.UpperShriek
public import Submission.WeilConjectures.SixFunctors.Etale.Derived.Stability.Generation
public import Submission.WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStar
public import Submission.WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Defs
public import Submission.WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Shriek
public import Submission.WeilConjectures.SixFunctors.Etale.Derived.Stability.OpenImmersion
public import Submission.WeilConjectures.Mathlib.CategoryTheory.Monoidal.Rigid.Braided
public import Submission.WeilConjectures.CategoryTheory.Monoidal.Instances.DerivedCategory
public import Submission.WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal.Comparison

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

/-!

# The Künneth–Verdier comparison maps on the étale site

## Main definitions

- `AlgebraicGeometry.Etale.HasKunnethComparisons` (`sk-def-sf-kv-maps`, `def-sf-kv-maps`): the
  four product comparison assertions `Ku_!`, `α`, `β`, `κ`, one per field.

## Main statements

- `AlgebraicGeometry.Etale.hasKunnethComparisons` (`sk-thm-sf-kunneth-verdier`): the four
  comparison maps are isomorphisms.

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
  (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]

namespace Etale

variable {B X Y : Scheme.{u}}

variable {FA : A → A → Type (u + 1)} {CA : A → Type (u + 1)}
  [∀ X Y, FunLike (FA X Y) (CA X) (CA Y)] [ConcreteCategory.{u + 1} A FA]
  [HasSmallSiteSheafify A]

/-- Blueprint `sk-def-sf-kv-maps`, `def-sf-kv-maps`: The product comparison maps.

The four product comparison maps of the six-functor formalism over a base scheme `S`, each
recorded as the assertion that it is an isomorphism. All external products are taken over
`S`.

* `kunnethShriek` is the `!`-Künneth map
  `Ku_! : Rf_! (M₁ ⊠ M₂) ⟶ Rf_{1!} M₁ ⊠ Rf_{2!} M₂` for `f = f₁ × f₂`, which is
  `AlgebraicGeometry.Etale.nonempty_iso_rightDerivedLowerShriek_externalProduct` for the base
  `Y₁ ×_S Y₂`, using `X₁ ×_S X₂ = (X₁ ×_S Y₂) ×_{Y₁ ×_S Y₂} (Y₁ ×_S X₂)`; it is an
  isomorphism *by construction*, being built out of isomorphisms. For a finite coefficient
  ring this is proved, from the relative product theorem and compact-support base change, as
  `AlgebraicGeometry.Etale.nonempty_iso_rightDerivedLowerShriek_mapOverBase_externalProduct`;
* `exceptional` is the exceptional Künneth map
  `α : Rf₁^! N₁ ⊠ Rf₂^! N₂ ⟶ Rf^! (N₁ ⊠ N₂)`, the exceptional adjoint of `Ku_!` followed by
  the two counits of `Rf_{i!} ⊣ Rf_i^!`;
* `externalHom` is the external Hom map
  `β : RHom(E₁, N₁) ⊠ RHom(E₂, N₂) ⟶ RHom(E₁ ⊠ E₂, N₁ ⊠ N₂)`, the tensor–Hom transpose of
  the two evaluation maps;
* `kunnethVerdier` is the Künneth–Verdier map
  `κ : M ⊠ 𝔻_Y N ⟶ RHom(p_Y^* N, Rp_X^! M)` on `X ×_S Y`, the composite of `β` applied to the
  pairs `(Λ_X, M)` and `(N, ω_Y)` with `RHom(1, α)` for `id_X × a_Y`, using the unit
  identifications `RHom(Λ_X, M) = M` and `Λ_X ⊠ N = p_Y^* N`.

Only `Ku_!` is built from isomorphisms; that `α`, `β` and `κ` are invertible is the content of
`AlgebraicGeometry.Etale.hasKunnethComparisons`, i.e. of `sk-thm-sf-kunneth-verdier`, which
holds over a field for finite coefficients of invertible exponent. Over a more general base the
comparisons fail: over `S = 𝔸¹_k`, with `E₁ = E₂ = i_*Λ` the skyscraper at the origin and
`N₁ = N₂ = Λ_S`, the source of `β` is `i_*Λ(-2)[-4]` and its target `i_*Λ(-1)[-2]`. -/
structure HasKunnethComparisons (S : Scheme.{u}) : Prop where
  /-- The `!`-Künneth map `Ku_!` is an isomorphism. -/
  kunnethShriek : ∀ {X₁ X₂ Y₁ Y₂ : Scheme.{u}} (b₁ : Y₁ ⟶ S) (b₂ : Y₂ ⟶ S)
      [LocallyOfFiniteType b₁] [QuasiCompact b₁] [LocallyOfFiniteType b₂] [QuasiCompact b₂]
      (f₁ : X₁ ⟶ Y₁) (f₂ : X₂ ⟶ Y₂) [HasCompactification f₁] [HasCompactification f₂]
      [QuasiCompact f₁] [QuasiCompact f₂]
      [HasCompactification (pullback.mapOverBase f₁ f₂ b₁ b₂)]
      {M₁ : _root_.DerivedCategory (Sheaf X₁.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
      {M₂ : _root_.DerivedCategory (Sheaf X₂.smallEtaleTopology (ModuleCat.{u + 1} Λ))},
      DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} Λ) X₁ M₁ →
      DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} Λ) X₂ M₂ →
      Nonempty ((R(pullback.mapOverBase f₁ f₂ b₁ b₂)_![ModuleCat.{u + 1} Λ]).obj
          (externalProduct (ModuleCat.{u + 1} Λ) (f₁ ≫ b₁) (f₂ ≫ b₂) M₁ M₂) ≅
        externalProduct (ModuleCat.{u + 1} Λ) b₁ b₂ ((R(f₁)_![ModuleCat.{u + 1} Λ]).obj M₁)
            ((R(f₂)_![ModuleCat.{u + 1} Λ]).obj M₂))
  /-- The exceptional Künneth map `α` is an isomorphism. -/
  exceptional : ∀ {X₁ X₂ Y₁ Y₂ : Scheme.{u}} (b₁ : Y₁ ⟶ S) (b₂ : Y₂ ⟶ S)
      [LocallyOfFiniteType b₁] [QuasiCompact b₁] [LocallyOfFiniteType b₂] [QuasiCompact b₂]
      (f₁ : X₁ ⟶ Y₁) (f₂ : X₂ ⟶ Y₂) [HasCompactification f₁] [HasCompactification f₂]
      [QuasiCompact f₁] [QuasiCompact f₂]
      [HasCompactification (pullback.mapOverBase f₁ f₂ b₁ b₂)]
      {N₁ : _root_.DerivedCategory (Sheaf Y₁.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
      {N₂ : _root_.DerivedCategory (Sheaf Y₂.smallEtaleTopology (ModuleCat.{u + 1} Λ))},
      DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} Λ) Y₁ N₁ →
      DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} Λ) Y₂ N₂ →
      Nonempty (externalProduct (ModuleCat.{u + 1} Λ) (f₁ ≫ b₁) (f₂ ≫ b₂)
          ((R(f₁)^![Λ]).obj N₁) ((R(f₂)^![Λ]).obj N₂) ≅
        (R(pullback.mapOverBase f₁ f₂ b₁ b₂)^![Λ]).obj (externalProduct (ModuleCat.{u + 1} Λ) b₁ b₂
            N₁ N₂))
  /-- The external Hom map `β` is an isomorphism. -/
  externalHom : ∀ {Z₁ Z₂ : Scheme.{u}} (c₁ : Z₁ ⟶ S) (c₂ : Z₂ ⟶ S)
      [IsSeparated c₁] [LocallyOfFiniteType c₁] [QuasiCompact c₁]
      [IsSeparated c₂] [LocallyOfFiniteType c₂] [QuasiCompact c₂]
      {E₁ N₁ : _root_.DerivedCategory (Sheaf Z₁.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
      {E₂ N₂ : _root_.DerivedCategory (Sheaf Z₂.smallEtaleTopology (ModuleCat.{u + 1} Λ))},
      DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} Λ) Z₁ E₁ →
      DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} Λ) Z₂ E₂ →
      DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} Λ) Z₁ N₁ →
      DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} Λ) Z₂ N₂ →
      Nonempty (externalProduct (ModuleCat.{u + 1} Λ) c₁ c₂ ((RHom(Z₁)[ModuleCat.{u + 1} Λ].obj (op
          E₁)).obj N₁)
          ((RHom(Z₂)[ModuleCat.{u + 1} Λ].obj (op E₂)).obj N₂) ≅
        (RHom(pullback c₁ c₂)[ModuleCat.{u + 1} Λ].obj (op (externalProduct (ModuleCat.{u + 1} Λ) c₁
            c₂ E₁ E₂))).obj
          (externalProduct (ModuleCat.{u + 1} Λ) c₁ c₂ N₁ N₂))
  /-- The Künneth–Verdier map `κ` is an isomorphism. -/
  kunnethVerdier : ∀ {X Y : Scheme.{u}} (a : X ⟶ S) (b : Y ⟶ S)
      [IsSeparated a] [LocallyOfFiniteType a] [QuasiCompact a]
      [HasCompactification b] [QuasiCompact b] [HasCompactification (pullback.fst a b)]
      {M : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
      {N : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))},
      DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} Λ) X M →
      DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} Λ) Y N →
      Nonempty (externalProduct (ModuleCat.{u + 1} Λ) a b M ((verdierDual Λ b).obj (op N)) ≅
        (RHom(pullback a b)[ModuleCat.{u + 1} Λ].obj (op ((L((pullback.snd a b)^*[ModuleCat.{u + 1}
            Λ])).obj N))).obj
          ((R(pullback.fst a b)^![Λ]).obj M))

end Etale

end AlgebraicGeometry
