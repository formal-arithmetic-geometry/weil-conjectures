/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.Kunneth.TensorBaseChange
public import WeilConjectures.SixFunctors.BaseChange.DerivedUnbounded

/-!
# The base change map for a pushforward tensored with the unit

For a commutative square `h ≫ f' = e ≫ g`, the base change map
`M ⊗ᴸ Lf'^* Rg_* F ⟶ Rh_* (Lh^* M ⊗ᴸ Le^* F)` of `AlgebraicGeometry.Etale.tensorBaseChangeMap`
at the unit `M = 𝟙_` is, up to the unitors and the monoidality of `Lh^*`, the derived base
change map `Lf'^* Rg_* F ⟶ Rh_* Le^* F` (`AlgebraicGeometry.Etale.derivedBaseChangeMap`).
In particular one is an isomorphism if and only if the other is
(`AlgebraicGeometry.Etale.isIso_tensorBaseChangeMap_unit_iff`).
-/

@[expose] public section

universe u' u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A] [Etale.UpperStarPreservesFlat A]

variable {X' S' T Y : Scheme.{u}}

/-- The base change map for a pushforward tensored with the unit `𝟙_` is an isomorphism if and
only if the derived base change map `Lf'^* Rg_* F ⟶ Rh_* Le^* F` is. -/
lemma isIso_tensorBaseChangeMap_unit_iff (h : Y ⟶ X') (e : Y ⟶ T) (f' : X' ⟶ S')
    (g : T ⟶ S') (w : h ≫ f' = e ≫ g) (F : DerivedCategory (Sheaf T.smallEtaleTopology A)) :
    IsIso (tensorBaseChangeMap A h e f' g w (𝟙_ _) F) ↔
      IsIso ((derivedBaseChangeMap A (CommSq.mk w.symm)).app F) :=
  sorry

end Etale

end AlgebraicGeometry
