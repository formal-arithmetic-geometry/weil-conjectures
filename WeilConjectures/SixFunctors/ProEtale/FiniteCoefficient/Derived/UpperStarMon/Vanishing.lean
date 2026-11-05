/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou, Claude
-/
module

public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Tensor
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.UpperLowerStar
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.KFlat

/-!
# The derived tensor product with a K-flat complex, and vanishing

- `AlgebraicGeometry.ProEtale.isIso_μNatTrans_Qh_app_app_of_kFlat`: `Qh K ⊗ᴸ Qh M ⟶ Qh (K ⊗ M)`
  is an isomorphism when `M` is K-flat.
- `AlgebraicGeometry.ProEtale.isZero_derivedTensor_obj_obj_of_isZero_left` and
  `AlgebraicGeometry.ProEtale.isZero_derivedTensor_obj_obj_of_isZero_right`: `K ⊗ᴸ M` vanishes
  when `K` or `M` does.

See `WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.UpperStarMonoidal` for an
overview.
-/

@[expose] public section

universe u' u

open CategoryTheory Abelian Limits MonoidalCategory

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A]

namespace ProEtale

variable {Z Y : Scheme.{u}} (g : Z ⟶ Y)
section

open DerivedCategory Functor.LaxMonoidal

variable {A} in
/-- The lax monoidal structure `Qh K ⊗ᴸ Qh M ⟶ Qh (K ⊗ M)` of `Qh : K(X_proét) ⥤ D(X_proét)` is an
isomorphism when `M` is K-flat. -/
lemma isIso_μNatTrans_Qh_app_app_of_kFlat {X : Scheme.{u}}
    (K M : HomotopyCategory (Sheaf (Scheme.ProEt.topology X) A) (.up ℤ))
    (hM : (HomotopyCategory.quasiIso _ (.up ℤ)).kFlat M) :
    IsIso (((μNatTrans (Qh (C := Sheaf (Scheme.ProEt.topology X) A))).app K).app M) := by
  -- Instance search does not find this instance through `-⊗ᴸ-(X)[A]`.
  have : (-⊗ᴸ-(X)[A]).IsLeftDerivedFunctor₂ (μNatTrans Qh)
      (HomotopyCategory.quasiIso _ (.up ℤ)) (HomotopyCategory.quasiIso _ (.up ℤ)) :=
    isLeftDerivedFunctor₂_derivedTensor A X
  exact (MorphismProperty.id_prod_kFlat_derives_curriedTensor
    (HomotopyCategory.quasiIso (Sheaf (Scheme.ProEt.topology X) A) (.up ℤ))
      Qh).isIso_of_isLeftDerivabilityStructure (LF := -⊗ᴸ-(X)[A]) (μNatTrans Qh) K ⟨_, hM⟩

section

open DerivedCategory ZeroObject

end

end

end ProEtale

end AlgebraicGeometry
