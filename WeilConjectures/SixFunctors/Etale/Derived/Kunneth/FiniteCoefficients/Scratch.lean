/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.Adjunction
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.Monoidal
public import WeilConjectures.CategoryTheory.Sites.ConstantSheafMonoidal
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Point.ConstantSheaf
public import WeilConjectures.SixFunctors.Etale.Derived.Kunneth.FiniteCoefficients.Defs

/-!
# Constant complexes, the constant-tensor comparison and the Künneth morphism

For a commutative ring `Λ` (in the blueprint `Λ = 𝒪_E/ϖⁿ` or a finite field `𝔽_{ℓ^r}`) and a
scheme `W`, the constant complex functor `c_W : D(Mod_Λ) ⥤ D(W_ét, Λ)` is left adjoint to the
derived sections `RΓ_W` (`AlgebraicGeometry.Etale.constantComplexAdjunction`), and comes with a
monoidal comparison `c_W(M ⊗ᴸ N) ⟶ c_W M ⊗ᴸ c_W N`
(`AlgebraicGeometry.Etale.constantComplexTensorComparison`), the derived comonoidal structure of
the exact monoidal constant sheaf functor. With these we define

- `AlgebraicGeometry.Etale.constantProjectionMap` (`pur7710-def-constant-projection`):
  `RΓ_W K ⊗ᴸ M ⟶ RΓ_W (K ⊗ᴸ c_W M)`;
- `AlgebraicGeometry.Etale.globalSectionsKunnethMap` (`pur7710-def-kunneth-map`) and
  `AlgebraicGeometry.Etale.globalSectionsKunnethMapFiniteField`
  (`pur7710-def-kunneth-map-field`): `RΓ_X K ⊗ᴸ RΓ_Y L ⟶ RΓ_Z (K ⊠ᴸ L)`.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

variable (Λ : Type (u + 1)) [CommRing Λ]

/-- The constant sheaf functor on étale sheaves of `Λ`-modules preserves flat objects: the stalk
of `M_W` at every geometric point is `M`. -/
instance preservesFlat_constantSheaf (W : Scheme.{u}) :
    (constantSheaf W.smallEtaleTopology (ModuleCat.{u + 1} Λ)).PreservesFlat where
  flat_obj {M} hM := (flat_iff_forall_flat_sheafFiber_obj _).2 fun s ↦
    ObjectProperty.prop_of_iso _
      ((pointSmallEtale s).ulift.{u + 1}.sheafFiberConstantSheafIso M).symm hM

noncomputable def testA (W : Scheme.{u}) (M N : DerivedCategory (ModuleCat.{u + 1} Λ)) :=
  ((constantSheaf W.smallEtaleTopology (ModuleCat.{u + 1} Λ)).leftDerivedTensorComparison.app M).app N

end Etale

end AlgebraicGeometry
