/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Triangulated.HomotopyLimit
public import Mathlib.RingTheory.AdicCompletion.Basic
public import WeilConjectures.CategoryTheory.Triangulated.HomotopyLimit.Basic
public import WeilConjectures.Algebra.Homology.HomotopyCategory.Products
public import WeilConjectures.SixFunctors.Etale.Derived.Coefficients
public import WeilConjectures.SixFunctors.Etale.Derived.Invertible
public import WeilConjectures.SixFunctors.Etale.Derived.TensorStructure
public import WeilConjectures.SixFunctors.Etale.Derived.Triangulated

/-!
# Reduction modulo a uniformizer is conservative on derived complete objects

Let `Λ` be a commutative ring and `ϖ ∈ Λ` a nonzerodivisor. On `D(X_ét, Λ)` the reduction
`K ↦ K ⊗ᴸ (Λ/ϖ)_X` (`AlgebraicGeometry.Etale.reductionModIdeal`) detects the invertibility
of `ϖ`: tensoring the triangle `Λ ⟶ Λ ⟶ Λ/ϖ ⟶ Λ⟦1⟧` with `K` shows that `ϖ` acts invertibly
on `K` as soon as `K ⊗ᴸ (Λ/ϖ)_X = 0`. Since a derived complete object on which `ϖ` acts
invertibly is zero, a morphism between objects which are derived complete for `(ϖ)` is an
isomorphism as soon as its reduction modulo `ϖ` is.

This is the passage to the limit in the proof of the projection formula at the integral stage
`𝒪_E` (blueprint `sk-thm-sf-pf-adic`, Step 3, and `thm-sf-pf-adic`: "the reduction functors
are conservative on derived-complete complexes").

## Main statements

- `AlgebraicGeometry.Etale.isIso_smul_id_of_isZero_reductionModIdeal`: if `K ⊗ᴸ (Λ/ϖ)_X = 0`
  then `ϖ` acts invertibly on `K`.
- `AlgebraicGeometry.Etale.isIso_of_derivedComplete_of_isIso_reductionModIdeal`: reduction
  modulo `ϖ` is conservative on objects that are derived complete for `(ϖ)`.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory Pretriangulated Opposite

namespace AlgebraicGeometry

open Scheme

namespace Etale

/-- The small étale site of a scheme is essentially small. Instance search does not find this
in the presence of the imports of this file. -/
local instance localInstance_ReductionConservative_1 (X : Scheme.{u}) :
    EssentiallySmall.{u + 1} X.Etale :=
  have : LocallySmall.{u + 1} X.Etale :=
    @locallySmall_of_univLE X.Etale _ (@univLE_of_max.{u, u + 1} UnivLE.self)
  essentiallySmall_of_small_of_locallySmall _

variable {Λ : Type (u + 1)} [CommRing Λ] {X : Scheme.{u}}

/-- The reduction `K ↦ K ⊗ᴸ (Λ/J)_X` commutes with shifts. -/
noncomputable instance (J : Ideal Λ) : (reductionModIdeal Λ X J).CommShift ℤ :=
  inferInstanceAs (((derivedTensor (ModuleCat.{u + 1} Λ) X).flip.obj _).CommShift ℤ)

/-- The reduction `K ↦ K ⊗ᴸ (Λ/J)_X` is triangulated. -/
instance (J : Ideal Λ) : (reductionModIdeal Λ X J).IsTriangulated :=
  inferInstanceAs (((derivedTensor (ModuleCat.{u + 1} Λ) X).flip.obj _).IsTriangulated)

/-- The unit `Λ` of the coefficients, as a constant sheaf placed in degree `0`, is a right unit
for the derived tensor product: `K ⊗ᴸ Λ_X ≅ K`. -/
noncomputable def derivedTensorSingleUnitIso
    (K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    ((derivedTensor (ModuleCat.{u + 1} Λ) X).obj K).obj
        ((_root_.DerivedCategory.singleFunctor _ 0).obj
          ((constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj
            (𝟙_ (ModuleCat.{u + 1} Λ)))) ≅ K :=
  ((derivedTensor (ModuleCat.{u + 1} Λ) X).obj K).mapIso
      (singleFunctorObjUnitIso (ModuleCat.{u + 1} Λ) X) ≪≫
    derivedTensorRightUnitor (ModuleCat.{u + 1} Λ) X K

end Etale

end AlgebraicGeometry
