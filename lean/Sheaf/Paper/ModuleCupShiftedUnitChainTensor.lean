/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group T2
-/
module

public import Sheaf.Paper.ModuleCupHomologyRepresentability
public import WeilConjectures.CategoryTheory.Monoidal.Instances.HomotopyCategory
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed

/-! # The normalized ordinary tensor of two shifted free modules

Source: Stacks Project, Tag 068G, the tensor-of-cocycles construction.
-/

@[expose] public section

universe u
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped TensorProduct

namespace AlgebraicGeometry.Scheme.Modules
noncomputable section

variable (k : Type u) [CommRing k]

/-- A normalized ordinary tensor isomorphism of shifted free rank-one complexes.
Source: Stacks Project, Tag 068G, equation-simple-tor-product.
(blueprint: lem-sc-module-cup-shifted-unit-chain-tensor)
Proof: both single complexes have zero terms outside their named degrees. Hence their
ordinary total tensor has a unique nonzero summand, in degree p+q. On that summand use
multiplication k tensor k to k, whose inverse sends 1 to 1 tensor 1. All differentials
are zero; these degreewise maps therefore define inverse chain maps. Under the
singleObjXSelf identifications, inverse multiplication followed by the (p,q) summand
inclusion sends 1 to 1 tensor 1, giving the displayed equality. No interchange of
shifts occurs, so there is no sign. Negative p,q, p=0, q=0 and the zero ring are
included: the single support degree and multiplication isomorphism work in each case. -/
theorem exists_cupShiftedUnitChainTensor (p q : ℤ) :
    ∃ i : cupSingleModule k (p + q) ≅
      cupSingleModule k p ⊗ cupSingleModule k q,
      ((HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) (p + q)
          (ModuleCat.of k k)).inv ≫ i.hom.f (p + q)) (1 : k) =
        (HomologicalComplex.ιTensorObj (cupSingleModule k p) (cupSingleModule k q)
          p q (p + q) rfl)
          (((HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) p
              (ModuleCat.of k k)).inv (1 : k)) ⊗ₜ[k]
            ((HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) q
              (ModuleCat.of k k)).inv (1 : k))) := by sorry

end
end AlgebraicGeometry.Scheme.Modules
