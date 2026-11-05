/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Coefficient.Derived.CoefficientDerivedSectionsScalarHomZeroCycleUnit
public import WeilConjectures.SecSmoothPurity.ModuleTensorGenerators

/-! # Transpose calculus for recorded closed structures

Naturality of the tensor-Hom transpose of a `CoefficientClosedStructure` in all three
variables, the action of total-tensor maps on homogeneous generators, and the
naturality of the degree-zero homology classes of cycles.

Source: Stacks Project, Tags 08J9, 03EK and 08JA.
-/

@[expose] public section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u c v w a b
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
namespace WeilConjectures

namespace CoefficientClosedStructure

variable {D : Type a} [Category.{b} D] {H : Dᵒᵖ × D ⥤ D}
  (S : CoefficientClosedStructure H)

end CoefficientClosedStructure

section TotalTensor

variable {C : Type c} [Category.{v} C] (J : GrothendieckTopology C)
  [HasSheafify J AddCommGrpCat.{max c v u}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max c v u}]
  (A : Sheaf J CommRingCat.{max c v u})

attribute [local instance] SheafOfModules.cochainModulesMonoidal

end TotalTensor

section UnitClass

variable {C : Type c} [Category.{v} C] (J : GrothendieckTopology C)
  [HasSheafify J AddCommGrpCat.{max c v u}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max c v u}]
  (A : Sheaf J CommRingCat.{max c v u})
  [HasDerivedCategory.{w} (SheafOfModules.{max c v u}
    ((sheafCompose J (forget₂ CommRingCat.{max c v u} RingCat.{max c v u})).obj A))]

end UnitClass

end WeilConjectures
