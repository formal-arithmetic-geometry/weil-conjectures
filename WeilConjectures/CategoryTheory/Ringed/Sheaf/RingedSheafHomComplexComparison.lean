/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Algebra.Homology.Additive
public import WeilConjectures.Algebra.Homology.HomComplexComponents
import WeilConjectures.CategoryTheory.Ringed.RingedHomComplexComparison

/-! # The product-total Hom comparison for actual sheaf complexes

Source: Stacks Project, Section 0A8X; the component calculation in the ringed-forgetting
argument (blueprint: lem-sf-ringed-sheaf-hom-complex-comparison).
-/

@[expose] public noncomputable section
set_option autoImplicit false

universe c v r d vd s
open CategoryTheory CategoryTheory.Limits Opposite
namespace CategoryTheory

variable {C : Type c} [Category.{v} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})]
  {R : Sheaf J CommRingCat.{max c v r}}
  {D : Type d} [Category.{vd} D] {J' : GrothendieckTopology D}
  [J'.HasSheafCompose (forget₂ CommRingCat.{max d vd s} RingCat.{max d vd s})]
  {R' : Sheaf J' CommRingCat.{max d vd s}}
  (U : SheafOfModules.{max c v r}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R) ⥤
    SheafOfModules.{max d vd s}
      ((sheafCompose J' (forget₂ CommRingCat RingCat)).obj R'))
  [U.Additive] [PreservesLimitsOfShape (Discrete ℤ) U]
  (h : Functor.uncurry.obj (SheafOfModules.homFunctor (R := R)) ⋙ U ≅
    (U.op.prod U) ⋙ Functor.uncurry.obj (SheafOfModules.homFunctor (R := R')))

attribute [local irreducible] homComplexFunctor homComplexπ

end CategoryTheory
