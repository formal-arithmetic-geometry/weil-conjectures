/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.DerivedMayerVietorisOpenCounitModel
import WeilConjectures.AlgebraicGeometry.OrdinaryOpenCounitSquare

/-! # The underived open counit square

Source: Stacks Project, Cohomology, Tags 08FE and 08BV.
(blueprint: lem-pc-mayer-vietoris-underived-open-counit-square).
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits TopologicalSpace
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 2048
noncomputable section
namespace AlgebraicGeometry

section

universe v

variable {A B C D : Type u} [Category.{v} A] [Category.{v} B]
  [Category.{v} C] [Category.{v} D]
  [Preadditive A] [Preadditive B] [Preadditive C] [Preadditive D]
  {LX : A ⥤ B} {RX : B ⥤ A} {LY : C ⥤ D} {RY : D ⥤ C}
  {F : A ⥤ C} {G : B ⥤ D}
  [LX.Additive] [RX.Additive] [LY.Additive] [RY.Additive]
  [F.Additive] [G.Additive]
  [(HomotopyCategory.quotient A (.up ℤ)).IsLocalization
    (HomologicalComplex.homotopyEquivalences A (.up ℤ))]
  [(HomotopyCategory.quotient B (.up ℤ)).IsLocalization
    (HomologicalComplex.homotopyEquivalences B (.up ℤ))]
  [(HomotopyCategory.quotient C (.up ℤ)).IsLocalization
    (HomologicalComplex.homotopyEquivalences C (.up ℤ))]
  [(HomotopyCategory.quotient D (.up ℤ)).IsLocalization
    (HomologicalComplex.homotopyEquivalences D (.up ℤ))]

end

end AlgebraicGeometry
