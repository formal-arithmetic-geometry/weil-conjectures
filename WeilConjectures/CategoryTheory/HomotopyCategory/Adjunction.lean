/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import Mathlib.Algebra.Homology.Additive
public import Mathlib.Algebra.Homology.HomotopyCategory.Plus
public import Mathlib.Algebra.Homology.Localization
public import Mathlib.CategoryTheory.Localization.Adjunction

/-!
# The adjunction induced on complexes, on the homotopy category, and on its bounded part

An adjunction `G ⊣ F` of additive functors induces an adjunction
`G.mapHomologicalComplex c ⊣ F.mapHomologicalComplex c` between the induced functors on
categories of homological complexes (`CategoryTheory.Adjunction.mapHomologicalComplex`),
with unit and counit given degreewise by the unit and counit of `adj`.

Since `HomotopyCategory.quotient` is a localization functor for the homotopy equivalences,
that adjunction descends to the homotopy categories
(`CategoryTheory.Adjunction.mapHomotopyCategory`), and restricting along the fully faithful
inclusions of the bounded below subcategories gives an adjunction between the bounded below
homotopy categories (`CategoryTheory.Adjunction.mapHomotopyCategoryPlus`).

## Main definitions

- `CategoryTheory.Adjunction.mapHomologicalComplex`
- `CategoryTheory.Adjunction.mapHomotopyCategory`
- `CategoryTheory.Adjunction.mapHomotopyCategoryPlus`
-/

@[expose] public section

universe v₁ v₂ u₁ u₂

open CategoryTheory

namespace CategoryTheory

variable {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]
  [Preadditive C] [Preadditive D] {ι : Type*} (c : ComplexShape ι)

/-- An adjunction `G ⊣ F` of additive functors induces an adjunction
`G.mapHomologicalComplex c ⊣ F.mapHomologicalComplex c` between the induced functors on
categories of homological complexes. -/
noncomputable def Adjunction.mapHomologicalComplex {G : D ⥤ C} {F : C ⥤ D} (adj : G ⊣ F)
    [G.Additive] [F.Additive] :
    G.mapHomologicalComplex c ⊣ F.mapHomologicalComplex c where
  unit :=
    { app := fun M =>
        { f := fun n => adj.unit.app (M.X n)
          comm' := fun i j _ => (adj.unit.naturality (M.d i j)).symm }
      naturality := fun M N φ => by
        ext n
        exact adj.unit.naturality (φ.f n) }
  counit :=
    { app := fun K =>
        { f := fun n => adj.counit.app (K.X n)
          comm' := fun i j _ => (adj.counit.naturality (K.d i j)).symm }
      naturality := fun K L ψ => by
        ext n
        exact adj.counit.naturality (ψ.f n) }
  left_triangle_components X := by
    ext n
    exact adj.left_triangle_components (X.X n)
  right_triangle_components Y := by
    ext n
    exact adj.right_triangle_components (Y.X n)

/-- An adjunction `G ⊣ F` of additive functors induces an adjunction
`G.mapHomotopyCategory c ⊣ F.mapHomotopyCategory c` between the induced functors on the
homotopy categories: both induced functors factor the corresponding functors on complexes
through the quotient functors, which are localization functors for the homotopy
equivalences, so `Adjunction.mapHomologicalComplex` descends. -/
noncomputable def Adjunction.mapHomotopyCategory {G : D ⥤ C} {F : C ⥤ D} (adj : G ⊣ F)
    [G.Additive] [F.Additive]
    [(HomotopyCategory.quotient C c).IsLocalization
      (HomologicalComplex.homotopyEquivalences C c)]
    [(HomotopyCategory.quotient D c).IsLocalization
      (HomologicalComplex.homotopyEquivalences D c)] :
    G.mapHomotopyCategory c ⊣ F.mapHomotopyCategory c := by
  letI : CatCommSq (G.mapHomologicalComplex c) (HomotopyCategory.quotient D c)
      (HomotopyCategory.quotient C c) (G.mapHomotopyCategory c) :=
    ⟨(G.mapHomotopyCategoryFactors c).symm⟩
  letI : CatCommSq (F.mapHomologicalComplex c) (HomotopyCategory.quotient C c)
      (HomotopyCategory.quotient D c) (F.mapHomotopyCategory c) :=
    ⟨(F.mapHomotopyCategoryFactors c).symm⟩
  exact (adj.mapHomologicalComplex c).localization
    (HomotopyCategory.quotient D c) (HomologicalComplex.homotopyEquivalences D c)
    (HomotopyCategory.quotient C c) (HomologicalComplex.homotopyEquivalences C c)
    (G.mapHomotopyCategory c) (F.mapHomotopyCategory c)

/-- An adjunction `G ⊣ F` of additive functors induces an adjunction
`G.mapHomotopyCategoryPlus ⊣ F.mapHomotopyCategoryPlus` between the bounded below homotopy
categories: both functors are restrictions of the corresponding functors on the ambient
homotopy categories along the fully faithful inclusions of the bounded below
subcategories. -/
noncomputable def Adjunction.mapHomotopyCategoryPlus [Limits.HasBinaryBiproducts C]
    [Limits.HasBinaryBiproducts D] {G : D ⥤ C} {F : C ⥤ D} (adj : G ⊣ F)
    [G.Additive] [F.Additive] :
    G.mapHomotopyCategoryPlus ⊣ F.mapHomotopyCategoryPlus :=
  Adjunction.restrictFullyFaithful (adj.mapHomotopyCategory (ComplexShape.up ℤ))
    (HomotopyCategory.plus D).fullyFaithfulι (HomotopyCategory.plus C).fullyFaithfulι
    (Iso.refl _) (Iso.refl _)

end CategoryTheory
