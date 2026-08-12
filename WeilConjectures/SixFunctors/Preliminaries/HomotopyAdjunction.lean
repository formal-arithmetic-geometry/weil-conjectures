/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import Mathlib.Algebra.Homology.Localization
public import Mathlib.CategoryTheory.Localization.Adjunction

/-!
# Lifting an adjunction of additive functors to homotopy categories

Given an adjunction `adj : f ⊣ g` between additive functors
`f : V ⥤ W` and `g : W ⥤ V` of preadditive categories, we construct

* `Adjunction.mapHomologicalComplex`: the induced adjunction
  `f.mapHomologicalComplex c ⊣ g.mapHomologicalComplex c` between the
  categories of homological complexes, and
* `Adjunction.mapHomotopyCategory`: the induced adjunction
  `f.mapHomotopyCategory c ⊣ g.mapHomotopyCategory c` between the homotopy
  categories, whenever the quotient functors to the homotopy categories are
  localizations with respect to homotopy equivalences (which holds, in
  particular, for the complex shapes `ComplexShape.up ℤ` and
  `ComplexShape.down ι`).

The second adjunction is obtained from the first one by descent along the
localization functors, using `Adjunction.localization`.

-/

@[expose] public section

open CategoryTheory Category

namespace CategoryTheory

variable {ι : Type*} {V W : Type*} [Category V] [Category W]
  [Preadditive V] [Preadditive W]
  {f : V ⥤ W} {g : W ⥤ V} [f.Additive] [g.Additive]

namespace Adjunction

/-- An adjunction `f ⊣ g` between additive functors induces an adjunction
between the induced functors on the categories of homological complexes.
The unit and counit are given degreewise by the unit and counit of `adj`. -/
@[simps]
def mapHomologicalComplex (adj : f ⊣ g) (c : ComplexShape ι) :
    f.mapHomologicalComplex c ⊣ g.mapHomologicalComplex c where
  unit :=
    { app K :=
        { f n := adj.unit.app (K.X n)
          comm' i j _ := (adj.unit.naturality (K.d i j)).symm }
      naturality K L φ := by
        ext n
        exact adj.unit.naturality (φ.f n) }
  counit :=
    { app L :=
        { f n := adj.counit.app (L.X n)
          comm' i j _ := (adj.counit.naturality (L.d i j)).symm }
      naturality K L φ := by
        ext n
        exact adj.counit.naturality (φ.f n) }
  left_triangle_components K := by
    ext n
    exact adj.left_triangle_components (K.X n)
  right_triangle_components L := by
    ext n
    exact adj.right_triangle_components (L.X n)

end Adjunction

variable (f) in
/-- The 2-commutative square expressing that `Functor.mapHomotopyCategory`
descends `Functor.mapHomologicalComplex` along the quotient functors to the
homotopy categories. -/
instance Functor.catCommSqMapHomotopyCategory (c : ComplexShape ι) :
    CatCommSq (f.mapHomologicalComplex c) (HomotopyCategory.quotient V c)
      (HomotopyCategory.quotient W c) (f.mapHomotopyCategory c) :=
  ⟨(f.mapHomotopyCategoryFactors c).symm⟩

/-- An adjunction `f ⊣ g` between additive functors induces an adjunction
between the induced functors on homotopy categories, whenever the quotient
functors to the homotopy categories are localizations with respect to
homotopy equivalences. This holds, in particular, for cochain complexes
indexed by `ℤ` (`ComplexShape.up ℤ`). -/
noncomputable def Adjunction.mapHomotopyCategory (adj : f ⊣ g) (c : ComplexShape ι)
    [(HomotopyCategory.quotient V c).IsLocalization
      (HomologicalComplex.homotopyEquivalences V c)]
    [(HomotopyCategory.quotient W c).IsLocalization
      (HomologicalComplex.homotopyEquivalences W c)] :
    f.mapHomotopyCategory c ⊣ g.mapHomotopyCategory c :=
  (adj.mapHomologicalComplex c).localization
    (HomotopyCategory.quotient V c) (HomologicalComplex.homotopyEquivalences V c)
    (HomotopyCategory.quotient W c) (HomologicalComplex.homotopyEquivalences W c)
    (f.mapHomotopyCategory c) (g.mapHomotopyCategory c)

end CategoryTheory
