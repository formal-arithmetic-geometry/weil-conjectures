/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.CategoryTheory.Monoidal.Category
public import Mathlib.CategoryTheory.Products.Associator
public import Mathlib.CategoryTheory.Functor.KanExtension.Basic
public import Mathlib.CategoryTheory.Localization.Predicate

/-!
# Binary and ternary derived monoidal comparison data

Source: blueprint `lem-sfb-derived-monoidal`, proof, binary and iterated ternary tensors;
`WeilConjectures.FromJoel.CategoryTheory.Monoidal.Derived`, counits and associator comparison
(blueprint: def-asd-derived-monoidal-comparison-data).

The tensors and associators are specified monoidal structures. The comparison need not be
invertible. The three universal properties use Mathlib's right Kan extension predicate.
-/

@[expose] public section

universe u₁ u₂ v₁ v₂

namespace CategoryTheory

open MonoidalCategory

variable {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]
  [MonoidalCategory C] [MonoidalCategory D]

/-- The left-associated ternary comparison, obtained by tensoring the binary comparison
with the identity and then applying the binary comparison again.
Source: blueprint `lem-sfb-derived-monoidal`, proof; `DerivedMonoidal.counit₁₂`
(blueprint: def-asd-derived-monoidal-comparison-data). -/
def derivedMonoidalComparisonLeft (L : C ⥤ D)
    (q : L.prod L ⋙ tensor D ⟶ tensor C ⋙ L) :
    L.prod (L.prod L) ⋙ leftAssocTensor D ⟶ leftAssocTensor C ⋙ L :=
  CategoryTheory.Functor.whiskerLeft (prod.inverseAssociator C C C)
    (CategoryTheory.Functor.whiskerRight (q.prod (𝟙 L)) (tensor D) ≫
      CategoryTheory.Functor.whiskerLeft ((tensor C).prod (𝟭 C)) q)

/-- The right-associated ternary comparison, obtained by tensoring the identity with
the binary comparison and then applying the binary comparison again.
Source: blueprint `lem-sfb-derived-monoidal`, proof; `DerivedMonoidal.counit₂₃`
(blueprint: def-asd-derived-monoidal-comparison-data). -/
def derivedMonoidalComparisonRight (L : C ⥤ D)
    (q : L.prod L ⋙ tensor D ⟶ tensor C ⋙ L) :
    L.prod (L.prod L) ⋙ rightAssocTensor D ⟶ rightAssocTensor C ⋙ L :=
  CategoryTheory.Functor.whiskerRight (NatTrans.prod (𝟙 L) q) (tensor D) ≫
    CategoryTheory.Functor.whiskerLeft ((𝟭 C).prod (tensor C)) q

/-- Binary and ternary derived monoidal comparison data for a specified monoidal target
of a localization. Each right Kan condition says that precomposition with the product
localization followed by its specified counit induces a bijection on natural transformations
from every functor. The final equation uses the forward associator maps.
Source: blueprint `lem-sfb-derived-monoidal`, proof, derived tensors and descended constraints;
`Functor.HasDerivedMonoidalCategory` (binary/ternary portion) and
`DerivedMonoidal.associator_hom_fac_app_app_app`
(blueprint: def-asd-derived-monoidal-comparison-data). -/
structure DerivedMonoidalComparisonData (L : C ⥤ D) (W : MorphismProperty C)
    [L.IsLocalization W] [W.ContainsIdentities] where
  /-- The specified natural binary comparison. -/
  q : L.prod L ⋙ tensor D ⟶ tensor C ⋙ L
  /-- The binary tensor and its comparison form a right Kan extension. -/
  binary_isRightKanExtension : (tensor D).IsRightKanExtension q
  /-- The left-associated triple tensor has the induced right Kan universal property. -/
  left_isRightKanExtension :
    (leftAssocTensor D).IsRightKanExtension (derivedMonoidalComparisonLeft L q)
  /-- The right-associated triple tensor has the induced right Kan universal property. -/
  right_isRightKanExtension :
    (rightAssocTensor D).IsRightKanExtension (derivedMonoidalComparisonRight L q)
  /-- The specified associators commute with the iterated comparisons. -/
  associator_comparison (X Y Z : C) :
    (α_ (L.obj X) (L.obj Y) (L.obj Z)).hom ≫
        (derivedMonoidalComparisonRight L q).app (X, Y, Z) =
      (derivedMonoidalComparisonLeft L q).app (X, Y, Z) ≫ L.map (α_ X Y Z).hom

end CategoryTheory
