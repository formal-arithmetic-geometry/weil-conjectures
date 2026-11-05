/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.Monoidal
/-! # Tensor comparison for a right exact scalar functor

The two-variable left derived universal property applies to flat K-flat models and
requires no exactness of the ordinary scalar functor. The cochain equation retains
the fixed derived counit, including the quotient-to-homotopy comparison maps.
-/

@[expose] public section
set_option autoImplicit false
universe u u₁ u₂ u₃ u₄

open CategoryTheory Abelian Limits MonoidalCategory DerivedCategory

open scoped CategoryTheory.Functor
open CategoryTheory.Functor

namespace CategoryTheory
variable {C D : Type*} [Category C] [Category D] [MonoidalCategory C] [MonoidalCategory D]
    (F G : C ⥤ D) (e : F ≅ G)

attribute [local irreducible] tensorConjugate

end CategoryTheory

namespace CategoryTheory.Functor

attribute [local irreducible] Functor.leftDerivedFunctor Functor.leftDerivedFunctorCounit
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {C : Type u₁} [Category.{u + 1} C] [Abelian C] [IsGrothendieckAbelian.{u + 1} C]
  [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalClosed C] [BraidedCategory C]
  [HasFunctorialFlatResolution C]
  {D : Type u₂} [Category.{u + 1} D] [Abelian D] [IsGrothendieckAbelian.{u + 1} D]
  [MonoidalCategory D] [MonoidalPreadditive D] [MonoidalClosed D] [BraidedCategory D]
  [HasFunctorialFlatResolution D]

attribute [local irreducible] rightExact_cochainCounit

section CachedMonoidalStructures

-- Cache the canonical structures. All public signatures are outside this section.

attribute [local instance 2000] complexMonoidalC complexMonoidalD
  homotopyMonoidalC homotopyMonoidalD derivedMonoidalC derivedMonoidalD

section GoodModels

variable (F : C ⥤ D) [F.Additive] [F.PreservesFlat] [F.IsLeftAdjoint]

end GoodModels

section Comparison

variable (F : C ⥤ D) [F.Additive] [F.PreservesKFlatQuasiIso]

variable [F.PreservesFlat] [F.IsLeftAdjoint]

variable [F.Monoidal]

attribute [local irreducible] rightExact_leftDerivedTensorComparison

attribute [local irreducible] DerivedCategory.Q DerivedCategory.Qh

end Comparison

section TransportedComparison

variable (F : C ⥤ D) [F.Additive] [F.PreservesKFlatQuasiIso]
  [F.PreservesFlat] [F.IsLeftAdjoint] [F.Monoidal]
  (G : DerivedCategory C ⥤ DerivedCategory D) (e : G ≅ F.leftDerivedFunctor)

attribute [local irreducible] normalizedTensorIso

end TransportedComparison

end CachedMonoidalStructures

end CategoryTheory.Functor
