/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.CategoryTheory.Adjunction.ProjectionMap
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Monoidal

/-!
# The canonical projection map for condensed module objects

The published module-object pullback tensor comparison is constructed on signed
K-flat total tensors and characterized by its derived counits. Its existing
right-adjoint mate gives the required map, without choosing a map between endpoints.

## References

* [Stacks, Tag 03EL](https://stacks.math.columbia.edu/tag/03EL)
* [Stacks, Tag 0943](https://stacks.math.columbia.edu/tag/0943)
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u v

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ] {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- A morphism together with its category and endpoints, used to keep the projection
map interface compact. -/
structure ProjectionMorphismData where
  carrier : Type (v + 1)
  [category : Category.{v} carrier]
  source : carrier
  target : carrier
  morphism : source ⟶ target

attribute [instance 20000] ProjectionMorphismData.category

/-- The canonical projection morphism, together with its category and endpoints. -/
def moduleObjectProjectionData
    (K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ X)))
    (L : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
      (condensedRingObj Λ Y))) : ProjectionMorphismData :=
  { carrier := _
    category := _
    source := _
    target := _
    morphism := (((derivedUpperStarLowerStarAdjunction Λ f).rightAdjointProjectionMap
      (T_C := derivedTensor Λ X) (T_D := derivedTensor Λ Y)
      (leftDerivedUpperStarTensor Λ f)).app K).app L }

/-- The canonical projection map: the adjoint transpose of the generic K-flat
pullback tensor comparison followed by counit tensor identity (Stacks, Tag 0943). -/
def moduleObjectProjectionMap
    (K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ X)))
    (L : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
      (condensedRingObj Λ Y))) :=
  (moduleObjectProjectionData Λ f K L).morphism

end AlgebraicGeometry.ProEtale.CondensedRing
