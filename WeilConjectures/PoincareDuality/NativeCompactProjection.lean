/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.PoincareDuality.ProperProjectionComp
public import WeilConjectures.PoincareDuality.ProjectionFormulaShift
public import WeilConjectures.SixFunctors.FrobeniusSquareExchange.FrobeniusSquareExchange
import all WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CondensedIsomorphismSquareExchange
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedPullbackCoherence
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.WeaklyEtale
import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate

/-! Split-off native specialization; the upstream derived-category comparison is its source.
(blueprint: lem-pod-condensed-cup-projection-intertwining). -/

@[expose] public noncomputable section
universe u
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open AlgebraicGeometry AlgebraicGeometry.ProEtale AlgebraicGeometry.ProEtale.CondensedRing
open scoped CategoryTheory.Obj
namespace WeilConjectures

/-- The projection square in a form that keeps the functors and tensorators as parameters.
This regular definition lets a consumer compare those data before taking their components.
Source: the native projection part of mixed-support cup naturality.
(blueprint: lem-pod-condensed-cup-projection-intertwining-native-compact). -/
def NativeProjectionCompatibility
    {A B : Type*} [Category A] [Category B]
    [MonoidalCategory A] [MonoidalCategory B]
    (U : B ⥤ A) (F : A ⥤ B)
    (P : B ⥤ B) (Q : A ⥤ A)
    (δQ : ∀ K L : A, Q.obj (K ⊗ L) ⟶ Q.obj K ⊗ Q.obj L)
    (δP : ∀ K L : B, P.obj (K ⊗ L) ⟶ P.obj K ⊗ P.obj L)
    (eF : F ⋙ P ⟶ Q ⋙ F)
    (χ : P ⋙ U ≅ U ⋙ Q)
    (π : ∀ (K : A) (L : B), F.obj K ⊗ L ⟶ F.obj (K ⊗ U.obj L)) : Prop :=
  ∀ (K : A) (L : B),
      P.map (π K L) ≫ eF.app (K ⊗ U.obj L) ≫
        F.map (δQ K (U.obj L) ≫ (𝟙 _ ⊗ₘ χ.inv.app L)) =
      δP (F.obj K) L ≫ (eF.app K ⊗ₘ 𝟙 _) ≫ π (Q.obj K) (P.obj L)

set_option maxHeartbeats 4000000 in
-- Native derived-functor comparisons require extra unification heartbeats.
end WeilConjectures
