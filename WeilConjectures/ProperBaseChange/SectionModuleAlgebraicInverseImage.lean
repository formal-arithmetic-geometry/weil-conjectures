/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
public import WeilConjectures.CategoryTheory.Monoidal.Mod.Tensor
public import Mathlib.Algebra.Category.ModuleCat.Sheaf
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.CategoryTheory.Monoidal.Internal.FunctorCategory
public import WeilConjectures.CategoryTheory.RingObjects.Ab
public import WeilConjectures.CategoryTheory.Sites.MonObj
public import WeilConjectures.CategoryTheory.ModuleObjects.MapMod
public import Mathlib.Algebra.Category.Grp.Limits
public import Mathlib.CategoryTheory.Sites.Whiskering
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Types.Basic
import WeilConjectures.CategoryTheory.Sites.PushforwardMonoidal
import WeilConjectures.Mathlib.CategoryTheory.Functor.Flat
import Mathlib.CategoryTheory.Sites.PreservesSheafification
import Mathlib.CategoryTheory.Functor.KanExtension.Preserves
import Mathlib.Algebra.Category.Grp.FilteredColimits

/-!
# Algebraic presentation of pro-étale internal inverse image
-/

@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory MonObj
open scoped CategoryTheory.Obj TensorProduct
namespace AlgebraicGeometry.ProEtale

set_option backward.isDefEq.respectTransparency false

/- The concrete inverse image and its comparison after forgetting abelian groups. -/
/- Concrete coefficient and module comparisons, including the universe lifts. -/
/- Compatibility with the two adjunction units. -/
/- The additive operation graphs follow by transposition through the set adjunction. -/
/- Pointwise ring and action formulas for pushforward and its adjunction unit. -/
private noncomputable def sectionRingMap {X : Scheme.{u}}
    {R S : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}}
    [MonObj R] [IsCommMonObj R] [MonObj S] [IsCommMonObj S]
    (g : R ⟶ S) [IsMonHom g] (W : X.ProEtᵒᵖ) :
    (InternalAbelianSheafModule.sectionRings (Scheme.ProEt.topology X) R).obj W →+*
      (InternalAbelianSheafModule.sectionRings (Scheme.ProEt.topology X) S).obj W := by
  let H := (sheafToPresheaf (Scheme.ProEt.topology X) Ab.{u + 1}).mapCommMon ⋙
    (Monoidal.commMonFunctorCategoryEquivalence X.ProEtᵒᵖ Ab.{u + 1}).functor
  exact InternalAbelianSheafModule.ringHom
    ((H.map (CommMon.homMk (A := CommMon.mk R) (B := CommMon.mk S) ⟨g⟩)).app W).hom.hom

by
  haveI : IsMonHom ((upperStarLowerStarAdjunction Ab.{u + 1} f).unit.app R) :=
    (upperStarLowerStarAdjunction Ab.{u + 1} f).isMonHom_unitAlgHom R
  haveI : IsMonHom (asIso ρ).inv := inferInstance
  haveI : IsMonHom (((f)_*[Ab.{u + 1}]).map (asIso ρ).inv) :=
    Functor.map.instIsMonHom (F := (f)_*[Ab.{u + 1}]) _ _ (asIso ρ).inv
  exact (pushforwardSectionRingHom f S W).comp
    (sectionRingMap ((upperStarLowerStarAdjunction Ab.{u + 1} f).unit.app R ≫
      ((f)_*[Ab.{u + 1}]).map (asIso ρ).inv) W)

/- Ring operation graphs, proved by transposition through the set adjunction. -/
end AlgebraicGeometry.ProEtale
