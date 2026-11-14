/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Standard.StandardSingleBaseChangeMap
import WeilConjectures.AlgebraicGeometry.Standard.StandardSingleBaseChangeTopRestrictionAux

/-! # Removing a redundant top-open restriction from the single comparison

Source: Stacks Project, Tags 08HY and 0D5S.
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry

/-- The canonical single-module comparison is compatible with the top-open isomorphism.
Source: Stacks Project, Tag 08HY, counit description of base change, and Tag 0D5S, composition of
derived pullback. -/
theorem standardSingleBaseChange_topRestriction_comparison
    {Y B A : Scheme.{u}} (p : Y ⟶ B) (M : Y.Modules) (g : A ⟶ B) :
    letI := fun X : Scheme.{u} ↦ HasDerivedCategory.standard
      (SheafOfModules.{u} (moduleRings X.toRingedSpace))
    let j := (⊤ : Y.Opens).ι
    let N := M.restrict j
    ∃ (e : (schemeDerivedDirectImage p).obj
          ((DerivedCategory.singleFunctor _ 0).obj M) ≅
        (schemeDerivedDirectImage (j ≫ p)).obj
          ((DerivedCategory.singleFunctor _ 0).obj N))
      (t : (schemeDerivedDirectImage (pullback.snd (j ≫ p) g)).obj
          ((DerivedCategory.singleFunctor _ 0).obj
            (Scheme.Modules.tensorPullbackObj (pullback.fst (j ≫ p) g) N)) ≅
        (schemeDerivedDirectImage (pullback.snd p g)).obj
          ((DerivedCategory.singleFunctor _ 0).obj
            (Scheme.Modules.tensorPullbackObj (pullback.fst p g) M))),
      standardSingleBaseChangeMap p M g =
        (derivedPullback g).map e.hom ≫
          standardSingleBaseChangeMap (j ≫ p) N g ≫ t.hom := by
  dsimp
  let e := standardSingleBaseChange_topRestriction_sourceIso p M
  exact ⟨e, standardSingleBaseChange_topRestriction_compatibility p M g e rfl⟩

end AlgebraicGeometry
