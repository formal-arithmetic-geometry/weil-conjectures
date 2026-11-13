/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.TensorPullback
public import WeilConjectures.AlgebraicGeometry.Modules.Invertible
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Module
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.CategoryTheory.Abelian.Images
import WeilConjectures.AlgebraicGeometry.ClosedImmersionDisjointIdealTwistMono
import WeilConjectures.AlgebraicGeometry.ClosedImmersionDisjointIdealTwistImage

/-! # Restricting a disjoint ideal times an invertible module

Source: Stacks Project, Varieties Remark 09NW and the local trivialization argument in
Lemma 09NX.
-/

@[expose] public section

universe u
open CategoryTheory MonoidalCategory Limits

namespace AlgebraicGeometry.Scheme.Modules

/-- If an ideal has zero intersection with the ideal of a closed immersion, restriction
identifies its product with an invertible module with the product of its image ideal
and the pulled-back module, for every linear tensor-power comparison `e`
(Stacks, Tags 09NW and 09NX). -/
theorem closedImmersion_disjointIdeal_twist {Y X : Scheme.{u}} (i : X ⟶ Y)
    [IsClosedImmersion i] (I : Y.IdealSheafData)
    (hzero : ∀ U : Y.Opens, I.idealOfOpens U ⊓ i.ker.idealOfOpens U = ⊥)
    (M : Y.Modules) [M.IsInvertible] (m : ℕ)
    (e : (tensorPullback i).obj (M.tensorPow m) ≅
      ((tensorPullback i).obj M).tensorPow m) :
    let adj := Classical.choice (nonempty_tensorPullbackAdjunction i)
    let φ := (adj.homEquiv I.toModules (SheafOfModules.unit X.ringCatSheaf)).symm
      (I.toModulesι ≫ SheafOfModules.unitToPushforwardObjUnit i.toRingCatSheafHom)
    let μ := I.toModulesι ▷ M.tensorPow m ≫ (λ_ (M.tensorPow m)).hom
    let μ₁ := image.ι φ ▷ ((tensorPullback i).obj M).tensorPow m ≫
      (λ_ (((tensorPullback i).obj M).tensorPow m)).hom
    ∃ ρ : image μ ⟶ (pushforward i).obj (image μ₁),
      ρ ≫ (pushforward i).map (image.ι μ₁) = image.ι μ ≫ adj.unit.app (M.tensorPow m) ≫
        (pushforward i).map e.hom ∧ ∀ U : Y.Opens, Function.Bijective (ρ.app U) := by
  dsimp only
  let adj := Classical.choice (nonempty_tensorPullbackAdjunction i)
  let φ := (adj.homEquiv I.toModules (SheafOfModules.unit X.ringCatSheaf)).symm
    (I.toModulesι ≫ SheafOfModules.unitToPushforwardObjUnit i.toRingCatSheafHom)
  let μ := I.toModulesι ▷ M.tensorPow m ≫ (λ_ (M.tensorPow m)).hom
  let μ₁ := image.ι φ ▷ ((tensorPullback i).obj M).tensorPow m ≫
    (λ_ (((tensorPullback i).obj M).tensorPow m)).hom
  let a := image.ι μ ≫ adj.unit.app (M.tensorPow m) ≫ (pushforward i).map e.hom
  let b := (pushforward i).map (image.ι μ₁)
  have : Mono (image.ι μ ≫ adj.unit.app (M.tensorPow m)) :=
    closedImmersion_disjointIdeal_twist_mono i I hzero M m
  have : Mono a := by
    dsimp only [a]
    rw [← Category.assoc]
    infer_instance
  have : Mono b := inferInstance
  have h := closedImmersion_disjointIdeal_twist_image i I M m e
  have hab : Subobject.mk a = Subobject.mk b := by
    simpa only [imageSubobject_mono] using h
  let q := Subobject.isoOfMkEqMk a b hab
  refine ⟨q.hom, ?_, ?_⟩
  · change q.hom ≫ b = a
    simp [q]
  · intro U
    exact (appLinearEquivOfIso q U).bijective

end AlgebraicGeometry.Scheme.Modules
