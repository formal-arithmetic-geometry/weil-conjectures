/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Semilinear.SemilinearOrdinaryInverseSystem
public import WeilConjectures.AlgebraicGeometry.Semilinear.SemilinearOrdinaryDirectSystemMate

/-! # Direct image and transposition on strict systems

Source: Zheng Construction 4.1; Stacks 03D2 and 03DA.
(blueprint: lem-coef-ordinary-direct-system).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option genInjectivity false
set_option genSizeOfSpec false
universe c v r
open CategoryTheory CategoryTheory.Limits Opposite
section
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
namespace WeilConjectures.SemilinearSections
variable {C : Type c} [Category.{v} C] (J : GrothendieckTopology C)
  [EssentiallySmall.{max c v r} C]
  (B : ℕ → Sheaf J CommRingCat.{max c v r}) (τ : ∀ n, B (n + 1) ⟶ B n)
  {C' : Type c} [Category.{v} C'] [EssentiallySmall.{max c v r} C']
  (J' : GrothendieckTopology C')
  (uInv : Sheaf J (Type (max c v r)) ⥤ Sheaf J' (Type (max c v r)))
  (F : ℕ → Sheaf J' CommRingCat.{max c v r}) (σ : ∀ n, F (n + 1) ⟶ F n)
  (I : ∀ n, SheafOfModules.AlgebraicInverseImage uInv (B n) (F n))

attribute [local irreducible] transition coefficientMap systemRing ringPresheaf rings

section ComponentMap
attribute [local semireducible] systemRing ringPresheaf rings

@[irreducible] private def systemHomApp {M N : Systems.{c, v, max c v r} J B τ}
    (f : ∀ n, (evaluation.{c, v, max c v r} J B τ n).obj M ⟶
      (evaluation.{c, v, max c v r} J B τ n).obj N) (X : (ℕ × C)ᵒᵖ) : M.val.obj X ⟶ N.val.obj X :=
  ModuleCat.ofHom {
    toFun := (f X.unop.1).val.app (op X.unop.2)
    map_add' := map_add _
    map_smul' := fun b x ↦ by
      have hh := ((f X.unop.1).val.app (op X.unop.2)).hom.map_smul b x
      have hm := system_evaluation_smul.{c, v, r} J B τ M X.unop.1 (op X.unop.2) b x
      have hn := system_evaluation_smul.{c, v, r} J B τ N X.unop.1 (op X.unop.2) b
        ((f X.unop.1).val.app (op X.unop.2) x)
      exact (congrArg ((f X.unop.1).val.app (op X.unop.2)) hm.symm).trans (hh.trans hn) }

end ComponentMap

@[irreducible] private def systemHomMk {M N : Systems.{c, v, max c v r} J B τ}
    (f : ∀ n, (evaluation.{c, v, max c v r} J B τ n).obj M ⟶
      (evaluation.{c, v, max c v r} J B τ n).obj N)
    (hf : ∀ {m n : ℕ} (h : n ≤ m),
      f m ≫ (transition.{c, v, max c v r} J B τ h).app N =
        (transition.{c, v, max c v r} J B τ h).app M ≫
          (res.{c, v, max c v r} (coefficientMap.{c, v, max c v r} J B τ h)).map (f n)) : M ⟶ N :=
  ⟨{
    app := systemHomApp.{c, v, r} J B τ f
    naturality := fun {X Y} k ↦ by
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro x
      change systemHomApp.{c, v, r} J B τ f Y (M.val.map k x) =
        N.val.map k (systemHomApp.{c, v, r} J B τ f X x)
      simp only [systemHomApp_apply]
      exact systemHom_naturality.{c, v, r} J B τ f hf k x }⟩

attribute [local irreducible] evaluation
attribute [local semireducible] coefficientMap systemRing ringPresheaf rings

variable (P : OrdinaryInverseSystem.{c, v, r} J B τ J' uInv F σ I)
  (V : ∀ n, Mod.{c, v, max c v r} J' (F n) ⥤ Mod.{c, v, max c v r} J (B n))
  (a : ∀ n, (I n).modules ⊣ V n)

end WeilConjectures.SemilinearSections

end
