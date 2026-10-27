/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group S8
-/
module

public import Sheaf.Paper.SemilinearSystemModels
import Sheaf.Paper.SemilinearSystemIsoAssembly

/-! # Natural isomorphisms from compatible ordinary evaluations

Source: Stacks Project, Tag 0941, strict coefficient systems.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option backward.defeqAttrib.useBackward true
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
universe t u
open CategoryTheory Opposite
namespace WeilConjectures.SemilinearSections

private theorem systemHom_ext
    {C : Type (t + 1)} [Category.{t} C] (J : GrothendieckTopology C)
    [EssentiallySmall.{max u (t + 1)} C]
    (B : ℕ → Sheaf J CommRingCat.{max u (t + 1)}) (τ : ∀ n, B (n + 1) ⟶ B n)
    {M N : SemilinearSections.Systems.{t + 1, t, max u (t + 1)} J B τ} {f g : M ⟶ N}
    (h : ∀ n, (SemilinearSections.evaluation J B τ n).map f =
      (SemilinearSections.evaluation J B τ n).map g) : f = g := by
  ext V x
  exact congrArg (fun k ↦ k.val.app (op V.unop.2) x) (h V.unop.1)

/-- Natural assembly from normalized finite isomorphisms and their transition squares.
Source: Stacks 0941; objectwise assembly followed by naturality.
(blueprint: lem-coef-natural-system-iso-assembly).

Proof: assemble the compatible finite isomorphisms at each object by
systemIsoOfEvaluation_exists. For an arrow of the input category, evaluate both
naturality composites at each coefficient level. The assembly's normalization
reduces them to naturality of the finite comparison. Ordinary evaluation is jointly
faithful, as is seen on every section of the sequence site, so the composites agree.
NatIso.ofComponents then assembles these objectwise isomorphisms naturally. -/
theorem naturalIsoOfEvaluation_exists
    {D : Type*} [Category D]
    {C : Type (t + 1)} [Category.{t} C] (J : GrothendieckTopology C)
    [EssentiallySmall.{max u (t + 1)} C]
    (B : ℕ → Sheaf J CommRingCat.{max u (t + 1)}) (τ : ∀ n, B (n + 1) ⟶ B n)
    (F G : D ⥤ SemilinearSections.Systems.{t + 1, t, max u (t + 1)} J B τ)
    (δ : ∀ n, F ⋙ SemilinearSections.evaluation J B τ n ≅
      G ⋙ SemilinearSections.evaluation J B τ n)
    (ht : ∀ P {m n} (h : n ≤ m),
      (SemilinearSections.transition J B τ h).app (F.obj P) ≫
        (SemilinearSections.res (SemilinearSections.coefficientMap J B τ h)).map
          ((δ n).hom.app P) =
      (δ m).hom.app P ≫ (SemilinearSections.transition J B τ h).app (G.obj P)) :
    ∃ ξ : F ≅ G, ∀ P n,
      (SemilinearSections.evaluation J B τ n).map (ξ.hom.app P) =
        (δ n).hom.app P := by
  classical
  have hex (P : D) : ∃ e : F.obj P ≅ G.obj P, ∀ n,
      (SemilinearSections.evaluation J B τ n).map e.hom = (δ n).hom.app P := by
    refine SemilinearSections.systemIsoOfEvaluation_exists.{t + 1, t, max u (t + 1)}
      J B τ (M := F.obj P) (N := G.obj P) (fun n ↦ (δ n).app P) ?_
    intro m n h
    exact ht P h
  choose e he using hex
  let ξ : F ≅ G := NatIso.ofComponents e (by
    intro P P' f
    apply systemHom_ext J B τ
    intro n
    rw [Functor.map_comp, Functor.map_comp, he, he]
    exact (δ n).hom.naturality f)
  exact ⟨ξ, he⟩

end WeilConjectures.SemilinearSections
