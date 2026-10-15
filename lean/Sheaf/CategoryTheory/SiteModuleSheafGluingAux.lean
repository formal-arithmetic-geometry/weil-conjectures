/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group C2
-/
module

public import Sheaf.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Module.Equiv.Defs
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
import Sheaf.CategoryTheory.SiteCoveringAxioms

/-! The compatible-tuples construction for module-sheaf gluing.
Source: Stacks Project, Sites, Tag 04TR (blueprint: lem-weil-pbc-site-module-sheaf-gluing-aux).
-/
@[expose] public section
set_option autoImplicit false
universe uC vC uR w v
open CategoryTheory Opposite
namespace SheafOfModules

/-- The explicit compatible-tuples construction yields a module sheaf, local maps and their
inverses.  For an object over `U`, sections are tuples of sections over the base-changed local
objects satisfying the transition equations.  Restrictions and module operations are componentwise.
The sheaf axiom is checked by gluing each component and using separatedness for compatibility.
Evaluation on a local object and extension by the transition maps are inverse by naturality and
the cocycle. Source: Stacks Project, Sites, Tag 04TR
(blueprint: lem-weil-pbc-site-module-sheaf-gluing-aux).
-/
theorem exists_moduleSheaf_of_cover_with_maps
    {C : Type uC} [Category.{vC} C]
    (J : Precoverage C) [J.HasIsos] [J.IsStableUnderComposition]
    [J.IsStableUnderBaseChange] [J.HasPullbacks]
    (U : C) (I : Type w) (Uᵢ : I → Over U)
    (hcover : Presieve.ofArrows (fun i ↦ (Uᵢ i).left) (fun i ↦ (Uᵢ i).hom) ∈ J U)
    (A : Sheaf (J.toGrothendieck.over U) RingCat.{uR})
    (hcomm : ∀ (W : (Over U)ᵒᵖ) (r s : A.obj.obj W), r * s = s * r)
    (Fᵢ : ∀ i : I, ringedSiteModules.{v, uR, vC, max uC vC}
      (A.over (Uᵢ i)))
    (φ : ∀ (i j : I) (W : Over U) (a : W ⟶ Uᵢ i) (b : W ⟶ Uᵢ j),
      (Fᵢ i).val.obj (op (Over.mk (T := Over U) a)) ≃ₗ[A.obj.obj (op W)]
        (Fᵢ j).val.obj (op (Over.mk (T := Over U) b)))
    (hnatural : ∀ (i j : I) (W V : Over U) (k : V ⟶ W)
      (a : W ⟶ Uᵢ i) (b : W ⟶ Uᵢ j) (x : (Fᵢ i).val.obj (op (Over.mk (T := Over U) a))),
      φ i j V (k ≫ a) (k ≫ b) ((Fᵢ i).val.map
        (Over.homMk (U := Over.mk (T := Over U) (k ≫ a))
          (V := Over.mk (T := Over U) a) k rfl).op x) =
        (Fᵢ j).val.map
          (Over.homMk (U := Over.mk (T := Over U) (k ≫ b)) (V := Over.mk (T := Over U) b) k rfl).op
            (φ i j W a b x))
    (hcocycle : ∀ (i j k : I) (W : Over U) (a : W ⟶ Uᵢ i) (b : W ⟶ Uᵢ j) (c : W ⟶ Uᵢ k)
      (x : (Fᵢ i).val.obj (op (Over.mk (T := Over U) a))),
      φ i k W a c x = φ j k W b c (φ i j W a b x)) :
    ∃ F : ringedSiteModules.{v, uR, vC, max uC vC} A,
      ∃ e : ∀ i : I, F.over (Uᵢ i) ⟶ Fᵢ i,
      ∃ e_inv : ∀ i : I, Fᵢ i ⟶ F.over (Uᵢ i),
        (∀ i, e_inv i ≫ e i = 𝟙 _) ∧
        (∀ i, e i ≫ e_inv i = 𝟙 _) ∧
        ∀ (i j : I) (W : Over U) (a : W ⟶ Uᵢ i) (b : W ⟶ Uᵢ j)
          (x : F.val.obj (op W)),
          φ i j W a b ((e i).val.app (op (Over.mk (T := Over U) a)) x) =
            (e j).val.app (op (Over.mk (T := Over U) b)) x := by
  sorry

end SheafOfModules
