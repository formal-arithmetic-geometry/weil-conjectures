/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Cohomology.ClosedImmersion
public import WeilConjectures.AlgebraicGeometry.Cohomology.PullbackComp

/-!
# Cohomology along a closed immersion commutes with base change
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite TopologicalSpace Abelian

namespace AlgebraicGeometry.Scheme.Modules

variable {W₀ W₁ : Scheme.{u}} (i : W₀ ⟶ W₁) [IsClosedImmersion i] (F : W₀.Modules) (n : ℕ)

attribute [local instance] Scheme.Hom.preservesFiniteColimits_pushforwardAb

/-- `H.pushforwardMap` is the pullback map on the cohomology of the underlying abelian sheaf,
followed by the counit of the adjunction `i^{-1} ⊣ i_♭`. -/
lemma H.pushforwardMap_eq (y : ((pushforward i).obj F).H n) :
    H.pushforwardMap i F n y =
      (Scheme.Hom.H.pullbackAddHom i ((toSheafAb W₁).obj ((pushforward i).obj F)) n y).comp
        (Ext.mk₀ (i.pullbackPushforwardAbAdjunction.counit.app ((toSheafAb W₀).obj F)))
        (add_zero n) := by
  simp only [H.pushforwardMap_apply, H.pushforwardAddEquiv, AddEquiv.symm_trans_apply,
    Ext.precompAddEquiv_symm_apply, Scheme.Hom.H.pullbackAddHom_apply,
    Ext.comp_assoc_of_third_deg_zero]
  refine congrArg (fun z ↦ (Ext.mk₀ (i.pullbackAbConstantSheafIso
      (AddCommGrpCat.of (ULift ℤ))).inv).comp z (zero_add n)) ?_
  exact i.pullbackPushforwardAbAdjunction.extAddEquiv_symm_apply
    ((constantSheaf (Opens.grothendieckTopology W₁) AddCommGrpCat.{u}).obj
      (AddCommGrpCat.of (ULift ℤ))) ((toSheafAb W₀).obj F) n y

/-- The pullback map on the cohomology of a sheaf of modules is the pullback map on the
cohomology of the underlying abelian sheaf, followed by the comparison map. -/
lemma H.pullbackAddHom_eq {X Y : Scheme.{u}} (f : X ⟶ Y) (G : Y.Modules) (m : ℕ) (e : G.H m) :
    H.pullbackAddHom f G m e =
      (Scheme.Hom.H.pullbackAddHom f ((toSheafAb Y).obj G) m e).comp
        (Ext.mk₀ ((pullbackAbComparison f).app G)) (add_zero m) := by
  simp only [H.pullbackAddHom_apply, Scheme.Hom.H.pullbackAddHom_apply,
    Ext.comp_assoc_of_third_deg_zero]

section BaseChange

variable {W'₀ W'₁ : Scheme.{u}} {i₀ : W₀ ⟶ W₁} {g : W'₁ ⟶ W₁} {g₀ : W'₀ ⟶ W₀} {i'₀ : W'₀ ⟶ W'₁}

/-- The key compatibility of the base change morphism of sheaves of modules with the
adjunctions for abelian sheaves. -/
lemma baseChange_key (w : g₀ ≫ i₀ = i'₀ ≫ g) (F : W₀.Modules) :
    eqToHom (congrArg (fun m : W'₀ ⟶ W₁ ↦
        m.pullbackAb.obj ((toSheafAb W₁).obj ((pushforward i₀).obj F))) w) ≫
      (Scheme.Hom.pullbackAbComp i'₀ g).hom.app
          ((toSheafAb W₁).obj ((pushforward i₀).obj F)) ≫
        i'₀.pullbackAb.map ((pullbackAbComparison g).app ((pushforward i₀).obj F) ≫
            (toSheafAb W'₁).map ((baseChange w).natTrans.app F)) ≫
          i'₀.pullbackPushforwardAbAdjunction.counit.app
            ((toSheafAb W'₀).obj ((pullback g₀).obj F)) =
      (Scheme.Hom.pullbackAbComp g₀ i₀).hom.app
          ((toSheafAb W₁).obj ((pushforward i₀).obj F)) ≫
        g₀.pullbackAb.map
            (i₀.pullbackPushforwardAbAdjunction.counit.app ((toSheafAb W₀).obj F)) ≫
          (pullbackAbComparison g₀).app F := by
  sorry

/-- **Cohomology along a closed immersion commutes with base change.** -/
theorem H.pushforwardMap_pullbackAddHom (w : g₀ ≫ i₀ = i'₀ ≫ g)
    [IsClosedImmersion i₀] [IsClosedImmersion i'₀] (F : W₀.Modules) (n : ℕ)
    (y : ((pushforward i₀).obj F).H n) :
    H.pushforwardMap i'₀ ((pullback g₀).obj F) n
        (H.map ((baseChange w).natTrans.app F) n
          (H.pullbackAddHom g ((pushforward i₀).obj F) n y)) =
      H.pullbackAddHom g₀ F n (H.pushforwardMap i₀ F n y) := by
  rw [H.pullbackAddHom_eq, H.map_apply, H.mapAddHom_apply_eq_comp,
    Ext.comp_assoc_of_third_deg_zero, Ext.mk₀_comp_mk₀, H.pushforwardMap_eq,
    Scheme.Hom.H.pullbackAddHom_comp_mk₀, Scheme.Hom.H.pullbackAddHom_comp,
    H.pushforwardMap_eq, H.pullbackAddHom_eq, Scheme.Hom.H.pullbackAddHom_comp_mk₀,
    Scheme.Hom.H.pullbackAddHom_comp]
  simp only [Ext.comp_assoc_of_third_deg_zero, Ext.mk₀_comp_mk₀, Category.assoc]
  rw [← Scheme.Hom.H.pullbackAddHom_eqToHom w, Ext.comp_assoc_of_third_deg_zero,
    Ext.mk₀_comp_mk₀, baseChange_key w F]

end BaseChange

end AlgebraicGeometry.Scheme.Modules
