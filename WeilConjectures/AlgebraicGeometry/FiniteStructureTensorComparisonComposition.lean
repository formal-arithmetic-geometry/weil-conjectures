/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.ModulePullbackTensor
public import WeilConjectures.AlgebraicGeometry.TensorPullbackCompositionIso

/-! # Tensor compatibility of the pinned composition comparison

## References

* Stacks Project, Tags 01CD, 0095 and 0096.
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory Opposite

namespace AlgebraicGeometry.Scheme.Modules

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

attribute [local irreducible] tensorPullback tensorPullbackObj

private theorem tensor_hom_ext {S : Scheme.{u}} {M N P : S.Modules}
    {a b : M ⊗ N ⟶ P}
    (h : ∀ (W : S.Opens) (s : Γ(M, W)) (t : Γ(N, W)),
      a.app W (tmulSection s t) = b.app W (tmulSection s t)) : a = b := by
  apply (cancel_epi (SheafOfModules.tensorObjIsoSheafification M N).inv).mp
  apply (PresheafOfModules.sheafificationAdjunction (𝟙 S.ringCatSheaf.obj)).homEquiv _ P
    |>.injective
  apply PresheafOfModules.hom_ext
  intro W
  apply ModuleCat.MonoidalCategory.tensor_ext
  intro s t
  exact h (unop W) s t

private theorem pullback_unit_naturality_sections
    {X S : Scheme.{u}} (g : S ⟶ X) {M N : X.Modules} (a : M ⟶ N)
    (U : X.Opens) (x : Γ(M, U)) :
    ((tensorPullback g).map a).app (g ⁻¹ᵁ U)
        (((Classical.choose (exists_tensorPullbackAdjunction g)).unit.app M).app U x) =
      ((Classical.choose (exists_tensorPullbackAdjunction g)).unit.app N).app U
        (a.app U x) := by
  exact congrArg (fun z ↦ z.app U x)
    ((Classical.choose (exists_tensorPullbackAdjunction g)).unit_naturality a)

private theorem composition_unit_sections
    {X S T : Scheme.{u}} (g : T ⟶ S) (h : S ⟶ X) (M : X.Modules)
    (U : X.Opens) (x : Γ(M, U)) :
    ((tensorPullbackCompositionIso g h (g ≫ h) rfl).inv.app M).app ((g ≫ h) ⁻¹ᵁ U)
      (((Classical.choose (exists_tensorPullbackAdjunction g)).unit.app
        ((tensorPullback h).obj M)).app (h ⁻¹ᵁ U)
        (((Classical.choose (exists_tensorPullbackAdjunction h)).unit.app M).app U x)) =
    ((Classical.choose (exists_tensorPullbackAdjunction (g ≫ h))).unit.app M).app U x := by
  let ah := Classical.choose (exists_tensorPullbackAdjunction h)
  let ag := Classical.choose (exists_tensorPullbackAdjunction g)
  let ak := Classical.choose (exists_tensorPullbackAdjunction (g ≫ h))
  let e := tensorPullbackCompositionIso g h (g ≫ h) rfl
  let q := pushforwardComp g h ≪≫ pushforwardCongr (rfl : g ≫ h = g ≫ h)
  have hu := unit_conjugateEquiv_symm (ah.comp ag) ak q.hom M
  have hu' : (ah.comp ag).unit.app M ≫ q.hom.app _ =
      ak.unit.app M ≫ (pushforward (g ≫ h)).map (e.hom.app M) := by
    simpa only [tensorPullbackCompositionIso, conjugateIsoEquiv_symm_apply_hom,
      ah, ag, ak, q, e] using hu
  have hu'' : (ah.comp ag).unit.app M ≫ q.hom.app _ ≫
      (pushforward (g ≫ h)).map (e.inv.app M) = ak.unit.app M := by
    rw [← Category.assoc, hu', Category.assoc, ← Functor.map_comp,
      e.hom_inv_id_app, CategoryTheory.Functor.map_id]
    exact Category.comp_id _
  have he := congrArg (fun z ↦ z.app U x) hu''
  simp only [Adjunction.comp_unit_app, Hom.comp_app, ConcreteCategory.comp_apply,
    pushforward_map_app, q, Iso.trans_hom, NatTrans.comp_app,
    pushforwardComp_hom_app_app, pushforwardCongr_hom_app_app,
    eqToHom_refl, op_id, CategoryTheory.Functor.map_id] at he
  change (e.inv.app M).app ((g ≫ h) ⁻¹ᵁ U)
    ((ag.unit.app ((tensorPullback h).obj M)).app (h ⁻¹ᵁ U)
      ((ah.unit.app M).app U x)) = (ak.unit.app M).app U x at he
  exact he

/-- The tensor comparisons respect the composition comparison pinned by adjunction mates. -/
theorem finiteStructure_tensorComparison_composition
    {X S T : Scheme.{u}} (g : T ⟶ S) (h : S ⟶ X) (k : T ⟶ X)
    (w : g ≫ h = k) (M N : X.Modules) :
    (tensorPullback g).map (Classical.choose (module_pullback_tensor h) M N).hom ≫
        (Classical.choose (module_pullback_tensor g)
          ((tensorPullback h).obj M) ((tensorPullback h).obj N)).hom ≫
        ((tensorPullbackCompositionIso g h k w).inv.app M ⊗ₘ
          (tensorPullbackCompositionIso g h k w).inv.app N) =
      (tensorPullbackCompositionIso g h k w).inv.app (M ⊗ N) ≫
        (Classical.choose (module_pullback_tensor k) M N).hom  := by
  subst k
  let ah := Classical.choose (exists_tensorPullbackAdjunction h)
  let ag := Classical.choose (exists_tensorPullbackAdjunction g)
  apply (ah.comp ag).homEquiv _ _ |>.injective
  apply tensor_hom_ext
  intro U s t
  let dh := Classical.choose (module_pullback_tensor h) M N
  let dg := Classical.choose (module_pullback_tensor g)
    ((tensorPullback h).obj M) ((tensorPullback h).obj N)
  let dk := Classical.choose (module_pullback_tensor (g ≫ h)) M N
  let c := (tensorPullbackCompositionIso g h (g ≫ h) rfl).inv
  change (c.app M ⊗ₘ c.app N).app ((g ≫ h) ⁻¹ᵁ U)
      (dg.hom.app ((g ≫ h) ⁻¹ᵁ U)
        (((tensorPullback g).map dh.hom).app ((g ≫ h) ⁻¹ᵁ U)
          ((ag.unit.app ((tensorPullback h).obj (M ⊗ N))).app (h ⁻¹ᵁ U)
            ((ah.unit.app (M ⊗ N)).app U (tmulSection s t))))) =
    dk.hom.app ((g ≫ h) ⁻¹ᵁ U)
      ((c.app (M ⊗ N)).app ((g ≫ h) ⁻¹ᵁ U)
        ((ag.unit.app ((tensorPullback h).obj (M ⊗ N))).app (h ⁻¹ᵁ U)
          ((ah.unit.app (M ⊗ N)).app U (tmulSection s t))))
  have hn := pullback_unit_naturality_sections g dh.hom (h ⁻¹ᵁ U)
    ((ah.unit.app (M ⊗ N)).app U (tmulSection s t))
  erw [hn, (Classical.choose_spec (module_pullback_tensor h)).2 M N U s t]
  erw [(Classical.choose_spec (module_pullback_tensor g)).2
    ((tensorPullback h).obj M) ((tensorPullback h).obj N) (h ⁻¹ᵁ U)
    ((ah.unit.app M).app U s) ((ah.unit.app N).app U t)]
  have hh := tensorHom_app_tmulSection (X := T) (c.app M) (c.app N)
    ((ag.unit.app ((tensorPullback h).obj M)).app (h ⁻¹ᵁ U) ((ah.unit.app M).app U s))
    ((ag.unit.app ((tensorPullback h).obj N)).app (h ⁻¹ᵁ U) ((ah.unit.app N).app U t))
  erw [hh, composition_unit_sections g h M U s, composition_unit_sections g h N U t,
    composition_unit_sections g h (M ⊗ N) U (tmulSection s t)]
  exact ((Classical.choose_spec (module_pullback_tensor (g ≫ h))).2 M N U s t).symm

end AlgebraicGeometry.Scheme.Modules
