/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.FieldLinearModuleCohomologyOperations
import WeilConjectures.CategoryTheory.ExtExactFunctorIdentityComparison

/-! # ScalarExtCupInverseImageFirst

## References

* [Stacks Project, Tag 01F7](https://stacks.math.columbia.edu/tag/01F7)
* [Stacks Project, Tag 01FD](https://stacks.math.columbia.edu/tag/01FD)
* [Stacks Project, Tag 07MB](https://stacks.math.columbia.edu/tag/07MB)
* [Stacks Project, Tag 0FKV](https://stacks.math.columbia.edu/tag/0FKV)
-/

@[expose] public section

universe w
set_option autoImplicit false
open CategoryTheory CategoryTheory.MonoidalCategory TopologicalSpace
namespace AlgebraicGeometry.Scheme.Modules
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {k : Type w} [Field k] {X Y : Scheme.{w}}

attribute [local instance] Sheaf.monoidalCategory HasExt.standard

-- Cancel the target unitor in the Ext identity comparison; the source unitors agree.
private theorem rightUnitTransport {Z : Scheme.{w}} {M : KSheaf Z k} {n : ℕ}
    (x : Abelian.Ext.{w + 1} (𝟙_ (KSheaf Z k)) M n) :
    (Abelian.Ext.mk₀ (λ_ (𝟙_ (KSheaf Z k))).inv).comp
      (x.mapExactFunctor (tensorRight (𝟙_ (KSheaf Z k)))) (zero_add n) =
      x.comp (Abelian.Ext.mk₀ (ρ_ M).inv) (add_zero n) := by
  have h := congrArg (fun z : Abelian.Ext.{w + 1}
      ((tensorRight (𝟙_ (KSheaf Z k))).obj (𝟙_ (KSheaf Z k))) M n ↦
      z.comp (Abelian.Ext.mk₀ (ρ_ M).inv) (add_zero n))
    (Abelian.Ext.exactFunctorIdentityComparison
      (tensorRight (𝟙_ (KSheaf Z k))) (rightUnitorNatIso (KSheaf Z k)) x)
  simp only [rightUnitorNatIso, NatIso.ofComponents_hom_app] at h
  simp only [Abelian.Ext.comp_assoc_of_third_deg_zero, Abelian.Ext.mk₀_comp_mk₀,
    Iso.hom_inv_id, Abelian.Ext.comp_mk₀_id] at h
  rw [h]
  rw [← Abelian.Ext.comp_assoc_of_second_deg_zero, Abelian.Ext.mk₀_comp_mk₀]
  rw [← unitors_equal, Iso.inv_hom_id, Abelian.Ext.mk₀_id_comp]

-- Comparing the composite sheaf adjunctions requires unfolding their evaluation functors.
private theorem unitComparison (t : Y ⟶ X) :
    (scalarInverseUnitIso (k := k) t).hom =
      ((Opens.map t.base).sheafAdjunctionContinuous (ModuleCat.{w} k)
        (Opens.grothendieckTopology X)
        (Opens.grothendieckTopology Y)).leftAdjointOplaxMonoidal.η := by
  let cX := constantSheafAdj (Opens.grothendieckTopology X)
    (ModuleCat.{w} k) Limits.isTerminalTop
  let cY := constantSheafAdj (Opens.grothendieckTopology Y)
    (ModuleCat.{w} k) Limits.isTerminalTop
  let adj := (Opens.map t.base).sheafAdjunctionContinuous (ModuleCat.{w} k)
    (Opens.grothendieckTopology X) (Opens.grothendieckTopology Y)
  let b := (cX.comp adj).ofNatIsoRight
    ((Opens.map t.base).sheafPushforwardContinuousCompSheafSectionsObjIso
      (ModuleCat.{w} k) (Opens.grothendieckTopology X)
      (Opens.grothendieckTopology Y) (Opposite.op ⊤))
  rw [← cancel_epi ((scalarInverseImage t).map
    (constantScalarUnitIso (X := X) (k := k)).hom)]
  unfold scalarInverseUnitIso
  dsimp only [scalarInverseImage]
  simp only [Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom,
    ← Functor.map_comp_assoc, Iso.hom_inv_id]
  rw [CategoryTheory.Functor.map_id, Category.id_comp]
  apply (b.homEquiv _ _).injective
  change b.homEquiv _ _ ((b.leftAdjointUniq cY).hom.app (ModuleCat.of k k) ≫
      (constantScalarUnitIso (X := Y) (k := k)).hom) = _
  rw [b.homEquiv_naturality_right, Adjunction.homEquiv_leftAdjointUniq_hom_app]
  erw [← cY.homEquiv_unit]
  change cY.homEquiv _ _ (constantScalarUnitIso (X := Y) (k := k)).hom =
    cX.homEquiv _ _ (adj.homEquiv _ _
      ((scalarInverseImage t).map (constantScalarUnitIso (X := X) (k := k)).hom ≫
        adj.leftAdjointOplaxMonoidal.η))
  erw [adj.homEquiv_naturality_left, Adjunction.leftAdjointOplaxMonoidal_η,
    Equiv.apply_symm_apply]
  erw [cX.homEquiv_naturality_right]
  -- The constant-unit comparison is adjoint to the unit of sheafToPresheaf.
  have hc (Z : Scheme.{w}) :
      (constantSheafAdj (Opens.grothendieckTopology Z) (ModuleCat.{w} k)
        Limits.isTerminalTop).homEquiv _ _ (constantScalarUnitIso (X := Z) (k := k)).hom =
      (Functor.LaxMonoidal.ε
        (sheafToPresheaf (Opens.grothendieckTopology Z) (ModuleCat.{w} k))).app
          (Opposite.op ⊤) := by
    change (constantPresheafAdj (ModuleCat.{w} k) Limits.isTerminalTop).homEquiv _ _
      ((CategoryTheory.sheafificationAdjunction (Opens.grothendieckTopology Z)
        (ModuleCat.{w} k)).homEquiv _ _
          (Functor.OplaxMonoidal.η
            (presheafToSheaf (Opens.grothendieckTopology Z) (ModuleCat.{w} k)))) = _
    erw [(CategoryTheory.sheafificationAdjunction
      (Opens.grothendieckTopology Z) (ModuleCat.{w} k)).homEquiv_unit,
      Adjunction.unit_app_unit_comp_map_η]
    rfl
  rw [hc Y, hc X]
  exact (Functor.ε_sheafToPresheaf_app_comp_ε_sheafPushforwardContinuous_app
    (Opens.map t.base) (ModuleCat.{w} k) (Opens.grothendieckTopology X)
      (Opens.grothendieckTopology Y) (Opposite.op ⊤)).symm

-- Normalize the inverse-image functor before applying monoidal coherence.
/-- Compatibility of the first tensor transport with exact inverse image.
-/
theorem scalarExtCup_inverseImage_first (t : Y ⟶ X)
    (A : KSheaf X k) (A' : KSheaf Y k)
    (φ : (scalarInverseImage t).obj A ⟶ A') (p : ℕ)
    (a : Abelian.Ext.{w + 1} (𝟙_ (KSheaf X k)) A p) :
    ((Abelian.Ext.mk₀ (scalarInverseUnitIso t).inv).comp
      (((Abelian.Ext.mk₀ (λ_ (𝟙_ (KSheaf X k))).inv).comp
        (a.mapExactFunctor (tensorRight (𝟙_ (KSheaf X k))))
          (zero_add p)).mapExactFunctor (scalarInverseImage t)) (zero_add p)).comp
      (Abelian.Ext.mk₀ (((Opens.map t.base).sheafAdjunctionContinuous (ModuleCat.{w} k)
          (Opens.grothendieckTopology X) (Opens.grothendieckTopology Y)).leftAdjointOplaxMonoidal.δ
        A (𝟙_ (KSheaf X k)) ≫ (φ ⊗ₘ (scalarInverseUnitIso t).hom))) (add_zero p) =
    (Abelian.Ext.mk₀ (λ_ (𝟙_ (KSheaf Y k))).inv).comp
      ((((Abelian.Ext.mk₀ (scalarInverseUnitIso t).inv).comp
        (a.mapExactFunctor (scalarInverseImage t)) (zero_add p)).comp
          (Abelian.Ext.mk₀ φ) (add_zero p)).mapExactFunctor
            (tensorRight (𝟙_ (KSheaf Y k)))) (zero_add p) := by
  rw [rightUnitTransport a, Abelian.Ext.mapExactFunctor_comp,
    Abelian.Ext.mapExactFunctor_mk₀, rightUnitTransport]
  simp only [Abelian.Ext.comp_assoc_of_third_deg_zero, Abelian.Ext.mk₀_comp_mk₀]
  have h : (scalarInverseImage t).map (ρ_ A).inv ≫
      ((Opens.map t.base).sheafAdjunctionContinuous (ModuleCat.{w} k)
        (Opens.grothendieckTopology X) (Opens.grothendieckTopology Y)).leftAdjointOplaxMonoidal.δ
          A (𝟙_ (KSheaf X k)) ≫ (φ ⊗ₘ (scalarInverseUnitIso t).hom) =
      φ ≫ (ρ_ A').inv := by
    let adj := (Opens.map t.base).sheafAdjunctionContinuous (ModuleCat.{w} k)
      (Opens.grothendieckTopology X) (Opens.grothendieckTopology Y)
    let : (scalarInverseImage (k := k) t).OplaxMonoidal := adj.leftAdjointOplaxMonoidal
    have hu : (scalarInverseUnitIso (k := k) t).hom =
        Functor.OplaxMonoidal.η (scalarInverseImage t) := unitComparison t
    dsimp only [scalarInverseImage] at hu φ ⊢
    rw [hu, tensorHom_def', ← Functor.OplaxMonoidal.right_unitality_assoc]
    exact (rightUnitor_inv_naturality φ).symm
  rw [h]

end
end AlgebraicGeometry.Scheme.Modules
