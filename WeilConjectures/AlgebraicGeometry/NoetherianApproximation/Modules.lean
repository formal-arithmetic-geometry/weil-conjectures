/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Mathlib.AlgebraicGeometry.AffineTransitionLimit
public import WeilConjectures.AlgebraicGeometry.Modules.DescentEffective
public import WeilConjectures.AlgebraicGeometry.Modules.FiniteDescent
public import WeilConjectures.AlgebraicGeometry.Modules.PreimageGlue
public import WeilConjectures.AlgebraicGeometry.Modules.ZariskiDescent
public import WeilConjectures.AlgebraicGeometry.NoetherianApproximation.ModulesAffine

/-!
# Modules of finite presentation descend to a finite stage of a cofiltered limit

Let `{Dⱼ}` be a cofiltered system of quasi-compact separated schemes with affine transition
morphisms and limit `lim Dⱼ`. Every module of finite presentation on `lim Dⱼ` is the pullback of
a module of finite presentation on some stage `Dⱼ` (Stacks, Tag 01ZR; EGA IV₃, 8.5.2).

## Proof

Fix a stage `S = Dᵢ₀` and a finite affine open cover `U a` of `S`. Over each `U a` the system
`{Dⱼᵢ₀⁻¹ U a}` consists of affine schemes, with limit the preimage of `U a` in `lim Dⱼ`, so the
restriction of the module descends to a module `O a` on some stage
(`AlgebraicGeometry.Scheme.Modules.exists_pullback_iso_of_isLimit_of_isAffine`). Since `S` is
separated, the intersections of the `U a` are affine, so the gluing isomorphisms of the
restrictions on the preimages of `U a ⊓ U b` descend to some stage
(`AlgebraicGeometry.Scheme.Modules.exists_pullHom_eq_of_isLimit_of_isAffine`), and the identity
and cocycle conditions, which hold in the limit, hold at some later stage
(`AlgebraicGeometry.Scheme.Modules.exists_pullHom_eq_pullHom_of_isLimit_of_isAffine`). At that
stage the gluing morphisms define a descent datum for the open cover by the preimages of the
`U a` (`CategoryTheory.Pseudofunctor.DescentData'.ofGlue`), which is effective. The glued
module is of finite presentation, and its pullback to the limit is the original module
(`CategoryTheory.Pseudofunctor.DescentData'.nonempty_map_iso_of_ofGlue`), since morphisms of
modules glue along open covers.
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite Pseudofunctor LocallyDiscreteOpToCat

namespace AlgebraicGeometry

namespace Scheme.Modules

lemma modulesPseudofunctor_pullHom_eq' {X₁ X₂ Y Y' : Scheme.{u}} {M₁ : X₁.Modules}
    {M₂ : X₂.Modules} {f₁ : Y ⟶ X₁} {f₂ : Y ⟶ X₂}
    (φ : (pullback f₁).obj M₁ ⟶ (pullback f₂).obj M₂) (g : Y' ⟶ Y) (gf₁ : Y' ⟶ X₁)
    (gf₂ : Y' ⟶ X₂) (h₁ : g ≫ f₁ = gf₁) (h₂ : g ≫ f₂ = gf₂) :
    pullHom (F := modulesPseudofunctor) φ g gf₁ gf₂ h₁ h₂ =
      (pullbackCompOfEq g f₁ gf₁ h₁ M₁).inv ≫ (pullback g).map φ ≫
        (pullbackCompOfEq g f₂ gf₂ h₂ M₂).hom := by
  subst h₁ h₂
  rw [modulesPseudofunctor_pullHom_eq]
  simp [pullbackCompOfEq, pullbackCongr]

section PullHom

variable {J : Type u} [Category.{u} J] [IsCofiltered J] {E : J ⥤ Scheme.{u}} {c : Cone E}
  [∀ j, IsAffine (E.obj j)]

set_option backward.isDefEq.respectTransparency false in
/-- **Morphisms of modules descend to a finite stage, affine case**, in the form of `pullHom`:
a morphism between the pullbacks to the limit of modules of finite presentation `O₁`, `O₂` along
morphisms factoring through a stage is the pullback of a morphism defined over a later stage. -/
theorem exists_pullHom_eq_of_isLimit_of_isAffine (hc : IsLimit c) {j : J} {W₁ W₂ : Scheme.{u}}
    {O₁ : W₁.Modules} {O₂ : W₂.Modules} [O₁.IsFinitePresentation] [O₂.IsFinitePresentation]
    (x₁ : E.obj j ⟶ W₁) (x₂ : E.obj j ⟶ W₂) {y₁ : c.pt ⟶ W₁} {y₂ : c.pt ⟶ W₂}
    (hy₁ : c.π.app j ≫ x₁ = y₁) (hy₂ : c.π.app j ≫ x₂ = y₂)
    (φ : (modulesPseudofunctor.map y₁.op.toLoc).toFunctor.obj O₁ ⟶
      (modulesPseudofunctor.map y₂.op.toLoc).toFunctor.obj O₂) :
    ∃ (k : J) (t : k ⟶ j)
      (ψ : (modulesPseudofunctor.map (E.map t ≫ x₁).op.toLoc).toFunctor.obj O₁ ⟶
        (modulesPseudofunctor.map (E.map t ≫ x₂).op.toLoc).toFunctor.obj O₂),
      pullHom ψ (c.π.app k) y₁ y₂ (by rw [← hy₁, c.w_assoc]) (by rw [← hy₂, c.w_assoc]) = φ := by
  let φ' : (pullback (c.π.app j)).obj ((pullback x₁).obj O₁) ⟶
      (pullback (c.π.app j)).obj ((pullback x₂).obj O₂) :=
    (modulesPseudofunctor.mapComp' x₁.op.toLoc (c.π.app j).op.toLoc y₁.op.toLoc
        (op_toLoc_comp_eq hy₁)).inv.toNatTrans.app O₁ ≫ φ ≫
      (modulesPseudofunctor.mapComp' x₂.op.toLoc (c.π.app j).op.toLoc y₂.op.toLoc
        (op_toLoc_comp_eq hy₂)).hom.toNatTrans.app O₂
  obtain ⟨k, t, ψ', hψ'⟩ := exists_pullback_map_eq_of_isLimit_of_isAffine' hc φ'
  refine ⟨k, t, (modulesPseudofunctor.mapComp' x₁.op.toLoc (E.map t).op.toLoc
      (E.map t ≫ x₁).op.toLoc (op_toLoc_comp_eq rfl)).hom.toNatTrans.app O₁ ≫ ψ' ≫
    (modulesPseudofunctor.mapComp' x₂.op.toLoc (E.map t).op.toLoc
      (E.map t ≫ x₂).op.toLoc (op_toLoc_comp_eq rfl)).inv.toNatTrans.app O₂, ?_⟩
  refine (pullHom_mapComp'_conj_symm (F := modulesPseudofunctor) x₁ x₂ (E.map t) (E.map t) _ _ rfl
    rfl ψ' (c.π.app k) (c.π.app j) (c.π.app j) (c.w t) (c.w t) y₁ y₂ hy₁ hy₂).trans ?_
  have : pullHom (F := modulesPseudofunctor) ψ' (c.π.app k) (c.π.app j) (c.π.app j) (c.w t)
      (c.w t) = φ' := by
    rw [modulesPseudofunctor_pullHom_eq']
    exact hψ'
  rw [this]
  simp only [φ', Category.assoc, Cat.Hom.hom_inv_id_toNatTrans_app_assoc,
    Cat.Hom.hom_inv_id_toNatTrans_app, Category.comp_id]

/-- **Equalities of morphisms of modules descend to a finite stage, affine case**, in the form
of `pullHom`. -/
theorem exists_pullHom_eq_pullHom_of_isLimit_of_isAffine (hc : IsLimit c) {j : J}
    {W₁ W₂ : Scheme.{u}} {O₁ : W₁.Modules} {O₂ : W₂.Modules} [O₁.IsFinitePresentation]
    [O₂.IsFinitePresentation] (x₁ : E.obj j ⟶ W₁) (x₂ : E.obj j ⟶ W₂) {y₁ : c.pt ⟶ W₁}
    {y₂ : c.pt ⟶ W₂} (hy₁ : c.π.app j ≫ x₁ = y₁) (hy₂ : c.π.app j ≫ x₂ = y₂)
    (ψ₁ ψ₂ : (modulesPseudofunctor.map x₁.op.toLoc).toFunctor.obj O₁ ⟶
      (modulesPseudofunctor.map x₂.op.toLoc).toFunctor.obj O₂)
    (h : pullHom ψ₁ (c.π.app j) y₁ y₂ hy₁ hy₂ = pullHom ψ₂ (c.π.app j) y₁ y₂ hy₁ hy₂) :
    ∃ (k : J) (t : k ⟶ j), pullHom ψ₁ (E.map t) (E.map t ≫ x₁) (E.map t ≫ x₂) rfl rfl =
      pullHom ψ₂ (E.map t) (E.map t ≫ x₁) (E.map t ≫ x₂) rfl rfl := by
  obtain ⟨k, t, ht⟩ := exists_pullback_map_eq_of_isLimit_of_isAffine hc
    (N₁ := (pullback x₁).obj O₁) (N₂ := (pullback x₂).obj O₂) ψ₁ ψ₂
    (map_eq_map_of_pullHom_eq _ _ _ hy₁ hy₂ h)
  exact ⟨k, t, pullHom_eq_pullHom_of_map_eq _ _ _ rfl rfl ht⟩

end PullHom

end Scheme.Modules

end AlgebraicGeometry
