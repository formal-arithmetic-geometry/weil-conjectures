/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.FundamentalGroup.Restriction

/-!
# Elementary paths between fibre functors

A *path* from a geometric point `y` to a geometric point `z` of a scheme `Y` is an isomorphism
`F_y ≅ F_z` of the fibre functors on finite étale `Y`-schemes. This file provides two elementary
sources of paths:

* reparametrising a geometric point `y : Spec Ω ⟶ Y` by an automorphism `a` of `Spec Ω` gives the
  path `F_{a ≫ y} ≅ F_y`, `x ↦ a⁻¹ ≫ x`
  (`AlgebraicGeometry.Scheme.FiniteEtale.fiberReparamIso`);
* a path `τ : F_y ≅ F_z` on `FÉt(X)` is carried by a morphism `f : X ⟶ Y` to a path
  `F_{y ≫ f} ≅ F_{z ≫ f}` on `FÉt(Y)`, through base change of finite étale schemes along `f`
  and the identification of `F_y ∘ f^*` with `F_{y ≫ f}`
  (`AlgebraicGeometry.Scheme.FiniteEtale.pullbackPathIso`).

These are the paths along which the stalks of lisse sheaves are transported in
`WeilConjectures.SixFunctors.ProEtale.Adic.LisseMonodromy`.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme.FiniteEtale

variable {X Y : Scheme.{u}} {Ω : Type u} [Field Ω] [IsSepClosed Ω]

/-- The path `F_{a ≫ y} ≅ F_y` attached to an automorphism `a` of `Spec Ω` and a geometric point
`y : Spec Ω ⟶ Y`: a point `x` of the fibre at `a ≫ y` goes to the point `a⁻¹ ≫ x` of the fibre
at `y`. -/
noncomputable def fiberReparamIso (a : Spec (.of Ω) ≅ Spec (.of Ω)) (y : Spec (.of Ω) ⟶ Y) :
    fiber (a.hom ≫ y) ≅ fiber y :=
  NatIso.ofComponents
    (fun P ↦ FintypeCat.equivEquivIso
      { toFun x := fiberMk y P (a.inv ≫ x.left) (by
          rw [Category.assoc, fiber_left_comp, a.inv_hom_id_assoc])
        invFun x := fiberMk (a.hom ≫ y) P (a.hom ≫ x.left) (by
          rw [Category.assoc, fiber_left_comp])
        left_inv x := fiber_ext _ (by simp)
        right_inv x := fiber_ext _ (by simp) })
    (by
      intro P Q φ
      ext x
      exact fiber_ext y (Category.assoc a.inv x.left φ.hom.left).symm)

@[simp]
lemma fiberReparamIso_hom_app_left (a : Spec (.of Ω) ≅ Spec (.of Ω)) (y : Spec (.of Ω) ⟶ Y)
    (P : Y.FiniteEtale) (x : (fiber (a.hom ≫ y)).obj P) :
    ((fiberReparamIso a y).hom.app P x).left = a.inv ≫ x.left :=
  rfl

@[simp]
lemma fiberReparamIso_inv_app_left (a : Spec (.of Ω) ≅ Spec (.of Ω)) (y : Spec (.of Ω) ⟶ Y)
    (P : Y.FiniteEtale) (x : (fiber y).obj P) :
    ((fiberReparamIso a y).inv.app P x).left = a.hom ≫ x.left :=
  rfl

/-- The path `F_{y ≫ f} ≅ F_{z ≫ f}` on `FÉt(Y)` induced by a path `τ : F_y ≅ F_z` on `FÉt(X)`
and a morphism `f : X ⟶ Y`: `F_{y ≫ f} ≅ F_y ∘ f^* ≅ F_z ∘ f^* ≅ F_{z ≫ f}`. -/
noncomputable def pullbackPathIso (f : X ⟶ Y) {y z : Spec (.of Ω) ⟶ X}
    (τ : fiber y ≅ fiber z) : fiber (y ≫ f) ≅ fiber (z ≫ f) :=
  (pullbackFiberIso f y).symm ≪≫ Functor.isoWhiskerLeft (pullback f) τ ≪≫ pullbackFiberIso f z

lemma pullbackPathIso_refl (f : X ⟶ Y) (y : Spec (.of Ω) ⟶ X) :
    pullbackPathIso f (Iso.refl (fiber y)) = Iso.refl _ := by
  ext P x
  simp [pullbackPathIso]

lemma pullbackPathIso_trans (f : X ⟶ Y) {y z w : Spec (.of Ω) ⟶ X} (τ : fiber y ≅ fiber z)
    (τ' : fiber z ≅ fiber w) :
    pullbackPathIso f (τ ≪≫ τ') = pullbackPathIso f τ ≪≫ pullbackPathIso f τ' := by
  ext P x
  simp [pullbackPathIso]

lemma pullbackPathIso_symm (f : X ⟶ Y) {y z : Spec (.of Ω) ⟶ X} (τ : fiber y ≅ fiber z) :
    pullbackPathIso f τ.symm = (pullbackPathIso f τ).symm := by
  sorry

/-- The path induced by an equality of geometric points is the equality of the images. -/
lemma pullbackPathIso_eqToIso (f : X ⟶ Y) {y z : Spec (.of Ω) ⟶ X} (h : y = z) :
    pullbackPathIso f (eqToIso (congrArg fiber h)) = eqToIso (by rw [h]) := by
  sorry

/-- Transporting a path along equal morphisms. -/
lemma pullbackPathIso_congr {f f' : X ⟶ Y} (hf : f = f') {y z : Spec (.of Ω) ⟶ X}
    (τ : fiber y ≅ fiber z) :
    pullbackPathIso f τ = eqToIso (by rw [hf]) ≪≫ pullbackPathIso f' τ ≪≫ eqToIso (by rw [hf]) := by
  sorry

/-- The path induced along a composite is the iterated induced path. -/
lemma pullbackPathIso_comp {Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) {y z : Spec (.of Ω) ⟶ X}
    (τ : fiber y ≅ fiber z) :
    pullbackPathIso (f ≫ g) τ =
      eqToIso (by rw [Category.assoc]) ≪≫ pullbackPathIso g (pullbackPathIso f τ) ≪≫
        eqToIso (by rw [Category.assoc]) := by
  sorry

/-- The path induced by a reparametrisation path is the reparametrisation path of the image. -/
lemma pullbackPathIso_fiberReparamIso (f : X ⟶ Y) (a : Spec (.of Ω) ≅ Spec (.of Ω))
    (y : Spec (.of Ω) ⟶ X) :
    pullbackPathIso f (fiberReparamIso a y) =
      eqToIso (by rw [Category.assoc]) ≪≫ fiberReparamIso a (y ≫ f) := by
  sorry

/-- A path `τ : F_y ≅ F_z` carries the point of a finite étale `P` on a section `σ` at `y` to the
point on the same section at `z`: naturality with respect to the morphism `Y ⟶ P` of finite
étale `Y`-schemes given by `σ`, the fibres of `Y` itself being points. -/
lemma path_section {y z : Spec (.of Ω) ⟶ Y} (τ : fiber y ≅ fiber z) (P : Y.FiniteEtale)
    (σ : Y ⟶ P.obj.left) (hσ : σ ≫ P.obj.hom = 𝟙 Y) (x : (fiber y).obj P)
    (hx : x.left = y ≫ σ) :
    (τ.hom.app P x).left = z ≫ σ := by
  sorry

end AlgebraicGeometry.Scheme.FiniteEtale
