/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.SecSmoothPurity.CochainCoefficientArrows
import Sheaf.SecSmoothPurity.ModuleTensorGenerators

/-! # The ordinary tensor square for composite pullback

Source: Stacks Project, sites-modules.tex, Tag 03EL, and
sites-cohomology.tex, Tag 07A4.
(blueprint: lem-pur-module-tensor-composition-equation)
-/

@[expose] public section

universe w uC vC uD vD uE vE
open CategoryTheory CategoryTheory.Limits MonoidalCategory
namespace CategoryTheory.CochainPullback
set_option autoImplicit false
set_option linter.checkUnivs false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {C : Type uC} [Category.{vC} C] [EssentiallySmall.{w} C]
  {D : Type uD} [Category.{vD} D] [EssentiallySmall.{w} D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D}
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [K.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  {R : Sheaf J CommRingCat.{w}} {S : Sheaf K CommRingCat.{w}}

variable {E : Type uE} [Category.{vE} E] [EssentiallySmall.{w} E]
  {H : GrothendieckTopology E}
  [H.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  {T : Sheaf H CommRingCat.{w}}

private noncomputable def compositeComparison
    (f : RingedPullback R S) (g : RingedPullback S T) (h : RingedPullback R T)
    (kf : Comparison f) (kg : Comparison g) (kh : Comparison h)
    (a : CompositePresentation f g h kf kg kh) : Comparison h where
  q := kh.q
  q_one := kh.q_one
  mu M N :=
    (compositionModule f g h a.rightModules).app (M ⊗ N) ≪≫
      g.L.mapIso (kf.mu M N) ≪≫ kg.mu (f.L.obj M) (f.L.obj N) ≪≫
        ((compositionModule f g h a.rightModules).app M ⊗ᵢ
          (compositionModule f g h a.rightModules).app N).symm
  naturality := by
    intro M M' N N' b c
    let e := compositionModule f g h a.rightModules
    change h.L.map (b ⊗ₘ c) ≫ e.hom.app (M' ⊗ N') ≫
        g.L.map (kf.mu M' N').hom ≫ (kg.mu (f.L.obj M') (f.L.obj N')).hom ≫
          (e.inv.app M' ⊗ₘ e.inv.app N') =
      e.hom.app (M ⊗ N) ≫ g.L.map (kf.mu M N).hom ≫
        (kg.mu (f.L.obj M) (f.L.obj N)).hom ≫
          (e.inv.app M ⊗ₘ e.inv.app N) ≫ (h.L.map b ⊗ₘ h.L.map c)
    rw [e.hom.naturality_assoc]
    change _ ≫ g.L.map (f.L.map (b ⊗ₘ c)) ≫ _ = _
    rw [← g.L.map_comp_assoc, kf.naturality, g.L.map_comp]
    simp only [Category.assoc]
    rw [← Category.assoc (g.L.map (f.L.map b ⊗ₘ f.L.map c))
      (kg.mu (f.L.obj M') (f.L.obj N')).hom, kg.naturality]
    simp only [Category.assoc]
    rw [tensorHom_comp_tensorHom, tensorHom_comp_tensorHom]
    rw [← e.inv.naturality b, ← e.inv.naturality c]
    rfl
  pure := by
    intro M N Z x y z hz W t
    let e := compositionModule f g h a.rightModules
    let v := ((conjugateIsoEquiv (f.adj.comp g.adj) h.adj).symm
      a.rightSets.symm).hom.app Z
    have hfp : generator f kf z ≫ (underlying S).map (kf.mu M N).hom =
        moduleTensorPair (generator f kf x) (generator f kf y) := by
      apply Sheaf.hom_ext
      ext U s
      exact kf.pure M N Z x y z hz U s
    have hgp := generator_tensorPair g kg (generator f kf x) (generator f kf y)
    have hs (A : Modules R) (z : Z ⟶ (underlying R).obj A) :
        generator h kh z ≫ (underlying T).map (e.hom.app A) =
          v ≫ generator g kg (generator f kf z) := a.scalarAssociation A Z z
    have he : generator h kh z ≫ (underlying T).map
        (e.hom.app (M ⊗ N) ≫ g.L.map (kf.mu M N).hom ≫
          (kg.mu (f.L.obj M) (f.L.obj N)).hom) =
        v ≫ moduleTensorPair (generator g kg (generator f kf x))
          (generator g kg (generator f kf y)) := by
      simp only [Functor.map_comp]
      rw [← Category.assoc (generator h kh z) ((underlying T).map (e.hom.app _)), hs]
      simp only [Category.assoc]
      have hn := generator_naturality g kg (kf.mu M N).hom (generator f kf z)
      have hn' := congrArg (fun s ↦ s ≫
        (underlying T).map (kg.mu (f.L.obj M) (f.L.obj N)).hom) hn.symm
      rw [hfp] at hn'
      exact congrArg (fun s ↦ v ≫ s) (hn'.trans hgp)
    have hh := congrArg (fun s ↦ s.hom.app W t) he
    have hx := congrArg (fun s ↦ s.hom.app W t) (hs M x)
    have hy := congrArg (fun s ↦ s.hom.app W t) (hs N y)
    change (e.hom.app M).val.app W ((generator h kh x).hom.app W t) =
      (generator g kg (generator f kf x)).hom.app W (v.hom.app W t) at hx
    change (e.hom.app N).val.app W ((generator h kh y).hom.app W t) =
      (generator g kg (generator f kf y)).hom.app W (v.hom.app W t) at hy
    change _ = moduleTmul (g.L.obj (f.L.obj M)) (g.L.obj (f.L.obj N)) W
      ((generator g kg (generator f kf x)).hom.app W (v.hom.app W t))
      ((generator g kg (generator f kf y)).hom.app W (v.hom.app W t)) at hh
    have hh' := congrArg (fun s ↦ (e.inv.app M ⊗ₘ e.inv.app N).val.app W s) hh
    have ht := moduleTmul_map (e.inv.app M) (e.inv.app N) W
      ((generator g kg (generator f kf x)).hom.app W (v.hom.app W t))
      ((generator g kg (generator f kf y)).hom.app W (v.hom.app W t))
    have hh'' := hh'.trans ht
    rw [← hx, ← hy] at hh''
    have hm (A : Modules R) (s : (h.L.obj A).val.obj W) :
        (e.inv.app A).val.app W ((e.hom.app A).val.app W s) = s :=
      congrArg (fun z ↦ z.val.app W s) (e.hom_inv_id_app A)
    rw [hm, hm] at hh''
    change ((generator h kh z ≫ (underlying T).map
      (e.hom.app (M ⊗ N) ≫ g.L.map (kf.mu M N).hom ≫
        (kg.mu (f.L.obj M) (f.L.obj N)).hom) ≫
      (underlying T).map (e.inv.app M ⊗ₘ e.inv.app N)).hom.app W) t =
      moduleTmul (h.L.obj M) (h.L.obj N) W
        ((generator h kh x).hom.app W t) ((generator h kh y).hom.app W t)
    exact hh''


/-- The tensor square for ordinary module pullback and its normalized composite.
Source: Stacks 03EL and 0D6D, scalar association for composite pullbacks.
(blueprint: lem-pur-module-tensor-composition-equation).

Proof: precompose with generalized inverse-image pure tensors of M tensor N.
The scalarAssociation field of the composite presentation identifies the
adjunction conjugate with insertion of the two scalar units. Apply the pure
field of each of the three normalized comparisons. Both sides send a tensor
with outside scalar t to (t tensor (1 tensor x)) tensor
(1 tensor (1 tensor y)). Scalars move across by the balanced tensor relation;
associativity of multiplication identifies their products. Scalar-extension
linearity, the sheaf tensor universal property and sheafification extend the
equality to all module sections. Generalized elements are required, so this
argument does not assume enough points or a continuous site functor. It uses
no invertibility of a coefficient map and applies to zero modules and rings. -/
theorem cochainModuleTensorComposition
    {E : Type uE} [Category.{vE} E] [EssentiallySmall.{w} E]
    {H : GrothendieckTopology E}
    [H.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
    {T : Sheaf H CommRingCat.{w}} (f : RingedPullback R S)
    (g : RingedPullback S T) (h : RingedPullback R T)
    (kf : Comparison f) (kg : Comparison g) (kh : Comparison h)
    (a : CompositePresentation f g h kf kg kh)
 :
    ∀ M N : Modules R,
      (kh.mu M N).hom ≫
          ((compositionModule f g h a.rightModules).hom.app M ⊗ₘ
            (compositionModule f g h a.rightModules).hom.app N) =
        (compositionModule f g h a.rightModules).hom.app (M ⊗ N) ≫
          g.L.map (kf.mu M N).hom ≫ (kg.mu (f.L.obj M) (f.L.obj N)).hom  := by
  let := h.finiteLimits
  let := (SheafOfModules.CochainTensorComparison.canonicalRingedTensorComparison_existsUnique
    R T h.RI h.uInv h.I h.coefficient h.L h.hobj h.uPush h.adj h.hmap).2
  have he : compositeComparison f g h kf kg kh a = kh := Subsingleton.elim _ _
  intro M N
  have hm := congrArg (fun k : Comparison h ↦ (k.mu M N).hom) he
  have hh := congrArg (fun z ↦ z ≫
    ((compositionModule f g h a.rightModules).hom.app M ⊗ₘ
      (compositionModule f g h a.rightModules).hom.app N)) hm.symm
  simp only [compositeComparison, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom,
    tensorIso_inv, Iso.app_inv, Category.assoc, tensorHom_comp_tensorHom,
    Iso.inv_hom_id_app, id_tensorHom_id, Iso.app_hom] at hh
  exact hh.trans (congrArg (fun z ↦
    (compositionModule f g h a.rightModules).hom.app (M ⊗ N) ≫
      g.L.map (kf.mu M N).hom ≫ z)
        (Category.comp_id (kg.mu (f.L.obj M) (f.L.obj N)).hom))

end CategoryTheory.CochainPullback
