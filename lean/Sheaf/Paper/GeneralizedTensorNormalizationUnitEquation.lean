/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.CategoryTheory.SiteCoveringAxioms
public import Sheaf.CategoryTheory.AlgebraicInverseImageOfUniverses
public import Sheaf.CategoryTheory.RingedSiteModules
public import Sheaf.Paper.RingedTopoiTensorComparisonData
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
import Mathlib.CategoryTheory.Sites.CartesianMonoidal

/-! # Generalized tensor normalization and the geometric unit

Source: Stacks Project, Modules on Sites, Tag 03EL,
lemma-tensor-product-pullback, third Hom/bilinear equality.
(blueprint: lem-pd-generalized-tensor-normalization-unit-equation)
-/

@[expose] public section

universe w uC vC uD vD
open CategoryTheory CategoryTheory.Limits MonoidalCategory
namespace SheafOfModules

attribute [local irreducible] monoidalCategory changeOfRings
attribute [local irreducible] PresheafOfModules.sheafification tensorObjIsoSheafification
attribute [local irreducible] PresheafOfModules.sheafificationAdjunction
attribute [local irreducible] ringedComparisonPure ringedComparisonScalarSection
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private theorem normalization_comparison_natural
    {P Q : Type*} [Category* P] [Category* Q]
    [MonoidalCategory P] [MonoidalCategory Q]
    (L : P ⥤ Q) [L.Monoidal]
    {A A' B B' : P} {X X' Y Y' : Q}
    (e : L.obj A ≅ X) (e' : L.obj A' ≅ X')
    (d : L.obj B ≅ Y) (d' : L.obj B' ≅ Y')
    (a : A ⟶ A') (b : B ⟶ B') (f : X ⟶ X') (g : Y ⟶ Y')
    (hf : f ≫ e'.inv = e.inv ≫ L.map a)
    (hg : g ≫ d'.inv = d.inv ≫ L.map b) :
    (f ⊗ₘ g) ≫ (e'.inv ⊗ₘ d'.inv) ≫ Functor.LaxMonoidal.μ L A' B' =
      (e.inv ⊗ₘ d.inv) ≫ Functor.LaxMonoidal.μ L A B ≫ L.map (a ⊗ₘ b) := by
  rw [← Category.assoc, tensorHom_comp_tensorHom, hf, hg,
    ← tensorHom_comp_tensorHom, Category.assoc, Functor.LaxMonoidal.μ_natural]

section TensorSections
variable {C : Type uC} [Category.{vC} C] [EssentiallySmall.{w} C]
  {J : GrothendieckTopology C} (R : Sheaf J CommRingCat.{w})

private theorem normalization_pure_restrict (M N : SheafOfModules.{w}
      ((sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).obj R))
    {U V : Cᵒᵖ} (i : U ⟶ V) (m : M.val.obj U) (n : N.val.obj U) :
    ((monoidalCategory R).tensorObj M N).val.map i (ringedComparisonPure R M N U m n) =
      ringedComparisonPure R M N V (M.val.map i m) (N.val.map i n) := by
  unfold ringedComparisonPure
  let adj := PresheafOfModules.sheafificationAdjunction.{w}
    (R := (sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).obj R) (𝟙 _)
  let t := m ⊗ₜ[R.obj.obj U] n
  have hi := PresheafOfModules.naturality_apply
    (tensorObjIsoSheafification (R := R) M N).inv.val i ((adj.unit.app (M.val ⊗ N.val)).app U t)
  have hu := PresheafOfModules.naturality_apply (adj.unit.app (M.val ⊗ N.val)) i t
  exact hi.symm.trans (congrArg ((tensorObjIsoSheafification (R := R) M N).inv.val.app V) hu.symm)

private theorem normalization_pure_hom_ext (M N H : SheafOfModules.{w}
      ((sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).obj R))
    {f g : (monoidalCategory R).tensorObj M N ⟶ H}
    (h : ∀ U m n, f.val.app U (ringedComparisonPure R M N U m n) =
      g.val.app U (ringedComparisonPure R M N U m n)) : f = g := by
  unfold ringedComparisonPure at h
  let adj := PresheafOfModules.sheafificationAdjunction.{w}
    (R := (sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).obj R) (𝟙 _)
  apply (cancel_epi (tensorObjIsoSheafification (R := R) M N).inv).mp
  apply (adj.homEquiv (M.val ⊗ N.val) H).injective
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
  apply PresheafOfModules.hom_ext
  intro U
  apply ModuleCat.MonoidalCategory.tensor_ext
  intro m n
  exact h U m n

set_option maxHeartbeats 800000 in
-- Keep the localization comparison abstract when using its naturality on sections.
private theorem normalization_tensor_iso_natural
    {M M' N N' : SheafOfModules.{w}
      ((sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).obj R)}
    (f : M ⟶ M') (g : N ⟶ N') :
    (monoidalCategory R).tensorHom f g ≫ (tensorObjIsoSheafification (R := R) M' N').hom =
      (tensorObjIsoSheafification (R := R) M N).hom ≫
        (PresheafOfModules.sheafification.{w}
          (R := (sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).obj R) (𝟙 _)).map
            (f.val ⊗ₘ g.val) := by
  let := monoidalCategory R
  let a := PresheafOfModules.sheafification.{w}
    (R := (sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).obj R) (𝟙 _)
  let adj := PresheafOfModules.sheafificationAdjunction.{w}
    (R := (sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).obj R) (𝟙 _)
  let e := asIso adj.counit
  have hf := e.inv.naturality f
  have hg := e.inv.naturality g
  change f ≫ (e.app M').inv = (e.app M).inv ≫ a.map f.val at hf
  change g ≫ (e.app N').inv = (e.app N).inv ≫ a.map g.val at hg
  unfold tensorObjIsoSheafification
  change (f ⊗ₘ g) ≫ ((e.app M').inv ⊗ₘ (e.app N').inv) ≫
      Functor.LaxMonoidal.μ a M'.val N'.val =
    ((e.app M).inv ⊗ₘ (e.app N).inv) ≫
      Functor.LaxMonoidal.μ a M.val N.val ≫ a.map (f.val ⊗ₘ g.val)
  exact normalization_comparison_natural a
    (show a.obj M.val ≅ M from e.app M) (show a.obj M'.val ≅ M' from e.app M')
    (show a.obj N.val ≅ N from e.app N) (show a.obj N'.val ≅ N' from e.app N')
    f.val g.val f g hf hg

set_option maxHeartbeats 800000 in
-- Naturality compares the localized tensor with the sheafification tensorator.
private theorem normalization_pure_map {M M' N N' : SheafOfModules.{w}
      ((sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).obj R)}
    (f : M ⟶ M') (g : N ⟶ N') (U : Cᵒᵖ) (m : M.val.obj U) (n : N.val.obj U) :
    ((monoidalCategory R).tensorHom f g).val.app U (ringedComparisonPure R M N U m n) =
      ringedComparisonPure R M' N' U (f.val.app U m) (g.val.app U n) := by
  unfold ringedComparisonPure
  let := monoidalCategory R
  let a := PresheafOfModules.sheafification.{w}
    (R := (sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).obj R) (𝟙 _)
  let adj := PresheafOfModules.sheafificationAdjunction.{w}
    (R := (sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).obj R) (𝟙 _)
  have hi : (tensorObjIsoSheafification (R := R) M N).inv ≫ (f ⊗ₘ g) =
      a.map (f.val ⊗ₘ g.val) ≫ (tensorObjIsoSheafification (R := R) M' N').inv := by
    rw [Iso.inv_comp_eq, ← Category.assoc, ← normalization_tensor_iso_natural R, Category.assoc,
      Iso.hom_inv_id, Category.comp_id]
  have hu := congrArg (fun k ↦ k.app U (m ⊗ₜ[R.obj.obj U] n))
    (adj.unit.naturality (f.val ⊗ₘ g.val))
  have hv := congrArg (fun k ↦ k.val.app U
    ((adj.unit.app (M.val ⊗ N.val)).app U (m ⊗ₜ[R.obj.obj U] n))) hi
  exact hv.trans (congrArg ((tensorObjIsoSheafification (R := R) M' N').inv.val.app U) hu.symm)

end TensorSections

set_option maxHeartbeats 800000 in
-- Elaborating the generalized section formulas compares several sheafification interfaces.
/-- Generalized pure-tensor normalization implies compatibility with the geometric unit.
Source: Stacks Project, Modules on Sites, Tag 03EL, third Hom/bilinear equality.
(blueprint: lem-pd-generalized-tensor-normalization-unit-equation)

Proof:
1. Take the test sheaf Z to be the product of the underlying sheaves of M and N.
   Pairs of matching sections glue componentwise. Its projections x and y and the
   canonical pure-tensor map z satisfy the test equation, by
   lem-pc-sites-sheaf-tensor-bilinear-universal.
2. For sections m and n over U, apply the geometric unit of Z to (m,n).
   Naturality for x, y and z identifies their inverse images on this section with
   the geometric units of m, n and their pure tensor. Pushforward is precomposition,
   so these are equalities over v(U).
3. Evaluate hnormalize at this section. The formula heta identifies its left side
   with P(mu)(eta(m tensor n)), and its right side with the S-pure tensor of
   eta(m) and eta(n).
4. Tensoring the two linear units sends a pure tensor to their R-pure tensor;
   hpairing then sends this to the same S-pure tensor. Both composites are R-linear.
   Injectivity in lem-pc-sites-sheaf-tensor-bilinear-universal gives equality of
   sheaf maps. This does not require all sections of a sheaf tensor to be pure. -/
theorem generalizedTensorNormalization_unit_equation
    {C : Type uC} {D : Type uD} [Category.{vC} C] [Category.{vD} D]
    [EssentiallySmall.{w} C] [EssentiallySmall.{w} D]
    (JC : GrothendieckTopology C) (JD : GrothendieckTopology D)
    (v : C ⥤ D) [v.IsContinuous JC JD]
    (R : Sheaf JC CommRingCat.{w}) (A S : Sheaf JD CommRingCat.{w})
    (F : Sheaf JC (Type w) ⥤ Sheaf JD (Type w))
    (adj : F ⊣ v.sheafPushforwardContinuous (Type w) JC JD)
    [PreservesFiniteLimits F]
    (I : AlgebraicInverseImageOfUniverses.{uC, vC, uD, vD, w, w} F R A)
    (α : A ⟶ S)
    (c : ((sheafCompose JC (forget₂ CommRingCat.{w} RingCat.{w})).obj R) ⟶
      (v.sheafPushforwardContinuous RingCat.{w} JC JD).obj
        ((sheafCompose JD (forget₂ CommRingCat.{w} RingCat.{w})).obj S))
    (hc : ∀ (U : Cᵒᵖ) (r : R.obj.obj U),
      ULift.up (c.hom.app U r) =
        (adj.homEquiv _ _ (I.ringUnderlying.hom ≫
          (sheafCompose JD (CategoryTheory.forget CommRingCat.{w} ⋙
            uliftFunctor.{w, w})).map α)).hom.app U (ULift.up r))
    (η : ∀ X : SheafOfModules.{w}
      ((sheafCompose JC (forget₂ CommRingCat.{w} RingCat.{w})).obj R),
      X ⟶ (pushforward.{w, vC, vD, uC, uD, w} (J := JC) (K := JD) (F := v) c).obj
        (changeOfRings.{vD, uD, w} (J := JD) (R₁ := A) (R₂ := S) α (I.modules.obj X)))
    (heta : ∀ (X : SheafOfModules.{w}
      ((sheafCompose JC (forget₂ CommRingCat.{w} RingCat.{w})).obj R))
      (U : Cᵒᵖ) (x : X.val.obj U),
      (η X).val.app U x =
        ringedComparisonScalarSection.{w, uD, vD} (J := JD) (A := A) (B := S) α (I.modules.obj X)
        (v.op.obj U) 1
        (((I.moduleUnderlying.inv.app X).hom.app (v.op.obj U)
          ((adj.unit.app ((toSheaf
            ((sheafCompose JC (forget₂ CommRingCat.{w} RingCat.{w})).obj R) ⋙
        sheafCompose JC
            (CategoryTheory.forget AddCommGrpCat.{w} ⋙ uliftFunctor.{w, w})).obj X)).hom.app
              U (ULift.up x))).down))
    (M N : SheafOfModules.{w} ((sheafCompose JC (forget₂ CommRingCat.{w} RingCat.{w})).obj R))
    (p : (monoidalCategory.{vC, uC, w} (J := JC) R).tensorObj
      ((pushforward.{w, vC, vD, uC, uD, w} (J := JC) (K := JD) (F := v) c).obj
        (changeOfRings.{vD, uD, w} (J := JD) (R₁ := A) (R₂ := S) α (I.modules.obj M)))
      ((pushforward.{w, vC, vD, uC, uD, w} (J := JC) (K := JD) (F := v) c).obj
        (changeOfRings.{vD, uD, w} (J := JD) (R₁ := A) (R₂ := S) α
            (I.modules.obj N))) ⟶
      (pushforward.{w, vC, vD, uC, uD, w} (J := JC) (K := JD) (F := v) c).obj
      ((monoidalCategory.{vD, uD, w} (J := JD) S).tensorObj
        (changeOfRings.{vD, uD, w} (J := JD) (R₁ := A) (R₂ := S) α (I.modules.obj M))
        (changeOfRings.{vD, uD, w} (J := JD) (R₁ := A) (R₂ := S) α
            (I.modules.obj N))))
    (hpairing : ∀ (U : Cᵒᵖ)
      (m : ((pushforward.{w, vC, vD, uC, uD, w} (J := JC) (K := JD) (F := v) c).obj
        (changeOfRings.{vD, uD, w} (J := JD) (R₁ := A) (R₂ := S) α (I.modules.obj M))).val.obj U)
      (n : ((pushforward.{w, vC, vD, uC, uD, w} (J := JC) (K := JD) (F := v) c).obj
        (changeOfRings.{vD, uD, w} (J := JD) (R₁ := A) (R₂ := S) α
            (I.modules.obj N))).val.obj U),
      p.val.app U (ringedComparisonPure.{w, uC, vC} (J := JC) R
        ((pushforward.{w, vC, vD, uC, uD, w} (J := JC) (K := JD) (F := v) c).obj
          (changeOfRings.{vD, uD, w} (J := JD) (R₁ := A) (R₂ := S) α (I.modules.obj M)))
        ((pushforward.{w, vC, vD, uC, uD, w} (J := JC) (K := JD) (F := v) c).obj
          (changeOfRings.{vD, uD, w} (J := JD) (R₁ := A) (R₂ := S) α
            (I.modules.obj N))) U m n) =
        ringedComparisonPure.{w, uD, vD} (J := JD) S
          (changeOfRings.{vD, uD, w} (J := JD) (R₁ := A) (R₂ := S) α (I.modules.obj M))
          (changeOfRings.{vD, uD, w} (J := JD) (R₁ := A) (R₂ := S) α
            (I.modules.obj N)) (v.op.obj U) m n)
    (μ : changeOfRings.{vD, uD, w} (J := JD) (R₁ := A) (R₂ := S) α
      (I.modules.obj ((monoidalCategory.{vC, uC, w} (J := JC) R).tensorObj M N)) ⟶
      (monoidalCategory.{vD, uD, w} (J := JD) S).tensorObj
        (changeOfRings.{vD, uD, w} (J := JD) (R₁ := A) (R₂ := S) α (I.modules.obj M))
        (changeOfRings.{vD, uD, w} (J := JD) (R₁ := A) (R₂ := S) α
            (I.modules.obj N)))
    (hnormalize : ∀ (Z : Sheaf JC (Type w))
      (x : Z ⟶ (toSheaf ((sheafCompose JC (forget₂ CommRingCat.{w} RingCat.{w})).obj R) ⋙
        sheafCompose JC
        (CategoryTheory.forget AddCommGrpCat.{w} ⋙ uliftFunctor.{w, w})).obj M)
      (y : Z ⟶ (toSheaf ((sheafCompose JC (forget₂ CommRingCat.{w} RingCat.{w})).obj R) ⋙
        sheafCompose JC
        (CategoryTheory.forget AddCommGrpCat.{w} ⋙ uliftFunctor.{w, w})).obj N)
      (z : Z ⟶ (toSheaf ((sheafCompose JC (forget₂ CommRingCat.{w} RingCat.{w})).obj R) ⋙
        sheafCompose JC
        (CategoryTheory.forget AddCommGrpCat.{w} ⋙ uliftFunctor.{w, w})).obj
          ((monoidalCategory.{vC, uC, w} (J := JC) R).tensorObj M N)),
      (∀ (U : Cᵒᵖ) (t : Z.obj.obj U),
        (z.hom.app U t).down = ringedComparisonPure.{w, uC, vC} (J := JC) R M N U
          (x.hom.app U t).down (y.hom.app U t).down) →
      ∀ (V : Dᵒᵖ) (t : (F.obj Z).obj.obj V),
        μ.val.app V
          (ringedComparisonScalarSection.{w, uD, vD} (J := JD) (A := A) (B := S) α
            (I.modules.obj ((monoidalCategory.{vC, uC, w} (J := JC) R).tensorObj M N)) V 1
            (((I.moduleUnderlying.inv.app
              ((monoidalCategory.{vC, uC, w} (J := JC) R).tensorObj M N)).hom.app V
              ((F.map z).hom.app V t)).down)) =
        ringedComparisonPure.{w, uD, vD} (J := JD) S
          (changeOfRings.{vD, uD, w} (J := JD) (R₁ := A) (R₂ := S) α (I.modules.obj M))
          (changeOfRings.{vD, uD, w} (J := JD) (R₁ := A) (R₂ := S) α
            (I.modules.obj N)) V
          (ringedComparisonScalarSection.{w, uD, vD} (J := JD) (A := A) (B := S) α
            (I.modules.obj M) V 1
            (((I.moduleUnderlying.inv.app M).hom.app V ((F.map x).hom.app V t)).down))
          (ringedComparisonScalarSection.{w, uD, vD} (J := JD) (A := A) (B := S) α
            (I.modules.obj N) V 1
            (((I.moduleUnderlying.inv.app N).hom.app V ((F.map y).hom.app V t)).down))) :
    η ((monoidalCategory.{vC, uC, w} (J := JC) R).tensorObj M N) ≫
      (pushforward.{w, vC, vD, uC, uD, w} (J := JC) (K := JD) (F := v) c).map μ =
      (monoidalCategory.{vC, uC, w} (J := JC) R).tensorHom (η M) (η N) ≫ p := by
  have := hc
  let T := (monoidalCategory.{vC, uC, w} R).tensorObj M N
  let underlying := toSheaf
    ((sheafCompose JC (forget₂ CommRingCat.{w} RingCat.{w})).obj R) ⋙
    sheafCompose JC (CategoryTheory.forget AddCommGrpCat.{w} ⋙ uliftFunctor.{w, w})
  let Z : Sheaf JC (Type w) := underlying.obj M ⊗ underlying.obj N
  let x : Z ⟶ underlying.obj M := CartesianMonoidalCategory.fst _ _
  let y : Z ⟶ underlying.obj N := CartesianMonoidalCategory.snd _ _
  let z : Z ⟶ underlying.obj T :=
    ⟨{ app := fun U ↦ ↾(fun t ↦ ULift.up
          (ringedComparisonPure R M N U t.1.down t.2.down))
       naturality := by
         intro U V i
         ext t
         exact congrArg ULift.up (normalization_pure_restrict R M N i _ _).symm }⟩
  have hz : ∀ (U : Cᵒᵖ) (t : Z.obj.obj U),
      (z.hom.app U t).down = ringedComparisonPure R M N U
        (x.hom.app U t).down (y.hom.app U t).down := fun _ _ ↦ rfl
  apply normalization_pure_hom_ext R M N
  intro U m n
  let t : Z.obj.obj U := (ULift.up m, ULift.up n)
  let ξ := (adj.unit.app Z).hom.app U t
  have hx := congrArg (fun k ↦ k.hom.app U t) (adj.unit.naturality x)
  have hy := congrArg (fun k ↦ k.hom.app U t) (adj.unit.naturality y)
  have hz' := congrArg (fun k ↦ k.hom.app U t) (adj.unit.naturality z)
  change (adj.unit.app (underlying.obj M)).hom.app U (ULift.up m) =
    (F.map x).hom.app (v.op.obj U) ξ at hx
  change (adj.unit.app (underlying.obj N)).hom.app U (ULift.up n) =
    (F.map y).hom.app (v.op.obj U) ξ at hy
  change (adj.unit.app (underlying.obj T)).hom.app U
      (ULift.up (ringedComparisonPure R M N U m n)) =
    (F.map z).hom.app (v.op.obj U) ξ at hz'
  have h := hnormalize Z x y z hz (v.op.obj U) ξ
  rw [← hx, ← hy, ← hz', ← heta, ← heta, ← heta] at h
  change μ.val.app (v.op.obj U) ((η T).val.app U
      (ringedComparisonPure R M N U m n)) =
    p.val.app U (((monoidalCategory.{vC, uC, w} R).tensorHom (η M) (η N)).val.app U
      (ringedComparisonPure R M N U m n))
  rw [normalization_pure_map, hpairing]
  exact h

end SheafOfModules
