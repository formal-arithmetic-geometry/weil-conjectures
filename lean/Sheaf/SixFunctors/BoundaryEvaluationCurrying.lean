/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NX
-/
module

public import Sheaf.SixFunctors.BoundaryAlphaNormalization
public import Sheaf.Paper.DualityPairing
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Hom
public import WeilConjectures.SixFunctors.Etale.Derived.TensorStructure
public import Sheaf.Algebra.Homology.OrdinaryModuleDerivedInternalHom
public import Sheaf.AlgebraicGeometry.ProEtaleFiniteModules
public import Sheaf.Paper.IntrinsicFiniteTorsionConstructibility
import Mathlib.CategoryTheory.Yoneda
import WeilConjectures.CategoryTheory.Monoidal.Instances.DerivedCategorySymmetric

/-! # Ringed-site boundary evaluation and opposite currying

Source: current blueprint, cor-weil-boundary-duality-discharge.proof.md,
second paragraph; Stacks Project 08J9, 08JA and 0FPT
(blueprint: lem-weil-boundary-evaluation-currying).

The conclusion predicates spell out internal currying, q naturality and the
opposite-currying identity. All tensor, Hom, evaluation, q and alpha maps are
those of the recorded dependencies. Positive coefficient levels are indexed by n+1.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u v a b
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open scoped CategoryTheory.Functor

namespace CategoryTheory.BoundaryEvaluation

/-- The three-variable internal currying assertion, with the evaluation-normalized
Hom adjunction and involutive signed symmetry. The Hom equivalence in right tensor
order is the given adjunction conjugated by the specified symmetry.
Source: Stacks 08J9, 08JA and 0FPT
(blueprint: lem-weil-boundary-evaluation-currying). -/
def TensorHomCurrying {C : Type a} [Category.{v} C]
    (T : C ⥤ C ⥤ C) (H : Cᵒᵖ ⥤ C ⥤ C) (adj : T ⊣₂ H)
    (σ : T ≅ T.flip)
    (assoc : ∀ X Y Z : C, (T.obj ((T.obj X).obj Y)).obj Z ≅
      (T.obj X).obj ((T.obj Y).obj Z)) : Prop :=
  (∃ e : ∀ B C₀ W : C,
      (H.obj (op B)).obj ((H.obj (op C₀)).obj W) ≅
        (H.obj (op ((T.obj B).obj C₀))).obj W,
    (∀ (B B' C₀ W : C) (f : B' ⟶ B),
      (H.map f.op).app ((H.obj (op C₀)).obj W) ≫ (e B' C₀ W).hom =
        (e B C₀ W).hom ≫ (H.map ((T.map f).app C₀).op).app W) ∧
    (∀ (B C₀ C' W : C) (g : C' ⟶ C₀),
      (H.obj (op B)).map ((H.map g.op).app W) ≫ (e B C' W).hom =
        (e B C₀ W).hom ≫ (H.map ((T.obj B).map g).op).app W) ∧
    (∀ (B C₀ W W' : C) (h : W ⟶ W'),
      (H.obj (op B)).map ((H.obj (op C₀)).map h) ≫ (e B C₀ W').hom =
        (e B C₀ W).hom ≫ (H.obj (op ((T.obj B).obj C₀))).map h) ∧
    (∀ (V B C₀ W : C) (f : V ⟶ (H.obj (op B)).obj ((H.obj (op C₀)).obj W)),
      ((σ.app ((T.obj V).obj B)).app C₀).hom ≫
          ((adj.adj C₀).homEquiv ((T.obj V).obj B) W).symm
            (((σ.app V).app B).hom ≫
              ((adj.adj B).homEquiv V ((H.obj (op C₀)).obj W)).symm f) =
        (assoc V B C₀).hom ≫ ((σ.app V).app ((T.obj B).obj C₀)).hom ≫
          ((adj.adj ((T.obj B).obj C₀)).homEquiv V W).symm (f ≫ (e B C₀ W).hom))) ∧
  (∀ (B C₀ W : C) (f : B ⟶ (H.obj (op C₀)).obj W),
    ((σ.app B).app C₀).hom ≫ ((adj.adj C₀).homEquiv B W).symm f =
      (T.map f).app C₀ ≫
        ((σ.app ((H.obj (op C₀)).obj W)).app C₀).hom ≫
          (adj.adj C₀).counit.app W) ∧
  ∀ B C₀ : C, ((σ.app B).app C₀).hom ≫ ((σ.app C₀).app B).hom = 𝟙 _

/-- The specified evaluation of RHom into W in the source category of the boundary.
This uses the already recorded tensor-Hom counit, in DK tensor K order.
Source: Stacks 08J9 (blueprint: lem-weil-boundary-evaluation-currying). -/
def sourceEvaluation {C : Type a} {D : Type b} [Category.{u} C] [Category.{v} D]
    (d : BoundaryData C D) (W : D) (K : C) :
    (d.P.obj ((d.J.obj (op K)).obj (d.G.obj W))).obj K ⟶ d.G.obj W :=
  ((d.sC.app ((d.J.obj (op K)).obj (d.G.obj W))).app K).hom ≫
    (d.aC.adj K).counit.app (d.G.obj W)

/-- The opposite-currying identity for the specified q and alpha. The two projection
components are proof data for the canonical inverses, not arbitrary comparison arrows.
The biduality map is the transpose of the already recorded evaluation.
Source: boundary-duality discharge proof, second paragraph; Stacks 08J9
(blueprint: lem-weil-boundary-evaluation-currying). -/
def OppositeCurrying {C : Type a} {D : Type b} [Category.{u} C] [Category.{v} D]
    (d : BoundaryData C D) (W L : D)
    (h₁ : IsIso (d.projection (d.G.obj L) ((d.H.obj (op L)).obj W)))
    (h₂ : IsIso (d.projection
      (d.G.obj ((d.H.obj (op ((d.H.obj (op L)).obj W))).obj W))
        ((d.H.obj (op L)).obj W))) : Prop :=
  (d.P.map
    (d.G.map ((d.aD.adj ((d.H.obj (op L)).obj W)).homEquiv L W (d.evaluation W L)) ≫
      d.alpha W ((d.H.obj (op L)).obj W) h₂)).app
        (d.L.obj ((d.H.obj (op L)).obj W)) ≫
      sourceEvaluation d W (d.L.obj ((d.H.obj (op L)).obj W)) =
    ((d.sC.app (d.G.obj L)).app (d.L.obj ((d.H.obj (op L)).obj W))).hom ≫
      d.q ((d.H.obj (op L)).obj W) L h₁ ≫ d.G.map (d.evaluation W L)

section Currying
variable {C : Type a} [Category.{v} C]
  (T : C ⥤ C ⥤ C) (H : Cᵒᵖ ⥤ C ⥤ C) (adj : T ⊣₂ H) (σ : T ≅ T.flip)

private def rightHom (V B W : C) :
    (V ⟶ (H.obj (op B)).obj W) ≃ ((T.obj V).obj B ⟶ W) :=
  ((adj.adj B).homEquiv V W).symm.trans
    (Iso.homCongr ((σ.app V).app B).symm (Iso.refl W))

private theorem rightHom_apply (V B W : C) (f : V ⟶ (H.obj (op B)).obj W) :
    rightHom T H adj σ V B W f =
      ((σ.app V).app B).hom ≫ ((adj.adj B).homEquiv V W).symm f := by
  simp only [rightHom, Equiv.trans_apply, Iso.homCongr_apply, Iso.symm_inv,
    Iso.refl_hom, Category.comp_id]

private theorem rightHom_left {V V' : C} (B W : C)
    (v : V' ⟶ V) (f : V ⟶ (H.obj (op B)).obj W) :
    rightHom T H adj σ V' B W (v ≫ f) =
      (T.map v).app B ≫ rightHom T H adj σ V B W f := by
  simp only [rightHom_apply, Adjunction.homEquiv_naturality_left_symm]
  simpa only [NatTrans.comp_app, Functor.flip_map_app, Iso.app_hom, Category.assoc] using
    congrArg (fun k ↦ k ≫ ((adj.adj B).homEquiv V W).symm f)
      (NatTrans.congr_app (σ.hom.naturality v) B).symm

private theorem rightHom_parameter (V W : C) {B B' : C}
    (b : B' ⟶ B) (f : V ⟶ (H.obj (op B)).obj W) :
    rightHom T H adj σ V B' W (f ≫ (H.map b.op).app W) =
      (T.obj V).map b ≫ rightHom T H adj σ V B W f := by
  simp only [rightHom_apply]
  erw [adj.homEquiv_symm_naturality_one]
  simpa only [Functor.flip_obj_map, Iso.app_hom,
    ParametrizedAdjunction.homEquiv_eq, Category.assoc] using
    congrArg (fun k ↦ k ≫ ((adj.adj B).homEquiv V W).symm f)
      ((σ.hom.app V).naturality b).symm

private theorem rightHom_right (V B : C) {W W' : C}
    (w : W ⟶ W') (f : V ⟶ (H.obj (op B)).obj W) :
    rightHom T H adj σ V B W' (f ≫ (H.obj (op B)).map w) =
      rightHom T H adj σ V B W f ≫ w := by
  simp only [rightHom_apply, Adjunction.homEquiv_naturality_right_symm, Category.assoc]

variable (assoc : ∀ X Y Z : C, (T.obj ((T.obj X).obj Y)).obj Z ≅
  (T.obj X).obj ((T.obj Y).obj Z))

private def curryHom (V B C₀ W : C) :
    (V ⟶ (H.obj (op B)).obj ((H.obj (op C₀)).obj W)) ≃
      (V ⟶ (H.obj (op ((T.obj B).obj C₀))).obj W) :=
  (rightHom T H adj σ V B _).trans
    ((rightHom T H adj σ ((T.obj V).obj B) C₀ W).trans
      ((Iso.homCongr (assoc V B C₀) (Iso.refl W)).trans
        (rightHom T H adj σ V ((T.obj B).obj C₀) W).symm))

private theorem curryHom_eq (V B C₀ W : C)
    (f : V ⟶ (H.obj (op B)).obj ((H.obj (op C₀)).obj W)) :
    rightHom T H adj σ ((T.obj V).obj B) C₀ W (rightHom T H adj σ V B _ f) =
      (assoc V B C₀).hom ≫ rightHom T H adj σ V ((T.obj B).obj C₀) W
        (curryHom T H adj σ assoc V B C₀ W f) := by
  simp only [curryHom, Equiv.trans_apply, Equiv.apply_symm_apply,
    Iso.homCongr_apply, Iso.refl_hom, Category.comp_id, Iso.hom_inv_id_assoc]

variable
  (ha : ∀ (V V' B C₀ : C) (f : V' ⟶ V),
    (T.map ((T.map f).app B)).app C₀ ≫ (assoc V B C₀).hom =
      (assoc V' B C₀).hom ≫ (T.map f).app ((T.obj B).obj C₀))

include ha in
private theorem curryHom_left {V V' : C} (B C₀ W : C) (v : V' ⟶ V)
    (f : V ⟶ (H.obj (op B)).obj ((H.obj (op C₀)).obj W)) :
    curryHom T H adj σ assoc V' B C₀ W (v ≫ f) =
      v ≫ curryHom T H adj σ assoc V B C₀ W f := by
  apply (rightHom T H adj σ V' ((T.obj B).obj C₀) W).injective
  apply (cancel_epi (assoc V' B C₀).hom).mp
  rw [← curryHom_eq, rightHom_left, rightHom_left,
    rightHom_left, ← reassoc_of% ha, ← curryHom_eq]

private def curryIso (B C₀ W : C) :
    (H.obj (op B)).obj ((H.obj (op C₀)).obj W) ≅
      (H.obj (op ((T.obj B).obj C₀))).obj W :=
  Yoneda.ext _ _ (fun {V} ↦ curryHom T H adj σ assoc V B C₀ W)
    (fun {V} ↦ (curryHom T H adj σ assoc V B C₀ W).symm)
    (fun f ↦ Equiv.symm_apply_apply _ f) (fun f ↦ Equiv.apply_symm_apply _ f)
    (fun v f ↦ curryHom_left T H adj σ assoc ha B C₀ W v f)

private theorem curryIso_postcomp (V B C₀ W : C)
    (f : V ⟶ (H.obj (op B)).obj ((H.obj (op C₀)).obj W)) :
    f ≫ (curryIso T H adj σ assoc ha B C₀ W).hom =
      curryHom T H adj σ assoc V B C₀ W f := by
  change f ≫ curryHom T H adj σ assoc _ B C₀ W (𝟙 _) = _
  rw [← curryHom_left T H adj σ assoc ha, Category.comp_id]

private theorem curryIso_hom (B C₀ W : C) :
    (curryIso T H adj σ assoc ha B C₀ W).hom =
      curryHom T H adj σ assoc _ B C₀ W (𝟙 _) := by
  simpa only [Category.id_comp] using curryIso_postcomp T H adj σ assoc ha _ B C₀ W (𝟙 _)

private theorem curryHom_B
    (hb : ∀ (V B B' C₀ : C) (f : B' ⟶ B),
      (T.map ((T.obj V).map f)).app C₀ ≫ (assoc V B C₀).hom =
        (assoc V B' C₀).hom ≫ (T.obj V).map ((T.map f).app C₀))
    (V B B' C₀ W : C) (b : B' ⟶ B)
    (f : V ⟶ (H.obj (op B)).obj ((H.obj (op C₀)).obj W)) :
    curryHom T H adj σ assoc V B' C₀ W
        (f ≫ (H.map b.op).app ((H.obj (op C₀)).obj W)) =
      curryHom T H adj σ assoc V B C₀ W f ≫
        (H.map ((T.map b).app C₀).op).app W := by
  apply (rightHom T H adj σ V ((T.obj B').obj C₀) W).injective
  apply (cancel_epi (assoc V B' C₀).hom).mp
  rw [← curryHom_eq, rightHom_parameter, rightHom_left,
    rightHom_parameter, ← reassoc_of% hb, ← curryHom_eq]

private theorem curryHom_C
    (hc : ∀ (V B C₀ C' : C) (f : C' ⟶ C₀),
      (T.obj ((T.obj V).obj B)).map f ≫ (assoc V B C₀).hom =
        (assoc V B C').hom ≫ (T.obj V).map ((T.obj B).map f))
    (V B C₀ C' W : C) (c : C' ⟶ C₀)
    (f : V ⟶ (H.obj (op B)).obj ((H.obj (op C₀)).obj W)) :
    curryHom T H adj σ assoc V B C' W
        (f ≫ (H.obj (op B)).map ((H.map c.op).app W)) =
      curryHom T H adj σ assoc V B C₀ W f ≫
        (H.map ((T.obj B).map c).op).app W := by
  apply (rightHom T H adj σ V ((T.obj B).obj C') W).injective
  apply (cancel_epi (assoc V B C').hom).mp
  rw [← curryHom_eq, rightHom_right, rightHom_parameter,
    rightHom_parameter, ← reassoc_of% hc, ← curryHom_eq]

private theorem curryHom_W (V B C₀ W W' : C) (w : W ⟶ W')
    (f : V ⟶ (H.obj (op B)).obj ((H.obj (op C₀)).obj W)) :
    curryHom T H adj σ assoc V B C₀ W'
        (f ≫ (H.obj (op B)).map ((H.obj (op C₀)).map w)) =
      curryHom T H adj σ assoc V B C₀ W f ≫
        (H.obj (op ((T.obj B).obj C₀))).map w := by
  apply (rightHom T H adj σ V ((T.obj B).obj C₀) W').injective
  apply (cancel_epi (assoc V B C₀).hom).mp
  rw [← curryHom_eq, rightHom_right, rightHom_right,
    rightHom_right, ← Category.assoc, ← curryHom_eq]

omit assoc ha in
private theorem right_uncurry (B C₀ W : C) (f : B ⟶ (H.obj (op C₀)).obj W) :
    ((σ.app B).app C₀).hom ≫ ((adj.adj C₀).homEquiv B W).symm f =
      (T.map f).app C₀ ≫ ((σ.app ((H.obj (op C₀)).obj W)).app C₀).hom ≫
        (adj.adj C₀).counit.app W := by
  rw [Adjunction.homEquiv_counit]
  simpa only [NatTrans.comp_app, Functor.flip_map_app, Iso.app_hom, Category.assoc] using
    congrArg (fun k ↦ k ≫ (adj.adj C₀).counit.app W)
      (NatTrans.congr_app (σ.hom.naturality f) C₀).symm

include ha in
private theorem tensorHomCurrying_of_natural_associator
    (hb : ∀ (V B B' C₀ : C) (f : B' ⟶ B),
      (T.map ((T.obj V).map f)).app C₀ ≫ (assoc V B C₀).hom =
        (assoc V B' C₀).hom ≫ (T.obj V).map ((T.map f).app C₀))
    (hc : ∀ (V B C₀ C' : C) (f : C' ⟶ C₀),
      (T.obj ((T.obj V).obj B)).map f ≫ (assoc V B C₀).hom =
        (assoc V B C').hom ≫ (T.obj V).map ((T.obj B).map f))
    (hσ : ∀ B C₀, ((σ.app B).app C₀).hom ≫ ((σ.app C₀).app B).hom = 𝟙 _) :
    TensorHomCurrying T H adj σ assoc := by
  refine ⟨⟨curryIso T H adj σ assoc ha, ?_, ?_, ?_, ?_⟩,
    right_uncurry T H adj σ, hσ⟩
  · intro B B' C₀ W f
    rw [curryIso_postcomp, curryIso_hom]
    simpa only [Category.id_comp] using
      curryHom_B T H adj σ assoc hb _ B B' C₀ W f (𝟙 _)
  · intro B C₀ C' W g
    rw [curryIso_postcomp, curryIso_hom]
    simpa only [Category.id_comp] using
      curryHom_C T H adj σ assoc hc _ B C₀ C' W g (𝟙 _)
  · intro B C₀ W W' h
    rw [curryIso_postcomp, curryIso_hom]
    simpa only [Category.id_comp] using
      curryHom_W T H adj σ assoc _ B C₀ W W' h (𝟙 _)
  · intro V B C₀ W f
    simpa only [curryIso_postcomp, rightHom_apply, Category.assoc] using
      curryHom_eq T H adj σ assoc V B C₀ W f
end Currying

private theorem derived_currying
    (C : Type a) [Category.{u + 1} C] [Abelian C]
    [IsGrothendieckAbelian.{u + 1} C] [HasDerivedCategory.{u + 1} C]
    [MonoidalCategory C] [MonoidalPreadditive C] [SymmetricCategory C]
    [MonoidalClosed C] [Abelian.HasFunctorialFlatResolution C] :
    TensorHomCurrying (curriedTensor (DerivedCategory C)) MonoidalClosed.internalHom
      MonoidalClosed.internalHomAdjunction₂ (DerivedCategory.canonicalTensorSymmetry C)
      (fun B C₀ W ↦ α_ B C₀ W) := by
  apply tensorHomCurrying_of_natural_associator
  · intro V V' B C₀ f
    exact associator_naturality_left f B C₀
  · intro V B B' C₀ f
    exact associator_naturality_middle V f C₀
  · intro V B C₀ C' f
    exact associator_naturality_right V B f
  · let : SymmetricCategory (DerivedCategory C) := DerivedCategory.symmetricCategory' C
    intro B C₀
    exact SymmetricCategory.symmetry B C₀

section Boundary
variable {C : Type a} {D : Type b} [Category.{u} C] [Category.{v} D]
  (d : BoundaryData C D)

private theorem q_left (M M' N : D)
    (h : IsIso (d.projection (d.G.obj N) M))
    (h' : IsIso (d.projection (d.G.obj N) M')) (f : M ⟶ M') :
    (d.P.map (d.L.map f)).app (d.G.obj N) ≫ d.q M' N h' =
      d.q M N h ≫ d.G.map ((d.Q.map f).app N) := by
  let := h
  let := h'
  have hp : d.F.map ((d.P.obj (d.G.obj N)).map (d.L.map f)) ≫
      inv (d.projection (d.G.obj N) M') =
      inv (d.projection (d.G.obj N) M) ≫ (d.Q.obj (d.F.obj (d.G.obj N))).map f := by
    apply (cancel_mono (d.projection (d.G.obj N) M')).mp
    simp only [Category.assoc, IsIso.inv_hom_id, Category.comp_id]
    rw [d.projection_right, IsIso.inv_hom_id_assoc]
  unfold BoundaryData.q
  rw [← d.adj.homEquiv_naturality_left, ← d.adj.homEquiv_naturality_right]
  apply (d.adj.homEquiv _ _).congr_arg
  have hs := NatTrans.congr_app (d.sC.hom.naturality (d.L.map f)) (d.G.obj N)
  have ht := (d.sD.hom.app (d.F.obj (d.G.obj N))).naturality f
  have hc := (d.Q.map f).naturality (d.adj.counit.app N)
  dsimp only [Functor.comp_obj, Functor.id_obj] at hc
  dsimp only [NatTrans.comp_app, Functor.flip_obj_map, Functor.flip_map_app] at hs ht
  simp only [Iso.app_hom]
  calc
    _ = d.F.map ((d.sC.hom.app (d.L.obj M)).app (d.G.obj N)) ≫
        d.F.map ((d.P.obj (d.G.obj N)).map (d.L.map f)) ≫
        inv (d.projection (d.G.obj N) M') ≫
        (d.sD.hom.app (d.F.obj (d.G.obj N))).app M' ≫
        (d.Q.obj M').map (d.adj.counit.app N) := by
      simp only [← Functor.map_comp, ← Category.assoc]
      rw [hs]
    _ = _ := by
      simp only [Category.assoc]
      rw [reassoc_of% hp, reassoc_of% ht, ← hc]

private theorem q_right (M N N' : D)
    (h : IsIso (d.projection (d.G.obj N) M))
    (h' : IsIso (d.projection (d.G.obj N') M)) (g : N ⟶ N') :
    (d.P.obj (d.L.obj M)).map (d.G.map g) ≫ d.q M N' h' =
      d.q M N h ≫ d.G.map ((d.Q.obj M).map g) := by
  let := h
  let := h'
  have hp : d.F.map ((d.P.map (d.G.map g)).app (d.L.obj M)) ≫
      inv (d.projection (d.G.obj N') M) =
      inv (d.projection (d.G.obj N) M) ≫ (d.Q.map (d.F.map (d.G.map g))).app M := by
    apply (cancel_mono (d.projection (d.G.obj N') M)).mp
    simp only [Category.assoc, IsIso.inv_hom_id, Category.comp_id]
    rw [d.projection_left, IsIso.inv_hom_id_assoc]
  unfold BoundaryData.q
  rw [← d.adj.homEquiv_naturality_left, ← d.adj.homEquiv_naturality_right]
  apply (d.adj.homEquiv _ _).congr_arg
  have hs := (d.sC.hom.app (d.L.obj M)).naturality (d.G.map g)
  have ht := NatTrans.congr_app (d.sD.hom.naturality (d.F.map (d.G.map g))) M
  have hc := d.adj.counit.naturality g
  dsimp only [Functor.comp_map, Functor.id_map] at hc
  dsimp only [NatTrans.comp_app, Functor.flip_obj_map, Functor.flip_map_app] at hs ht
  simp only [Iso.app_hom]
  calc
    _ = d.F.map ((d.sC.hom.app (d.L.obj M)).app (d.G.obj N)) ≫
        d.F.map ((d.P.map (d.G.map g)).app (d.L.obj M)) ≫
        inv (d.projection (d.G.obj N') M) ≫
        (d.sD.hom.app (d.F.obj (d.G.obj N'))).app M ≫
        (d.Q.obj M).map (d.adj.counit.app N') := by
      simp only [← Functor.map_comp, ← Category.assoc]
      rw [hs]
    _ = _ := by
      simp only [Category.assoc]
      rw [reassoc_of% hp, reassoc_of% ht, ← Functor.map_comp, hc, Functor.map_comp]

private theorem alpha_uncurry (W K : D)
    (h : IsIso (d.projection (d.G.obj ((d.H.obj (op K)).obj W)) K)) :
    ((d.aC.adj (d.L.obj K)).homEquiv _ _).symm (d.alpha W K h) =
      d.q K ((d.H.obj (op K)).obj W) h ≫ d.G.map ((d.aD.adj K).counit.app W) := by
  unfold BoundaryData.alpha boundaryNormalizationMap
  rw [Equiv.symm_apply_apply]
  change ((d.sC.app (d.L.obj K)).app _).hom ≫
    ((d.sC.app _).app (d.L.obj K)).hom ≫ d.q K _ h ≫
      d.G.map (((d.sD.app K).app _).hom ≫
        ((d.sD.app _).app K).hom ≫ (d.aD.adj K).counit.app W) = _
  rw [reassoc_of% d.involutionC, reassoc_of% d.involutionD]

private theorem opposite_currying (W L : D)
    (h₁ : IsIso (d.projection (d.G.obj L) ((d.H.obj (op L)).obj W)))
    (h₂ : IsIso (d.projection
      (d.G.obj ((d.H.obj (op ((d.H.obj (op L)).obj W))).obj W))
        ((d.H.obj (op L)).obj W))) : OppositeCurrying d W L h₁ h₂ := by
  let DL := (d.H.obj (op L)).obj W
  let δ := (d.aD.adj DL).homEquiv L W (d.evaluation W L)
  change (d.P.map (d.G.map δ ≫ d.alpha W DL h₂)).app (d.L.obj DL) ≫
      sourceEvaluation d W (d.L.obj DL) = _
  unfold sourceEvaluation
  rw [← right_uncurry d.P d.J d.aC d.sC]
  rw [Adjunction.homEquiv_naturality_left_symm, alpha_uncurry]
  simp only [Iso.app_hom]
  rw [reassoc_of% (q_right d DL L ((d.H.obj (op DL)).obj W) h₁ h₂ δ)]
  rw [← d.G.map_comp]
  have hd : (d.Q.obj DL).map δ ≫ (d.aD.adj DL).counit.app W = d.evaluation W L := by
    exact ((d.aD.adj DL).homEquiv L W).symm_apply_apply (d.evaluation W L)
  rw [hd]
end Boundary

end CategoryTheory.BoundaryEvaluation

namespace AlgebraicGeometry.Etale

/-- Ordinary unbounded tensor-Hom currying on both sites. All objects, not just
constructible ones, are allowed. Both symmetries are the canonical descended Koszul swaps.
Source: Stacks 08J9, 08JA, 0FPT
(blueprint: lem-weil-boundary-evaluation-currying). -/
def BoundarySiteCurrying (A : Type (u + 1)) [CommRing A] (X : Scheme.{u}) : Prop :=
  CategoryTheory.BoundaryEvaluation.TensorHomCurrying
    (derivedTensor (ModuleCat.{u + 1} A) X) (derivedHom (ModuleCat.{u + 1} A) X)
    (derivedTensorHomAdjunction₂ (ModuleCat.{u + 1} A) X)
    (derivedTensorSymmetry (ModuleCat.{u + 1} A) X)
    (derivedTensorAssociator (ModuleCat.{u + 1} A) X) ∧
  CategoryTheory.BoundaryEvaluation.TensorHomCurrying
    (ProEtale.derivedTensor (ModuleCat.{u + 1} A) X)
    (ProEtale.derivedHom (ModuleCat.{u + 1} A) X)
    (ProEtale.derivedTensorHomAdjunction₂ (ModuleCat.{u + 1} A) X)
    (DerivedCategory.canonicalTensorSymmetry
      (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A)))
    (fun B C₀ W ↦ α_ B C₀ W)

private theorem site_currying (A : Type (u + 1)) [CommRing A] (X : Scheme.{u}) :
    BoundarySiteCurrying A X := by
  constructor
  · exact CategoryTheory.BoundaryEvaluation.derived_currying
      (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A))
  · exact CategoryTheory.BoundaryEvaluation.derived_currying
      (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A))

end AlgebraicGeometry.Etale

namespace CategoryTheory.BoundaryEvaluation

/-- Naturality of q in both parameters and the opposite-currying equality on the
specified admissible classes. This predicate only spells out the theorem's conclusions.
Source: boundary-duality discharge proof, second paragraph
(blueprint: lem-weil-boundary-evaluation-currying). -/
def Conclusions {C : Type a} {D : Type b} [Category.{u} C] [Category.{v} D]
    (d : BoundaryData C D) (W : D) (PT : D → Prop) (PZ : C → Prop)
    (hG : ∀ N, PT N → PZ (d.G.obj N))
    (hD : ∀ N, PT N → PT ((d.H.obj (op N)).obj W))
    (hPF : ∀ B, PZ B → ∀ M, PT M → IsIso (d.projection B M)) : Prop :=
  (∀ (M M' N N' : D) (hM : PT M) (hM' : PT M') (hN : PT N) (hN' : PT N')
      (f : M ⟶ M') (g : N ⟶ N'),
    (d.P.map (d.L.map f)).app (d.G.obj N) ≫
        (d.P.obj (d.L.obj M')).map (d.G.map g) ≫
          d.q M' N' (hPF _ (hG N' hN') _ hM') =
      d.q M N (hPF _ (hG N hN) _ hM) ≫
        d.G.map ((d.Q.map f).app N ≫ (d.Q.obj M').map g)) ∧
  ∀ (L : D) (hL : PT L), OppositeCurrying d W L
    (hPF _ (hG L hL) _ (hD L hL))
    (hPF _ (hG _ (hD _ (hD L hL))) _ (hD L hL))

private theorem conclusions {C : Type a} {D : Type b}
    [Category.{u} C] [Category.{v} D] (d : BoundaryData C D) (W : D)
    (PT : D → Prop) (PZ : C → Prop)
    (hG : ∀ N, PT N → PZ (d.G.obj N))
    (hD : ∀ N, PT N → PT ((d.H.obj (op N)).obj W))
    (hPF : ∀ B, PZ B → ∀ M, PT M → IsIso (d.projection B M)) :
    Conclusions d W PT PZ hG hD hPF := by
  refine ⟨?_, ?_⟩
  · intro M M' N N' hM hM' hN hN' f g
    rw [q_right d M' N N' (hPF _ (hG N hN) _ hM') (hPF _ (hG N' hN') _ hM') g,
      ← Category.assoc, q_left d M M' N
        (hPF _ (hG N hN) _ hM) (hPF _ (hG N hN) _ hM') f,
      Category.assoc, ← d.G.map_comp]
  · intro L hL
    exact opposite_currying d W L _ _

end CategoryTheory.BoundaryEvaluation

namespace AlgebraicGeometry.Etale

/-- Ringed-site currying and exceptional evaluation for a closed immersion, on the
ordinary constant-coefficient derived categories. No inverse of alpha or delta occurs.

Source: current blueprint, cor-weil-boundary-duality-discharge.proof.md, second paragraph;
Stacks Project 08J9, 08JA, 0FPT
(blueprint: lem-weil-boundary-evaluation-currying).

Proof:
1. Apply lem-sf-ringed-derived-closed-symmetric-monoidal on each small site. Its
   evaluation-normalized adjunction gives uncurrying by tensoring with the identity
   and evaluating. The signed swap on degrees a,b has square (-1)^(2ab)=1.
2. Apply tensor-Hom twice to Hom(V,RHom(B,RHom(C,H))), reassociate tensor and
   curry back. The resulting bijection is natural in V,B,C,H. Yoneda full
   faithfulness (lem-galois-yoneda-fully-faithful) supplies the natural internal-Hom iso.
3. The canonical projection map is F(alpha) eta, where alpha is inverse-image
   tensor comparison followed by counit tensor identity. Naturality of the comparison
   (lem-kun-inverse-image-monoidal), unit and counit gives projection naturality.
   Conjugate by symmetry and invert the assumed projection components. Transposing
   inverse projection followed by identity tensor the exceptional counit gives the
   two-variable naturality of q (thm-amb-etale-exceptional-adjoint).
4. Put e_H = ev_H sigma_(H,DH). The definition of delta in lem-weil-duality-pairing
   and the counit identity give ev_DL (delta_L tensor identity) = e_L. Naturality
   and involutivity of symmetry imply e_DL (identity tensor delta_L) = ev_L.
5. Uncurry alpha_DL G(delta_L). Expand r_DL, move G(delta_L) through symmetry,
   and use q naturality for identity_DL and delta_L. Apply step 4 and functoriality
   of G. The result is q_DL,L followed by G(ev_L), precomposed with sigma_(GL,sDL).
   Preservation supplies admissibility of DL and DDL. The codomain is G(omega_T)
   throughout, and only projection-formula components are inverted. -/
theorem boundaryEvaluationCurrying
    (D : WeilConjectures.FiniteFieldDatum.{u})
    (l : ℕ) [Fact l.Prime] (_hl : l ≠ D.p)
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (n : ℕ) {Z T : Scheme.{u}} (aT : T ⟶ Spec (.of D.k))
    [IsSeparated aT] [LocallyOfFiniteType aT] [QuasiCompact aT]
    (i : Z ⟶ T) [IsClosedImmersion i]
    (_hs : ∀ K : DerivedCategoryModule (boundaryCoefficient l E n) T,
      WeilConjectures.finiteTorConstructibleEtale l E (n + 1) (Nat.succ_pos n) T K →
      WeilConjectures.finiteTorConstructibleEtale l E (n + 1) (Nat.succ_pos n) Z
        ((L(upperStar (ModuleCat.{u + 1} (boundaryCoefficient l E n)) i)).obj K))
    (hG : ∀ K : DerivedCategoryModule (boundaryCoefficient l E n) T,
      WeilConjectures.finiteTorConstructibleEtale l E (n + 1) (Nat.succ_pos n) T K →
      WeilConjectures.finiteTorConstructibleEtale l E (n + 1) (Nat.succ_pos n) Z
        ((boundaryG (boundaryCoefficient l E n) i).obj K))
    (hD : ∀ K : DerivedCategoryModule (boundaryCoefficient l E n) T,
      WeilConjectures.finiteTorConstructibleEtale l E (n + 1) (Nat.succ_pos n) T K →
      WeilConjectures.finiteTorConstructibleEtale l E (n + 1) (Nat.succ_pos n) T
        ((boundaryDT (boundaryCoefficient l E n) aT).obj (op K)))
    (_hDZ : ∀ K : DerivedCategoryModule (boundaryCoefficient l E n) Z,
      WeilConjectures.finiteTorConstructibleEtale l E (n + 1) (Nat.succ_pos n) Z K →
      WeilConjectures.finiteTorConstructibleEtale l E (n + 1) (Nat.succ_pos n) Z
        ((boundaryDZ (boundaryCoefficient l E n) i aT).obj (op K)))
    (hPF : ∀ B : DerivedCategoryModule (boundaryCoefficient l E n) Z,
      DerivedCategory.isBoundedConstructible (boundaryCoefficient l E n) Z B →
      ∀ M : DerivedCategoryModule (boundaryCoefficient l E n) T,
      WeilConjectures.finiteTorConstructibleEtale l E (n + 1) (Nat.succ_pos n) T M →
      IsIso (boundaryProjection (boundaryCoefficient l E n) i B M)) :
    BoundarySiteCurrying (boundaryCoefficient l E n) T ∧
    BoundarySiteCurrying (boundaryCoefficient l E n) Z ∧
    CategoryTheory.BoundaryEvaluation.Conclusions
      (boundaryData (boundaryCoefficient l E n) i) (boundaryOmegaT (boundaryCoefficient l E n) aT)
      (WeilConjectures.finiteTorConstructibleEtale l E (n + 1) (Nat.succ_pos n) T)
      (WeilConjectures.finiteTorConstructibleEtale l E (n + 1) (Nat.succ_pos n) Z)
      hG hD (fun B hB M hM ↦ hPF B hB.1 M hM)  := by
  exact ⟨site_currying (boundaryCoefficient l E n) T,
    site_currying (boundaryCoefficient l E n) Z,
    CategoryTheory.BoundaryEvaluation.conclusions
      (boundaryData (boundaryCoefficient l E n) i) _ _ _ hG hD
      (fun B hB M hM ↦ hPF B hB.1 M hM)⟩

end AlgebraicGeometry.Etale
