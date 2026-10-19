/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NS
-/
module

public import Mathlib.CategoryTheory.Monoidal.Braided.Basic
public import Mathlib.CategoryTheory.Adjunction.Basic
import Mathlib.CategoryTheory.Yoneda

/-!
# Absolute trace exchange

Source: blueprint main-20261015, `sec-six-functors/sk-thm-sf-package/`
`lem-coef-finite-exceptional.proof.md`, paragraph 1, displayed Hom bijections;
the explicit categorical extraction (blueprint: lem-sf-absolute-trace-exchange).
-/

@[expose] public section

universe uX uY uS vX vY vS

open CategoryTheory CategoryTheory.MonoidalCategory Opposite

namespace CategoryTheory

variable {X : Type uX} {Y : Type uY} {S : Type uS}
  [Category.{vX} X] [Category.{vY} Y] [Category.{vS} S]
  [MonoidalCategory X] [SymmetricCategory X]
  [MonoidalCategory Y] [SymmetricCategory Y]
  {PX : X ⥤ S} {AX : S ⥤ X} {PY : Y ⥤ S} {AY : S ⥤ Y}
  (adjX : PX ⊣ AX) (adjY : PY ⊣ AY) (Ω : S)
  {F : X ⥤ Y} {U : Y ⥤ X} {R : X ⥤ Y} (adj : U ⊣ R)
  (κ : F ⋙ PY ≅ PX)
  (θ : ∀ (M : X) (W : Y), F.obj M ⊗ W ≅ F.obj (M ⊗ U.obj W))
  (DX : Xᵒᵖ ⥤ X) (DY : Yᵒᵖ ⥤ Y)
  (evX : ∀ M : X, DX.obj (op M) ⊗ M ⟶ AX.obj Ω)
  (eX : ∀ W M : X, (W ⟶ DX.obj (op M)) ≃ (W ⊗ M ⟶ AX.obj Ω))
  (eY : ∀ W M : Y, (W ⟶ DY.obj (op M)) ≃ (W ⊗ M ⟶ AY.obj Ω))

/-- The transpose of the absolute trace through compact-support composition.
Source: blueprint `lem-coef-finite-exceptional.proof.md`, paragraph 1, categorical extraction
(blueprint: lem-sf-absolute-trace-exchange). -/
def absoluteTraceExchangeTrace : F.obj (AX.obj Ω) ⟶ AY.obj Ω :=
  adjY.homEquiv _ Ω (κ.hom.app (AX.obj Ω) ≫ adjX.counit.app Ω)

/-- The exchange arrow is the tensor-Hom transpose of symmetry, projection, ordinary
counit, evaluation, and absolute trace, in that order.
Source: blueprint `lem-coef-finite-exceptional.proof.md`, paragraph 1, categorical extraction
(blueprint: lem-sf-absolute-trace-exchange). -/
def absoluteTraceExchangeMap (M : X) :
    R.obj (DX.obj (op M)) ⟶ DY.obj (op (F.obj M)) :=
  (eY _ _).symm
    ((β_ (R.obj (DX.obj (op M))) (F.obj M)).hom ≫
      (θ M (R.obj (DX.obj (op M)))).hom ≫
      F.map (𝟙 M ⊗ₘ adj.counit.app (DX.obj (op M))) ≫
      F.map ((β_ M (DX.obj (op M))).hom ≫ evX M) ≫
      absoluteTraceExchangeTrace adjX adjY Ω κ)

/-- The six-step Hom bijection in the absolute trace exchange lemma.
The middle step transports along `PY(σ ≫ θ) ≫ κ`; the fifth step uses symmetry in `X`.
Source: blueprint `lem-coef-finite-exceptional.proof.md`, paragraph 1, displayed Hom bijections
(blueprint: lem-sf-absolute-trace-exchange). -/
def absoluteTraceExchangeHomEquiv (M : X) (W : Y) :
    (W ⟶ DY.obj (op (F.obj M))) ≃ (W ⟶ R.obj (DX.obj (op M))) :=
  (eY W (F.obj M)).trans
    (((adjY.homEquiv _ Ω).symm).trans
      ((Iso.homFromEquiv
        (PY.mapIso ((β_ W (F.obj M)) ≪≫ θ M W) ≪≫ κ.app (M ⊗ U.obj W))).trans
        ((adjX.homEquiv _ Ω).trans
          ((Iso.homFromEquiv (β_ M (U.obj W))).trans
            (((eX (U.obj W) M).symm).trans (adj.homEquiv W (DX.obj (op M))))))))

/-- Absolute trace exchange, with its precise action on all represented Hom sets.
Source: blueprint `lem-coef-finite-exceptional.proof.md`, paragraph 1, categorical extraction
(blueprint: lem-sf-absolute-trace-exchange).

Proof plan (the seven steps of the DAG node):
1. Naturality of the adjunction bijections identifies their inverse transposes with
   the appropriate counit after functorial image. The trace transpose therefore satisfies
   `PY(τ) ≫ trY = κ ≫ trX`.
2. Reverse the displayed six-step bijection. Starting with `h : W ⟶ R(DX M)`, obtain
   `g = U(h) ≫ ε`, then `b = (1 ⊗ g) ≫ σ ≫ evX`, then its absolute trace,
   then precompose with `PY(σ ≫ θ) ≫ κ`, and transpose twice.
3. Naturality of κ and the trace identity identify the intermediate `PY ⊣ AY`
   transpose with `σ ≫ θ ≫ F(b) ≫ τ`.
4. Naturality of θ and symmetry in W, followed by the tensor bifunctor laws
   (def-sfb-monoidal-category), identify this with `(h ⊗ 1) ≫ λ_M`.
5. Injectivity of the stipulated Y tensor-Hom bijection identifies the final transpose
   with `h ≫ E_M`. This proves the precise Hom clause.
6. For `a : M' ⟶ M`, counit naturality, evaluation naturality, and θ naturality
   identify the two inverse-Hom constructions, proving contravariant naturality of E.
7. The inverse Hom bijection is natural in W; Yoneda full faithfulness
   (lem-galois-yoneda-fully-faithful, Stacks 001P) identifies its inverse with a morphism
   inverse to E. Thus every E_M is an isomorphism.
-/
theorem absoluteTraceExchange
    (evY : ∀ M : Y, DY.obj (op M) ⊗ M ⟶ AY.obj Ω)
    (hX : ∀ (W M : X) (v : W ⟶ DX.obj (op M)),
      eX W M v = (v ⊗ₘ 𝟙 M) ≫ evX M)
    (hY : ∀ (W M : Y) (v : W ⟶ DY.obj (op M)),
      eY W M v = (v ⊗ₘ 𝟙 M) ≫ evY M)
    (hXM : ∀ (M' M : X) (a : M' ⟶ M),
      (DX.map a.op ⊗ₘ 𝟙 M') ≫ evX M' = (𝟙 (DX.obj (op M)) ⊗ₘ a) ≫ evX M)
    (hYM : ∀ (M' M : Y) (a : M' ⟶ M),
      (DY.map a.op ⊗ₘ 𝟙 M') ≫ evY M' = (𝟙 (DY.obj (op M)) ⊗ₘ a) ≫ evY M)
    (hθW : ∀ (M : X) (W W' : Y) (b : W ⟶ W'),
      (𝟙 (F.obj M) ⊗ₘ b) ≫ (θ M W').hom =
        (θ M W).hom ≫ F.map (𝟙 M ⊗ₘ U.map b))
    (hθM : ∀ (M M' : X) (a : M ⟶ M') (W : Y),
      (F.map a ⊗ₘ 𝟙 W) ≫ (θ M' W).hom =
        (θ M W).hom ≫ F.map (a ⊗ₘ 𝟙 (U.obj W))) :
    (∀ M : X, IsIso (absoluteTraceExchangeMap adjX adjY Ω adj κ θ DX DY evX eY M)) ∧
    (∀ (M' M : X) (a : M' ⟶ M),
      R.map (DX.map a.op) ≫ absoluteTraceExchangeMap adjX adjY Ω adj κ θ DX DY evX eY M' =
        absoluteTraceExchangeMap adjX adjY Ω adj κ θ DX DY evX eY M ≫ DY.map (F.map a).op) ∧
    (∀ (M : X) (W : Y) (h : W ⟶ R.obj (DX.obj (op M))),
      (absoluteTraceExchangeHomEquiv adjX adjY Ω adj κ θ DX DY eX eY M W).symm h =
        h ≫ absoluteTraceExchangeMap adjX adjY Ω adj κ θ DX DY evX eY M) := by
  have htrace : PY.map (absoluteTraceExchangeTrace adjX adjY Ω κ) ≫
      adjY.counit.app Ω = κ.hom.app (AX.obj Ω) ≫ adjX.counit.app Ω := by
    exact (adjY.homEquiv _ Ω).symm_apply_apply _
  have htranspose (M : X) (W : Y) (b : M ⊗ U.obj W ⟶ AX.obj Ω) :
      adjY.homEquiv _ Ω
        (PY.map ((β_ W (F.obj M)).hom ≫ (θ M W).hom) ≫
          κ.hom.app (M ⊗ U.obj W) ≫ (adjX.homEquiv _ Ω).symm b) =
        (β_ W (F.obj M)).hom ≫ (θ M W).hom ≫ F.map b ≫
          absoluteTraceExchangeTrace adjX adjY Ω κ := by
    apply (adjY.homEquiv _ Ω).symm.injective
    simp only [Equiv.symm_apply_apply, Adjunction.homEquiv_counit,
      Functor.map_comp, Category.assoc, htrace]
    have hn : PY.map (F.map b) ≫ κ.hom.app (AX.obj Ω) =
        κ.hom.app (M ⊗ U.obj W) ≫ PX.map b := κ.hom.naturality b
    rw [← Category.assoc (PY.map (F.map b)), hn, Category.assoc]
  have hformula (M : X) (W : Y) (h : W ⟶ R.obj (DX.obj (op M))) :
      eY W (F.obj M)
        ((absoluteTraceExchangeHomEquiv adjX adjY Ω adj κ θ DX DY eX eY M W).symm h) =
        (β_ W (F.obj M)).hom ≫ (θ M W).hom ≫
          F.map ((β_ M (U.obj W)).hom ≫
            eX (U.obj W) M ((adj.homEquiv _ _).symm h)) ≫
          absoluteTraceExchangeTrace adjX adjY Ω κ := by
    simpa only [absoluteTraceExchangeHomEquiv, Equiv.symm_trans_apply,
      Equiv.trans_apply, Equiv.symm_symm, Equiv.apply_symm_apply,
      Iso.homFromEquiv, Iso.homToEquiv, Iso.trans_hom, Functor.mapIso_hom, Iso.app_hom,
      Equiv.coe_fn_mk, Equiv.coe_fn_symm_mk, Category.assoc, Functor.map_comp] using
      htranspose M W ((β_ M (U.obj W)).hom ≫
        eX (U.obj W) M ((adj.homEquiv _ _).symm h))
  have hhom (M : X) (W : Y) (h : W ⟶ R.obj (DX.obj (op M))) :
      (absoluteTraceExchangeHomEquiv adjX adjY Ω adj κ θ DX DY eX eY M W).symm h =
        h ≫ absoluteTraceExchangeMap adjX adjY Ω adj κ θ DX DY evX eY M := by
    apply (eY W (F.obj M)).injective
    rw [hformula, hY]
    have heval := (eY _ _).apply_symm_apply
      ((β_ (R.obj (DX.obj (op M))) (F.obj M)).hom ≫
        (θ M (R.obj (DX.obj (op M)))).hom ≫
        F.map (𝟙 M ⊗ₘ adj.counit.app (DX.obj (op M))) ≫
        F.map ((β_ M (DX.obj (op M))).hom ≫ evX M) ≫
        absoluteTraceExchangeTrace adjX adjY Ω κ)
    rw [hY] at heval
    change (absoluteTraceExchangeMap adjX adjY Ω adj κ θ DX DY evX eY M ⊗ₘ
      𝟙 (F.obj M)) ≫ evY (F.obj M) = _ at heval
    rw [← Category.id_comp (𝟙 (F.obj M)), ← tensorHom_comp_tensorHom,
      Category.assoc, heval]
    rw [hX, Adjunction.homEquiv_counit]
    rw [← BraidedCategory.braiding_naturality_assoc]
    have ht : (𝟙 M ⊗ₘ (U.map h ≫ adj.counit.app (DX.obj (op M)))) =
        (𝟙 M ⊗ₘ U.map h) ≫ (𝟙 M ⊗ₘ adj.counit.app (DX.obj (op M))) := by
      simp only [tensorHom_comp_tensorHom, Category.comp_id]
    rw [ht]
    simp only [Functor.map_comp, Category.assoc]
    rw [BraidedCategory.braiding_naturality_assoc]
    rw [← Category.assoc (𝟙 (F.obj M) ⊗ₘ h), hθW]
    simp only [Category.assoc]
  have hb (M' M : X) (a : M' ⟶ M) (W : Y)
      (h : W ⟶ R.obj (DX.obj (op M))) :
      (β_ M' (U.obj W)).hom ≫
          eX (U.obj W) M' ((adj.homEquiv _ _).symm (h ≫ R.map (DX.map a.op))) =
        (a ⊗ₘ 𝟙 (U.obj W)) ≫ (β_ M (U.obj W)).hom ≫
          eX (U.obj W) M ((adj.homEquiv _ _).symm h) := by
    rw [adj.homEquiv_naturality_right_symm, hX, hX]
    rw [← Category.comp_id (𝟙 M'), ← tensorHom_comp_tensorHom, Category.assoc,
      hXM, tensorHom_comp_tensorHom_assoc]
    rw [BraidedCategory.braiding_naturality_assoc]
    rw [← BraidedCategory.braiding_naturality_assoc]
    simp only [tensorHom_comp_tensorHom_assoc, Category.id_comp, Category.comp_id]
    rw [BraidedCategory.braiding_naturality_assoc]
  have hnat (M' M : X) (a : M' ⟶ M) :
      R.map (DX.map a.op) ≫ absoluteTraceExchangeMap adjX adjY Ω adj κ θ DX DY evX eY M' =
        absoluteTraceExchangeMap adjX adjY Ω adj κ θ DX DY evX eY M ≫ DY.map (F.map a).op := by
    let J := R.obj (DX.obj (op M))
    apply (eY J (F.obj M')).injective
    rw [← hhom, hformula, hY]
    rw [← Category.comp_id (𝟙 (F.obj M')), ← tensorHom_comp_tensorHom,
      Category.assoc, hYM, tensorHom_comp_tensorHom_assoc]
    rw [Category.comp_id, Category.id_comp]
    rw [← Category.id_comp
      (absoluteTraceExchangeMap adjX adjY Ω adj κ θ DX DY evX eY M),
      ← Category.comp_id (F.map a), ← tensorHom_comp_tensorHom,
      Category.assoc, ← hY]
    rw [← Category.id_comp
      (absoluteTraceExchangeMap adjX adjY Ω adj κ θ DX DY evX eY M),
      ← hhom, hformula]
    rw [← Category.id_comp (R.map (DX.map a.op)), hb]
    simp only [Functor.map_comp, Category.assoc]
    rw [BraidedCategory.braiding_naturality_assoc]
    rw [← Category.assoc (F.map a ⊗ₘ 𝟙 J), hθM]
    simp only [Category.assoc]
    rfl
  refine ⟨?_, hnat, hhom⟩
  intro M
  apply isIso_of_yoneda_map_bijective
  intro W
  have heq : (fun h : W ⟶ R.obj (DX.obj (op M)) ↦
      h ≫ absoluteTraceExchangeMap adjX adjY Ω adj κ θ DX DY evX eY M) =
      (absoluteTraceExchangeHomEquiv adjX adjY Ω adj κ θ DX DY eX eY M W).symm := by
    funext h
    exact (hhom M W h).symm
  rw [heq]
  exact (absoluteTraceExchangeHomEquiv adjX adjY Ω adj κ θ DX DY eX eY M W).symm.bijective

end CategoryTheory
