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
  sorry

end CategoryTheory
