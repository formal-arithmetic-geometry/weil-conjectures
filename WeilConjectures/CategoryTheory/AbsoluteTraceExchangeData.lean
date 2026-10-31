/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.CategoryTheory.Monoidal.Braided.Basic
public import Mathlib.CategoryTheory.Adjunction.Basic

/-! # Canonical absolute trace and exchange constructions

Source: blueprint latest, sec-six-functors/sk-thm-sf-package/
lem-coef-finite-exceptional.proof.md, paragraphs 1 and 2, the displayed Hom
bijections and the evaluation, projection and counit transposes.
(blueprint: def-sf-absolute-trace-exchange-data)

These are the three original definitions extracted without changing their names,
signatures or bodies from the absolute trace exchange theorem module.
-/

@[expose] public section

set_option autoImplicit false

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
(blueprint: def-sf-absolute-trace-exchange-data). -/
def absoluteTraceExchangeTrace : F.obj (AX.obj Ω) ⟶ AY.obj Ω :=
  adjY.homEquiv _ Ω (κ.hom.app (AX.obj Ω) ≫ adjX.counit.app Ω)

/-- The exchange arrow is the tensor-Hom transpose of symmetry, projection, ordinary
counit, evaluation, and absolute trace, in that order.
Source: blueprint `lem-coef-finite-exceptional.proof.md`, paragraph 1, categorical extraction
(blueprint: def-sf-absolute-trace-exchange-data). -/
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
(blueprint: def-sf-absolute-trace-exchange-data). -/
def absoluteTraceExchangeHomEquiv (M : X) (W : Y) :
    (W ⟶ DY.obj (op (F.obj M))) ≃ (W ⟶ R.obj (DX.obj (op M))) :=
  (eY W (F.obj M)).trans
    (((adjY.homEquiv _ Ω).symm).trans
      ((Iso.homFromEquiv
        (PY.mapIso ((β_ W (F.obj M)) ≪≫ θ M W) ≪≫ κ.app (M ⊗ U.obj W))).trans
        ((adjX.homEquiv _ Ω).trans
          ((Iso.homFromEquiv (β_ M (U.obj W))).trans
            (((eX (U.obj W) M).symm).trans (adj.homEquiv W (DX.obj (op M))))))))

end CategoryTheory
