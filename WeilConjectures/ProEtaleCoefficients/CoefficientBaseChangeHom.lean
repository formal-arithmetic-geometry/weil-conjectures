/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.CoefficientClosedStructure.CoefficientRingedTensorHomModelSupplement
public import Mathlib.CategoryTheory.Monoidal.Closed.Basic

/-! # Evaluation-defined coefficient-Hom comparison

Source: Stacks 08J9, and blueprint def-weil-derived-pullback-tensor-hom,
closed tensor-Hom and scalar-extension paragraphs
(blueprint: def-pur-coefficient-base-change-hom).
This module supplies the abstract definition without the withdrawn coefficient realization.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
universe a b v w
open CategoryTheory MonoidalCategory Opposite

namespace WeilConjectures
/-- The inverse tensor comparison followed by mapped evaluation, transposed in the
supplied target closed structure. No invertibility of this arrow is assumed.
Source: Stacks 08J9 (blueprint: def-pur-coefficient-base-change-hom). -/
def coefficientHomComparison
    {A : Type a} {B : Type b} [Category.{v} A] [Category.{w} B]
    {HA : Aᵒᵖ × A ⥤ A} {HB : Bᵒᵖ × B ⥤ B}
    (SA : CoefficientClosedStructure HA) (SB : CoefficientClosedStructure HB)
    (F : A ⥤ B) (μ : SA.tensor ⋙ F ≅ F.prod F ⋙ SB.tensor) (P Q : A) :
    F.obj (HA.obj (op P, Q)) ⟶ HB.obj (op (F.obj P), F.obj Q) :=
  SB.transpose _ (F.obj P) (F.obj Q)
    (μ.inv.app (HA.obj (op P, Q), P) ≫ F.map (SA.evaluation P Q))

/-- The same transpose construction in the existing left-tensor closed convention.
On symmetric derived tensor categories this is the symmetry transport of the right-
tensor convention above. The tensorator and evaluation are supplied, not chosen.
Source: Stacks 08J9 (blueprint: def-pur-coefficient-base-change-hom). -/
def coefficientHomComparisonLeft
    {A : Type a} {B : Type b} [Category.{v} A] [Category.{w} B]
    [MonoidalCategory A] [MonoidalClosed A] [MonoidalCategory B] [MonoidalClosed B]
    (F : A ⥤ B) (μ : ∀ P Q : A, F.obj (P ⊗ Q) ≅ F.obj P ⊗ F.obj Q) (P Q : A) :
    F.obj ((ihom P).obj Q) ⟶ (ihom (F.obj P)).obj (F.obj Q) :=
  MonoidalClosed.curry ( (μ P ((ihom P).obj Q)).inv ≫ F.map ((ihom.ev P).app Q))
end WeilConjectures
