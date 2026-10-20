/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q17
-/
module
public import Sheaf.SixFunctors.CoefTowerNaturalCurrying
public import WeilConjectures.Algebra.Homology.HomotopyCategory.OplaxMonoidal
public import Mathlib.CategoryTheory.Adjunction.Evaluation

/-! # Normalized tensor evaluation of strict coefficient towers

Source: blueprint main-20261015, integral-dualizing proof, paragraph 2
(blueprint: def-coef-tower-normalized-tensor-evaluation).
-/
@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open scoped MonoidalClosed.FunctorCategory
namespace WeilConjectures.FiniteAdjunctionTransition
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
/-- Ordinary evaluation of strict module towers.
Source: blueprint integral-dualizing proof, paragraph 2
(blueprint: def-coef-tower-normalized-tensor-evaluation). -/
abbrev ordinaryEvaluation (n : ℕ) :=
  (evaluation ℕᵒᵖ (ModuleCat.{u + 1} (coefTraceRing l E))).obj (op n)
/-- Evaluation has the pointwise identity tensor and unit maps.
Source: blueprint integral-dualizing proof, paragraph 2
(blueprint: def-coef-tower-normalized-tensor-evaluation). -/
instance ordinaryEvaluationMonoidal (n : ℕ) : (ordinaryEvaluation l E n).Monoidal :=
  Functor.CoreMonoidal.toMonoidal
    { εIso := Iso.refl _
      μIso := fun _ _ => Iso.refl _ }
/-- The type of finite-level tensor comparison isomorphisms.
Source: blueprint integral-dualizing proof, paragraph 2
(blueprint: def-coef-tower-normalized-tensor-evaluation). -/
abbrev TensorEvaluation (n : ℕ) :=
    coefPairingTensor l E ⋙ coefTraceEvaluation l E n ≅
      (coefTraceEvaluation l E n).prod (coefTraceEvaluation l E n) ⋙
        MonoidalCategory.tensor
          (DerivedCategory (ModuleCat.{u + 1} (coefTraceRing l E)))
/-- Normalization by the actual localization tensor counit and pointwise tensor
map. This fixes a derived comparison, including its sign, before applying any trace.
Source: blueprint integral-dualizing proof, paragraph 2; Stacks 06YY, 0941
(blueprint: def-coef-tower-normalized-tensor-evaluation). -/
def TensorEvaluationNormalized (n : ℕ) (δ : TensorEvaluation l E n) : Prop :=
  ∀ (A B : HomotopyCategory (coefPairingModules l E) (.up ℤ)),
    δ.inv.app (DerivedCategory.Qh.obj A, DerivedCategory.Qh.obj B) ≫
        (coefTraceEvaluation l E n).map (Functor.LaxMonoidal.μ DerivedCategory.Qh A B) =
      ((ordinaryEvaluation l E n).mapDerivedCategoryFactorsh.hom.app A ⊗ₘ
        (ordinaryEvaluation l E n).mapDerivedCategoryFactorsh.hom.app B) ≫
      Functor.LaxMonoidal.μ DerivedCategory.Qh
        ((ordinaryEvaluation l E n).mapHomotopyCategory (.up ℤ) |>.obj A)
        ((ordinaryEvaluation l E n).mapHomotopyCategory (.up ℤ) |>.obj B) ≫
      DerivedCategory.Qh.map (((asIso
        (Functor.OplaxMonoidal.mapHomotopyCategoryδNatTrans (.up ℤ)
          (ordinaryEvaluation l E n))).inv.app A).app B) ≫
      (ordinaryEvaluation l E n).mapDerivedCategoryFactorsh.inv.app (A ⊗ B)
/-- The evaluation tensor comparison is uniquely fixed by its localization
normalization. Source: blueprint integral-dualizing proof, paragraph 2; Stacks 06YY,
0941 (blueprint: def-coef-tower-normalized-tensor-evaluation).
Proof: evaluation is exact and pointwise strong monoidal, with identity tensor map.
It preserves flat towers: compose tensoring by a flat tower with the exact constant
functor and evaluation. Evaluation therefore preserves K-flat complexes. Derive its
identity tensor map on K-flat representatives and use the exact localization
comparison mapDerivedCategoryFactorsh. The derived tensor universal property gives
the displayed equation on arbitrary homotopy complexes. On K-flat representatives
the comparison is invertible. Every derived object has such a representative, so
the comparison is a natural isomorphism. The universal property of the derived
bifunctor makes its inverse unique from the displayed counit equation; an
isomorphism is determined by its inverse. -/
theorem tensorEvaluation_existsUnique (n : ℕ) :
    ∃! δ : TensorEvaluation l E n, TensorEvaluationNormalized l E n δ := by
  sorry
/-- The uniquely normalized evaluation tensor comparison. This choice is from
a theorem determining the isomorphism uniquely, rather than from bare existence.
Source: blueprint integral-dualizing proof, paragraph 2
(blueprint: def-coef-tower-normalized-tensor-evaluation). -/
def canonicalTensorEvaluation (n : ℕ) : TensorEvaluation l E n :=
  (tensorEvaluation_existsUnique l E n).exists.choose
end WeilConjectures.FiniteAdjunctionTransition
