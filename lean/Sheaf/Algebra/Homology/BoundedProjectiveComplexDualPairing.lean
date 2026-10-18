/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q01
-/
module

public import Sheaf.ZetaWeil.FiniteProjectiveModuleDualPairing
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.Algebra.Homology.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Colimits
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
public import Mathlib.CategoryTheory.Monoidal.Closed.Braided
public import Mathlib.Data.Int.Interval

/-!
# Explicit dual pairing for a bounded finite-projective complex

Source: Stacks Project, More on Algebra, Tag 0FNK, converse of
`lemma-left-dual-complex`, and Tag 0FNJ
(blueprint: lem-zl-bounded-projective-complex-dual-pairing).

The degree identifications are indexed by `n` as `D.X (-n) ≅ Hom(P.X n, A)`.
This avoids dependent casts in the formulas for evaluation and coevaluation.
The monoidal tensor is the signed direct-sum total tensor `mapBifunctor`.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory

namespace CochainComplex

/-- A bounded finite-projective complex has its explicitly specified signed dual and
its evaluation and coevaluation satisfy both triangle identities.

Source: Stacks Project, More on Algebra, Tag 0FNK, converse of
`lemma-left-dual-complex`, with Tag 0FNJ for the dual terms
(blueprint: lem-zl-bounded-projective-complex-dual-pairing).

Proof:
1. Set `D^n = Hom_A(P^(-n), A)`. Its support is `[-b,-a]`. The module dual pairing
   lemma `lem-zl-finite-projective-module-dual-pairing` makes every dual term finite
   projective, including terms outside the support.
2. Define the differential by `(-1)^(n+1)` times precomposition. Two successive
   differentials give minus precomposition with two successive differentials of P,
   which is zero by `def-weil-abstract-derived-category`.
3. Evaluation on the total-degree-zero summands and zero elsewhere commutes with
   the differential: its two terms have coefficients `(-1)^(1-n)` and `(-1)^n`.
   The finite sum of the module coevaluation tensors defines coevaluation.
   In the component `P^(n+1) tensor D^(-n)`, its differential is the sum of
   `(d_P tensor 1)c_n` and `(-1)^(n+1)(1 tensor d_D)c_(n+1)`.
   The module triangle identities give
   `(1 tensor d_D)c_(n+1) = (-1)^n(d_P tensor 1)c_n`, so this sum is zero.
   These calculations use the signed total tensor of `def-pc-tensor-complex-sheaves`.
4. On P^n and D^(-n), the two chain triangle identities reduce to the corresponding
   module identities of `lem-zl-finite-projective-module-dual-pairing`.
   Mixed-degree contributions vanish under evaluation. The canonical associator
   has no sign and the maps have degree zero, so no further signs occur.
5. For the zero complex the sums and maps vanish. For a one-term complex this is
   precisely the ordinary module pairing; no endpoint or characteristic exception arises.
-/
theorem boundedProjectiveComplexDualPairing (A : Type u) [CommRing A]
    (P : CochainComplex (ModuleCat.{u} A) ℤ) (a b : ℤ) (hab : a ≤ b)
    (hP : ∀ n : ℤ, n < a ∨ b < n → IsZero (P.X n))
    [∀ n : ℤ, Module.Finite A (P.X n)] [∀ n : ℤ, Module.Projective A (P.X n)] :
    ∃ (D : CochainComplex (ModuleCat.{u} A) ℤ)
      (e : ∀ n : ℤ, D.X (-n) ≅ ModuleCat.of A (Module.Dual A (P.X n))),
      (∀ n m : ℤ, D.d (-n) (-m) =
        (e n).hom ≫ ModuleCat.ofHom ((-m).negOnePow • (P.d m n).hom.dualMap) ≫
          (e m).inv) ∧
      (∀ n : ℤ, n < -b ∨ -a < n → IsZero (D.X n)) ∧
      (∀ n : ℤ, Module.Finite A (D.X n) ∧ Module.Projective A (D.X n)) ∧
      ∃ (ε : D ⊗ P ⟶ 𝟙_ (CochainComplex (ModuleCat.{u} A) ℤ))
        (η : 𝟙_ (CochainComplex (ModuleCat.{u} A) ℤ) ⟶ P ⊗ D),
        (∀ n : ℤ,
          HomologicalComplex.ιTensorObj D P (-n) n 0 (neg_add_cancel n) ≫ ε.f 0 ≫
              (HomologicalComplex.singleObjXSelf (.up ℤ) 0 (ModuleCat.of A A)).hom =
            (e n).hom ▷ P.X n ≫
              ModuleCat.ofHom (LinearMap.finiteProjectiveEvaluation A (P.X n))) ∧
        (η.f 0 =
          (HomologicalComplex.singleObjXSelf (.up ℤ) 0 (ModuleCat.of A A)).hom ≫
            ∑ n ∈ Finset.Icc a b,
              ModuleCat.ofHom (LinearMap.finiteProjectiveCoevaluation A (P.X n)) ≫
                P.X n ◁ (e n).inv ≫
                  HomologicalComplex.ιTensorObj P D n (-n) 0 (add_neg_cancel n)) ∧
        (∀ n : ℤ, n ≠ 0 → ε.f n = 0 ∧ η.f n = 0) ∧
        ((λ_ P).inv ≫ η ▷ P ≫ (α_ P D P).hom ≫ P ◁ ε ≫ (ρ_ P).hom = 𝟙 P) ∧
        ((ρ_ D).inv ≫ D ◁ η ≫ (α_ D P D).inv ≫ ε ▷ D ≫ (λ_ D).hom = 𝟙 D) := by
  sorry

end CochainComplex
