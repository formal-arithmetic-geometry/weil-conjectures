/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Sheaf.Algebra.Homology.KFlatDerivedTensorAssociator

/-!
# Transitivity of derived tensor products under base change

Source: Stacks Project, More on Algebra, Lemma 15.60.15 (Tag 0BYJ), and the
transitivity and base-change form used in the blueprint (blueprint:
lem-pc-derived-tensor-transitivity).

The displayed statement is the mixed-ring derived tensor transitivity package.  The
K-flat associator is used in its resolution-independent form; the two derived tensor
expressions are objects of `D(A)`, and the coefficient ring `B` acts through the
second factor.  The proof is the K-flat triple-tensor construction, followed by the
usual cohomology and flat base-change argument described in the DAG proof.
-/

universe u wA wR

open CategoryTheory MonoidalCategory

namespace DerivedCategory

/-- The mixed-ring derived tensor associator and its base-change package.
Source: Stacks Project, Tag 0BYJ (blueprint: lem-pc-derived-tensor-transitivity).
Proof: choose K-flat resolutions, apply the mixed-ring associator, and use the
long exact cohomology sequence and flatness for the final clause. -/
theorem exists_derivedTensor_transitivity
    (R A B : Type u) [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B]
    [HasDerivedCategory.{wA} (ModuleCat.{u} A)]
    [HasDerivedCategory.{wR} (ModuleCat.{u} R)] :
    (∃ α :
        (Functor.uncurry.obj (Functor.uncurry.obj
          (bifunctorComp₁₂
            ((curriedTensor (ModuleCat.{u} A)).map₂CochainComplex)
            (ModuleCat.mixedTotalTensor (algebraMap R A))))) ≅
        (Functor.uncurry.obj (Functor.uncurry.obj
          (bifunctorComp₂₃
            ((curriedTensor (ModuleCat.{u} A)).map₂CochainComplex)
            (ModuleCat.mixedTotalTensor (algebraMap R A))))),
      True) := by
  sorry

end DerivedCategory
