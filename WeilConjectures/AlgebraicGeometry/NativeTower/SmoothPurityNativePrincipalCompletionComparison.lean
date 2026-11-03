/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.NativeTower.SmoothPurityNativeTowerLimitData
public import WeilConjectures.AlgebraicGeometry.NativeTower.SmoothPurityNativeEllRegular
public import WeilConjectures.CategoryTheory.PrincipalQuotientCompletion.PrincipalQuotientCompletionModel

/-! # Comparison of the native tower unit with principal quotient completion

Source: current blueprint sk-lem-sp-tower, first paragraph and native completion step 2.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.ProEtale.NativeTower

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (T : Scheme.{u})

/-- The normalized tower adjunction presents the actual principal ell-completion,
with equality of the augmented units, without any completeness hypothesis.
Source: current blueprint sk-lem-sp-tower, first paragraph, native completion step 2;
Stacks 0940 and 0941
(blueprint: lem-sp-native-principal-completion-comparison).

Proof: the normalized coefficient comparison identifies its ell-power quotient
projection with the pulled-back native quotient. Cokernel uniqueness therefore
identifies each principal quotient module with that finite coefficient module.
The scalar tensor adjunction identifies the restricted ordinary reduction of P
with the strict quotient tensor tower of P. On pure tensors this comparison is
c tensor x to c tensor x, so it commutes with all quotient transitions and sends
the ordinary unit to the family of quotient tensor units. Exact countable products
identify the right derived inverse limit of the restricted strict tower with its
signed Roos cone. Derive the quotient tensor tower on K-flat representatives and
use the universal left-derived comparisons. The representative normalization of L
identifies the adjunction unit with the Roos augmentation: its shifted coordinate
is zero and its other coordinate is the product of quotient units. Universal
uniqueness of the two derived constructions gives the natural isomorphism and
its displayed equation on every object. No constructibility, bound, or choice of
a complete object is involved. -/
theorem principal_completion_comparison
    (D : SpCoefficientTowersAbelian l E T) (R : SpReductionTower l E T D)
    (L : Limit l E T D R) :
    ∃ M : PrincipalQuotientCompletion.Model.{u + 1, u, u + 1, u + 2}
      (spIntegralSectionRing l E T) (ellSection l E T),
      ∃ e : R.red ⋙ L.derived ≅ M.completion,
      ∀ K : DerivedCategory (spIntegralSectionModules l E T),
        L.adjunction.unit.app K ≫ e.hom.app K = M.unit.app K := by
  sorry

end AlgebraicGeometry.ProEtale.NativeTower
