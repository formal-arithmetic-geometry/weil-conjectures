/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group M5
-/
module

public import Sheaf.CategoryTheory.CyclicDerivedHomData

/-! # Right-derived transport of cyclic presentations

Source: Stacks Project, Derived Categories, Tags 070I, 070K, 070Y and 0152;
the right-derived companion proof plan in CyclicDerivedHomExactSequence.
-/

@[expose] public noncomputable section
set_option autoImplicit false

universe u v w wF uD vD wD wG

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.Endofunctor.IsoAlgebra

variable {C : Type u} [Category.{v} C] [Abelian C]
  (F : C ⥤ C) [F.Additive] [F.IsEquivalence]
  [HasDerivedCategory.{w} C] [HasDerivedCategory.{wF} (IsoAlgebra F)]
  {D : Type uD} [Category.{vD} D] [Abelian D]
  (G : D ⥤ D) [G.Additive] [G.IsEquivalence]
  [HasDerivedCategory.{wD} D] [HasDerivedCategory.{wG} (IsoAlgebra G)]
  (L : C ⥤ D) [L.Additive] (e : L ⋙ G ≅ F ⋙ L)
  [IsGrothendieckAbelian.{v} C] [IsGrothendieckAbelian.{vD} D]
  [PreservesFiniteLimits L]
  (hF : ∀ K : CochainComplex (IsoAlgebra F) ℤ,
    ∃ (I : CochainComplex (IsoAlgebra F) ℤ) (s : K ⟶ I), I.IsKInjective ∧ QuasiIso s)
  (hC : ∀ K : CochainComplex C ℤ,
    ∃ (I : CochainComplex C ℤ) (s : K ⟶ I), I.IsKInjective ∧ QuasiIso s)
  [(L.rightDerivedFunctorOfQuasiIsoResolutions hC).CommShift ℤ]
  (hσ : NatTrans.CommShift (L.rightDerivedFunctorOfQuasiIsoResolutionsUnit hC) ℤ)

include hσ in
/-- Right-derived transport with a unit-compatible shift commutes with cyclic conjugation.

Proof: represent each native object by a K-injective complex. Exact forgetting preserves
K-injectives, and applying the exact autoequivalence preserves K-injectives too. Compute
both right derived functors by their units on these complexes. The unit equation defining
cyclicDerivedRightForgetComparison identifies the underlying computation with L(U I).
Naturality of e gives the structure equation relating the target action to L of the
source action. The unit shift equation identifies the comparison on I[r] with the
shifted comparison on I. Represent a morphism into the shifted K-injective target by a
homotopy class and apply the two structure equations, at its source and target. Naturality
of e moves the morphism across the comparison between P' L and L P. Associativity,
shift compatibility and the inverse-isomorphism equations give the displayed equality.
The K-injective Hom bijection and naturality of the computation units transport it to
arbitrary native derived objects. No boundary map or exact-sequence assertion is used.

Source: the action calculation in the parent right-derived companion, and the comparison of
lem-sf-fixed-pair-derived-forget-comparison; Stacks Tags 070I, 070K and 070Y.
(blueprint: lem-sf-cyclic-derived-right-action). -/
theorem cyclicDerivedHomTransport_rightDerived_action
    (M N : DerivedCategory (IsoAlgebra F)) (r : ℤ)
    (u : CyclicDerivedHom F M N r) :
    cyclicDerivedHomTransport F G
      ((mapOfNatIso e).rightDerivedFunctorOfQuasiIsoResolutions hF)
      (L.rightDerivedFunctorOfQuasiIsoResolutions hC)
      (fun r ↦ (L.rightDerivedFunctorOfQuasiIsoResolutions hC).commShiftIso r)
      (cyclicDerivedRightForgetComparison F G L e hF hC) M N r
      (cyclicDerivedHomAction F M N r u) =
      cyclicDerivedHomAction G
        (((mapOfNatIso e).rightDerivedFunctorOfQuasiIsoResolutions hF).obj M)
        (((mapOfNatIso e).rightDerivedFunctorOfQuasiIsoResolutions hF).obj N) r
        (cyclicDerivedHomTransport F G
          ((mapOfNatIso e).rightDerivedFunctorOfQuasiIsoResolutions hF)
          (L.rightDerivedFunctorOfQuasiIsoResolutions hC)
          (fun r ↦ (L.rightDerivedFunctorOfQuasiIsoResolutions hC).commShiftIso r)
          (cyclicDerivedRightForgetComparison F G L e hF hC) M N r u) := by sorry

end CategoryTheory.Endofunctor.IsoAlgebra
