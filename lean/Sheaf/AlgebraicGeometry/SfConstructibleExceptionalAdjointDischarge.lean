/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NY
-/
module

public import Sheaf.AlgebraicGeometry.SfClassFullCohomologicalDimension
public import Sheaf.Paper.FiniteFieldFiber
public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FiniteType

/-!
# The relative interpretation of the exceptional adjoint

Source: Weil blueprint, sk-prop-sf-existence, cor-sf-ambient-adjoint-discharge
(blueprint: cor-sf-ambient-adjoint-discharge).
The statement below spells out exactly the class-restricted vanishing and natural
relative Hom bijections. It imposes no ambient exceptional datum.
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.ProEtale
open Scheme

/-- The bounded-class interpretation combines the sharp class vanishing bound and the
relative adjunction for the explicitly defined transported etale functor. The inverse
Hom map sends a to Rf_!(a) followed by the relative counit eps; functoriality gives
naturality in its source, and the last equation gives naturality in its target.
Source: blueprint, cor-sf-ambient-adjoint-discharge
(blueprint: cor-sf-ambient-adjoint-discharge).
Proof: thm-sf-fullcd-class gives FullCD_cls with bound 2d on the proper part, uniformly
on the weakly-etale base changes. This uses etale-origin sheaves only, not all sheaves.
Theorem thm-sf-ambient-adjoint-class supplies the relative Hom bijections and coherent
compactification comparisons for bounded-below etale-origin K and every bounded-below
L. Substituting the defining formula ν_X^* f× Rν_Y* identifies the right-hand functor
with sfFiniteExceptionalFixed. Its relative counit supplies eps, and the Hom
bijections give the asserted bijectivity. Their naturality gives the last equation.
No unrestricted ambient adjunction or all-sheaf dimension bound follows. -/
theorem sfConstructibleExceptionalAdjointDischarge
    (Dk : WeilConjectures.FiniteFieldDatum.{u})
    (l : ℕ) [Fact l.Prime] (_hl : l ≠ Dk.p)
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (n : ℕ)
    (X Y : Scheme.{u}) [X.Over (Spec (CommRingCat.of Dk.k))]
    [Y.Over (Spec (CommRingCat.of Dk.k))]
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of Dk.k))]
    [QuasiCompact (X ↘ Spec (CommRingCat.of Dk.k))]
    [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of Dk.k))]
    [QuasiCompact (Y ↘ Spec (CommRingCat.of Dk.k))]
    (f : X ⟶ Y) [f.IsOver (Spec (CommRingCat.of Dk.k))]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (c : Compactification f) (d : ℕ)
    (_hd : topologicalKrullDim c.Z ≤ (d : WithBot ℕ∞)) :
    sfClassFullCohomologicalDimension c.g (Padic.coefficientExtensionRing l E (n + 1))
        (2 * d) ∧
    ∃ eps : ∀ (L : DerivedCategory (Sheaf (ProEt.topology Y)
          (ModuleCat.{u + 1} (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E (n + 1))))))
        (_hL : DerivedCategory.TStructure.t.plus L),
      (sfFixedCompactSupport (Padic.coefficientExtensionRing l E (n + 1)) c).obj
        ((sfFiniteExceptionalFixed (Padic.coefficientExtensionRing l E (n + 1)) c).obj L) ⟶ L,
      (∀ (L) (hL : DerivedCategory.TStructure.t.plus L) (K)
          (_hK : (DerivedCategory.Plus.ι ⋙
            (comparisonUpperStar (ModuleCat.{u + 1}
              (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E (n + 1))))
                X).mapDerivedCategory).essImage K),
        Function.Bijective (fun a : K ⟶
            (sfFiniteExceptionalFixed (Padic.coefficientExtensionRing l E (n + 1)) c).obj L ↦
          (sfFixedCompactSupport (Padic.coefficientExtensionRing l E (n + 1)) c).map a ≫
            eps L hL)) ∧
      ∀ (L L') (hL : DerivedCategory.TStructure.t.plus L)
          (hL' : DerivedCategory.TStructure.t.plus L') (a : L ⟶ L'),
        (sfFixedCompactSupport (Padic.coefficientExtensionRing l E (n + 1)) c).map
            ((sfFiniteExceptionalFixed (Padic.coefficientExtensionRing l E (n + 1)) c).map a) ≫
              eps L' hL' = eps L hL ≫ a := by
  sorry

end AlgebraicGeometry.ProEtale
