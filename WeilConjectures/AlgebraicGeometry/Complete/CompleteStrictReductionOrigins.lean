/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Strict.Tower.StrictTowerExchangeMateNormalization
public import WeilConjectures.AlgebraicGeometry.Bounded.BoundedConstructibleCompleteSupplement
public import WeilConjectures.AlgebraicGeometry.StrictTower.FiniteConstantCoefficientTransport
public import WeilConjectures.AlgebraicGeometry.CoefficientSheafificationSquare.CoefficientSheafificationScalarSquare

/-!
# Etale origins of restricted strict reduction towers

Compatible bounded-below etale origins of a completed object give finite constant-coefficient
etale origins at every level of its strict reduction tower, after restriction to constant
coefficients.

Source: Weil conjectures blueprint, node thm-cbc-complete-proetale, proof step 8
(blueprint: thm-cbc-complete-proetale).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false

universe t

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme

variable {A : Type (t + 1)} [CommRing A] (d : AdicCoefficientDatum A)

/-- The n-th level of the restricted strict reduction tower of K is the constant-coefficient
restriction of the realized n-th witnessed level, given an identification of that realized
level with the n-th completed reduction of K.
Source: blueprint def-weil-pbc-bounded-constructible-complete and
def-cbc-finite-constant-coefficient-transport (blueprint: thm-cbc-complete-proetale).
Proof sketch: realization along the constant-section map and along the continuous-function
presentation differ by restriction along the finite ring comparison (the sheafification
scalar square `rawIso`); the constant-section map to the finite ring followed by that
comparison is the constant-coefficient scalar map followed by the n-th projection, as both
are fixed on constant sections. Apply `e`, the reduction-evaluation comparison
`completedReductionEvaluation` and the commutation of evaluation with termwise restriction,
all exact functors. -/
theorem cbcStrictReductionLevel_originIso (V : Scheme.{t}) (K : d.derived V) (n : ℕ)
    (X : ProEtale.PbcWitnessAmbient V d n)
    (e : (pbcDerivedFunctionRealization V d n).obj X ≅ (pbcCompletedReduction V d n).obj K) :
    Nonempty ((ProEtale.StrictTower.finiteRestriction A V (ProEtale.PbcQuotient d n)
        (Ideal.Quotient.mk _)).mapDerivedCategory.obj
          ((ProEtale.finiteCoefficientRealization V
            (ProEtale.PbcQuotient d n)).mapDerivedCategory.obj X) ≅
      (ProEtale.StrictTower.ev A V n).obj
        ((exchangeTowerRes d V).obj ((completedReductionTower V d).obj K))) := by
  sorry

/-- Compatible etale origins of a completed object give finite constant-coefficient etale
origins of every level of its restricted strict reduction tower.
Source: blueprint step 8 (blueprint: thm-cbc-complete-proetale). -/
theorem cbcStrictReductionLevel_scalarEtaleOrigin (V : Scheme.{t}) (K : d.derived V)
    (origins : PbcHasCompatibleEtaleOrigins V d K) (n : ℕ) :
    Nonempty (ProEtale.StrictTower.ScalarEtaleOrigin A V
      ((ProEtale.StrictTower.ev A V n).obj
        ((exchangeTowerRes d V).obj ((completedReductionTower V d).obj K)))) := by
  obtain ⟨P, e, -⟩ := origins
  obtain ⟨iso⟩ := cbcStrictReductionLevel_originIso d V K n (P.K n) (e n)
  exact ⟨{ Λ := ProEtale.PbcQuotient d n
           φ := Ideal.Quotient.mk _
           F := ⟨_, P.boundedBelow n⟩
           origin := P.origin n
           iso := iso }⟩

end AlgebraicGeometry.Scheme
