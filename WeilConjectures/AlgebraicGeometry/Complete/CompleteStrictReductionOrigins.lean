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
attribute [local instance] ProEtale.StrictTower.finiteRestriction_finiteLimits
  ProEtale.StrictTower.finiteRestriction_finiteColimits

/-- Constant-coefficient restriction of the completed coefficient ring is exact. -/
instance exchangeScalarRestrict_finiteLimits (V : Scheme.{t}) :
    PreservesFiniteLimits (proEtaleRingRestrictScalars (exchangeScalar d V)) :=
  (proEtaleRingRestrictScalars_properties (exchangeScalar d V)).1

/-- Constant-coefficient restriction of the completed coefficient ring is exact. -/
instance exchangeScalarRestrict_finiteColimits (V : Scheme.{t}) :
    PreservesFiniteColimits (proEtaleRingRestrictScalars (exchangeScalar d V)) :=
  (proEtaleRingRestrictScalars_properties (exchangeScalar d V)).2.1

/-- The two coefficient presentations of a finite-level sheaf, restricted to constant
coefficients, agree: realization along constant sections followed by restriction along
A → A/I^(n+1), and realization along continuous functions followed by restriction along the
n-th projection and the constant-coefficient scalar map.
Source: blueprint def-cbc-finite-constant-coefficient-transport
(blueprint: thm-cbc-complete-proetale).
Proof sketch: `rawIso` for the finite ring comparison identifies the two realizations up to
restriction along that comparison; the composite ring maps out of the constant ring agree
on constant sections, hence agree. -/
theorem cbcFiniteRealizationRestrictIso (V : Scheme.{t}) (n : ℕ) :
    Nonempty (ProEtale.finiteCoefficientRealization V (ProEtale.PbcQuotient d n) ⋙
        ProEtale.StrictTower.finiteRestriction A V (ProEtale.PbcQuotient d n)
          (Ideal.Quotient.mk _) ≅
      pbcFunctionRealization V d n ⋙ reductionRestrict V (completedReductionProjection V d n) ⋙
        proEtaleRingRestrictScalars (exchangeScalar d V)) := by
  sorry

/-- The n-th level of the restricted strict reduction tower of K is the constant-coefficient
restriction of the realized n-th witnessed level, given an identification of that realized
level with the n-th completed reduction of K.
Source: blueprint def-weil-pbc-bounded-constructible-complete and
def-cbc-finite-constant-coefficient-transport (blueprint: thm-cbc-complete-proetale). -/
theorem cbcStrictReductionLevel_originIso (V : Scheme.{t}) (K : d.derived V) (n : ℕ)
    (X : ProEtale.PbcWitnessAmbient V d n)
    (e : (pbcDerivedFunctionRealization V d n).obj X ≅ (pbcCompletedReduction V d n).obj K) :
    Nonempty ((ProEtale.StrictTower.finiteRestriction A V (ProEtale.PbcQuotient d n)
        (Ideal.Quotient.mk _)).mapDerivedCategory.obj
          ((ProEtale.finiteCoefficientRealization V
            (ProEtale.PbcQuotient d n)).mapDerivedCategory.obj X) ≅
      (ProEtale.StrictTower.ev A V n).obj
        ((exchangeTowerRes d V).obj ((completedReductionTower V d).obj K))) := by
  obtain ⟨b⟩ := cbcFiniteRealizationRestrictIso d V n
  let real := ProEtale.finiteCoefficientRealization V (ProEtale.PbcQuotient d n)
  let RF := ProEtale.StrictTower.finiteRestriction A V (ProEtale.PbcQuotient d n)
    (Ideal.Quotient.mk (d.ideal ^ (n + 1)))
  let pbcR := pbcFunctionRealization V d n
  let resN := reductionRestrict V (completedReductionProjection V d n)
  let resA := proEtaleRingRestrictScalars (exchangeScalar d V)
  let ev := (CategoryTheory.evaluation ℕᵒᵖ
    (proEtaleRingModules V (d.completedRing V))).obj (op n)
  let i₁ := (Functor.mapDerivedCategoryCompIso real RF).symm.app X
  let i₂ := (Functor.mapDerivedCategoryNatIso b).app X
  let i₃ := (Functor.mapDerivedCategoryCompIso pbcR (resN ⋙ resA)).app X
  let i₄ := (resN ⋙ resA).mapDerivedCategory.mapIso e
  let i₅ := (Functor.mapDerivedCategoryCompIso resN resA).app
    ((pbcCompletedReduction V d n).obj K)
  let i₆ := resA.mapDerivedCategory.mapIso
    ((asIso (completedReductionEvaluation V d n)).symm.app K)
  let i₇ := (Functor.mapDerivedCategoryCompIso ev resA).symm.app
    ((completedReductionTower V d).obj K)
  let i₈ := (Functor.mapDerivedCategoryCompIso (exchangeTowerModuleRes d V)
    ((CategoryTheory.evaluation ℕᵒᵖ (ProEtale.StrictTower.Modules A V)).obj (op n))).app
      ((completedReductionTower V d).obj K)
  exact ⟨i₁ ≪≫ i₂ ≪≫ i₃ ≪≫ i₄ ≪≫ i₅ ≪≫ i₆ ≪≫ i₇ ≪≫ i₈⟩


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
