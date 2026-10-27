/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group P9
-/
module

public import Sheaf.Paper.SmoothPurityTowerReconstructionData

/-! # Derived completeness of a coefficient tower limit

Source: current blueprint, sec-smooth-purity/sk-lem-sp-tower, completeness sentence.
(blueprint: lem-sp-tower-limit-derived-complete)
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe u
open CategoryTheory CategoryTheory.Limits Opposite SheafOfModules
namespace AlgebraicGeometry.ProEtale

attribute [-instance] spCoefficientModulesAbelian
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (T : Scheme.{u})
  (D : SpCoefficientTowersAbelian l E T)

/-- Completeness of any derived coefficient-tower limit. Neither normalization nor
constructibility is needed.
Source: current blueprint, sk-lem-sp-tower.proof.md, sentence "The complex C is
derived complete as a limit of complexes killed by powers of ell"; Bhatt--Scholze,
Lemmas 3.5.4--3.5.7 (blueprint: lem-sp-tower-limit-derived-complete).

Proof: use the semilinear K-flat model and restrict its actual chain transitions to
completed coefficients. The coefficient factorization ell = v*pi^e, e>=1, implies
that level n is termwise killed by pi^(e*(n+1)). Apply the power-torsion sheaf-limit
completeness theorem to this strict tower. For each fixed n the Koszul reductions
split, after its own torsion cutoff, into a constant tower and a pro-zero shifted
tower. Their limits identify the row completion unit with an isomorphism. Signed
interchange of the two Roos directions then proves that the limit's own completion
unit is invertible. The theorem's quotient comparison retains all quotient units.
Use one K-flat resolution of the limit to identify those quotient units and
transitions with sfDerivedReductionUnit and sfDerivedReductionTransition: the
normalizations on representatives agree, and localization determines the latter
uniquely. The semilinear model's completed lift identifies its Roos triangle with
the given triangle for M. Transporting the unit-normalized quotient Roos triangle
along that isomorphism gives exactly IsSfDerivedComplete M. No common torsion
exponent, cohomological bound, or normalization of C is used. -/
theorem spTower_limit_derived_complete
    (C : spDerivedCoefficientTowers l E T D)
    (M : DerivedCategory (WeilConjectures.scalarReductionSource.{u, u} l E T))
    [HasProduct (fun n : ℕ ↦ (spDerivedCompletedEvaluation l E T D n).obj C)]
    (p : M ⟶ ∏ᶜ fun n : ℕ ↦ (spDerivedCompletedEvaluation l E T D n).obj C)
    (δ : (∏ᶜ fun n : ℕ ↦ (spDerivedCompletedEvaluation l E T D n).obj C) ⟶ M⟦(1 : ℤ)⟧)
    (hlim : IsDerivedLimitTriangle
      (fun n : ℕ ↦ (spDerivedCompletedTransition l E T D n).app C) M p δ) :
    WeilConjectures.IsSfDerivedComplete l E T M := by sorry

end AlgebraicGeometry.ProEtale
