/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Smooth.SmoothPurityReductionTowerData
public import WeilConjectures.AlgebraicGeometry.Smooth.SmoothPurityTowerReconstructionData
public import WeilConjectures.AlgebraicGeometry.AdicCompletion.DerivedCompletionSupplement
public import WeilConjectures.AlgebraicGeometry.ProEtaleMilnor
public import WeilConjectures.AlgebraicGeometry.IntegralPointMonEquality
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients

/-!
# Effectivity of normalized towers

Source: literature/blueprint/latest/blueprint/part-duality-trace-formula/sec-smooth-purity/
sec-sp-grp-ladic-summary/sec-towers-and-integral-coefficients/sk-lem-sp-tower/
lem-coef-normalized-dvr-effectivity.md,
node `lem-coef-normalized-dvr-effectivity` (blueprint: lem-coef-normalized-dvr-effectivity).
The inverse limit is the strict Milnor/Roos fiber after restriction of scalars.
The finite comparisons are the scalar adjoints of its actual projections.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite SheafOfModules
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale
attribute [local irreducible] upperStarFromPoint

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (T : Scheme.{u})

/-- Exact scalar transport using the coefficient equality directly.
Source: integral coefficient comparison (blueprint: lem-coef-normalized-dvr-effectivity). -/
def spDVRCompletionTransport :
    DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1})
      (condensedRingObj (spIntegralCondensed l E) T)) ⥤
      DerivedCategory (AdicCompletion.Modules l E T) :=
  let e := eqToIso (integralPointMon_eq l E)
  let F : Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1})
      (condensedRingObj (spIntegralCondensed l E) T) ⥤ AdicCompletion.Modules l E T :=
    Mod.comap (coefficientMap e.hom.hom T)
  letI : F.IsEquivalence :=
    (Mod.comapEquivalenceOfIsIso (coefficientMap e.hom.hom T)).isEquivalence_functor
  letI := Functor.additive_of_preserves_binary_products F
  F.mapDerivedCategory

/-- Restrict completed finite coefficients to the native integral section ring.
Source: restriction before inverse limit (blueprint: lem-coef-normalized-dvr-effectivity). -/
abbrev spDVRIntegralRestriction (D : SpCoefficientTowersAbelian l E T)
    (R : SpReductionTower l E T D) :=
  restrictScalars.{u + 1} ((sheafCompose (Scheme.ProEt.topology T)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map R.coefficient.hom)

/-- The original strict tower with every finite scalar action restricted to the integral ring.
Source: definition of M in (blueprint: lem-coef-normalized-dvr-effectivity). -/
def spDVRRestrictedTower (D : SpCoefficientTowersAbelian l E T)
    (R : SpReductionTower l E T D) :
    spCoefficientTowers l E T ⥤ (ℕᵒᵖ ⥤ spIntegralSectionModules l E T) :=
  (Functor.ofOpSequence
    (X := fun n : ℕ ↦ spCompletedEvaluation l E T D n ⋙
      spDVRIntegralRestriction l E T D R)
    (fun n ↦ Functor.whiskerRight (spCompletedTransition l E T D n)
      (spDVRIntegralRestriction l E T D R))).flip

/-- The strict complex tower underlying a representative of the derived coefficient tower.
Source: strict derived tower convention (blueprint: lem-coef-normalized-dvr-effectivity). -/
def spDVRRestrictedComplex (D : SpCoefficientTowersAbelian l E T)
    (R : SpReductionTower l E T D) (P : CochainComplex (spCoefficientTowers l E T) ℤ) :=
  Functor.ofOpSequence
    (X := fun n : ℕ ↦
      (((spCompletedEvaluation l E T D n ⋙
        spDVRIntegralRestriction l E T D R).mapHomologicalComplex (.up ℤ)).obj P))
    (fun n ↦ (NatTrans.mapHomologicalComplex
      (Functor.whiskerRight (spCompletedTransition l E T D n)
        (spDVRIntegralRestriction l E T D R)) (.up ℤ)).app P)

/-- M is exactly the Milnor/Roos derived inverse limit, with integral scalar actions.
Source: sk-prop-pe-milnor (blueprint: lem-coef-normalized-dvr-effectivity). -/
def spDVRLimit (D : SpCoefficientTowersAbelian l E T)
    (R : SpReductionTower l E T D) (P : CochainComplex (spCoefficientTowers l E T) ℤ) :=
  DerivedCategory.Q.obj
    (WeilConjectures.integralOperationsRoos (spDVRRestrictedComplex l E T D R P))

/-- The canonical limit projection, induced by the first Roos coordinate and product projection.
Source: sk-prop-pe-milnor (blueprint: lem-coef-normalized-dvr-effectivity). -/
def spDVRLimitProjection (D : SpCoefficientTowersAbelian l E T)
    (R : SpReductionTower l E T D) (P : CochainComplex (spCoefficientTowers l E T) ℤ)
    (n : ℕ) :=
  let K := spDVRRestrictedComplex l E T D R P
  DerivedCategory.Q.map
    (CochainComplex.mappingCocone.fst
      (towerTransitionEndomorphism (K := fun k : ℕ ↦ K.obj (op k))
        (WeilConjectures.integralOperationsTowerStep K)) ≫
      Pi.π (fun k : ℕ ↦ K.obj (op k)) n)

/-- Restriction of a finite level directly to integral coefficients.
Source: quotient coefficient map (blueprint: lem-coef-normalized-dvr-effectivity). -/
abbrev spDVRLevelRestriction (D : SpCoefficientTowersAbelian l E T)
    (R : SpReductionTower l E T D) (n : ℕ) :=
  restrictScalars.{u + 1} ((sheafCompose (Scheme.ProEt.topology T)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
      (spIntegralReductionScalar l E T R.coefficient n))

/-- Canonical finite reduction: transpose the actual Milnor projection, using the canonical
composition of scalar restrictions and the exact localization comparison.
Source: displayed canonical map (blueprint: lem-coef-normalized-dvr-effectivity). -/
def spDVRFiniteComparison (D : SpCoefficientTowersAbelian l E T)
    (R : SpReductionTower l E T D) (P : CochainComplex (spCoefficientTowers l E T) ℤ)
    (n : ℕ) :=
  letI := D.hasDerived
  letI := D.equivalenceAdditive
  letI := D.evaluationLimits n
  letI := D.evaluationColimits n
  letI : (spCoefficientEvaluation l E T D.equivalence n).Additive :=
    Functor.additive_of_preserves_binary_products _
  let V := ((spCoefficientEvaluation l E T D.equivalence n).mapHomologicalComplex (.up ℤ)).obj P
  let e := systemScalarRestrictionComposition R.coefficient.hom
    (spCompletedEllCommProjection l E T n)
    (spIntegralReductionScalar l E T R.coefficient n) (by rfl)
  let p := spDVRLimitProjection l E T D R P n ≫
    DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex e.hom (.up ℤ)).app V) ≫
    (spDVRLevelRestriction l E T D R n).mapDerivedCategoryFactors.inv.app V
  ((D.scalar (spIntegralReductionScalar l E T R.coefficient n)).adjunction.homEquiv
    (spDVRLimit l E T D R P) (DerivedCategory.Q.obj V)).symm p

/-- Exact evaluation identifies the localized tower level with the localized strict level.
Source: the finite-level comparison (blueprint: lem-coef-normalized-dvr-effectivity). -/
def spDVRLevelLocalization (D : SpCoefficientTowersAbelian l E T)
    (P : CochainComplex (spCoefficientTowers l E T) ℤ) (n : ℕ) :
    (spDerivedCoefficientEvaluation l E T D n).obj
        ((spTowerLocalization l E T D).obj P) ≅
      DerivedCategory.Q.obj
        (((spCoefficientEvaluation l E T D.equivalence n).mapHomologicalComplex (.up ℤ)).obj P) :=
  letI := D.hasDerived
  letI := D.equivalenceAdditive
  letI := D.evaluationLimits n
  letI := D.evaluationColimits n
  letI : (spCoefficientEvaluation l E T D.equivalence n).Additive :=
    Functor.additive_of_preserves_binary_products _
  (spCoefficientEvaluation l E T D.equivalence n).mapDerivedCategoryFactors.app P

/-- The integral limit in the continuous coefficient presentation used for derived completeness.
Source: coefficient identification (blueprint: lem-coef-normalized-dvr-effectivity). -/
def spDVRCompletedLimit (D : SpCoefficientTowersAbelian l E T)
    (R : SpReductionTower l E T D) (P : CochainComplex (spCoefficientTowers l E T) ℤ) :=
  (spDVRCompletionTransport l E T).obj
    ((spIntegralInternalization l E T).obj (spDVRLimit l E T D R P))

set_option maxHeartbeats 10000000 in
-- Explicit scalar transports and the Roos projection require deeper category elaboration.
/-- Every normalized unbounded tower is recovered from its Milnor derived inverse limit.
The canonical finite comparisons are invertible; the reduction tower is isomorphic to
that original derived tower, and the inverse limit is derived complete.

Source: latest blueprint (blueprint: lem-coef-normalized-dvr-effectivity).
Proof: resolve the quotient by the two-term free coefficient complex. Its augmentation fiber
at level m is A_n[1], with transition multiplication by the corresponding generator power.
Tensor with the strict normalized tower; these give compatible triangles. Every n consecutive
fiber transitions vanish, so the finite geometric sum inverts one minus the Roos shift.
Thus that fiber limit is zero. The bounded free quotient resolution commutes with products
and fibers, so Milnor identifies each finite reduction of the limit with the given level.
The identifications are the transposes of the displayed projections, hence coherent.
They assemble to the tower isomorphism. Taking its limit identifies the canonical completion
map with the identity and proves derived completeness. No constructibility or boundedness is used.
-/
theorem normalized_dvr_effectivity
    (D : SpCoefficientTowersAbelian l E T) (R : SpReductionTower l E T D)
    (P : CochainComplex (spCoefficientTowers l E T) ℤ)
    (hP : IsSpNormalizedTower l E T D ((spTowerLocalization l E T D).obj P)) :
    (∀ n : ℕ, IsIso (spDVRFiniteComparison l E T D R P n)) ∧
      (∃ e : (R.red.obj (spDVRLimit l E T D R P)) ≅
          (spTowerLocalization l E T D).obj P,
        ∀ n : ℕ,
          (spDerivedCoefficientEvaluation l E T D n).map e.hom ≫
              (spDVRLevelLocalization l E T D P n).hom =
            (R.evaluation n).hom.app (spDVRLimit l E T D R P) ≫
              spDVRFiniteComparison l E T D R P n) ∧
      IsDerivedComplete l E T (spDVRCompletedLimit l E T D R P) := by
  sorry

end AlgebraicGeometry.ProEtale
