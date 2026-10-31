/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SmoothPurityNormalizedEquivalence
public import WeilConjectures.CategoryTheory.SystemRingedSequenceSite
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import WeilConjectures.SixFunctors.IntegralCompactificationSystemRealization
public import WeilConjectures.AlgebraicGeometry.VaryingRingTensorComparison
public import WeilConjectures.AlgebraicGeometry.CondensedModuleDerivedPushpull
public import WeilConjectures.SixFunctors.ProEtale.DerivedCompletionSupplement
import WeilConjectures.CategoryTheory.SequenceProjectionDerivedAdjunction
import WeilConjectures.CategoryTheory.SequencePushforwardLimitProjections
import WeilConjectures.AlgebraicGeometry.RingedExchangeTensorCoherence
import WeilConjectures.SixFunctors.OpenTensorNormalization
import WeilConjectures.SixFunctors.RingedDerivedMonoidalComparisons
import Mathlib.CategoryTheory.Adjunction.Mates

/-! # Normalized reduction presentation for projection descent

Source: current Weil blueprint, sec-smooth-purity,
`sk-prop-sp-integral-adjunction-direct-image.proof.md`, paragraphs (2)--(3)
(blueprint: def-sp-projection-reduction-presentation).

Positive exponent n+1 is indexed by n : ℕ. System operations take place on the
vertical ringed sequence site, before any evaluation or total derived limit.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option genCtorIdx false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open WeilConjectures WeilConjectures.SemilinearSections

namespace AlgebraicGeometry.ProEtale.CompleteProjectionDescent

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- The specified ell-power coefficient rings, lifted only for the site universe.
Source: blueprint paragraph (3) (blueprint: def-sp-projection-reduction-presentation). -/
abbrev rings (n : ℕ) : CommRingCat.{u + 1} :=
  CommRingCat.of (ULift.{u + 1}
    (Padic.coefficientExtensionIntegers l E ⧸ spEllIdeal l E ^ (n + 1)))

/-- The actual quotient maps, with no chosen transition isomorphisms.
Source: blueprint paragraph (3) (blueprint: def-sp-projection-reduction-presentation). -/
abbrev transitions (n : ℕ) : rings l E (n + 1) ⟶ rings l E n :=
  CommRingCat.ofHom (ULift.ringEquiv.symm.toRingHom.comp
    ((Ideal.Quotient.factorPowSucc (spEllIdeal l E) (n + 1)).comp ULift.ringEquiv.toRingHom))

/-- The existing ordinary unbounded derived category over completed coefficients.
Source: blueprint paragraph (2) (blueprint: def-sp-projection-reduction-presentation). -/
abbrev Integral (T : Scheme.{u}) :=
  DerivedCategory (scalarReductionSource l E T)

/-- The existing ordinary derived category on the ell-power ringed sequence site.
Source: blueprint paragraph (3) (blueprint: def-sp-projection-reduction-presentation). -/
abbrev System (T : Scheme.{u}) :=
  VaryingRing.Derived (rings l E) (transitions l E) T

/-- Uncurrying the recorded tower presentation, with unchanged sections and maps.
Source: blueprint paragraph (3) (blueprint: def-sp-projection-reduction-presentation). -/
def towerEquivalence (T : Scheme.{u}) (D : SpCoefficientTowersAbelian l E T) :
    spCoefficientTowers l E T ≌ VaryingRing.Modules (rings l E) (transitions l E) T :=
  D.equivalence.trans (SheafOfModules.strictSystemSequenceEquivalence
    (spCoefficientCommRings l E T))

/-- Exact uncurrying is additive.
Source: Zheng 4.1 (blueprint: def-sp-projection-reduction-presentation). -/
instance towerFunctorAdditive (T : Scheme.{u}) (D : SpCoefficientTowersAbelian l E T) :
    (towerEquivalence l E T D).functor.Additive :=
  Functor.additive_of_preserves_binary_products _

/-- Exact currying is additive.
Source: Zheng 4.1 (blueprint: def-sp-projection-reduction-presentation). -/
instance towerInverseAdditive (T : Scheme.{u}) (D : SpCoefficientTowersAbelian l E T) :
    (towerEquivalence l E T D).inverse.Additive :=
  Functor.additive_of_preserves_binary_products _

/-- The localization of that exact equivalence, on whole derived systems.
Source: blueprint paragraph (3) (blueprint: def-sp-projection-reduction-presentation). -/
def derivedTowerEquivalence (T : Scheme.{u}) (D : SpCoefficientTowersAbelian l E T) :
    spDerivedCoefficientTowers l E T D ≌ System l E T :=
  letI := D.hasDerived
  letI := Functor.additive_of_preserves_binary_products (towerEquivalence l E T D).functor
  letI := Functor.additive_of_preserves_binary_products (towerEquivalence l E T D).inverse
  (towerEquivalence l E T D).mapDerivedCategory

/-- Derived reduction, transported by the fixed sectionwise equivalence.
Source: blueprint paragraph (3) (blueprint: def-sp-projection-reduction-presentation). -/
def reduction (T : Scheme.{u}) (D : SpCoefficientTowersAbelian l E T)
    (R : SpReductionTower l E T D) : Integral l E T ⥤ System l E T :=
  spCompletedReduction l E T D R ⋙ (derivedTowerEquivalence l E T D).functor

/-- Total derived limit after exact forgetting, retaining its strict-diagram model.
Source: blueprint paragraphs (2)--(3)
(blueprint: def-sp-projection-reduction-presentation). -/
def totalLimit (T : Scheme.{u}) (D : SpCoefficientTowersAbelian l E T)
    (R : SpReductionTower l E T D) (A : SpNormalizedEquivalence l E T D R) :
    System l E T ⥤ Integral l E T :=
  letI := A.forgetAdditive
  letI := A.forgetLimits
  letI := A.forgetColimits
  (derivedTowerEquivalence l E T D).inverse ⋙ spCompletedTotalLimit l E T D

/-- The actual reduction/limit adjunction, including its unit and reconstruction counit.
Source: blueprint paragraphs (2)--(3)
(blueprint: def-sp-projection-reduction-presentation). -/
def reductionAdjunction (T : Scheme.{u}) (D : SpCoefficientTowersAbelian l E T)
    (R : SpReductionTower l E T D) (A : SpNormalizedEquivalence l E T D R) :
    reduction l E T D R ⊣ totalLimit l E T D R A :=
  A.adjunction.comp (derivedTowerEquivalence l E T D).toAdjunction


open WeilConjectures.IntegralSystemRealization

/-- The existing section-model calculus, for exactly the ell-power tower.
Source: blueprint paragraph (3) (blueprint: def-sp-projection-reduction-presentation). -/
abbrev Calculus (T : Scheme.{u}) :=
  SemilinearSections.Data.{u + 1, u, u + 1} (Scheme.ProEt.topology T)
    (VaryingRing.coefficients (rings l E) T)
    (VaryingRing.coefficientTransition (rings l E) (transitions l E) T)

/-- Ordinary reduction, with its original quotient sections and transitions.
Source: blueprint paragraph (3) (blueprint: def-sp-projection-reduction-presentation). -/
def ordinaryReduction (T : Scheme.{u}) (D : SpCoefficientTowersAbelian l E T)
    (R : SpReductionTower l E T D) :
    scalarReductionSource l E T ⥤ VaryingRing.Modules (rings l E) (transitions l E) T :=
  SheafOfModules.restrictScalars ((sheafCompose _
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map R.coefficient.hom) ⋙
    R.ordinary ⋙ (towerEquivalence l E T D).functor

/-- Additivity of the actual simultaneous quotient functor.
Source: blueprint paragraph (3) (blueprint: def-sp-projection-reduction-presentation). -/
instance ordinaryReductionAdditive (T : Scheme.{u}) (D : SpCoefficientTowersAbelian l E T)
    (R : SpReductionTower l E T D) : (ordinaryReduction l E T D R).Additive :=
  letI := R.additive
  inferInstanceAs (SheafOfModules.restrictScalars ((sheafCompose _
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map R.coefficient.hom) ⋙
      R.ordinary ⋙ (towerEquivalence l E T D).functor).Additive

/-- The actual localization comparison for simultaneous reduction.
Source: blueprint paragraph (3) (blueprint: def-sp-projection-reduction-presentation). -/
def reductionEpsilon (T : Scheme.{u}) (D : SpCoefficientTowersAbelian l E T)
    (R : SpReductionTower l E T D)
    (P : CochainComplex (scalarReductionSource l E T) ℤ) :
    (reduction l E T D R).obj (DerivedCategory.Q.obj P) ⟶
      DerivedCategory.Q.obj
        (((ordinaryReduction l E T D R).mapHomologicalComplex (.up ℤ)).obj P) :=
  letI := D.hasDerived
  letI := R.additive
  let S := SheafOfModules.restrictScalars ((sheafCompose _
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map R.coefficient.hom)
  (R.red ⋙ (derivedTowerEquivalence l E T D).functor).map
      (S.mapDerivedCategoryFactors.hom.app P) ≫
    (derivedTowerEquivalence l E T D).functor.map
      (R.counit.app ((S.mapHomologicalComplex (.up ℤ)).obj P)) ≫
    ((towerEquivalence l E T D).functor.mapDerivedCategoryFactors).hom.app
      ((R.ordinary.mapHomologicalComplex (.up ℤ)).obj
        ((S.mapHomologicalComplex (.up ℤ)).obj P))

/-- The quotient-augmentation generator in the simultaneous ordinary reduction.
Source: blueprint paragraph (3) (blueprint: def-sp-projection-reduction-presentation). -/
def reductionGenerator (T : Scheme.{u}) (D : SpCoefficientTowersAbelian l E T)
    (R : SpReductionTower l E T D) (M : scalarReductionSource l E T)
    (n : ℕ) (U : T.ProEtᵒᵖ) (x : M.val.obj U) :
    ((ordinaryReduction l E T D R).obj M).val.obj (op (n, U.unop)) :=
  spReductionGenerator l E T D R.coefficient R.ordinary R.level
    ((SheafOfModules.restrictScalars ((sheafCompose _
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map R.coefficient.hom)).obj M)
    n U 1 x

attribute [local irreducible] HasDerivedCategory.standard constantSheaf
  Functor.mapDerivedCategory SheafOfModules.changeOfRings
  SheafOfModules.monoidalCategory

attribute [local irreducible] reductionEpsilon reductionGenerator ordinaryReduction
  derivedTowerEquivalence towerEquivalence reduction totalLimit

set_option maxHeartbeats 600000 in
-- Elaborate the two-variable total-tensor representative square on the sequence site.
/-- The representative normalization of the tensor/scalar comparison on the
whole sequence site. The generator equation fixes every total summand and all
quotient augmentations before localization.
Source: blueprint paragraph (3), tensor reductions
(blueprint: def-sp-projection-reduction-presentation). -/
def TensorReductionModel (T : Scheme.{u}) (D : SpCoefficientTowersAbelian l E T)
    (R : SpReductionTower l E T D) (d : RingedModels l E) (S : Calculus l E T)
    (mu : (d.tensor T).ordinary.tensor ⋙ reduction l E T D R ≅
      ((reduction l E T D R).prod (reduction l E T D R)) ⋙ S.closed.tensor) : Prop :=
  ∃ chain : coefficientTotalTensor.{u + 1, u + 1, u} (Scheme.ProEt.topology T)
      (completedIntegralCommRingSheafUnrestricted l E T) ⋙
        (ordinaryReduction l E T D R).mapHomologicalComplex (.up ℤ) ≅
      ((ordinaryReduction l E T D R).mapHomologicalComplex (.up ℤ)).prod
        ((ordinaryReduction l E T D R).mapHomologicalComplex (.up ℤ)) ⋙
          totalTensor.{u + 1, u, u + 1} (coefficientSequenceTopology (Scheme.ProEt.topology T))
            (systemRing (Scheme.ProEt.topology T)
              (VaryingRing.coefficients (rings l E) T)
              (VaryingRing.coefficientTransition (rings l E) (transitions l E) T)),
    (∀ (P Q : CochainComplex (scalarReductionSource l E T) ℤ)
    (a b k : ℤ) (h : a + b = k) (n : ℕ) (U : T.ProEtᵒᵖ)
    (x : (P.X a).val.obj U) (y : (Q.X b).val.obj U),
    ((chain.hom.app (P, Q)).f k).val.app (op (n, U.unop))
      (reductionGenerator l E T D R _ n U
        (coefficientTensorGenerator.{u + 1, u + 1, u} (Scheme.ProEt.topology T)
          (completedIntegralCommRingSheafUnrestricted l E T) P Q a b k h U x y)) =
      coefficientTensorGenerator.{u + 1, u + 1, u}
        (coefficientSequenceTopology (Scheme.ProEt.topology T))
        (systemRing (Scheme.ProEt.topology T)
          (VaryingRing.coefficients (rings l E) T)
          (VaryingRing.coefficientTransition (rings l E) (transitions l E) T))
        (((ordinaryReduction l E T D R).mapHomologicalComplex (.up ℤ)).obj P)
        (((ordinaryReduction l E T D R).mapHomologicalComplex (.up ℤ)).obj Q)
        a b k h (op (n, U.unop))
        (reductionGenerator l E T D R (P.X a) n U x)
        (reductionGenerator l E T D R (Q.X b) n U y)) ∧
    ∃ kflat : ∀ (P : CochainComplex (scalarReductionSource l E T) ℤ),
    Scheme.proEtaleFlatRepresentatives T
      (completedIntegralCommRingSheafUnrestricted l E T) P →
    CochainComplex.IsKFlatIndependentCoefficients.{u + 1, u, u + 1}
      (R := systemRing (Scheme.ProEt.topology T)
        (VaryingRing.coefficients (rings l E) T)
        (VaryingRing.coefficientTransition (rings l E) (transitions l E) T))
      (((ordinaryReduction l E T D R).mapHomologicalComplex (.up ℤ)).obj P),
    ∀ (P Q : CochainComplex (scalarReductionSource l E T) ℤ)
    (hP : Scheme.proEtaleFlatRepresentatives T
      (completedIntegralCommRingSheafUnrestricted l E T) P)
    (hQ : Scheme.proEtaleFlatRepresentatives T
      (completedIntegralCommRingSheafUnrestricted l E T) Q),
    HEq ((reduction l E T D R).map
        ((d.tensor T).ordinary.representative.hom.app (⟨P, hP⟩, ⟨Q, hQ⟩)) ≫
      mu.hom.app (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q) ≫
      S.closed.tensor.map (Prod.mkHom
        (reductionEpsilon l E T D R P) (reductionEpsilon l E T D R Q)))
    (reductionEpsilon l E T D R
        ((coefficientTotalTensor.{u + 1, u + 1, u} (Scheme.ProEt.topology T)
          (completedIntegralCommRingSheafUnrestricted l E T)).obj (P, Q)) ≫
      DerivedCategory.Q.map (chain.hom.app (P, Q)) ≫
      (tensorModelIso.{u + 1, u, u + 1}
      (coefficientSequenceTopology (Scheme.ProEt.topology T))
      (systemRing (Scheme.ProEt.topology T)
        (VaryingRing.coefficients (rings l E) T)
        (VaryingRing.coefficientTransition (rings l E) (transitions l E) T))
      S.closed S.tensorModels
      (((ordinaryReduction l E T D R).mapHomologicalComplex (.up ℤ)).obj P)
      (((ordinaryReduction l E T D R).mapHomologicalComplex (.up ℤ)).obj Q)
      (kflat P hP) (kflat Q hQ)).hom)

end AlgebraicGeometry.ProEtale.CompleteProjectionDescent
