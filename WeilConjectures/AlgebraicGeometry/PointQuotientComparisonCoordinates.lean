/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.PointFrobeniusNormalizationDefinitions

/-! Canonical strict point quotient and cone comparisons, with their coordinate API. -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme AlgebraicGeometry.ProEtale
namespace WeilConjectures.PointFrobeniusNormalization
variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
  (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

attribute [local irreducible] completedIntegralCoefficientSheafUnrestricted
  constantSheaf HasDerivedCategory.standard SheafOfModules.monoidalCategory
  CategoryTheory.Limits.limit frobeniusPointIso FrobeniusExchange.models
attribute [local implicit_reducible] integralOperationsRoosFunctor integralOperationsRoos

set_option genInjectivity false in
/-- The strict tower comparison and its whole-cone comparison.
Source: multiplication-cone descent, strict coordinates
(blueprint: def-pur-point-quotient-comparison-coordinates). -/
structure PointQuotientComparisonData
    (g : Spec (.of D.k) ⟶ Spec (.of D.k)) [IsIso g] where
  j : (integralOperationsGoodComplex l E (Spec (.of D.k))).ι ⋙
        integralOperationsPullbackTowerFunctor l E g ≅
      (integralOperationsGoodComplex l E (Spec (.of D.k))).ι ⋙
        trfQuotientTowerFunctor l E (Spec (.of D.k)) ⋙ trfInverseImageTower l E g
  eta : (integralOperationsGoodComplex l E (Spec (.of D.k))).ι ⋙
        trfQuotientTowerFunctor l E (Spec (.of D.k)) ⋙ integralOperationsRoosFunctor ⋙
          trfInverseImageComplex l E g ≅
      (integralOperationsGoodComplex l E (Spec (.of D.k))).ι ⋙
        trfQuotientTowerFunctor l E (Spec (.of D.k)) ⋙
          trfInverseImageTower l E g ⋙ integralOperationsRoosFunctor

/-- The inverse generator and both cone coordinates fix the data uniquely.
Source: multiplication-cone descent, generator and two-coordinate specifications
(blueprint: def-pur-point-quotient-comparison-coordinates). -/
def PointQuotientComparisonNormalized
    (g : Spec (.of D.k) ⟶ Spec (.of D.k)) [IsIso g]
    (d : PointQuotientComparisonData D l E g) : Prop :=
  (∀ (P : (integralOperationsGoodComplex l E (Spec (.of D.k))).FullSubcategory)
    (n : ℕ) (i : ℤ) (U : (Spec (.of D.k)).ProEt)
    (x : (((unrestrictedIntegralFiniteComplex l E (Spec (.of D.k)) n).obj P.obj).X i).val.obj
      (op ((proEtaleIsoPostcompose g).obj U))),
    (((d.j.hom.app P).app (op n)).f i).val.app (op U)
      ((((integralOperationsPullbackLevel l E g n).obj P.obj).X i).val.map
        (proEtaleIsoCommaArrow g U).op
        (integralOperationsPullbackGenerator l E g n
          (((unrestrictedIntegralFiniteComplex l E (Spec (.of D.k)) n).obj P.obj).X i)
          ((proEtaleIsoPostcompose g).obj U) x)) = x) ∧
  (∀ (P : (integralOperationsGoodComplex l E (Spec (.of D.k))).FullSubcategory)
    (n : ℕ) (i : ℤ) (U : (Spec (.of D.k)).ProEt)
    (x : (((unrestrictedIntegralFiniteComplex l E (Spec (.of D.k)) n).obj P.obj).X i).val.obj
      (op ((proEtaleIsoPostcompose g).obj U))),
    (((d.j.inv.app P).app (op n)).f i).val.app (op U) x =
      ((((integralOperationsPullbackLevel l E g n).obj P.obj).X i).val.map
        (proEtaleIsoCommaArrow g U).op
        (integralOperationsPullbackGenerator l E g n
          (((unrestrictedIntegralFiniteComplex l E (Spec (.of D.k)) n).obj P.obj).X i)
          ((proEtaleIsoPostcompose g).obj U) x))) ∧
  (∀ P : (integralOperationsGoodComplex l E (Spec (.of D.k))).FullSubcategory,
    d.eta.hom.app P ≫ CochainComplex.mappingCocone.fst
        (trfInverseQuotientDifference l E g P.obj) =
      (trfInverseImageComplex l E g).map
        (CochainComplex.mappingCocone.fst (trfQuotientDifference l E (Spec (.of D.k)) P.obj)) ≫
      trfQuotientProductComparison l E g P.obj) ∧
  (∀ (P : (integralOperationsGoodComplex l E (Spec (.of D.k))).FullSubcategory) (p : ℤ),
    (d.eta.hom.app P).f (p + 1) ≫
      (CochainComplex.mappingCocone.snd (trfInverseQuotientDifference l E g P.obj)).v
        (p + 1) p (add_neg_cancel_right p 1) =
      (inverseImageIntegralModules l E g).map
        ((CochainComplex.mappingCocone.snd
          (trfQuotientDifference l E (Spec (.of D.k)) P.obj)).v
          (p + 1) p (add_neg_cancel_right p 1)) ≫
      (trfQuotientProductComparison l E g P.obj).f p)

include hl in
/-- Existence of the point comparison data with their determining coordinates.
Source: multiplication-cone descent
(blueprint: def-pur-point-quotient-comparison-coordinates).
Proof: take its strict natural isomorphisms j and eta. Its generator, inverse generator,
and two cone equations are exactly the four fields of the normalization predicate. -/
theorem pointQuotientComparison_exists
    (g : Spec (.of D.k) ⟶ Spec (.of D.k)) [IsIso g]
    (S : CoefficientDerivedSystemCalculus l E (Spec (.of D.k)))
    (r : IntegralComparisonRoosModel l E (Spec (.of D.k))) :
    ∃ d : PointQuotientComparisonData D l E g, PointQuotientComparisonNormalized D l E g d := by
  obtain ⟨_, _, _, _, j, eta, _, _, hj, hi, _, hf, hs, _, _, _⟩ :=
    isomorphismMultiplicationConeDescent l E g
      (frobeniusPointPrimeUnit D l hl) (frobeniusPointPrimeUnit D l hl) S r
  exact ⟨⟨j, eta⟩, hj, hi, hf, hs⟩

include hl in
/-- The uniquely specified strict point comparison data.
Source: multiplication-cone descent
(blueprint: def-pur-point-quotient-comparison-coordinates).

The existence theorem determines both data fields. The inverse of j is prescribed on every
section in every degree and tower level, determining the tower natural isomorphism by
extensionality and uniqueness of inverses. The two cone coordinates determine every component
of eta.hom by binary biproduct extensionality on the shifted cone; its inverse is then unique.
Thus the definition chooses no arbitrary mathematical object from mere existence. The auxiliary
calculus and Roos model only supply the existence proof, and cannot change either data field. -/
def pointQuotientComparisonData
    (g : Spec (.of D.k) ⟶ Spec (.of D.k)) [IsIso g]
    (S : CoefficientDerivedSystemCalculus l E (Spec (.of D.k)))
    (r : IntegralComparisonRoosModel l E (Spec (.of D.k))) :
    PointQuotientComparisonData D l E g :=
  (pointQuotientComparison_exists D l hl E g S r).choose

end WeilConjectures.PointFrobeniusNormalization
