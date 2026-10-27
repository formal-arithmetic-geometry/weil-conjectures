/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group G6
-/
module

public import Sheaf.Paper.PointTransportStrictQuotient
import Sheaf.Paper.PointTransportStrictQuotientIdentities
import Sheaf.Paper.PointTransportStrictQuotientSections

/-! # Strict finite point transport on arbitrary complexes
Source: blueprint rational Frobenius integral model, clause (3), strict quotient step.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.ProEtale
namespace WeilConjectures

attribute [local instance 5000] integralTowerHasDerivedCategory
attribute [local irreducible] CategoryTheory.Limits.limit
  completedIntegralCoefficientSheafUnrestricted completedIntegralCommRingSheafUnrestricted
  HasDerivedCategory.standard HasDerivedCategory.ofIsGrothendieckAbelian
  HasDerivedCategory.ofHasKInjectiveResolutions DerivedCategory.Q
  integralDerivedPullback integralDerivedPullbackComparison
  Functor.mapDerivedCategory Functor.mapDerivedCategoryFactors
  unrestrictedTowerUnit unrestrictedIntegralTransition strictQuotientPointMap

variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime]
  (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- The specified finite point maps commute with quotient transitions and arbitrary
complex maps before localization, and have the prescribed section formula.
Source: blueprint main-20261015, prop-trf-rational-frobenius-integral-model.proof.md,
clause (3), realization steps 1--2 and chain naturality in step 6
(blueprint: lem-trf-point-transport-strict-quotient-all-complexes).

Proof: restriction of presheaf sections is natural in the module. The finite sigma
is that restriction followed by insertion into the sectionwise inverse image.
The normalized finite comparison inserts the tensor unit and sheafifies. Both
identity-on-sections scalar comparisons in strictQuotientPointMap leave the underlying
section unchanged, giving the displayed formula. Quotient transitions preserve this
insertion because they send a tensor generator to the generator with its coefficient
reduced; the completed coefficient projection square makes the resulting maps linear.
This proves the transition equality on sheafified generators, hence on all sections.
The same calculation for an arbitrary module homomorphism proves degreewise naturality.
All operations commute with differentials, so these are equalities of chain maps.
The assumption l ≠ D.p supplies the usual invertibility of l on the point.
No K-flatness, flatness, boundedness or constructibility is used in these calculations. -/
theorem pointTransport_strictQuotient_allComplexes (_hl : l ≠ D.p) :
    (∀ (P : CochainComplex (integralTowerModules l E (Spec (.of D.k))) ℤ) (n : ℕ),
      ((pointIntegralSections l E D.k).mapHomologicalComplex (.up ℤ)).map
          ((unrestrictedIntegralTransition l E (Spec (.of D.k)) n).app P) ≫
          strictQuotientPointMap D l E n P =
        strictQuotientPointMap D l E (n + 1) P ≫
          ((pointIntegralSections l E D.k).mapHomologicalComplex (.up ℤ)).map
            ((integralOperationsPullbackTransition l E (frobeniusPointIso D).hom n).app P)) ∧
    (∀ (P P' : CochainComplex (integralTowerModules l E (Spec (.of D.k))) ℤ)
      (f : P ⟶ P') (n : ℕ),
      ((pointIntegralSections l E D.k).mapHomologicalComplex (.up ℤ)).map
          ((unrestrictedIntegralComplexFunctor l E (Spec (.of D.k)) n).map f) ≫
          strictQuotientPointMap D l E n P' =
        strictQuotientPointMap D l E n P ≫
          ((pointIntegralSections l E D.k).mapHomologicalComplex (.up ℤ)).map
            ((integralOperationsPullbackLevel l E (frobeniusPointIso D).hom n).map f)) ∧
    (∀ (P : CochainComplex (integralTowerModules l E (Spec (.of D.k))) ℤ)
      (n : ℕ) (i : ℤ)
      (x : (((unrestrictedIntegralFiniteComplex l E (Spec (.of D.k)) n).obj P).X i).val.obj
        (op (ProEt.mk (𝟙 (Spec (.of D.k)))))),
      ((strictQuotientPointMap D l E n P).f i) x =
        ((((integralOperationsPullbackLevel l E (frobeniusPointIso D).hom n).obj P).X i).val.map
          (proEtaleIsoCommaArrow (frobeniusPointIso D).hom
            (ProEt.mk (𝟙 (Spec (.of D.k))))).op
          (integralOperationsPullbackGenerator l E (frobeniusPointIso D).hom n
            (((unrestrictedIntegralFiniteComplex l E (Spec (.of D.k)) n).obj P).X i)
            ((proEtaleIsoPostcompose (frobeniusPointIso D).hom).obj
              (ProEt.mk (𝟙 (Spec (.of D.k)))))
            ((((unrestrictedIntegralFiniteComplex l E (Spec (.of D.k)) n).obj P).X i).val.map
              (frobeniusPointRestriction D).op x)))) := by
  exact ⟨(strictQuotientPointMap_identities D l E).1,
    (strictQuotientPointMap_identities D l E).2.2,
    fun P n i x ↦ strictQuotientPointMap_sections D l E n P i x⟩

end WeilConjectures
