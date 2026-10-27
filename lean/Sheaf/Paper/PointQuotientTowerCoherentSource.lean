/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group E4
-/
module

public import Sheaf.Paper.PointQuotientTowerData
import all Sheaf.Paper.AdicCoefficientDatum
import Sheaf.Paper.PbcIsoRestrictionKFlat
import Sheaf.Paper.PointQuotientTowerStrictComparison

/-! # The canonical comparison for the whole quotient tower

(blueprint: lem-trf-point-quotient-tower-coherent-source)

This is the coherent-source part of lem-trf-point-quotient-tower-homotopy.
The public statement and its constructions are unchanged by the file split.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option synthInstance.maxSize 4096

universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.ProEtale
namespace WeilConjectures.PointQuotientTower

variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime]
  (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

attribute [local irreducible] completedIntegralCoefficientSheafUnrestricted
  completedIntegralCommRingSheafUnrestricted scalarReductionDerivedExistence
  HasDerivedCategory.standard pointIntegralSectionMap
  unrestrictedTowerResolutionIso unrestrictedTowerUnit unrestrictedIntegralTransition
  unrestrictedIntegralReductionExistence scalarReductionExistence


attribute [local irreducible] constantSheaf presheafToSheaf integralCoefficientCommRingSheaf

attribute [local irreducible] Functor.mapDerivedCategory Functor.mapDerivedCategoryFactors
  Functor.mapDerivedCategoryFactorsh

attribute [local irreducible] completedReductionTower
/-- The source represents exact sections of the entire coherent reduction tower.
Proof: pbcIntegralDatum supplies the Noetherian, finite torsion residue and perfect
finite quotient hypotheses of def-weil-pbc-adic-coefficient-datum. The normalized
coefficient isomorphisms are those of
lem-weil-pbc-integral-coefficient-presentation-comparison. Transport P along e;
restriction along a ring isomorphism preserves flatness and K-flatness. Send
b tensor x to e_n(b) tensor x, with inverse using e_n inverse. The projection
identities make this balanced; the quotient-transition identities make the maps
commute with every transition. They commute with differentials and give r on the
whole complex of towers. The universal coherent-tower counit is invertible on
the transported K-flat P. Compose it with the exact restriction and sections
factorizations and the image of r. Every factor is invertible, giving precisely
the displayed gamma. This proves the comparison in the derived category of whole
diagrams, before any separate evaluation.
Source: blueprint clause (3) (blueprint: lem-trf-point-quotient-tower-homotopy). -/
theorem coherentSource (_hl : l ≠ D.p) :
    ∀ q : ∀ n : ℕ, PbcIntegralRing l E ⧸ (pbcIntegralDatum l E).ideal ^ (n + 1) ≃+*
        ULift.{u + 1} (Padic.coefficientExtensionRing l E (n + 1)),
      (∀ (n : ℕ) (x : PbcIntegralRing l E), q n (Ideal.Quotient.mk _ x) =
        ULift.up (Ideal.Quotient.mk _ x.down)) →
      ∀ e : pbcAdicCompletion (Spec (.of D.k)) (pbcIntegralDatum l E) ≅
          completedIntegralCommRingSheafUnrestricted l E (Spec (.of D.k)),
        (∀ n : ℕ, e.hom ≫ completedIntegralCommRingProjectionUnrestricted l E
            (Spec (.of D.k)) n =
          pbcAdicProjection (Spec (.of D.k)) (pbcIntegralDatum l E) n ≫
            (IntegralCoefficientPresentation.level l E (Spec (.of D.k)) q n).hom) →
        CoherentSourceComparison D l E q e := by
  intro q hq e he P
  obtain ⟨r, hr⟩ := strictPresentationComparison l E (Spec (.of D.k)) q hq e he P.obj
  have hk := pbcIsoRestriction_isKFlat (Spec (.of D.k)) e P.obj P.property.1
  have hc : IsIso (completedReductionTowerComplexCounit (Spec (.of D.k))
      (pbcIntegralDatum l E)
      (((pbcRestrict e.hom).mapHomologicalComplex (.up ℤ)).obj P.obj)) := by
    exact AlgebraicGeometry.Scheme.towerCounit_isIso (Spec (.of D.k))
      (pbcIntegralDatum l E) _ hk
  let γ :=
    (sectionsTowers D l E).mapDerivedCategory.mapIso
      ((restrictTowers D l E e).mapDerivedCategory.mapIso
        ((completedReductionTower (Spec (.of D.k)) (pbcIntegralDatum l E)).mapIso
          ((pbcRestrict e.hom).mapDerivedCategoryFactors.app P.obj) ≪≫
          (@asIso _ _ _ _ _ hc))) ≪≫
      (sectionsTowers D l E).mapDerivedCategory.mapIso
        ((restrictTowers D l E e).mapDerivedCategoryFactors.app
          ((completedReductionComplexTowerFunctor (Spec (.of D.k))
            (pbcIntegralDatum l E)).obj
              (((pbcRestrict e.hom).mapHomologicalComplex (.up ℤ)).obj P.obj))) ≪≫
      (sectionsTowers D l E).mapDerivedCategory.mapIso (DerivedCategory.Q.mapIso r) ≪≫
      (sectionsTowers D l E).mapDerivedCategoryFactors.app
        ((sourceSheafTower D l E).obj P.obj)
  exact ⟨r, hr, γ, rfl⟩

end WeilConjectures.PointQuotientTower
