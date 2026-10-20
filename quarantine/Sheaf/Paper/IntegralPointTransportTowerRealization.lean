/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q14
-/
module

public import Sheaf.SixFunctors.FrobeniusPointTransport
public import Sheaf.Paper.SfIntegralConstructible
public import Sheaf.AlgebraicGeometry.ProEtaleCohomologicalSupport
public import Sheaf.Paper.IntrinsicFiniteTorsionConstructibility
public import Sheaf.Paper.SfDerivedComplete
public import Sheaf.Paper.AdicCoefficientDatum
import Sheaf.Paper.DerivedPullbackTensorHom
import Sheaf.Paper.FiniteFreeCompletedScalarComparison
import Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients
import Sheaf.AlgebraicGeometry.ProEtaleCountableProductsExact
import WeilConjectures.CategoryTheory.Triangulated.DerivedLimitExistence
import Sheaf.Paper.PointProEtaleSectionsExact
import Sheaf.Paper.IntegralOperationsWellDefined
import Sheaf.Paper.InverseImagePullbackComparisonDerived

/-!
# Integral point transport as the realization of the finite transports

Source: Weil blueprint, main-20261015, sec-trace-formula/sk-d-weil,
prop-trf-rational-frobenius-integral-model.proof.md, clause (3)
(blueprint: lem-trf-integral-point-transport-tower-realization).

All towers below are strict towers of complexes over the single integral coefficient
ring. The index n denotes exponent n+1. The existential comparisons are normalized
on both cone components, so the assertion fixes the specified derived morphism.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 2048

universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.ProEtale

namespace WeilConjectures

variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime]
  (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- Termwise integral sections, with the recorded O_E action.
Source: blueprint clause (3) (blueprint: lem-trf-integral-point-transport-tower-realization). -/
abbrev trfPointSectionsComplex :=
  (pointIntegralSections l E D.k).mapHomologicalComplex (ComplexShape.up ℤ)

/-- The evaluated quotient-induced tower, before any localization.
Source: blueprint clause (3), common K-flat model
(blueprint: lem-trf-integral-point-transport-tower-realization). -/
def trfPointSourceTower :=
  (Functor.ofOpSequence (X := fun n ↦
    unrestrictedIntegralComplexFunctor l E (Spec (.of D.k)) n)
    (unrestrictedIntegralTransition l E (Spec (.of D.k)))).flip ⋙
      (Functor.whiskeringRight _ _ _).obj (trfPointSectionsComplex D l E)

/-- The evaluated strict tower Res_n g_n^*(P_n), with its coefficient-induced transitions.
Source: blueprint clause (3), completed pullback model
(blueprint: lem-trf-integral-point-transport-tower-realization). -/
def trfPointTargetTower :=
  integralOperationsPullbackTowerFunctor l E (frobeniusPointIso D).hom ⋙
    (Functor.whiskeringRight _ _ _).obj (trfPointSectionsComplex D l E)

/-- The specified 1-s on the evaluated source tower.
Source: blueprint clause (3), shifted cone
(blueprint: lem-trf-integral-point-transport-tower-realization). -/
def trfPointSourceEnd (P : CochainComplex (integralTowerModules l E (Spec (.of D.k))) ℤ) :=
  towerTransitionEndomorphism
    (K := fun n ↦ ((trfPointSourceTower D l E).obj P).obj (op n))
    (integralOperationsTowerStep ((trfPointSourceTower D l E).obj P))

/-- The specified 1-s on the evaluated pullback tower.
Source: blueprint clause (3), shifted cone
(blueprint: lem-trf-integral-point-transport-tower-realization). -/
def trfPointTargetEnd (P : CochainComplex (integralTowerModules l E (Spec (.of D.k))) ℤ) :=
  towerTransitionEndomorphism
    (K := fun n ↦ ((trfPointTargetTower D l E).obj P).obj (op n))
    (integralOperationsTowerStep ((trfPointTargetTower D l E).obj P))

/-- The same 1-s before applying sections.
Source: blueprint clause (3), sectionwise product computation
(blueprint: lem-trf-integral-point-transport-tower-realization). -/
def trfPointSheafTargetEnd
    (P : CochainComplex (integralTowerModules l E (Spec (.of D.k))) ℤ) :=
  towerTransitionEndomorphism
    (K := fun n ↦
      ((integralOperationsPullbackTowerFunctor l E (frobeniusPointIso D).hom).obj P).obj (op n))
    (integralOperationsTowerStep
      ((integralOperationsPullbackTowerFunctor l E (frobeniusPointIso D).hom).obj P))

/-- The finite transports form a strict tower morphism; its specified cone realization
is the actual integral point transport, naturally in the derived object.

Source: blueprint main-20261015, prop-trf-rational-frobenius-integral-model.proof.md,
clause (3) (blueprint: lem-trf-integral-point-transport-tower-realization).

Proof:
1. By lem-pc-kflat-resolution choose a common flat-term K-flat representative P.
   Its strict quotients represent the coherent reduction tower of
   def-weil-pbc-adic-coefficient-datum. Finite comparison (a) and sigma in
   def-weil-frobenius-point-transport give u_n by restriction and the tensor unit.
2. Restriction, colimit insertion and sheafification commute with quotient maps.
   The coefficient projection square of def-weil-inverse-image-pullback-comparison
   makes this equality linear. Thus the displayed u_n form the strict map U.
3. Apply the two-component cone construction of lem-pur-integral-operations-well-defined.
   Its map is diagonal on the two products. Products are exact and sectionwise by
   lem-weil-proetale-countable-products-exact; lem-weil-derived-limit-existence
   identifies them with derived products. Exact point sections, from
   lem-weil-point-proetale-sections-exact, preserve quasi-isomorphisms. The map beta
   below is the identity on these two sectionwise product components.
4. The normalized alpha has components x to 1 tensor x and zero. It is the
   identity-extension completeness unit of lem-weil-finite-free-completed-scalar-comparison,
   transported by the canonical balanced tensor identification. Derived completeness
   makes it invertible. The target comparison is the recorded completed pullback
   comparison followed by beta, and hence is invertible too.
5. Comparison (b) in def-weil-inverse-image-pullback-comparison is the zero-homotopy
   lift of theta_n. On sections theta_n sigma equals u_n r_n. Consequently the two
   sides of the displayed realization equation agree in both cone components,
   including the zero shifted component. This compares the specified integral map,
   rather than deducing equality from its reductions.
6. All formulas commute with complex maps. Normalized descent and exact sections
   extend them across quasi-isomorphisms. Applying the chain-map equalities to both
   arrows of a roof proves naturality for arbitrary derived morphisms and independence
   of the common resolution. Thus alpha, beta and the realized tower morphism give
   the asserted natural completeness identifications. -/
theorem integralPointTransportTowerRealization (hl : l ≠ D.p) :
    ∃ (U : trfPointSourceTower D l E ⟶ trfPointTargetTower D l E)
      (α : trfPointSectionsComplex D l E ⟶
        trfPointSourceTower D l E ⋙ integralOperationsRoosFunctor)
      (β : integralOperationsPullbackComplexFunctor l E (frobeniusPointIso D).hom ⋙
          trfPointSectionsComplex D l E ≅
        trfPointTargetTower D l E ⋙ integralOperationsRoosFunctor),
      (∀ (P : CochainComplex (integralTowerModules l E (Spec (.of D.k))) ℤ)
        (n : ℕ) (i : ℤ)
        (x : (((unrestrictedIntegralFiniteComplex l E (Spec (.of D.k)) n).obj P).X i).val.obj
          (op (ProEt.mk (𝟙 (Spec (.of D.k)))))),
        (((U.app P).app (op n)).f i) x =
          ((((integralOperationsPullbackLevel l E (frobeniusPointIso D).hom n).obj P).X i).val.map
            (proEtaleIsoCommaArrow (frobeniusPointIso D).hom
              (ProEt.mk (𝟙 (Spec (.of D.k))))).op
            (integralOperationsPullbackGenerator l E (frobeniusPointIso D).hom n
              (((unrestrictedIntegralFiniteComplex l E (Spec (.of D.k)) n).obj P).X i)
              ((proEtaleIsoPostcompose (frobeniusPointIso D).hom).obj
                (ProEt.mk (𝟙 (Spec (.of D.k)))))
              ((((unrestrictedIntegralFiniteComplex l E (Spec (.of D.k)) n).obj P).X i).val.map
                (frobeniusPointRestriction D).op x)))) ∧
      (∀ (P : CochainComplex (integralTowerModules l E (Spec (.of D.k))) ℤ)
        (i : ℤ) (n : ℕ) (x : (P.X i).val.obj (op (ProEt.mk (𝟙 (Spec (.of D.k)))))),
        ((α.app P).f i ≫ (CochainComplex.mappingCocone.fst
            (trfPointSourceEnd D l E P)).f i ≫
          (Pi.π (fun n ↦ ((trfPointSourceTower D l E).obj P).obj (op n)) n).f i) x =
          unrestrictedIntegralTensorSection l E (Spec (.of D.k)) n (P.X i)
            (op (ProEt.mk (𝟙 (Spec (.of D.k))))) 1 x) ∧
      (∀ (P : CochainComplex (integralTowerModules l E (Spec (.of D.k))) ℤ) (i : ℤ),
        (α.app P).f i ≫ (CochainComplex.mappingCocone.snd
          (trfPointSourceEnd D l E P)).v i (i - 1) (by omega) = 0) ∧
      (∀ (P : CochainComplex (integralTowerModules l E (Spec (.of D.k))) ℤ)
        (i : ℤ) (n : ℕ),
        (β.hom.app P).f i ≫ (CochainComplex.mappingCocone.fst
            (trfPointTargetEnd D l E P)).f i ≫
          (Pi.π (fun n ↦ ((trfPointTargetTower D l E).obj P).obj (op n)) n).f i =
        ((trfPointSectionsComplex D l E).map
          (CochainComplex.mappingCocone.fst (trfPointSheafTargetEnd D l E P) ≫
            Pi.π (fun n ↦
              ((integralOperationsPullbackTowerFunctor l E (frobeniusPointIso D).hom).obj P).obj
                (op n)) n)).f i) ∧
      (∀ (P : CochainComplex (integralTowerModules l E (Spec (.of D.k))) ℤ)
        (i : ℤ) (n : ℕ),
        (β.hom.app P).f i ≫ (CochainComplex.mappingCocone.snd
            (trfPointTargetEnd D l E P)).v i (i - 1) (by omega) ≫
          (Pi.π (fun n ↦ ((trfPointTargetTower D l E).obj P).obj (op n)) n).f (i - 1) =
        (pointIntegralSections l E D.k).map
          ((CochainComplex.mappingCocone.snd (trfPointSheafTargetEnd D l E P)).v
              i (i - 1) (by omega) ≫
            (Pi.π (fun n ↦
              ((integralOperationsPullbackTowerFunctor l E (frobeniusPointIso D).hom).obj P).obj
                (op n)) n).f (i - 1))) ∧
      (∀ P : (integralOperationsGoodComplex l E (Spec (.of D.k))).FullSubcategory,
        sfIntegralConstructible l E (Spec (.of D.k)) (DerivedCategory.Q.obj P.obj) →
        IsIso (DerivedCategory.Q.map (α.app P.obj)) ∧
          frobeniusPointTransportIntegral D l hl E (DerivedCategory.Q.obj P.obj) ≫
            (pointFibreIntegralAmbient D l E).map
              ((integralDerivedPullbackComparison l E (frobeniusPointIso D).hom).hom.app P) ≫
            (pointIntegralSections l E D.k).mapDerivedCategoryFactors.hom.app
              ((integralOperationsPullbackComplexFunctor l E (frobeniusPointIso D).hom).obj
                P.obj) ≫
            DerivedCategory.Q.map (β.hom.app P.obj) =
          (pointIntegralSections l E D.k).mapDerivedCategoryFactors.hom.app P.obj ≫
            DerivedCategory.Q.map (α.app P.obj) ≫
            DerivedCategory.Q.map (integralOperationsRoosMap (U.app P.obj))) ∧
      (∀ (N N' : sfIntegralConstructibleCategory l E (Spec (.of D.k)))
        (f : N ⟶ N'),
        (pointFibreIntegralAmbient D l E).map f.hom ≫
            frobeniusPointTransportIntegral D l hl E N'.obj =
          frobeniusPointTransportIntegral D l hl E N.obj ≫
            (pointFibreIntegralAmbient D l E).map
              ((integralDerivedPullback l E (frobeniusPointIso D).hom).map f.hom)) := by
  sorry

end WeilConjectures
