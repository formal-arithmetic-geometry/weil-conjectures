/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q14
-/
module

public import Sheaf.Algebra.Homology.KFlatIndependentCoefficients
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import Sheaf.AlgebraicGeometry.FrobeniusDetailed
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Sheaf.Paper.IntegralOperationsWellDefined
public import Sheaf.Paper.DerivedPullbackTensorHom
public import Sheaf.Paper.TraceFormulaCoefficientConventions
public import Sheaf.Paper.AdicCoefficientDatum
public import Sheaf.Paper.InverseImagePullbackComparisonDerived
public import Sheaf.Paper.IntegralDerivedOperationsOnSlices
public import Sheaf.Paper.CompletedIntegralConstantMapOfUniverses
public import Sheaf.SixFunctors.FrobeniusPointTransport
public import Sheaf.Paper.CompletedStalkReparametrizationCoherence
public import Sheaf.Paper.IntegralReductionTowerCanonical
import Sheaf.AlgebraicGeometry.ProEtaleCountableProductsExact
public import Sheaf.Paper.PointProEtaleSectionsExact
import Sheaf.SixFunctors.FrobeniusPointTransportNatural
import Sheaf.Algebra.Homology.SiteDerivedTensorDescentIndependentCoefficients
import Mathlib.CategoryTheory.Localization.Predicate

/-! # Point transport, both Roos coordinates, and descent through roofs

Source: blueprint main-20261015, sec-trace-formula/sk-d-weil/
prop-trf-rational-frobenius-integral-model.proof.md, clause (3), realization steps 5--6
(blueprint: lem-trf-point-transport-cone-comparison-descent).

The natural index n denotes the positive exponent n+1. All section complexes have
one integral coefficient ring. The cone and its section comparison are the existing
constructions, including their shifted product coordinate. No completeness is assumed.

## Main statements

* `pointTransportConeComparison`: the strict equality and both resolution identities.
* `pointTransportConeComparisonDescent`: independence and naturality for all derived roofs.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 4096
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall

universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.ProEtale

attribute [local irreducible] limit WeilConjectures.completedIntegralCoefficientSheafUnrestricted
  HasDerivedCategory.standard CochainComplex.mappingCocone towerTransitionEndomorphism
attribute [local irreducible] WeilConjectures.pointIntegralSections
  WeilConjectures.integralOperationsPullbackLevel
namespace WeilConjectures.PointTransportCone

variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime]
  (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- The exact section-complex functor with its canonical integral action.
Source: blueprint clause (3) (blueprint: lem-trf-point-transport-cone-comparison-descent). -/
abbrev sections := (pointIntegralSections l E D.k).mapHomologicalComplex (.up ℤ)

/-- The existing small-Hom localization for integral module complexes at the point.
Source: blueprint clause (3) (blueprint: lem-trf-point-transport-cone-comparison-descent). -/
abbrev moduleQ := CompletedStalk.moduleQ l E

/-- The exact-sections localization comparison, with both localization sizes explicit.
Source: blueprint clause (3) (blueprint: lem-trf-point-transport-cone-comparison-descent). -/
def sectionsFactors :=
  @Functor.mapDerivedCategoryFactors _ _ _ (HasDerivedCategory.standard _)
    _ _ _ (HasDerivedCategory.ofIsGrothendieckAbelian _)
    (pointIntegralSections l E D.k) _ _ _

/-- D(P), the strict tower of sections of restricted finite reductions.
Source: blueprint clause (3) (blueprint: lem-trf-point-transport-cone-comparison-descent). -/
def reductionTowers :=
  (Functor.ofOpSequence (X := unrestrictedIntegralComplexFunctor l E (Spec (.of D.k)))
    (unrestrictedIntegralTransition l E (Spec (.of D.k)))).flip ⋙
      (Functor.whiskeringRight ℕᵒᵖ _ _).obj (sections D l E)

/-- B(P), the strict tower of sections of the actual finite pullbacks C(P).
Source: blueprint clause (3) (blueprint: lem-trf-point-transport-cone-comparison-descent). -/
def pullbackTowers :=
  integralOperationsPullbackTowerFunctor l E (frobeniusPointIso D).hom ⋙
    (Functor.whiskeringRight ℕᵒᵖ _ _).obj (sections D l E)

attribute [local irreducible] reductionTowers

/-- The two published scalar-extension presentations give the identical section complex.
Source: blueprint clause (3), the common integral coefficient convention
(blueprint: lem-trf-point-transport-cone-comparison-descent).
Proof: unfold unrestrictedTowerComplex and unrestrictedTowerFiniteComplex, then
scalarReductionExtension and scalarReductionExistence. Unfold reductionTowers and
unrestrictedIntegralComplexFunctor, unrestrictedIntegralFiniteComplex,
unrestrictedIntegralReductionFunctor and unrestrictedIntegralReductionExistence.
The two witnesses are the same derived-change-of-rings theorem on the same limit
projection with the same standard localization instances. Restriction of scalars
and termwise sections are identical. The resulting object equality is reflexivity. -/
theorem reductionSectionModel_eq
    (P : CochainComplex (integralTowerModules l E (Spec (.of D.k))) ℤ) (n : ℕ) :
    (sections D l E).obj (unrestrictedTowerComplex l E (Spec (.of D.k)) n P) =
      ((reductionTowers D l E).obj P).obj (op n) := by
  sorry

/-- Gamma(r_n), with explicit transport between the identical published tensor models.
This uses the existing unit, with no choice of a different reduction map.
Source: blueprint clause (3) (blueprint: lem-trf-point-transport-cone-comparison-descent). -/
def reductionUnit
    (P : CochainComplex (integralTowerModules l E (Spec (.of D.k))) ℤ) (n : ℕ) :=
  (sections D l E).map (unrestrictedTowerUnit l E (Spec (.of D.k)) P n) ≫
    eqToHom (reductionSectionModel_eq D l E P n)

/-- The product of the maps Gamma(r_n), using the published tensor-unit reduction.
Source: blueprint clause (3) (blueprint: lem-trf-point-transport-cone-comparison-descent). -/
def reductionProduct (P : CochainComplex (integralTowerModules l E (Spec (.of D.k))) ℤ) :
    (sections D l E).obj P ⟶
      ∏ᶜ fun n ↦ ((reductionTowers D l E).obj P).obj (op n) :=
  Pi.lift (f := fun n ↦ ((reductionTowers D l E).obj P).obj (op n))
    (fun n ↦ reductionUnit D l E P n)

/-- The actual one-minus-shift endomorphism of the product of D(P).
Source: blueprint clause (3) (blueprint: lem-trf-point-transport-cone-comparison-descent). -/
def reductionEnd (P : CochainComplex (integralTowerModules l E (Spec (.of D.k))) ℤ) :=
  towerTransitionEndomorphism (K := fun n ↦ ((reductionTowers D l E).obj P).obj (op n))
    (integralOperationsTowerStep ((reductionTowers D l E).obj P))

/-- Strict compatibility of reductions makes the zero-homotopy lift a chain map.
Source: blueprint clause (3), node proof step 1
(blueprint: lem-trf-point-transport-cone-comparison-descent).
Proof: reduction sends 1 tensor x to 1 tensor x. Thus r_(n+1) followed by t_n is r_n.
After each product projection the product of reductions followed by 1-s is zero.
Product extensionality gives zero before localization. The differential of the zero
cochain is zero, which is precisely the mapping-cocone lift condition. -/
theorem augmentation_condition
    (P : CochainComplex (integralTowerModules l E (Spec (.of D.k))) ℤ) :
    CochainComplex.HomComplex.δ (-1) 0
        (0 : CochainComplex.HomComplex.Cochain ((sections D l E).obj P)
          (∏ᶜ fun n ↦ ((reductionTowers D l E).obj P).obj (op n)) (-1)) +
      CochainComplex.HomComplex.Cochain.ofHom
        (reductionProduct D l E P ≫ reductionEnd D l E P) = 0 := by
  sorry

/-- a_P is the specified lift (0,(Gamma(r_n)z)_n), with zero shifted component.
Source: blueprint clause (3) (blueprint: lem-trf-point-transport-cone-comparison-descent). -/
def augmentation (P : CochainComplex (integralTowerModules l E (Spec (.of D.k))) ℤ) :=
  CochainComplex.mappingCocone.lift
    (reductionEnd D l E P)
    (reductionProduct D l E P) 0
    (augmentation_condition D l E P)

/-- c_C is the existing unique comparison preserving both sectionwise cone coordinates.
Source: blueprint clause (3) (blueprint: lem-trf-point-transport-cone-comparison-descent). -/
def coneSections (P : CochainComplex (integralTowerModules l E (Spec (.of D.k))) ℤ) :=
  CompletedStalk.sectionsRoos D l E
    ((integralOperationsPullbackTowerFunctor l E (frobeniusPointIso D).hom).obj P)

/-- The specified b_q: completed pullback comparison, exact sections, then c_C.
Source: blueprint clause (3) (blueprint: lem-trf-point-transport-cone-comparison-descent). -/
def representativeComparison
    (N : CochainComplex (integralTowerModules l E (Spec (.of D.k))) ℤ)
    (P : (integralOperationsGoodComplex l E (Spec (.of D.k))).FullSubcategory)
    (q : P.obj ⟶ N) [QuasiIso q] :
    (pointFibreIntegralAmbient D l E).obj
        ((integralDerivedPullback l E (frobeniusPointIso D).hom).obj
          (DerivedCategory.Q.obj N)) ≅
      (moduleQ l E).obj (integralOperationsRoos ((pullbackTowers D l E).obj P.obj)) :=
  (pointFibreIntegralAmbient D l E).mapIso
      ((integralDerivedPullback l E (frobeniusPointIso D).hom).mapIso
        (asIso (DerivedCategory.Q.map q)).symm) ≪≫
    (pointFibreIntegralAmbient D l E).mapIso
      ((integralDerivedPullbackComparison l E (frobeniusPointIso D).hom).app P) ≪≫
    (sectionsFactors D l E).app
      ((integralOperationsPullbackComplexFunctor l E (frobeniusPointIso D).hom).obj P.obj) ≪≫
    (moduleQ l E).mapIso (coneSections D l E P.obj)

/-- The actual chain map H(u)a_P in its localized section-complex presentation.
Source: blueprint clause (3) (blueprint: lem-trf-point-transport-cone-comparison-descent). -/
def coneArrow (P : CochainComplex (integralTowerModules l E (Spec (.of D.k))) ℤ)
    (v : (reductionTowers D l E).obj P ⟶ (pullbackTowers D l E).obj P) :=
  (moduleQ l E).map (augmentation D l E P ≫ integralOperationsRoosMap v)

/-- The same arrow with domain the derived sections of [P], via the canonical factorization.
Source: blueprint clause (3) (blueprint: lem-trf-point-transport-cone-comparison-descent). -/
def resolvedArrow
    (P : CochainComplex (integralTowerModules l E (Spec (.of D.k))) ℤ)
    (v : (reductionTowers D l E).obj P ⟶ (pullbackTowers D l E).obj P) :=
  (sectionsFactors D l E).hom.app P ≫ coneArrow D l E P v

/-- The strict comparison on both cone components and the two resolution identities.
Source: blueprint clause (3), realization steps 5--6
(blueprint: lem-trf-point-transport-cone-comparison-descent).
Proof (node steps 1--5): the reductions and theta maps are strictly compatible,
so their zero-first-component lifts are chain maps. Strictness of v makes H(v)
the diagonal map on both products. Exact point sections identify both products and
the finite biproduct, so c_C is the identity in these coordinates. On a section z,
the two composites are (0,(Gamma(theta_n)sigma_P z)_n) and
(0,(v_n Gamma(r_n)z)_n), equal by the augmentation equations, including the zero
shifted component. Point-transport naturality gives sigma_N Gamma(q) =
Gamma(g^-1 q) sigma_P. Exact sections and exact inverse image preserve q's
quasi-isomorphism. Under the specified representative comparison, kappa is the
zero-homotopy theta lift preceded by the inverse of g^-1(q). Cancel this inverse
against the sigma square and apply the strict identity. This gives the first
derived formula. Right cancellation of Gamma(q) gives the second; a_P is never inverted. -/
theorem pointTransportConeComparison (hl : l ≠ D.p)
    (N : CochainComplex (integralTowerModules l E (Spec (.of D.k))) ℤ)
    (P : (integralOperationsGoodComplex l E (Spec (.of D.k))).FullSubcategory)
    (q : P.obj ⟶ N) [QuasiIso q]
    (v : (reductionTowers D l E).obj P.obj ⟶ (pullbackTowers D l E).obj P.obj)
    (hv : ∀ n : ℕ,
      frobeniusPointIntegralSigma D l E P.obj ≫
          (sections D l E).map
            (inverseImageReductionTheta l E (frobeniusPointIso D).hom n P.obj) =
        reductionUnit D l E P.obj n ≫
          v.app (op n)) :
    (frobeniusPointIntegralSigma D l E P.obj ≫
        (sections D l E).map
          (inverseImageRoosComparisonComplex l E (frobeniusPointIso D).hom P.obj) ≫
        (coneSections D l E P.obj).hom =
      augmentation D l E P.obj ≫ integralOperationsRoosMap v) ∧
    IsIso ((pointFibreIntegralAmbient D l E).map (DerivedCategory.Q.map q)) ∧
    ((sections D l E).map q ≫ frobeniusPointIntegralSigma D l E N =
      frobeniusPointIntegralSigma D l E P.obj ≫ (sections D l E).map
        (((inverseImageIntegralModules l E (frobeniusPointIso D).hom).mapHomologicalComplex
          (.up ℤ)).map q)) ∧
    ((pointFibreIntegralAmbient D l E).map (DerivedCategory.Q.map q) ≫
        frobeniusPointTransportIntegral D l hl E (DerivedCategory.Q.obj N) ≫
        (representativeComparison D l E N P q).hom = resolvedArrow D l E P.obj v) ∧
    (frobeniusPointTransportIntegral D l hl E (DerivedCategory.Q.obj N) ≫
        (representativeComparison D l E N P q).hom =
      inv ((pointFibreIntegralAmbient D l E).map (DerivedCategory.Q.map q)) ≫
        resolvedArrow D l E P.obj v) := by
  sorry

/-- Good quasi-isomorphisms induce invertible maps on the whole sectionwise Roos cone.
Source: blueprint clause (3), node steps 4 and 7
(blueprint: lem-trf-point-transport-cone-comparison-descent).
Proof: integral-operations well-definedness gives a quasi-isomorphism on the sheaf
Roos complexes. Exact sections preserve it. The natural c_C comparison conjugates
its class to the displayed diagonal Roos map, which is therefore invertible. -/
theorem pullbackRoof_isIso
    (P Q : (integralOperationsGoodComplex l E (Spec (.of D.k))).FullSubcategory)
    (a : Q ⟶ P) [QuasiIso a.hom] :
    IsIso ((moduleQ l E).map
      (integralOperationsRoosMap ((pullbackTowers D l E).map a.hom))) := by
  sorry

/-- The isomorphism T(a) for a good quasi-isomorphism, with the actual diagonal map as hom.
Source: blueprint clause (3) (blueprint: lem-trf-point-transport-cone-comparison-descent). -/
def pullbackRoofIso
    (P Q : (integralOperationsGoodComplex l E (Spec (.of D.k))).FullSubcategory)
    (a : Q ⟶ P) [QuasiIso a.hom] :=
  @asIso _ _ _ _
    ((moduleQ l E).map (integralOperationsRoosMap ((pullbackTowers D l E).map a.hom)))
    (pullbackRoof_isIso D l E P Q a)

/-- Chain-natural tower maps give the specified natural transformation on all derived
objects, independent of good representatives, with its explicit square for every roof.
Source: blueprint clause (3), realization steps 5--6
(blueprint: lem-trf-point-transport-cone-comparison-descent).
Proof (node steps 6--8): reduction and its unit commute with every chain map h;
finite inverse image and its tensor-unit comparison do as well. The zero shifted
coordinates remain zero. Naturality of v and the diagonal formula for H give
H(h_B) eta_P = eta_P' Gamma(h). The two-coordinate comparison c_C commutes with
these maps. Exact sections invert quasi-isomorphisms. The completed-pullback
well-definedness theorem inverts good quasi-isomorphisms and supplies its natural
representative comparisons. Localization of flat-term K-flat complexes is the
ambient derived category by site-derived-tensor descent. Apply the localization
universal property for natural transformations and its uniqueness to descend eta.
For a roof P <-a- Q -b-> P', invert the naturality square for a and compose with
that for b. This gives T(a)^-1 T(b) after eta_P equal to S(a)^-1 S(b) before
eta_P'. Localization makes this independent of the roof presentation. The preceding
comparison theorem identifies the descended component with the specified integral
point transport on each resolution q. Uniqueness gives independence for any two
resolutions. Neither completeness of N nor invertibility of its augmentation is used. -/
theorem pointTransportConeComparisonDescent (hl : l ≠ D.p)
    (v : (integralOperationsGoodComplex l E (Spec (.of D.k))).ι ⋙ reductionTowers D l E ⟶
      (integralOperationsGoodComplex l E (Spec (.of D.k))).ι ⋙ pullbackTowers D l E)
    (hv : ∀ (P : (integralOperationsGoodComplex l E (Spec (.of D.k))).FullSubcategory)
      (n : ℕ),
      frobeniusPointIntegralSigma D l E P.obj ≫
          (sections D l E).map
            (inverseImageReductionTheta l E (frobeniusPointIso D).hom n P.obj) =
        reductionUnit D l E P.obj n ≫
          (v.app P).app (op n)) :
    (∃! η : pointFibreIntegralAmbient D l E ⟶
        integralDerivedPullback l E (frobeniusPointIso D).hom ⋙ pointFibreIntegralAmbient D l E,
      (∀ N : DerivedCategory (integralTowerModules l E (Spec (.of D.k))),
        η.app N = frobeniusPointTransportIntegral D l hl E N) ∧
      (∀ (N : CochainComplex (integralTowerModules l E (Spec (.of D.k))) ℤ)
        (P : (integralOperationsGoodComplex l E (Spec (.of D.k))).FullSubcategory)
        (q : P.obj ⟶ N) [QuasiIso q],
        η.app (DerivedCategory.Q.obj N) ≫ (representativeComparison D l E N P q).hom =
          inv ((pointFibreIntegralAmbient D l E).map (DerivedCategory.Q.map q)) ≫
            resolvedArrow D l E P.obj (v.app P))) ∧
    (∀ (N : CochainComplex (integralTowerModules l E (Spec (.of D.k))) ℤ)
      (P P' : (integralOperationsGoodComplex l E (Spec (.of D.k))).FullSubcategory)
      (q : P.obj ⟶ N) (q' : P'.obj ⟶ N) [QuasiIso q] [QuasiIso q'],
      inv ((pointFibreIntegralAmbient D l E).map (DerivedCategory.Q.map q)) ≫
          resolvedArrow D l E P.obj (v.app P) ≫
          (representativeComparison D l E N P q).inv =
        inv ((pointFibreIntegralAmbient D l E).map (DerivedCategory.Q.map q')) ≫
          resolvedArrow D l E P'.obj (v.app P') ≫
          (representativeComparison D l E N P' q').inv) ∧
    (∀ (P Q P' : (integralOperationsGoodComplex l E (Spec (.of D.k))).FullSubcategory)
      (a : Q ⟶ P) (b : Q ⟶ P') [QuasiIso a.hom],
      IsIso ((moduleQ l E).map
        (integralOperationsRoosMap ((pullbackTowers D l E).map a.hom))) ∧
      (coneArrow D l E P.obj (v.app P) ≫
          (pullbackRoofIso D l E P Q a).inv ≫
          (moduleQ l E).map
            (integralOperationsRoosMap ((pullbackTowers D l E).map b.hom)) =
        inv ((moduleQ l E).map ((sections D l E).map a.hom)) ≫
          (moduleQ l E).map ((sections D l E).map b.hom) ≫
          coneArrow D l E P'.obj (v.app P'))) := by
  sorry

end WeilConjectures.PointTransportCone
