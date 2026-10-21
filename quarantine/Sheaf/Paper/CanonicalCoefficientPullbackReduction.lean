/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NG
-/
module

public import Sheaf.Paper.ConstantWeilStructure
public import Sheaf.AlgebraicGeometry.ProEtale.InverseImagePullbackComparison
public import Sheaf.Paper.CompletedIntegralConstantMapOfUniverses
public import Sheaf.Paper.IntegralDerivedOperationsOnSlices
public import Sheaf.Algebra.Homology.KFlat
import Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients
import Sheaf.Algebra.Category.ModuleCat.Sheaf.SiteTensorFunctoriality
import Sheaf.AlgebraicGeometry.ProEtaleCountableProductsExact
import WeilConjectures.CategoryTheory.Triangulated.DerivedLimitExistence
import Sheaf.Paper.IntegralOperationsWellDefined
import Sheaf.CategoryTheory.StrictRoosComparison
import Sheaf.Paper.FiniteFreeCompletedScalarComparison
import Sheaf.Paper.IntegralReductionTowerWellDefinedUnrestricted
import Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel
import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
import Sheaf.AlgebraicGeometry.ProEtale.IsoSectionwiseInverseImage
import Sheaf.Paper.ConstantCoefficientScalarNormalization
import Sheaf.Paper.InverseImagePullbackComparisonDerived
import Sheaf.Algebra.Homology.KFlatIndependentCoefficients

/-!
# Canonical coefficient pullback and its finite quotient projections

Source: Stacks Tags 03D6 and 08TC; blueprint prop-cohomological-finiteness, Step 7
(blueprint: lem-pod-canonical-coefficient-pullback-reduction).

The sectionwise inverse image used by the specified kappa is compared with the
normalized constant Weil structure through the actual regular-module coefficient
maps. Finite multiplication and projection from the strict Roos cone are retained
as morphisms, including their transition maps before localization. Level n means
positive exponent n+1 throughout.

## Main definitions

* `canonicalCoefficientKappa`: the recorded comparison on the regular good complex.
* `canonicalCoefficientLambda`, `canonicalCoefficientLambdaFinite`: the normalized
  integral comparison and finite multiplication, with coefficient-model transport.
* `canonicalCoefficientRho`: the actual quotient-cone projection and reduction.
* `canonicalCoefficientProjection`, `canonicalCoefficientInverseProjection`: the
  two coefficient projections in the same integral derived category.
* `canonicalCoefficientPullbackTransition`, `canonicalCoefficientInverseTransition`:
  the strict finite quotient transitions.

## Main statements

* `canonicalCoefficientModelMaps_isIso`: the regular coefficient identifications.
* `canonicalCoefficientPullbackReduction`: inverse and projection identities,
  strict transition compatibility, and the published constant-Weil normalization.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 2048

universe u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme AlgebraicGeometry.ProEtale

namespace WeilConjectures

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- The regular-module map R_X to the sectionwise inverse image of R_Y.
Its sectionwise formula is c_R inverse: send 1 to 1 and transport scalars by c_R.
Source: Stacks 03D6; inverse-image-pullback-comparison, structure isomorphism
(blueprint: lem-pod-canonical-coefficient-pullback-reduction). -/
def canonicalCoefficientIntegralUnit {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g] :
    SheafOfModules.unit (completedIntegralCoefficientSheafUnrestricted l E X) ⟶
    (inverseImageIntegralModules l E g).obj
      (SheafOfModules.unit (completedIntegralCoefficientSheafUnrestricted l E Y)) :=
  (SheafOfModules.unitHomEquiv _).symm
    (PresheafOfModules.sectionsMk
      (fun U ↦ (1 : (completedIntegralCoefficientSheafUnrestricted l E Y).obj.obj
        (op ((proEtaleIsoPostcompose g).obj U.unop))))
      (fun {_ _} f ↦ map_one
        ((completedIntegralCoefficientSheafUnrestricted l E Y).obj.map
          ((proEtaleIsoPostcompose g).map f.unop).op).hom))
/-- The finite regular-module map B_X,n to inverse image of B_Y,n,
sending 1 to 1 with scalar action through c_n inverse.
Source: Stacks 03D6, module pullback along the coefficient isomorphism
(blueprint: lem-pod-canonical-coefficient-pullback-reduction). -/
def canonicalCoefficientFiniteUnit {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
    (n : ℕ) : SheafOfModules.unit (integralCoefficientSheaf l E X n) ⟶
    (inverseImageFiniteModules l E g n).obj
      (SheafOfModules.unit (integralCoefficientSheaf l E Y n)) :=
  (SheafOfModules.unitHomEquiv _).symm
    (PresheafOfModules.sectionsMk
      (fun U ↦ (1 : (integralCoefficientSheaf l E Y n).obj.obj
        (op ((proEtaleIsoPostcompose g).obj U.unop))))
      (fun {_ _} f ↦ map_one
        ((integralCoefficientSheaf l E Y n).obj.map
          ((proEtaleIsoPostcompose g).map f.unop).op).hom))
/-- The canonical multiplication identification of reduction of the regular
module with the finite regular module, transposed from the actual coefficient
projection under the normalized tensor/restriction adjunction.
Source: Stacks 03D6; node proof Step 7
(blueprint: lem-pod-canonical-coefficient-pullback-reduction). -/
def canonicalCoefficientReduction (W : Scheme.{u}) (n : ℕ) :=
  ((scalarReductionExtension_adjunction l E W n).choose.homEquiv _ _).symm
    (constantCoefficientProjection l E W n)
/-- The same canonical reduction identification on the regular complexes,
using the exact degree-zero single-complex comparison.
Source: Stacks 03D6; node proof Step 7
(blueprint: lem-pod-canonical-coefficient-pullback-reduction). -/
def canonicalCoefficientReductionComplex (W : Scheme.{u}) (n : ℕ) :=
  ((unrestrictedIntegralReductionFunctor l E W n).mapCochainComplexSingleFunctor 0).hom.app
      (SheafOfModules.unit (completedIntegralCoefficientSheafUnrestricted l E W)) ≫
    (CochainComplex.singleFunctor _ 0).map (canonicalCoefficientReduction l E W n)

/-- The regular finite coefficient complex B_Y,n[0].
Source: node statement, finite coefficient objects; Stacks 03D6
(blueprint: lem-pod-canonical-coefficient-pullback-reduction). -/
def canonicalCoefficientFiniteComplex (W : Scheme.{u}) (n : ℕ) :=
  (CochainComplex.singleFunctor (integralOperationsFiniteModules l E W n) 0).obj
    (SheafOfModules.unit (integralCoefficientSheaf l E W n))

/-- The finite tensor-unit chain map x to x tensor 1, whose inverse is multiplication.
Source: inverse-image-pullback-comparison (a); node proof Step 2; Stacks 03D6
(blueprint: lem-pod-canonical-coefficient-pullback-reduction). -/
def canonicalCoefficientFiniteKappaComplex {X Y : Scheme.{u}}
    (g : X ⟶ Y) [IsIso g] (n : ℕ) :=
  inverseImageFiniteComparisonComplex l E g n (canonicalCoefficientFiniteComplex l E Y n)

/-- The maps used to identify the coefficient models are isomorphisms.
Source: node statement, c_R and c_n, finite multiplication and canonical reduction;
node proof Steps 2 and 7; Stacks 03D6
(blueprint: lem-pod-canonical-coefficient-pullback-reduction).
Proof: on sections the integral and finite unit maps are c_R inverse and c_n inverse,
respectively, so the coefficient isomorphisms give their inverses. The reduction map
s tensor x to s*pi_n(x) is inverse to b to b tensor 1 by the balancing relation.
These commute with differentials, giving the reduction complex isomorphism. Finally
x tensor b to c_n inverse(b)*x is inverse to the sheafified tensor-unit map in every
degree. The formulas commute with restrictions, so they descend from presheaves to
sheaves. Exact degree-zero comparisons preserve all these inverse identities. -/
theorem canonicalCoefficientModelMaps_isIso {X Y : Scheme.{u}}
    (g : X ⟶ Y) [IsIso g] :
    IsIso (canonicalCoefficientIntegralUnit l E g) ∧
      ∀ n : ℕ, IsIso (canonicalCoefficientFiniteUnit l E g n) ∧
        IsIso (canonicalCoefficientReductionComplex l E Y n) ∧
        IsIso (canonicalCoefficientFiniteKappaComplex l E g n) := by
  sorry

/-- c_R on regular objects in the sectionwise inverse-image presentation.
It is defined from the actual coefficient map, independently of kappa and lambda.
Source: node structure isomorphism and proof Step 1; Stacks 03D6
(blueprint: lem-pod-canonical-coefficient-pullback-reduction). -/
def canonicalCoefficientIntegralComparison {X Y : Scheme.{u}}
    (g : X ⟶ Y) [IsIso g] :=
  ((inverseImageIntegralModules l E g).mapDerivedCategorySingleFunctor 0).app
      (SheafOfModules.unit (completedIntegralCoefficientSheafUnrestricted l E Y)) ≪≫
    (DerivedCategory.singleFunctor (integralTowerModules l E X) 0).mapIso
      (@asIso _ _ _ _ (canonicalCoefficientIntegralUnit l E g)
        (canonicalCoefficientModelMaps_isIso l E g).1).symm

/-- The canonical transport from the normalized termwise inverse-image realization
of constantWeilIntegralLambda to the sectionwise realization of the specified kappa.
It uses only the two independently constructed coefficient comparisons c_R.
Source: node proof Steps 1 and 9; Stacks 03D6
(blueprint: lem-pod-canonical-coefficient-pullback-reduction). -/
def canonicalCoefficientInverseImageTransport {X Y : Scheme.{u}}
    (g : X ⟶ Y) [IsIso g] :=
  constantWeilDerivedCoefficientComparison l E g ≪≫
    (canonicalCoefficientIntegralComparison l E g).symm

/-- lambda_R is the normalized multiplication/completeness comparison, transported
by the coefficient-model identification. No inverse of kappa is used to define it.
Source: node proof Steps 2--6 and 9; Stacks 03D6 and 08TC
(blueprint: lem-pod-canonical-coefficient-pullback-reduction). -/
def canonicalCoefficientLambda {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g] :=
  constantWeilIntegralLambda l E g ≪≫ canonicalCoefficientInverseImageTransport l E g

/-- kappa_R is exactly the specified zero-homotopy Roos augmentation of definition
(b), on the regular flat-term K-flat representative with its identity resolution.
Source: inverse-image-pullback-comparison (b); node proof Step 6; Stacks 08TC
(blueprint: lem-pod-canonical-coefficient-pullback-reduction). -/
def canonicalCoefficientKappa {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
    (hX : ∀ x : X, IsUnit (l : X.presheaf.stalk x))
    (hY : ∀ y : Y, IsUnit (l : Y.presheaf.stalk y)) :=
  inverseImagePullbackComparison l E g hX hY
    (constantWeilIntegralComplex l E Y) (constantWeilIntegralGood l E Y) (𝟙 _)

/-- The actual finite multiplication chain isomorphism lambda_n. Its inverse is the
recorded sheafified x to x tensor 1 map, which uniquely fixes multiplication.
Source: node proof Step 2; Stacks 03D6
(blueprint: lem-pod-canonical-coefficient-pullback-reduction). -/
def canonicalCoefficientLambdaFinite {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
    (n : ℕ) :=
  (@asIso _ _ _ _ (canonicalCoefficientFiniteKappaComplex l E g n)
    ((canonicalCoefficientModelMaps_isIso l E g).2 n).2.2).symm

/-- c_n on finite regular complexes in the sectionwise inverse-image model.
Source: node structure isomorphism and proof Step 2; Stacks 03D6
(blueprint: lem-pod-canonical-coefficient-pullback-reduction). -/
def canonicalCoefficientFiniteComparison {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
    (n : ℕ) :=
  ((inverseImageFiniteModules l E g n).mapCochainComplexSingleFunctor 0).app
      (SheafOfModules.unit (integralCoefficientSheaf l E Y n)) ≪≫
    (CochainComplex.singleFunctor (integralOperationsFiniteModules l E X n) 0).mapIso
      (@asIso _ _ _ _ (canonicalCoefficientFiniteUnit l E g n)
        ((canonicalCoefficientModelMaps_isIso l E g).2 n).1).symm

/-- The finite restriction of scalars Res_n, on actual complexes.
Source: completed-integral-coefficients; node statement; Stacks 03D6
(blueprint: lem-pod-canonical-coefficient-pullback-reduction). -/
abbrev canonicalCoefficientRes (W : Scheme.{u}) (n : ℕ) :=
  integralOperationsRestrict l E W n

/-- The pulled-back canonical reduction identification, followed by restriction
of scalars. It identifies the strict quotient tower term with Res_n Lg_n^* B_Y,n.
Source: node proof Step 7; Stacks 03D6
(blueprint: lem-pod-canonical-coefficient-pullback-reduction). -/
def canonicalCoefficientPullbackReductionIso {X Y : Scheme.{u}}
    (g : X ⟶ Y) [IsIso g] (n : ℕ) :=
  (canonicalCoefficientRes l E X n).mapIso
    (((integralOperationsLevelPullback l E g n).mapHomologicalComplex (.up ℤ)).mapIso
      (@asIso _ _ _ _ (canonicalCoefficientReductionComplex l E Y n)
        ((canonicalCoefficientModelMaps_isIso l E g).2 n).2.1))

/-- rho_n is the defining good-representative comparison, the actual first Roos
coordinate and nth product projection, then the pulled reduction identification.
Its source is P_g R_Y; its target is Res_n Lg_n^* B_Y,n in the single R_X category.
Source: node proof Steps 3, 4 and 7; Stacks 08TC
(blueprint: lem-pod-canonical-coefficient-pullback-reduction). -/
def canonicalCoefficientRho {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g] (n : ℕ) :=
  (integralDerivedPullbackComparison l E g).hom.app (constantWeilIntegralGood l E Y) ≫
    DerivedCategory.Q.map
      (CochainComplex.mappingCocone.fst (constantWeilPullbackRoosEndomorphism l E g) ≫
        Pi.π (fun m ↦ (constantWeilPullbackTower l E g).obj (op m)) n) ≫
    DerivedCategory.Q.map (canonicalCoefficientPullbackReductionIso l E g n).hom

/-- pi_n,X as an R_X-linear derived morphism, with exact restriction-of-scalars
and degree-zero comparisons included.
Source: node proof Step 7; Stacks 03D6
(blueprint: lem-pod-canonical-coefficient-pullback-reduction). -/
def canonicalCoefficientProjection (W : Scheme.{u}) (n : ℕ) :=
  DerivedCategory.Q.map
    ((CochainComplex.singleFunctor _ 0).map (constantCoefficientProjection l E W n) ≫
      ((scalarReductionRestriction l E W n).mapCochainComplexSingleFunctor 0).inv.app
        (SheafOfModules.unit (integralCoefficientSheaf l E W n)))

/-- The inverse-image projection g^-1(pi_n,Y), expressed using the actual canonical
coefficient square c_R*pi_n,X = g^-1(pi_n,Y)*c_n. All maps here depend only on
coefficient projections and c_R,c_n, independently of lambda and rho.
Source: node structure square and proof Steps 1 and 8; Stacks 03D6
(blueprint: lem-pod-canonical-coefficient-pullback-reduction). -/
def canonicalCoefficientInverseProjection {X Y : Scheme.{u}}
    (g : X ⟶ Y) [IsIso g] (n : ℕ) :=
  (canonicalCoefficientIntegralComparison l E g).hom ≫
    canonicalCoefficientProjection l E X n ≫
    DerivedCategory.Q.map
      ((canonicalCoefficientRes l E X n).map
        (canonicalCoefficientFiniteComparison l E g n).inv)

/-- theta_R = c_R composed with lambda_R in the recorded sectionwise model.
Source: node statement and proof Steps 8--9; Stacks 03D6 and blueprint Step 7
(blueprint: lem-pod-canonical-coefficient-pullback-reduction). -/
def canonicalCoefficientTheta {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g] :=
  canonicalCoefficientLambda l E g ≪≫ canonicalCoefficientIntegralComparison l E g

/-- The specified finite pullback transition, transported by the two canonical
reduction identifications. This is a chain map before taking the derived limit.
Source: node proof Steps 3 and 7; Stacks 03D6 and 08TC
(blueprint: lem-pod-canonical-coefficient-pullback-reduction). -/
def canonicalCoefficientPullbackTransition {X Y : Scheme.{u}}
    (g : X ⟶ Y) [IsIso g] (n : ℕ) :=
  (canonicalCoefficientPullbackReductionIso l E g (n + 1)).inv ≫
    (integralOperationsPullbackTransition l E g n).app (constantWeilIntegralComplex l E Y) ≫
    (canonicalCoefficientPullbackReductionIso l E g n).hom

/-- The actual A_(n+2) to A_(n+1) quotient map on restricted regular complexes.
Reduction of the unit complex is identified with B_n by multiplication, so conjugating
the recorded pure-tensor transition gives precisely the quotient map.
Source: node proof Step 7; Stacks 03D6
(blueprint: lem-pod-canonical-coefficient-pullback-reduction). -/
def canonicalCoefficientTransition (W : Scheme.{u}) (n : ℕ) :=
  (canonicalCoefficientRes l E W (n + 1)).map
      ((@asIso _ _ _ _ (canonicalCoefficientReductionComplex l E W (n + 1))
        ((canonicalCoefficientModelMaps_isIso l E (𝟙 W)).2 (n + 1)).2.1).inv) ≫
    (unrestrictedIntegralTransition l E W n).app (constantWeilIntegralComplex l E W) ≫
    (canonicalCoefficientRes l E W n).map (canonicalCoefficientReductionComplex l E W n)

/-- The corresponding inverse-image quotient transition, transported through c_n.
Source: node proof Step 3; Stacks 03D6
(blueprint: lem-pod-canonical-coefficient-pullback-reduction). -/
def canonicalCoefficientInverseTransition {X Y : Scheme.{u}}
    (g : X ⟶ Y) [IsIso g] (n : ℕ) :=
  (canonicalCoefficientRes l E X (n + 1)).map
      (canonicalCoefficientFiniteComparison l E g (n + 1)).hom ≫
    canonicalCoefficientTransition l E X n ≫
    (canonicalCoefficientRes l E X n).map (canonicalCoefficientFiniteComparison l E g n).inv

/-- The normalized comparison inverts the specified kappa and preserves its quotient
projections, including the theta projection and strict transition compatibility.
Source: Stacks 03D6, 08TC; blueprint prop-cohomological-finiteness, Proof Step 7
(blueprint: lem-pod-canonical-coefficient-pullback-reduction).
Proof:
1. The pro-etale isomorphism inverse-image theorem relabels sheaves, actions and
products; c_R and c_n transport actions by their inverse coefficient maps.
2. Multiplication x tensor b to c_n inverse(b)*x is inverse to x to x tensor 1.
These are the actual finite chain maps used in lambda_n and commute with reduction.
3. Apply multiplication in both coordinates of Cone(1-s)[-1], using its actual
product projections. This gives L and F(e_n)*L = mu_n*e'_n strictly.
4. Exact countable products and strict Roos comparison identify these concrete
complexes and projections with the specified completed derived pullback model.
5. The regular complex is K-flat with flat terms. Its zero-shifted-coordinate
augmentation is the canonical completeness map eta, invertible by constant
coefficient constructibility and the finite-free-completed-scalar comparison at L=E.
6. The specified kappa is the zero-homotopy augmentation. Multiplication sends
that augmentation to F(eta) in both cone coordinates. Thus the normalized
lambda = F(eta)^(-1)*L has both inverse identities with this actual kappa.
7. The reduction identification is multiplication, transposed from pi_n under the
normalized scalar adjunction. Its quotient and transition equations follow on
pure tensors, so rho is exactly the defining cone projection followed by it.
8. Naturality of multiplication and the cone-projection equation give
Res(lambda_n)*rho_n = F(pi_n)*lambda_R. Compose with c_n and use the coefficient
square to obtain pi_n,X*theta_R = Res(c_n*lambda_n)*rho_n. The strict multiplication
squares give compatibility before localization; the cone homotopy gives rho
compatibility in the derived category.
9. The transport between the two inverse-image models uses only c_R. Consequently
theta is the published normalized constantWeilIntegralTheta, including its
geometric-Frobenius specialization, without a cohomological Frobenius assertion. -/
theorem canonicalCoefficientPullbackReduction (D : FiniteFieldDatum.{u}) (_hl : l ≠ D.p)
    {X Y : Scheme.{u}}
    (g : X ⟶ Y) [IsIso g]
    (hX : ∀ x : X, IsUnit (l : X.presheaf.stalk x))
    (hY : ∀ y : Y, IsUnit (l : Y.presheaf.stalk y)) :
    canonicalCoefficientKappa l E g hX hY ≫ (canonicalCoefficientLambda l E g).hom = 𝟙 _ ∧
      (canonicalCoefficientLambda l E g).hom ≫ canonicalCoefficientKappa l E g hX hY =
        𝟙 _ ∧
      (∀ n : ℕ,
        canonicalCoefficientRho l E g n ≫ DerivedCategory.Q.map
            ((canonicalCoefficientRes l E X n).map
              (canonicalCoefficientLambdaFinite l E g n).hom) =
          (canonicalCoefficientLambda l E g).hom ≫
            canonicalCoefficientInverseProjection l E g n) ∧
      (∀ n : ℕ,
        (canonicalCoefficientTheta l E g).hom ≫ canonicalCoefficientProjection l E X n =
          canonicalCoefficientRho l E g n ≫ DerivedCategory.Q.map
            ((canonicalCoefficientRes l E X n).map
              ((canonicalCoefficientLambdaFinite l E g n).hom ≫
                (canonicalCoefficientFiniteComparison l E g n).hom))) ∧
      (∀ n : ℕ,
        canonicalCoefficientPullbackTransition l E g n ≫
            (canonicalCoefficientRes l E X n).map
              (canonicalCoefficientLambdaFinite l E g n).hom =
          (canonicalCoefficientRes l E X (n + 1)).map
              (canonicalCoefficientLambdaFinite l E g (n + 1)).hom ≫
            canonicalCoefficientInverseTransition l E g n) ∧
      (∀ n : ℕ,
        canonicalCoefficientRho l E g (n + 1) ≫
            DerivedCategory.Q.map (canonicalCoefficientPullbackTransition l E g n) =
          canonicalCoefficientRho l E g n) ∧
      canonicalCoefficientTheta l E g = constantWeilIntegralTheta l E g := by
  sorry

end WeilConjectures
