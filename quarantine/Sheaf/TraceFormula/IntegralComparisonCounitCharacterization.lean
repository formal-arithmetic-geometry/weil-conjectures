/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q116
-/
module

public import Sheaf.Paper.InverseImagePullbackComparisonDerived
public import Sheaf.Paper.IntegralComparisonRealizationModels
public import Sheaf.Paper.SfIntegralConstructible
public import Sheaf.CategoryTheory.StrictRoosComparison
import Sheaf.CategoryTheory.PreDerivedAdjointFunctorsGeneral
import WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction
import Sheaf.AlgebraicGeometry.ProEtaleCountableProductsExact

/-!
# Whole-tower characterization of the specified integral comparison

Source: Stacks Project, Derived Categories, Tags 0FND and 0DVC, and Cohomology on
Sites, Tag 0941; blueprint Global powers, Step 1 of
`sec-trace-formula/sk-thm-trace-transport/thm-trf-l-function-euler-product.proof.md`
(blueprint: lem-trf-integral-comparison-counit-characterization).

The first statement includes arbitrary unbounded derived variables, normalization on
every simultaneous K-injective resolution, and hence independence of the resolution.
The second uses the actual quotient tower and the actual zero-homotopy Roos lift.
The index n denotes the positive exponent n+1 throughout.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 4096
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] WeilConjectures.sfAbSheafify WeilConjectures.sfAbBijective

universe t u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry.Scheme
open WeilConjectures

namespace AlgebraicGeometry.ProEtale

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- The derived constant-tower/limit Hom map is bijective, natural in both derived
variables, and given by the ordinary projection counit on every K-injective resolution.
The last equality identifies every choice with the same natural counit; thus the Hom
map is independent of that choice under the canonical derived-limit identifications.

Source: Stacks Project, Tags 0FND, 0DVC and 0941
(blueprint: lem-trf-integral-comparison-counit-characterization).

Proof plan (Steps 1--3 of the node): the sectionwise limit universal property gives
the additive ordinary adjunction constLimAdj. Levelwise exactness of towers makes
the constant functor exact. Lift the adjunction to homotopy categories using
lem-weil-pbc-termwise-adjunction-homotopy. The total derived limit exists and is
computed on a simultaneous K-injective resolution by
lem-weil-pbc-ringed-strict-tower-homotopy-limit. Apply
lem-pc-pre-derived-adjoint-functors-general with F=lim and G=Delta. Its canonical
fraction formula at s=j, t=id, f=id identifies the adjunct of the identity with
the localized projection counit followed by [j] inverse. Naturality gives the
displayed formula for every morphism and both arbitrary localized variables.
The formula for every j also proves independence of the resolution. -/
theorem integralComparisonLimitCounitCharacterization (X : AlgebraicGeometry.Scheme.{t}) :
    (∀ (H : DerivedCategory (integralTowerModules l E X))
      (T : coefficientSequenceRestrictedDerived l E X),
      Function.Bijective (fun f : H ⟶ (coefficientConstantTowerLimit l E X).obj T ↦
        (integralComparisonConstantTower l E X).map f ≫
          (integralComparisonTowerCounit l E X).app T)) ∧
    (∀ (H H' : DerivedCategory (integralTowerModules l E X))
      (T T' : coefficientSequenceRestrictedDerived l E X)
      (a : H' ⟶ H) (b : T ⟶ T')
      (f : H ⟶ (coefficientConstantTowerLimit l E X).obj T),
      (integralComparisonConstantTower l E X).map
          (a ≫ f ≫ (coefficientConstantTowerLimit l E X).map b) ≫
          (integralComparisonTowerCounit l E X).app T' =
        (integralComparisonConstantTower l E X).map a ≫
          ((integralComparisonConstantTower l E X).map f ≫
            (integralComparisonTowerCounit l E X).app T) ≫ b) ∧
    (∀ (T I : CochainComplex (ℕᵒᵖ ⥤ integralTowerModules l E X) ℤ)
      (j : T ⟶ I) [QuasiIso j] [I.IsKInjective]
      (_hI : ∀ p : ℤ, Injective (I.X p)),
      (integralComparisonTowerCounit l E X).app (DerivedCategory.Q.obj T) =
        (integralComparisonConstantTower l E X).map
          ((coefficientConstantTowerLimit l E X).map (DerivedCategory.Q.map j) ≫
            (Functor.rightDerivedFunctorObjQIso
              (lim : (ℕᵒᵖ ⥤ integralTowerModules l E X) ⥤ integralTowerModules l E X) I).hom) ≫
        (Functor.const ℕᵒᵖ : integralTowerModules l E X ⥤
          ℕᵒᵖ ⥤ integralTowerModules l E X).mapDerivedCategoryFactors.hom.app
            (((lim : (ℕᵒᵖ ⥤ integralTowerModules l E X) ⥤
              integralTowerModules l E X).mapHomologicalComplex (.up ℤ)).obj I) ≫
        DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex
          (constLimAdj (J := ℕᵒᵖ) (C := integralTowerModules l E X)).counit (.up ℤ)).app I) ≫
        inv (DerivedCategory.Q.map j)) := by
  sorry

variable {X Y : AlgebraicGeometry.Scheme.{t}} (g : X ⟶ Y) [IsIso g]

/-- The actual tower Res_n g_n^*(P_n), read as a complex in the tower category by
the existing equivalence between diagrams of complexes and complexes of diagrams.
Source: the specified comparison definition (b), Stacks Tag 0941
(blueprint: lem-trf-integral-comparison-counit-characterization). -/
abbrev integralComparisonPullbackStrictTower
    (P : CochainComplex (integralTowerModules l E Y) ℤ) :=
  (HomologicalComplex.functorEquivalence (integralTowerModules l E X) (.up ℤ) ℕᵒᵖ).inverse.obj
    ((integralOperationsPullbackTowerFunctor l E g).obj P)

/-- The strict tensor-unit family theta, retaining all actual quotient transitions.
Source: the specified comparison definition (b), Stacks Tags 03D6 and 08TC
(blueprint: lem-trf-integral-comparison-counit-characterization). -/
def integralComparisonThetaStrictTower
    (P : CochainComplex (integralTowerModules l E Y) ℤ) :=
  (HomologicalComplex.functorEquivalence (integralTowerModules l E X) (.up ℤ) ℕᵒᵖ).inverse.map
    (NatTrans.ofOpSequence
      (F := (Functor.const ℕᵒᵖ).obj
        (((inverseImageIntegralModules l E g).mapHomologicalComplex (.up ℤ)).obj P))
      (G := (integralOperationsPullbackTowerFunctor l E g).obj P)
      (fun n ↦ inverseImageReductionTheta l E g n P)
      (fun n ↦ by
        simpa [integralOperationsPullbackTowerFunctor] using
          (inverseImageReductionTheta_compatible l E g n P).symm))

/-- Identify completed derived pullback with the total limit of the actual tower,
using precisely the normalized Roos comparison and the chosen resolution q.
Source: comparison definition (b) and Stacks Tag 0941
(blueprint: lem-trf-integral-comparison-counit-characterization). -/
def integralComparisonPullbackLimitIso
    (ρ : IntegralComparisonRoosModel l E X)
    (K : CochainComplex (integralTowerModules l E Y) ℤ)
    (P : (integralOperationsGoodComplex l E Y).FullSubcategory)
    (q : P.obj ⟶ K) [QuasiIso q] :
    (integralDerivedPullback l E g).obj (DerivedCategory.Q.obj K) ≅
      (coefficientConstantTowerLimit l E X).obj
        (DerivedCategory.Q.obj (integralComparisonPullbackStrictTower l E g P.obj)) :=
  ((integralDerivedPullback l E g).mapIso (asIso (DerivedCategory.Q.map q))).symm ≪≫
    (integralDerivedPullbackComparison l E g).app P ≪≫
    (ρ.comparison.app (integralComparisonPullbackStrictTower l E g P.obj)).symm

/-- The specified comparison is the unique arrow with the whole-tower adjunct
theta composed with the inverse of inverse-image(q). The second conjunct identifies
the same arrow with the actual zero shifted-product cone lift after normalized Roos
transport. K is in the recorded bounded constructible complete integral subcategory.

Source: comparison definition (b); Stacks Tags 0FND, 0DVC and 0941; blueprint Global
powers, Step 1 of thm-trf-l-function-euler-product
(blueprint: lem-trf-integral-comparison-counit-characterization).

Proof plan (Steps 4--6 of the node): form the actual restricted finite pullback
tower C_g and its compatible quotient-unit family theta using
def-weil-inverse-image-pullback-comparison. Countable products are exact on the
small pro-etale site by lem-weil-proetale-countable-products-exact, so
lem-weil-strict-roos-comparison identifies its specified cone with total limit.
Choose j:C_g to J. The strict family j theta has the unique ordinary limit lift a.
On the two cone coordinates C(j) thetaTilde=i_J a, both being (0,j theta).
The normalization rho=[i_J] inverse [C(j)] therefore sends thetaTilde to [a].
The ordinary projection identity then gives epsilon Delta([a])=[theta] in the
derived category of whole towers. Conjugate by [g inverse(q)] inverse. By Steps
1--3 the Hom map is bijective, proving existence and uniqueness of this adjunct.
The definition of kappa gives exactly the second displayed equality. No equality
is inferred solely from projections after localization. -/
theorem integralComparisonCounitCharacterization
    {S T : AlgebraicGeometry.Scheme.{u}} (h : S ⟶ T) [IsIso h]
    (hS : ∀ x : S, IsUnit (l : S.presheaf.stalk x))
    (hT : ∀ y : T, IsUnit (l : T.presheaf.stalk y))
    (ρ : IntegralComparisonRoosModel l E S)
    (K : CochainComplex (integralTowerModules l E T) ℤ)
    (_hK : sfIntegralConstructible l E T (DerivedCategory.Q.obj K))
    (P : (integralOperationsGoodComplex l E T).FullSubcategory)
    (q : P.obj ⟶ K) [QuasiIso q] :
    (∀ f : (inverseImageIntegralDerived l E h).obj (DerivedCategory.Q.obj K) ⟶
        (integralDerivedPullback l E h).obj (DerivedCategory.Q.obj K),
      ((integralComparisonConstantTower l E S).map
          (f ≫ (integralComparisonPullbackLimitIso l E h ρ K P q).hom) ≫
        (integralComparisonTowerCounit l E S).app
          (DerivedCategory.Q.obj (integralComparisonPullbackStrictTower l E h P.obj)) =
      (integralComparisonConstantTower l E S).map
          ((inverseImageIntegralModules l E h).mapDerivedCategoryFactors.hom.app K ≫
            inv (DerivedCategory.Q.map
              (((inverseImageIntegralModules l E h).mapHomologicalComplex (.up ℤ)).map q))) ≫
        (Functor.const ℕᵒᵖ : integralTowerModules l E S ⥤
          ℕᵒᵖ ⥤ integralTowerModules l E S).mapDerivedCategoryFactors.hom.app
            (((inverseImageIntegralModules l E h).mapHomologicalComplex (.up ℤ)).obj P.obj) ≫
        DerivedCategory.Q.map (integralComparisonThetaStrictTower l E h P.obj)) ↔
      f = inverseImagePullbackComparison l E h hS hT K P q) ∧
    (inverseImagePullbackComparison l E h hS hT K P q ≫
        (integralComparisonPullbackLimitIso l E h ρ K P q).hom =
      (inverseImageIntegralModules l E h).mapDerivedCategoryFactors.hom.app K ≫
        inv (DerivedCategory.Q.map
          (((inverseImageIntegralModules l E h).mapHomologicalComplex (.up ℤ)).map q)) ≫
        DerivedCategory.Q.map (inverseImageRoosComparisonComplex l E h P.obj) ≫
        (ρ.comparison.app (integralComparisonPullbackStrictTower l E h P.obj)).inv) := by
  sorry

end AlgebraicGeometry.ProEtale
