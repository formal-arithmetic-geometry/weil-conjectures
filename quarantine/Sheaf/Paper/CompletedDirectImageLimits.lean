/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q07
-/
module

public import Sheaf.Paper.CompletedPullback
public import Sheaf.Paper.FourArrows
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.KInjective
public import Mathlib.CategoryTheory.Adjunction.Whiskering
public import Sheaf.Algebra.Homology.KFlatIndependentCoefficients
import WeilConjectures.Algebra.Homology.TowerEvaluationKInjective
import Sheaf.Algebra.Homology.KInjectiveProductsTermwise
import Sheaf.AlgebraicGeometry.ProEtaleConstantRingOperations
import Sheaf.AlgebraicGeometry.ProEtaleCountableProductsExact
import Sheaf.AlgebraicGeometry.ProfiniteCoefficientInverseImage
import Sheaf.CategoryTheory.DiagramSiteRealization
import Sheaf.CategoryTheory.KInjectiveTotalDerived
import Sheaf.CategoryTheory.RingedStrictTowerHomotopyLimitIndependentCoefficients
import Sheaf.Paper.AdicCoefficientDatum
import Sheaf.Paper.CompletedDerivedInverseLimit
import Sheaf.Paper.IntrinsicCompletionCompleted
import Sheaf.Paper.KoszulReconstruction
import Sheaf.Paper.PerfectProjectionFormula
import Sheaf.Paper.ProjectionFormulaBaseChangeNaturality
import Sheaf.Paper.ProjectionMateExact
import Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses
import WeilConjectures.Algebra.Homology.RoosComplex
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp
import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution
import WeilConjectures.CategoryTheory.RingedSiteGrothendieckAbelian

/-!
# The canonical direct-image/derived-limit comparison

Source: blueprint proper base change, direct image and limits; Stacks Tag 099N
and Cohomology on Sites, lemma-Rf-commutes-with-Rlim
(blueprint: prop-weil-pbc-direct-image-limits).

## Main statements

- `AlgebraicGeometry.Scheme.AdicCoefficientDatum.directImageRlimIso`:
  the recorded construction or statement of this node.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe t
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme
variable {A : Type (t + 1)} [CommRing A] (d : AdicCoefficientDatum A)
variable {U V : Scheme.{t}} (f : U ⟶ V)

/-- The ordinary direct image on strict towers applies the actual module functor levelwise.
Source: blueprint direct image and limits (blueprint: prop-weil-pbc-direct-image-limits). -/
abbrev AdicCoefficientDatum.towerModulePush : d.towers U ⥤ d.towers V :=
  (Functor.whiskeringRight _ _ _).obj
    (proEtaleRingModuleDirectImage f (d.completedRing V) (d.completedRing U)
      (d.integralRingIso f))

/-- Direct image of strict towers is additive termwise.
Source: blueprint direct image and limits (blueprint: prop-weil-pbc-direct-image-limits). -/
instance AdicCoefficientDatum.towerModulePush_additive :
    (d.towerModulePush f).Additive := inferInstance

/-- The canonical termwise module adjunction on strict towers.
Source: blueprint direct image and limits (blueprint: prop-weil-pbc-direct-image-limits). -/
def AdicCoefficientDatum.towerModuleAdjunction :
    d.towerModulePull f ⊣ d.towerModulePush f :=
  (proEtaleRingModuleAdjunction f (d.completedRing V) (d.completedRing U)
    (d.integralRingIso f)).whiskerRight ℕᵒᵖ

/-- The total right derived direct image in the abelian category of strict towers.
Source: blueprint direct image and limits (blueprint: prop-weil-pbc-direct-image-limits). -/
abbrev AdicCoefficientDatum.towerPush := (d.towerModulePush f).rightDerivedFunctor

/-- The derived tower adjunction comes from its canonical ordinary adjunction.
Source: blueprint direct image and limits (blueprint: prop-weil-pbc-direct-image-limits). -/
def AdicCoefficientDatum.towerAdjunction : d.towerPull f ⊣ d.towerPush f :=
  (d.towerModuleAdjunction f).mapDerivedCategoryRightDerivedAdjunction

/-- Evaluation of strict towers preserves K-injective complexes: its left adjoint
is the exact sum of copies indexed by arrows into the chosen level.
Source: blueprint direct image and limits, evaluation clause; Stacks 079P
(blueprint: prop-weil-pbc-direct-image-limits).
Proof: the left adjoint is left Kan extension from the one-object subcategory.
Its values are sums of copies indexed by arrows into the evaluation index. These
sums are exact in the Grothendieck module category. Adjunction transports maps from
acyclic complexes to null-homotopic maps into the given K-injective tower. -/
@[instance]
theorem completedTowerEvaluation_kinjective (T : Scheme.{t})
    (R : Sheaf (ProEt.topology T) CommRingCat.{t + 1}) (n : ℕ)
    (J : CochainComplex (reductionTowerCategory T (reductionModuleRing T R)) ℤ)
    [J.IsKInjective] :
    CochainComplex.IsKInjective
      (((reductionTowerEvaluation T (reductionModuleRing T R) n).mapHomologicalComplex
        (.up ℤ)).obj J) := by
  exact tower_evaluation_isKInjective _ J (Opposite.op n)

set_option linter.defProp false in
/-- The exact K-injective normalization of tower direct-image evaluation.
Source: blueprint direct image and limits, evaluation clause; Stacks 099N
(blueprint: prop-weil-pbc-direct-image-limits). -/
def AdicCoefficientDatum.IsTowerPushEvaluation (n : ℕ)
    (α : d.towerPush f ⋙
        reductionTowerDerivedEvaluation V (reductionModuleRing V (d.completedRing V)) n ≅
        reductionTowerDerivedEvaluation U (reductionModuleRing U (d.completedRing U)) n ⋙
          d.push f) : Prop :=
  ∀ (J : CochainComplex (d.towers U) ℤ) [J.IsKInjective],
        (reductionTowerDerivedEvaluation V
            (reductionModuleRing V (d.completedRing V)) n).map
            ((d.towerModulePush f).rightDerivedFunctorObjQIso J).hom ≫
          (reductionTowerEvaluation V
            (reductionModuleRing V (d.completedRing V)) n).mapDerivedCategoryFactors.hom.app
              (((d.towerModulePush f).mapHomologicalComplex (.up ℤ)).obj J) =
        α.hom.app (DerivedCategory.Q.obj J) ≫
          (d.push f).map ((reductionTowerEvaluation U
            (reductionModuleRing U (d.completedRing U)) n).mapDerivedCategoryFactors.hom.app J) ≫
          ((proEtaleRingModuleDirectImage f (d.completedRing V) (d.completedRing U)
            (d.integralRingIso f)).rightDerivedFunctorObjQIso
              (((reductionTowerEvaluation U
                (reductionModuleRing U (d.completedRing U)) n).mapHomologicalComplex
                  (.up ℤ)).obj J)).hom

/-- The levelwise direct image comparison is fixed on K-injective towers by the
identity of the two termwise evaluations. It is a natural isomorphism.
Source: blueprint direct image and limits, first clause; Stacks 099N
(blueprint: prop-weil-pbc-direct-image-limits).
Proof: evaluation preserves K-injectives by its exact left adjoint. Thus each side
is computed by evaluating the same termwise direct image of a K-injective tower.
The two factorization maps and universal derived units give the displayed equation.
It descends through localization; every tower has such a resolution, so the equation
uniquely specifies the natural comparison. -/
theorem AdicCoefficientDatum.towerPushEvaluation_existsUnique (n : ℕ) :
    ∃! α : d.towerPush f ⋙
        reductionTowerDerivedEvaluation V (reductionModuleRing V (d.completedRing V)) n ≅
        reductionTowerDerivedEvaluation U (reductionModuleRing U (d.completedRing U)) n ⋙
          d.push f,
      d.IsTowerPushEvaluation f n α := by
  sorry

/-- The canonical tower direct-image evaluation comparison, retaining its model equation.
Source: blueprint direct image and limits (blueprint: prop-weil-pbc-direct-image-limits). -/
def AdicCoefficientDatum.towerPushEvaluation (n : ℕ) :
    d.towerPush f ⋙
        reductionTowerDerivedEvaluation V (reductionModuleRing V (d.completedRing V)) n ≅
      reductionTowerDerivedEvaluation U (reductionModuleRing U (d.completedRing U)) n ⋙
        d.push f :=
  (d.towerPushEvaluation_existsUnique f n).choose

/-- The canonical comparison is the conjugate of the identity constant/pullback square.
It is therefore the comparison of the two composite right adjoints, including their units.
No arbitrary isomorphism of the resulting objects is chosen.
Source: blueprint direct image and limits; lemma-Rf-commutes-with-Rlim
(blueprint: prop-weil-pbc-direct-image-limits). -/
def AdicCoefficientDatum.directImageRlimIso :
    completedRlim U (d.completedRing U) ⋙ d.push f ≅
      d.towerPush f ⋙ completedRlim V (d.completedRing V) :=
  conjugateIsoEquiv
    ((proEtaleRingDerivedAdjunction f (d.completedRing V) (d.completedRing U)
      (d.integralRingIso f)).comp (d.constantRlimAdjunction U))
    ((d.constantRlimAdjunction V).comp (d.towerAdjunction f))
    (d.derivedConstantPullbackIso f)

/-- The product comparison is the product of the actual direct-image projections,
followed by the normalized evaluation comparisons.
Source: blueprint direct image and limits, derived-product clause
(blueprint: prop-weil-pbc-direct-image-limits). -/
def AdicCoefficientDatum.directImageProductComparison
    (M : DerivedCategory (d.towers U))
    [HasProduct (completedTowerDerivedSequence U d M)]
    [HasProduct (completedTowerDerivedSequence V d ((d.towerPush f).obj M))] :
    (d.push f).obj (∏ᶜ (completedTowerDerivedSequence U d M)) ⟶
      ∏ᶜ (completedTowerDerivedSequence V d ((d.towerPush f).obj M)) :=
  Pi.lift (fun n ↦ (d.push f).map
    (Pi.π (completedTowerDerivedSequence U d M) n) ≫
      (d.towerPushEvaluation f n).inv.app M)

/-- The actual product comparison is invertible, and the specified Rlim comparison
is induced by it on the Roos triangles, with the shift maps retained.
Source: blueprint direct image and limits, Roos-triangle clauses; Stacks 099N and 07KC
(blueprint: prop-weil-pbc-direct-image-limits).
Proof: direct image is a right adjoint of exact inverse image. It preserves
K-injective tower models and products. Its ordinary product comparison is the
product of the images of the tower projections; this commutes with every transition,
hence with one minus shift. On a K-injective tower the ordinary limit comparison
is the conjugate of the constant/pullback comparison, exactly the defining
comparison directImageRlimIso. Apply the derived localization to this morphism of
Roos sequences. Exact countable products compute the two derived products, giving
the asserted isomorphism and the first and third squares of the triangle map. -/
theorem AdicCoefficientDatum.directImageRlim_roos
    (M : DerivedCategory (d.towers U))
    [HasProduct (completedTowerDerivedSequence U d M)]
    [HasProduct (completedTowerDerivedSequence V d ((d.towerPush f).obj M))] :
    IsIso (d.directImageProductComparison f M) ∧
      (d.push f).map (towerTransitionEndomorphism (completedTowerDerivedStep U d M)) ≫
          d.directImageProductComparison f M =
        d.directImageProductComparison f M ≫ towerTransitionEndomorphism
          (completedTowerDerivedStep V d ((d.towerPush f).obj M)) ∧
      ∃ (δU : ∏ᶜ (completedTowerDerivedSequence U d M) ⟶
          ((completedRlim U (d.completedRing U)).obj M)⟦(1 : ℤ)⟧)
        (δV : ∏ᶜ (completedTowerDerivedSequence V d ((d.towerPush f).obj M)) ⟶
          ((completedRlim V (d.completedRing V)).obj ((d.towerPush f).obj M))⟦(1 : ℤ)⟧),
        IsDerivedLimitTriangle (completedTowerDerivedStep U d M)
          ((completedRlim U (d.completedRing U)).obj M)
          (completedRlimRoosProjection U d M) δU ∧
        IsDerivedLimitTriangle
          (completedTowerDerivedStep V d ((d.towerPush f).obj M))
          ((completedRlim V (d.completedRing V)).obj ((d.towerPush f).obj M))
          (completedRlimRoosProjection V d ((d.towerPush f).obj M)) δV ∧
        (d.directImageRlimIso f).hom.app M ≫
            completedRlimRoosProjection V d ((d.towerPush f).obj M) =
          (d.push f).map (completedRlimRoosProjection U d M) ≫
            d.directImageProductComparison f M ∧
        (d.push f).map δU ≫
            ((d.push f).commShiftIso (1 : ℤ)).hom.app
              ((completedRlim U (d.completedRing U)).obj M) ≫
            ((d.directImageRlimIso f).hom.app M)⟦(1 : ℤ)⟧' =
          d.directImageProductComparison f M ≫ δV := by
  sorry

/-- The ordinary scalar/pullback mate, in the inverse direction of chi.
Source: blueprint four corners and tower compatibility; Stacks 06YY and 0D6D
(blueprint: prop-weil-pbc-direct-image-limits). -/
def completedOrdinaryReductionPullbackInv (n : ℕ) :
    proEtaleRingModulePullback f (d.completedRing V) (d.completedRing U)
        (d.integralRingIso f) ⋙ proEtaleRingExtension (d.projection U n) ⟶
      proEtaleRingExtension (d.projection V n) ⋙
        proEtaleRingModulePullback f (d.finiteRing V n) (d.finiteRing U n)
          (d.finiteRingIso f n) :=
  (mateEquiv (proEtaleRingExtensionAdjunction (d.projection V n))
    (proEtaleRingExtensionAdjunction (d.projection U n))).symm
      (proEtaleRingRestrictionPullbackInv f (d.completedRing V) (d.finiteRing V n)
        (d.completedRing U) (d.finiteRing U n) (d.projection V n) (d.projection U n)
          (d.integralRingIso f) (d.finiteRingIso f n) (d.projection_comm f n))

/-- The normalized ordinary mate is the invertible tensor balancing map.
Source: blueprint tower compatibility; Stacks 03EL and 06YY
(blueprint: prop-weil-pbc-direct-image-limits).
Proof: the tensor-unit normalized adjunctions compute this mate on pure tensors.
It sends the inverse image of m tensored with p to the inverse image of m tensor p.
The coefficient projection square makes the map quotient-linear. The reverse tensor
reassociation is inverse, as checked on pure tensors and then on sheafifications. -/
theorem completedOrdinaryReductionPullbackInv_isIso (n : ℕ) :
    IsIso (completedOrdinaryReductionPullbackInv d f n) := by
  sorry

attribute [instance] completedOrdinaryReductionPullbackInv_isIso

/-- The ordinary reduction-level comparison after restriction to completed coefficients.
Source: blueprint tower compatibility (blueprint: prop-weil-pbc-direct-image-limits). -/
def completedReductionLevelPullbackIso (n : ℕ) :
    completedReductionLevel V d n ⋙
        proEtaleRingModulePullback f (d.completedRing V) (d.completedRing U)
          (d.integralRingIso f) ≅
      proEtaleRingModulePullback f (d.completedRing V) (d.completedRing U)
        (d.integralRingIso f) ⋙ completedReductionLevel U d n :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (proEtaleRingExtension (d.projection V n))
      (@asIso _ _ _ _ (proEtaleRingRestrictionPullbackInv f
        (d.completedRing V) (d.finiteRing V n) (d.completedRing U) (d.finiteRing U n)
        (d.projection V n) (d.projection U n) (d.integralRingIso f)
        (d.finiteRingIso f n) (d.projection_comm f n))
        (proEtaleRingRestrictionPullbackInv_isIso f
          (d.completedRing V) (d.finiteRing V n) (d.completedRing U) (d.finiteRing U n)
          (d.projection V n) (d.projection U n) (d.integralRingIso f)
          (d.finiteRingIso f n) (d.projection_comm f n))) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (asIso (completedOrdinaryReductionPullbackInv d f n)).symm
      (proEtaleRingRestrictScalars (d.projection U n)) ≪≫
    Functor.associator _ _ _

/-- The level tensor comparisons commute with every quotient transition, including identities.
Source: blueprint tower compatibility, step 1 (blueprint: prop-weil-pbc-direct-image-limits).
Proof: both composites send a local pure tensor to its pullback with the quotient image
of its coefficient. Equality on pure tensors descends through sheafification. Arbitrary
quotient transitions are composites of consecutive ones, with identities included. -/
theorem completedReductionLevelPullbackIso_transition
    (M : reductionModules V (d.completedRing V)) {n m : ℕᵒᵖ} (a : n ⟶ m) :
    ((completedReductionModuleTowerFunctor V d ⋙ d.towerModulePull f).obj M).map a ≫
        (completedReductionLevelPullbackIso d f m.unop).hom.app M =
      (completedReductionLevelPullbackIso d f n.unop).hom.app M ≫
        ((proEtaleRingModulePullback f (d.completedRing V) (d.completedRing U)
          (d.integralRingIso f) ⋙ completedReductionModuleTowerFunctor U d).obj M).map a := by
  sorry

/-- The actual strict tower isomorphism of ordinary tensor/pullback computations.
Source: blueprint tower compatibility (blueprint: prop-weil-pbc-direct-image-limits). -/
def completedReductionOrdinaryPullbackIso :
    completedReductionModuleTowerFunctor V d ⋙ d.towerModulePull f ≅
      proEtaleRingModulePullback f (d.completedRing V) (d.completedRing U)
        (d.integralRingIso f) ⋙ completedReductionModuleTowerFunctor U d :=
  NatIso.ofComponents
    (fun M ↦ NatIso.ofComponents
      (fun n ↦ (completedReductionLevelPullbackIso d f n.unop).app M)
      (fun a ↦ completedReductionLevelPullbackIso_transition d f M a))
    (fun a ↦ by
      apply NatTrans.ext
      funext n
      exact (completedReductionLevelPullbackIso d f n.unop).hom.naturality a)

set_option linter.defProp false in
/-- The strict ordinary comparison and universal counits fix the derived comparison.
Source: blueprint tower compatibility, steps 1--3; Stacks 06YY and 0D6D
(blueprint: prop-weil-pbc-direct-image-limits). -/
def IsCompletedReductionPullbackComparison
    (τ : completedReductionTower V d ⋙ d.towerPull f ≅
        d.pull f ⋙ completedReductionTower U d) : Prop :=
  ∀ P : CochainComplex (reductionModules V (d.completedRing V)) ℤ,
        CochainComplex.IsKFlatIndependentCoefficients (R := d.completedRing V) P →
        τ.hom.app (DerivedCategory.Q.obj P) ≫
            (completedReductionTower U d).map
              ((proEtaleRingDerivedPullbackFactors f (d.completedRing V) (d.completedRing U)
                (d.integralRingIso f)).hom.app P) ≫
            completedReductionTowerComplexCounit U d
              (((proEtaleRingModulePullback f (d.completedRing V) (d.completedRing U)
                (d.integralRingIso f)).mapHomologicalComplex (.up ℤ)).obj P) =
          (d.towerPull f).map (completedReductionTowerComplexCounit V d P) ≫
            (d.towerModulePull f).mapDerivedCategoryFactors.hom.app
              ((completedReductionComplexTowerFunctor V d).obj P) ≫
            DerivedCategory.Q.map
              ((NatIso.mapHomologicalComplex (completedReductionOrdinaryPullbackIso d f)
                (.up ℤ)).hom.app P)

/-- The canonical derived comparison is uniquely fixed on K-flat representatives by the
strict ordinary comparison and the two universal derived counits.
Source: blueprint tower compatibility, steps 1--3; Stacks 06YY and 0D6D
(blueprint: prop-weil-pbc-direct-image-limits).
Proof: choose a K-flat flat-term representative P. Its pullback remains K-flat with flat
terms. The two reduction-tower counits are invertible there, so the displayed equation
uniquely defines the component by the ordinary strict tower isomorphism above. Naturality
for chain maps, compatible homotopies, and inverse quasi-isomorphisms descends this to
all derived objects. Every object has a K-flat representative; hence the natural
isomorphism is unique. Its evaluation is chi, since both have the same ordinary tensor
normalization, and the transition compatibility is retained from the strict comparison. -/
theorem completedReductionPullbackIso_existsUnique :
    ∃! τ : completedReductionTower V d ⋙ d.towerPull f ≅
        d.pull f ⋙ completedReductionTower U d,
      IsCompletedReductionPullbackComparison d f τ := by
  sorry

/-- The normalized reduction-tower/pullback isomorphism, rather than an arbitrary lift
of levelwise maps. Source: blueprint tower compatibility
(blueprint: prop-weil-pbc-direct-image-limits). -/
def AdicCoefficientDatum.reductionTowerPullbackIso :
    completedReductionTower V d ⋙ d.towerPull f ≅
      d.pull f ⋙ completedReductionTower U d :=
  (completedReductionPullbackIso_existsUnique d f).choose

/-- The strict derived projection map is the adjunct of tower chi followed by the
reduction of the ambient counit. Its evaluation is the specified finite projection.
Source: blueprint tower compatibility (blueprint: prop-weil-pbc-direct-image-limits). -/
def AdicCoefficientDatum.towerProjection (K : d.derived U) :
    (completedReductionTower V d).obj ((d.push f).obj K) ⟶
      (d.towerPush f).obj ((completedReductionTower U d).obj K) :=
  (d.towerAdjunction f).homEquiv _ _
    ((d.reductionTowerPullbackIso f).hom.app ((d.push f).obj K) ≫
      (completedReductionTower U d).map
        ((proEtaleRingDerivedAdjunction f (d.completedRing V) (d.completedRing U)
          (d.integralRingIso f)).counit.app K))


/-- Evaluate the pushed reduction tower using its canonical K-injective evaluation
comparison, the normalized reduction counit, and the specified scalar-restriction
comparison. Source: blueprint direct image and limits, projection-formula clause
(blueprint: prop-weil-pbc-direct-image-limits). -/
def AdicCoefficientDatum.towerPushReductionEvaluation
    (K : d.derived U) (n : ℕ) :
    (reductionTowerDerivedEvaluation V
        (reductionModuleRing V (d.completedRing V)) n).obj
        ((d.towerPush f).obj ((completedReductionTower U d).obj K)) ⟶
      (reductionDerivedRestrict V (d.projection V n)).obj
        ((d.finitePush f n).obj ((d.reduction U n).obj K)) :=
  (d.towerPushEvaluation f n).hom.app ((completedReductionTower U d).obj K) ≫
    (d.push f).map ((completedReductionEvaluation U d n).app K) ≫
      (proEtaleRingRestrictionDerivedDirectImage f
        (d.completedRing V) (d.finiteRing V n) (d.completedRing U) (d.finiteRing U n)
        (d.projection V n) (d.projection U n) (d.integralRingIso f)
        (d.finiteRingIso f n) (d.projection_comm f n)).inv.app ((d.reduction U n).obj K)

/-- The specified tower projection evaluates to the finite projection formula, is
natural in arbitrary morphisms, and identifies the two completion units. The map
is one morphism of derived strict towers, retaining every quotient transition.
Source: blueprint direct image and limits, projection and completeness clauses;
Stacks Tags 0944 and 099N (blueprint: prop-weil-pbc-direct-image-limits).
Proof: on flat-term K-flat models the scalar/pullback mate is tensor balancing.
Transposition of its composite with the counit is exactly finiteProjection, by the
normalized scalar-change adjunction comparison. The same tensor maps commute with
quotient transitions and chain maps, giving the strict tower map and naturality.
The constant-to-reduction augmentation has the same quotient-unit formula. Apply
adjunction transposition and the constant/pullback comparison: the resulting
completion map is direct image of the original unit followed by directImageRlimIso.
This is the last displayed equality. Perfectness makes the tower projection
invertible, by conservativity of evaluation for isomorphisms. -/
theorem AdicCoefficientDatum.towerProjection_properties (K : d.derived U) :
    (∀ n : ℕ,
      (reductionTowerDerivedEvaluation V
          (reductionModuleRing V (d.completedRing V)) n).map (d.towerProjection f K) ≫
          d.towerPushReductionEvaluation f K n =
        (completedReductionEvaluation V d n).app ((d.push f).obj K) ≫
          (reductionDerivedRestrict V (d.projection V n)).map (d.finiteProjection f K n)) ∧
      (∀ (H : d.derived U) (a : K ⟶ H),
        (completedReductionTower V d).map ((d.push f).map a) ≫ d.towerProjection f H =
          d.towerProjection f K ≫
            (d.towerPush f).map ((completedReductionTower U d).map a)) ∧
      d.completionUnit V ((d.push f).obj K) ≫
          (completedRlim V (d.completedRing V)).map (d.towerProjection f K) =
        (d.push f).map (d.completionUnit U K) ≫
          (d.directImageRlimIso f).hom.app ((completedReductionTower U d).obj K) := by
  sorry

/-- Perfect quotient coefficients make the specified strict projection invertible.
Source: blueprint tower compatibility; Stacks Tags 0944 and 015F
(blueprint: prop-weil-pbc-direct-image-limits).
Proof: evaluate the tower adjunction mate. The coefficient restriction/pullback
comparisons identify its evaluation with the restriction of the finite projection.
The latter is invertible by the perfect projection formula. The cone of the tower map
therefore has zero cohomology at every index. Tower cohomology is levelwise, hence its
cone is acyclic and the original strict derived tower map is invertible. This uses
conservativity for isomorphisms, without claiming faithfulness of derived evaluations. -/
theorem AdicCoefficientDatum.towerProjection_isIso {U V : Scheme.{t}} (f : U ⟶ V)
    (K : d.derived U) : IsIso (d.towerProjection f K) := by
  have he (n : ℕ) : IsIso
      ((reductionTowerDerivedEvaluation V
        (reductionModuleRing V (d.completedRing V)) n).map (d.towerProjection f K)) := by
    have h := (d.towerProjection_properties f K).1 n
    have : IsIso ((reductionTowerDerivedEvaluation V
        (reductionModuleRing V (d.completedRing V)) n).map (d.towerProjection f K) ≫
        d.towerPushReductionEvaluation f K n) := by
      rw [h]
      infer_instance
    have : IsIso (d.towerPushReductionEvaluation f K n) := by
      unfold AdicCoefficientDatum.towerPushReductionEvaluation
      infer_instance
    exact IsIso.of_isIso_comp_right _ (d.towerPushReductionEvaluation f K n)
  rw [DerivedCategory.isIso_iff]
  intro i
  have (n : ℕᵒᵖ) : IsIso
      (((DerivedCategory.homologyFunctor (d.towers V) i).map
        (d.towerProjection f K)).app n) := by
    let E := reductionTowerEvaluation V (reductionModuleRing V (d.completedRing V)) n.unop
    have : IsIso ((E.mapDerivedCategory ⋙ DerivedCategory.homologyFunctor _ i).map
        (d.towerProjection f K)) := by
      change IsIso ((DerivedCategory.homologyFunctor _ i).map
        ((reductionTowerDerivedEvaluation V
          (reductionModuleRing V (d.completedRing V)) n.unop).map (d.towerProjection f K)))
      have := he n.unop
      infer_instance
    exact (NatIso.isIso_map_iff (E.mapDerivedCategoryHomologyFunctorIso i)
      (d.towerProjection f K)).2 inferInstance
  exact NatIso.isIso_of_isIso_app _

attribute [instance] AdicCoefficientDatum.towerProjection_isIso

/-- Direct image preserves quotient-tower completeness, with the specified completion unit.
Source: blueprint direct image and limits; Stacks Tag 099N (3), (4)
(blueprint: prop-weil-pbc-direct-image-limits).
Proof: the perfect projection-formula maps identify the strict reduction tower of Rf_*K
with derived tower pushforward of K's strict reduction tower. Their quotient compatibility
is the tensor-unit normalization. The canonical completion unit of Rf_*K
then equals Rf_* of K's completion unit followed by the canonical direct-image/Rlim
comparison. Both maps are invertible, the first by hK and the second by its construction
as a conjugate of the constant/pullback identity square. Thus the completion unit is
invertible, which is exactly quotient-tower completeness at V.
No faithfulness of derived evaluations is invoked. -/
theorem AdicCoefficientDatum.push_complete (K : d.derived U)
    (hK : d.TowerComplete U K) : d.TowerComplete V ((d.push f).obj K) := by
  let : IsIso (d.completionUnit U K) := hK
  change IsIso (d.completionUnit V ((d.push f).obj K))
  have h := (d.towerProjection_properties f K).2.2
  have : IsIso (d.completionUnit V ((d.push f).obj K) ≫
      (completedRlim V (d.completedRing V)).map (d.towerProjection f K)) := by
    rw [h]
    infer_instance
  exact IsIso.of_isIso_comp_right _
    ((completedRlim V (d.completedRing V)).map (d.towerProjection f K))

end AlgebraicGeometry.Scheme
