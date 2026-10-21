/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N2
-/
module

public import Sheaf.Paper.CompletedTowerPullback
public import Sheaf.AlgebraicGeometry.ProEtaleOperations
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.MapDerivedCategory

import Sheaf.Paper.CompleteCoefficientDatum
import Sheaf.Paper.ProjectionFormulaArrows
import Sheaf.Paper.StrictPerfectPackageOnSite
import Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients
import Sheaf.Paper.ConstantCompletionEquivalence
import Sheaf.CategoryTheory.RingedKoszulCompletionReflector
import Sheaf.CategoryTheory.RingedStrictTowerHomotopyLimit
import Sheaf.Paper.ProjectionFormulaTotalization

import Sheaf.Algebra.Homology.KFlatCoefficientUniverse
public import Sheaf.Algebra.Homology.KFlatIndependentCoefficients
import Sheaf.Paper.AdicCoefficientDatum
import Sheaf.Paper.AdicCompletionReduction
import Sheaf.Paper.IntrinsicCompletionCompleted
import Sheaf.Paper.PbcFiniteCompletedCoefficientMap
import Sheaf.Paper.ProEtaleProjectionFormulaArrows
import Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses
import Sheaf.Paper.WeilCompletedTensorReflector
/-! # Finite reduction of completed pullback

Source: Stacks Project, Tag 099N (5), and blueprint order 1262
(blueprint: lemma-weil-pbc-completed-pullback-reduction).

## Main definitions

- `completedPullbackReductionArrow`: adjunct of the actual limit projection.
- `completedReductionTargetNormalization`: canonical scalar normalization of finite pullback.

## Main statements

- `completedPullback_reduction`: completeness, finite reduction and every coherence clause.

All coefficients remain sheaves on the original small pro-etale sites. Positive
level n is encoded by n-1, so a natural number n denotes the quotient by I^(n+1).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe u
open CategoryTheory CategoryTheory.Limits Opposite MonoidalCategory
open AlgebraicGeometry.ProEtale
open scoped ChangeOfRings TensorProduct
namespace AlgebraicGeometry.Scheme
variable {X Y : Scheme.{u}} (g : X ⟶ Y) {A : Type (u + 1)} [CommRing A]
variable (d : AdicCoefficientDatum A)

/-- The functor whose object map is the published completed pullback.
Source: blueprint order 1262 (blueprint: lemma-weil-pbc-completed-pullback-reduction). -/
def completedPullbackFunctor :
    DerivedCategory (pbcModules Y (pbcAdicCompletion Y d)) ⥤
      DerivedCategory (pbcModules X (pbcAdicCompletion X d)) :=
  completedReductionTower Y d ⋙ completedTowerPullback g d ⋙ completedTowerRlim d X

/-- The small-model module pushforward has its canonical pullback adjunction.
Source: Stacks 03D2 (blueprint: lemma-weil-pbc-completed-pullback-reduction).
Proof: the small-model site functor is continuous and cocontinuous. Compose its
module inverse image with module sheafification; Mathlib's pullback construction
is left adjoint to the specified sectionwise pushforward. -/
theorem completedReductionModelPushforward_isRightAdjoint
    (R : Sheaf (ProEt.topology Y) CommRingCat.{u + 1}) :
    (@SheafOfModules.pushforward.{u + 1} _ _ _ _ _ _ _ _ _
      (proEtaleModelBaseChange_isContinuous g) (proEtaleModelRingUnit g R)).IsRightAdjoint := by
  infer_instance

/-- An inverse-image generator from an object V and a base-change arrow U→g*V.
It is the small-model module-adjunction unit followed by restriction along that arrow.
Source: Stacks 03D2, 00VC (blueprint: lemma-weil-pbc-completed-pullback-reduction). -/
def completedReductionInverseImageGenerator
    (R : Sheaf (ProEt.topology Y) CommRingCat.{u + 1}) (M : pbcModules Y R)
    (V : Y.ProEt) (U : X.ProEt) (f : U ⟶ (proEtaleBaseChange g).obj V)
    (m : M.val.obj (op V)) :
    ((proEtaleModuleInverseImage g R).obj M).val.obj (op U) :=
  ((proEtaleModuleInverseImage g R).obj M).val.map f.op
    (((@SheafOfModules.pullbackPushforwardAdjunction.{u + 1} _ _ _ _ _ _ _ _ _
        (proEtaleModelBaseChange_isContinuous g) (proEtaleModelRingUnit g R)
        (completedReductionModelPushforward_isRightAdjoint g R)).unit.app
      ((proEtaleModuleToModel ((adicLisseForget Y).obj R)).obj M)).val.app
        (op (AsSmall.up.obj V)) m)

attribute [irreducible] completedReductionInverseImageGenerator

/-- The standard localization comparison for exact restriction, with its exactness
instances supplied by the existing coefficient interface.
Source: Stacks 03D3 (blueprint: lemma-weil-pbc-completed-pullback-reduction). -/
def completedReductionRestrictionFactors (T : Scheme.{u})
    {R S : Sheaf (ProEt.topology T) CommRingCat.{u + 1}} (φ : R ⟶ S) :
    DerivedCategory.Q ⋙ pbcDerivedRestrict φ ≅
      (pbcRestrict φ).mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q :=
  (pbcRestrict φ).mapDerivedCategoryFactors

/-- The existing tensor-formula module pullback over the finite coefficient sheaves.
Source: Stacks 099N (5) (blueprint: lemma-weil-pbc-completed-pullback-reduction). -/
abbrev completedReductionFiniteModules (n : ℕ) :=
  proEtaleRingModulePullback g (reductionCoefficient Y d n)
    (reductionCoefficient X d n) (asIso (completedFiniteCoefficientMap g d n))

/-- Exact finite-coefficient pullback, with the standard localization on both sites.
Source: Stacks 099N (5) (blueprint: lemma-weil-pbc-completed-pullback-reduction). -/
abbrev completedReductionFiniteDerived (n : ℕ) :=
  proEtaleRingDerivedPullback g (reductionCoefficient Y d n)
    (reductionCoefficient X d n) (asIso (completedFiniteCoefficientMap g d n))

/-- Finite pullback of the finite reduction, with its quotient action retained.
Source: blueprint order 1262 (blueprint: lemma-weil-pbc-completed-pullback-reduction). -/
def completedReductionFiniteTarget (n : ℕ) :
    DerivedCategory (pbcModules Y (pbcAdicCompletion Y d)) ⥤
      DerivedCategory (pbcModules X (reductionCoefficient X d n)) :=
  reductionDerivedChange Y (completedReductionProjection Y d n) ⋙
    completedReductionFiniteDerived g d n

/-- The actual sheafified pure tensor in the tensor-formula finite pullback.
Source: Stacks 03EK (blueprint: lemma-weil-pbc-completed-pullback-reduction). -/
def completedReductionFiniteTensor (n : ℕ)
    (M : pbcModules Y (reductionCoefficient Y d n))
    (U : X.ProEtᵒᵖ) (s : (reductionCoefficient X d n).obj.obj U)
    (m : ((proEtaleModuleInverseImage g
      (reductionCoefficient Y d n)).obj M).val.obj U) :
    ((completedReductionFiniteModules g d n).obj M).val.obj U :=
  ((PresheafOfModules.sheafificationAdjunction
    (𝟙 ((adicLisseForget X).obj (reductionCoefficient X d n)).obj)).unit.app
      (SheafOfModules.changeOfRingsPresheaf.{u, u + 1, u + 1} (completedFiniteCoefficientMap g d n)
        ((proEtaleModuleInverseImage g (reductionCoefficient Y d n)).obj M))).app U
          (s ⊗ₜ[((proEtaleSheafInverseImage g CommRingCat.{u + 1}).obj
            (reductionCoefficient Y d n)).obj.obj U,
              ((completedFiniteCoefficientMap g d n).hom.app U).hom] m)

attribute [irreducible] completedReductionFiniteTensor

/-- A pure tensor generator of the finite pullback of a reduction.
This uses the recorded scalar-extension tensor, the module inverse-image unit,
and the actual tensor-formula finite pullback, without any choice of sections.
Source: blueprint finite arrows (blueprint: lemma-weil-pbc-completed-pullback-reduction). -/
def completedReductionFiniteGenerator (n : ℕ)
    (M : pbcModules Y (pbcAdicCompletion Y d)) (V : Y.ProEt) (U : X.ProEt)
    (f : U ⟶ (proEtaleBaseChange g).obj V)
    (s : (reductionCoefficient X d n).obj.obj (op U))
    (z : (reductionCoefficient Y d n).obj.obj (op V)) (m : M.val.obj (op V)) :
    ((completedReductionFiniteModules g d n).obj
      ((reductionChange Y (completedReductionProjection Y d n)).obj M)).val.obj (op U) :=
  completedReductionFiniteTensor g d n _ (op U) s
    (completedReductionInverseImageGenerator g (reductionCoefficient Y d n)
      ((reductionChange Y (completedReductionProjection Y d n)).obj M) V U f
        (pbcTensorSection (completedReductionProjection Y d n) M (op V) z m))

attribute [irreducible] completedReductionFiniteGenerator

/-- Explicitly inherit zero preservation before forming the complex comparison.
Source: Stacks 03EK (blueprint: lemma-weil-pbc-completed-pullback-reduction). -/
instance completedReductionOrdinarySource_preservesZero (n : ℕ) :
    (completedReductionModuleTowerFunctor Y d ⋙ completedTowerModulePullback g d ⋙
      (CategoryTheory.evaluation ℕᵒᵖ (pbcModules X (pbcAdicCompletion X d))).obj
        (op n)).PreservesZeroMorphisms :=
  letI := completedReductionModuleTowerFunctor_additive Y d
  letI := completedTowerModulePullback_additive g d
  Functor.preservesZeroMorphisms_of_additive _

/-- The canonical limit projection, derived from the ordinary projection.
Source: Stacks 08TC (blueprint: lemma-weil-pbc-completed-pullback-reduction). -/
def completedReductionLimitProjection (n : ℕ) :
    completedTowerRlim d X ⟶ pbcTowerEvaluation X (pbcAdicCompletion X d) n :=
  Functor.rightDerivedFunctorNatTrans
    (lim.π (C := pbcModules X (pbcAdicCompletion X d)) (op n)) ≫
      ((CategoryTheory.evaluation ℕᵒᵖ (pbcModules X (pbcAdicCompletion X d))).obj
        (op n)).rightDerivedFunctorIsoMapDerivedCategory.hom

/-- Canonical balancing across two quotient maps, using the existing scalar adjunctions.
Source: blueprint quotient cocycle (blueprint: lemma-weil-pbc-completed-pullback-reduction). -/
def completedReductionQuotientAssoc (T : Scheme.{u}) (a b c : ℕ)
    (hab : a ≤ b) (hbc : b ≤ c)
    (M : DerivedCategory (pbcModules T (reductionCoefficient T d c))) :=
  pbcReductionNormalization (reductionCoefficientMap T d c b hbc)
    (reductionCoefficientMap T d b a hab)
    (reductionCoefficientMap T d c a (hab.trans hbc))
    (reductionCoefficientMap_comp T d c b a hab hbc) M

/-- Canonical scalar balancing for the finite reductions of a completed-coefficient object.
Source: blueprint normalization (blueprint: lemma-weil-pbc-completed-pullback-reduction). -/
def completedPullbackSourceNormalization (T : Scheme.{u}) (a b : ℕ) (h : a ≤ b)
    (M : DerivedCategory (pbcModules T (pbcAdicCompletion T d))) :=
  pbcReductionNormalization (completedReductionProjection T d b)
    (reductionCoefficientMap T d b a h) (completedReductionProjection T d a)
    (completedReductionProjection_comp T d b a h) M

/-- An equality of sections of a scalar-semilinear module map, stated over abstract rings.
Naming this predicate keeps concrete finite-ring constructions out of kernel conversion.
Source: blueprint finite arrows (blueprint: lemma-weil-pbc-completed-pullback-reduction). -/
def completedReductionSectionEquation (T : Scheme.{u})
    {R S : Sheaf (ProEt.topology T) CommRingCat.{u + 1}} (φ : R ⟶ S)
    {M : pbcModules T R} {N : pbcModules T S}
    (ν : M ⟶ (pbcRestrict φ).obj N) (U : T.ProEtᵒᵖ)
    (x : M.val.obj U) (y : N.val.obj U) : Prop := ν.val.app U x = y

attribute [irreducible] completedReductionSectionEquation

/-- The representative normalization specifying the ordinary finite comparison uniquely.
Source: blueprint finite arrows (blueprint: lemma-weil-pbc-completed-pullback-reduction). -/
def HasCompletedReductionOrdinaryComparisonNormalization (n : ℕ)
    (e : completedReductionModuleTowerFunctor Y d ⋙ completedTowerModulePullback g d ⋙
        (CategoryTheory.evaluation ℕᵒᵖ (pbcModules X (pbcAdicCompletion X d))).obj (op n) ≅
      reductionChange Y (completedReductionProjection Y d n) ⋙
        completedReductionFiniteModules g d n ⋙
          SheafOfModules.restrictScalars.{u + 1}
            ((adicLisseForget X).map (completedReductionProjection X d n))) : Prop :=
  ∀ (M : pbcModules Y (pbcAdicCompletion Y d)) (V : Y.ProEt) (U : X.ProEt)
        (f : U ⟶ (proEtaleBaseChange g).obj V)
        (b : (pbcAdicCompletion X d).obj.obj (op U))
        (m : M.val.obj (op V)),
        completedReductionSectionEquation X (completedReductionProjection X d n)
          (e.hom.app M) (op U)
          (reductionTensorSection X (completedCoefficientMap g d) _ (op U) b
            (completedReductionInverseImageGenerator g (pbcAdicCompletion Y d)
              (((completedReductionModuleTowerFunctor Y d).obj M).obj (op n)) V U f
                ((((completedReductionModuleUnit d Y).app M).app (op n)).val.app (op V) m)))
          (completedReductionFiniteGenerator g d n M V U f
            ((completedReductionProjection X d n).hom.app (op U) b) 1 m)

attribute [irreducible] HasCompletedReductionOrdinaryComparisonNormalization

/-- The ordinary finite comparison is fixed on inverse images of the quotient unit.
Source: blueprint finite evaluation (blueprint: lemma-weil-pbc-completed-pullback-reduction).
Proof: send b tensor the inverse image of (m tensor z) to pi(b) times the pullback
of z tensor the inverse image of (1 tensor m). The coefficient-map projection
identity makes this balanced. The inverse inserts 1 in the completed scalar factor.
The quotient unit sends m to m tensor 1. Balancing determines the map from its
values on these generators, and both maps respect restrictions. Sheafification
extends them uniquely. The same formula commutes with maps of M and with quotients. -/
theorem completedReductionOrdinaryComparison_exists (n : ℕ) :
    ∃! e : completedReductionModuleTowerFunctor Y d ⋙ completedTowerModulePullback g d ⋙
        (CategoryTheory.evaluation ℕᵒᵖ (pbcModules X (pbcAdicCompletion X d))).obj (op n) ≅
      reductionChange Y (completedReductionProjection Y d n) ⋙
        completedReductionFiniteModules g d n ⋙
          SheafOfModules.restrictScalars.{u + 1}
            ((adicLisseForget X).map (completedReductionProjection X d n)),
      HasCompletedReductionOrdinaryComparisonNormalization g d n e := by
  sorry

/-- The finite comparison with its unique local generator normalization.
Source: blueprint finite evaluation (blueprint: lemma-weil-pbc-completed-pullback-reduction). -/
def completedReductionOrdinaryComparison (n : ℕ) :
    completedReductionModuleTowerFunctor Y d ⋙ completedTowerModulePullback g d ⋙
        (CategoryTheory.evaluation ℕᵒᵖ (pbcModules X (pbcAdicCompletion X d))).obj (op n) ≅
      reductionChange Y (completedReductionProjection Y d n) ⋙
        completedReductionFiniteModules g d n ⋙
          SheafOfModules.restrictScalars.{u + 1}
            ((adicLisseForget X).map (completedReductionProjection X d n)) :=
  (completedReductionOrdinaryComparison_exists g d n).exists.choose

/-- The universal comparison from the pulled derived reduction tower to its ordinary
computation on a complex. This retains the actual strict tower counits.
Source: blueprint finite projections (blueprint: lemma-weil-pbc-completed-pullback-reduction). -/
def completedReductionPulledModelMap (n : ℕ)
    (P : CochainComplex (pbcModules Y (pbcAdicCompletion Y d)) ℤ) :=
  (pbcTowerEvaluation X (pbcAdicCompletion X d) n).map
    ((completedTowerPullback g d).map
      (Functor.leftDerivedCounitOnComplex (completedReductionModuleTowerFunctor Y d)
        (completedReductionTower Y d) (completedReductionTowerCounit d Y) P) ≫
      completedTowerPullbackComplexCounit g d
        (((completedReductionModuleTowerFunctor Y d).mapHomologicalComplex (.up ℤ)).obj P)) ≫
    ((CategoryTheory.evaluation ℕᵒᵖ (pbcModules X (pbcAdicCompletion X d))).obj
      (op n)).mapDerivedCategoryFactors.hom.app
        (((completedTowerModulePullback g d).mapHomologicalComplex (.up ℤ)).obj
          (((completedReductionModuleTowerFunctor Y d).mapHomologicalComplex (.up ℤ)).obj P))

/-- The finite target's canonical comparison with a K-flat computation.
Source: blueprint finite coefficients (blueprint: lemma-weil-pbc-completed-pullback-reduction). -/
def completedReductionFiniteModelMap (n : ℕ)
    (P : CochainComplex (pbcModules Y (pbcAdicCompletion Y d)) ℤ) :=
  (completedReductionFiniteDerived g d n).map
    (pbcComplexCounit (completedReductionProjection Y d n) P) ≫
      (completedReductionFiniteModules g d n).mapDerivedCategoryFactors.hom.app
        (((reductionChange Y (completedReductionProjection Y d n)).mapHomologicalComplex
          (.up ℤ)).obj P)

/-- The representative normalization specifying the derived finite evaluation comparison uniquely.
Source: blueprint finite arrows (blueprint: lemma-weil-pbc-completed-pullback-reduction). -/
def HasCompletedReductionFiniteEvaluationNormalization (n : ℕ)
    (e : completedReductionTower Y d ⋙ completedTowerPullback g d ⋙
        pbcTowerEvaluation X (pbcAdicCompletion X d) n ≅
      completedReductionFiniteTarget g d n ⋙
        pbcDerivedRestrict (completedReductionProjection X d n)) : Prop :=
  ∀ P : CochainComplex (pbcModules Y (pbcAdicCompletion Y d)) ℤ,
        CochainComplex.IsKFlatIndependentCoefficients (R := pbcAdicCompletion Y d) P →
        completedReductionPulledModelMap g d n P ≫
            DerivedCategory.Q.map
              ((NatTrans.mapHomologicalComplex
                (completedReductionOrdinaryComparison g d n).hom (.up ℤ)).app P) =
          e.hom.app (DerivedCategory.Q.obj P) ≫
            (pbcDerivedRestrict (completedReductionProjection X d n)).map
              (completedReductionFiniteModelMap g d n P) ≫
            (completedReductionRestrictionFactors X (completedReductionProjection X d n)).hom.app
                (((completedReductionFiniteModules g d n).mapHomologicalComplex (.up ℤ)).obj
                  (((reductionChange Y
                    (completedReductionProjection Y d n)).mapHomologicalComplex
                      (.up ℤ)).obj P))

attribute [irreducible] HasCompletedReductionFiniteEvaluationNormalization

/-- The finite evaluation comparison is the descent of the specified ordinary map.
Thus it cannot be changed by an automorphism of the finite target.
Source: blueprint order 1262 (blueprint: lemma-weil-pbc-completed-pullback-reduction).
Proof: take a flat-term K-flat representative. The constant/completed comparison
computes the pulled reduction tower at each finite level by ordinary pullback.
Apply completedReductionOrdinaryComparison and the exact restriction comparison.
All quasi-isomorphisms between these models are inverted. Naturality and the
universal counits descend the comparison uniquely, with the displayed equation. -/
theorem completedReductionFiniteEvaluation_exists (n : ℕ) :
    ∃! e : completedReductionTower Y d ⋙ completedTowerPullback g d ⋙
        pbcTowerEvaluation X (pbcAdicCompletion X d) n ≅
      completedReductionFiniteTarget g d n ⋙
        pbcDerivedRestrict (completedReductionProjection X d n),
      HasCompletedReductionFiniteEvaluationNormalization g d n e := by
  sorry

/-- The canonical finite evaluation isomorphism fixed by the complex computation.
Source: blueprint order 1262 (blueprint: lemma-weil-pbc-completed-pullback-reduction). -/
def completedReductionFiniteEvaluation (n : ℕ) :
    completedReductionTower Y d ⋙ completedTowerPullback g d ⋙
        pbcTowerEvaluation X (pbcAdicCompletion X d) n ≅
      completedReductionFiniteTarget g d n ⋙
        pbcDerivedRestrict (completedReductionProjection X d n) :=
  (completedReductionFiniteEvaluation_exists g d n).exists.choose

/-- The projection-induced reduction arrow is the scalar-extension adjunct of the
actual derived-limit projection, followed by the normalized finite evaluation map.
Source: blueprint alpha_n (blueprint: lemma-weil-pbc-completed-pullback-reduction). -/
def completedPullbackReductionArrow
    (K : DerivedCategory (pbcModules Y (pbcAdicCompletion Y d))) (n : ℕ) :
    (reductionDerivedChange X (completedReductionProjection X d n)).obj
        (completedPullbackObject g d K) ⟶ (completedReductionFiniteTarget g d n).obj K :=
  ((pbcDerivedScalarAdjunction (completedReductionProjection X d n)).homEquiv _ _).symm
    ((completedReductionLimitProjection d (X := X) n).app
        ((completedTowerPullback g d).obj ((completedReductionTower Y d).obj K)) ≫
      (completedReductionFiniteEvaluation g d n).hom.app K)

/-- The sectionwise normalization specifying the ordinary quotient transition uniquely.
Source: blueprint finite arrows (blueprint: lemma-weil-pbc-completed-pullback-reduction). -/
def HasCompletedReductionOrdinaryTransitionNormalization (a b : ℕ) (h : a ≤ b)
    (τ : reductionChange Y (completedReductionProjection Y d b) ⋙
        completedReductionFiniteModules g d b ⟶
      reductionChange Y (completedReductionProjection Y d a) ⋙
        completedReductionFiniteModules g d a ⋙
          SheafOfModules.restrictScalars.{u + 1}
            ((adicLisseForget X).map (reductionCoefficientMap X d b a h))) : Prop :=
  ∀ (M : pbcModules Y (pbcAdicCompletion Y d)) (V : Y.ProEt) (U : X.ProEt)
        (f : U ⟶ (proEtaleBaseChange g).obj V)
        (s : (reductionCoefficient X d b).obj.obj (op U))
        (z : (reductionCoefficient Y d b).obj.obj (op V))
        (m : M.val.obj (op V)),
        completedReductionSectionEquation X (reductionCoefficientMap X d b a h)
          (τ.app M) (op U) (completedReductionFiniteGenerator g d b M V U f s z m)
          (completedReductionFiniteGenerator g d a M V U f
            ((reductionCoefficientMap X d b a h).hom.app (op U) s)
            ((reductionCoefficientMap Y d b a h).hom.app (op V) z) m)

attribute [irreducible] HasCompletedReductionOrdinaryTransitionNormalization

/-- The finite quotient transition before localization, fixed on all local generators.
Source: blueprint transition clause (blueprint: lemma-weil-pbc-completed-pullback-reduction).
Proof: apply the quotient to each coefficient in an inverse-image tensor. The square
of finite coefficient structure maps commutes with the quotients, so balancing and
restriction are respected. Local generators determine the map uniquely. Naturality
in the module follows from the same formula. -/
theorem completedReductionOrdinaryTransition_exists (a b : ℕ) (h : a ≤ b) :
    ∃! τ : reductionChange Y (completedReductionProjection Y d b) ⋙
        completedReductionFiniteModules g d b ⟶
      reductionChange Y (completedReductionProjection Y d a) ⋙
        completedReductionFiniteModules g d a ⋙
          SheafOfModules.restrictScalars.{u + 1}
            ((adicLisseForget X).map (reductionCoefficientMap X d b a h)),
      HasCompletedReductionOrdinaryTransitionNormalization g d a b h τ := by
  sorry

/-- The actual quotient transition on ordinary finite pullback reductions.
Source: blueprint transitions (blueprint: lemma-weil-pbc-completed-pullback-reduction). -/
def completedReductionOrdinaryTransition (a b : ℕ) (h : a ≤ b) :
    reductionChange Y (completedReductionProjection Y d b) ⋙
        completedReductionFiniteModules g d b ⟶
      reductionChange Y (completedReductionProjection Y d a) ⋙
        completedReductionFiniteModules g d a ⋙
          SheafOfModules.restrictScalars.{u + 1}
            ((adicLisseForget X).map (reductionCoefficientMap X d b a h)) :=
  (completedReductionOrdinaryTransition_exists g d a b h).exists.choose

/-- The representative normalization specifying the derived quotient transition comparison uniquely.
Source: blueprint finite arrows (blueprint: lemma-weil-pbc-completed-pullback-reduction). -/
def HasCompletedReductionTargetTransitionNormalization (a b : ℕ) (h : a ≤ b)
    (τ : completedReductionFiniteTarget g d b ⟶
        completedReductionFiniteTarget g d a ⋙
          pbcDerivedRestrict (reductionCoefficientMap X d b a h)) : Prop :=
  ∀ P : CochainComplex (pbcModules Y (pbcAdicCompletion Y d)) ℤ,
        CochainComplex.IsKFlatIndependentCoefficients (R := pbcAdicCompletion Y d) P →
        completedReductionFiniteModelMap g d b P ≫ DerivedCategory.Q.map
            ((NatTrans.mapHomologicalComplex
              (completedReductionOrdinaryTransition g d a b h) (.up ℤ)).app P) =
          τ.app (DerivedCategory.Q.obj P) ≫
            (pbcDerivedRestrict (reductionCoefficientMap X d b a h)).map
              (completedReductionFiniteModelMap g d a P) ≫
            (completedReductionRestrictionFactors X
              (reductionCoefficientMap X d b a h)).hom.app
                  (((completedReductionFiniteModules g d a).mapHomologicalComplex (.up ℤ)).obj
                    (((reductionChange Y
                      (completedReductionProjection Y d a)).mapHomologicalComplex
                        (.up ℤ)).obj P))

attribute [irreducible] HasCompletedReductionTargetTransitionNormalization

/-- The derived quotient transition, characterized by the universal K-flat comparisons.
Source: blueprint transitions (blueprint: lemma-weil-pbc-completed-pullback-reduction).
Proof: the ordinary quotient formula is natural on K-flat complexes and commutes
with differentials. Both finite pullback and coefficient restriction are exact.
Invert the scalar-extension comparisons on K-flat representatives and descend the
ordinary map. The universal derived comparisons give its unique natural descent. -/
theorem completedReductionTargetTransition_exists (a b : ℕ) (h : a ≤ b) :
    ∃! τ : completedReductionFiniteTarget g d b ⟶
        completedReductionFiniteTarget g d a ⋙
          pbcDerivedRestrict (reductionCoefficientMap X d b a h),
      HasCompletedReductionTargetTransitionNormalization g d a b h τ := by
  sorry

/-- The canonical derived transition before scalar-extension adjunction.
Source: blueprint transitions (blueprint: lemma-weil-pbc-completed-pullback-reduction). -/
def completedReductionTargetTransition (a b : ℕ) (h : a ≤ b) :
    completedReductionFiniteTarget g d b ⟶
        completedReductionFiniteTarget g d a ⋙
          pbcDerivedRestrict (reductionCoefficientMap X d b a h) :=
  (completedReductionTargetTransition_exists g d a b h).exists.choose

/-- Normalization of the pulled reduction tower is the scalar-extension adjunct of
its genuine quotient transition, with no reference to alpha or an arbitrary map.
Source: blueprint normalization clause (blueprint: lemma-weil-pbc-completed-pullback-reduction). -/
def completedReductionTargetNormalization
    (K : DerivedCategory (pbcModules Y (pbcAdicCompletion Y d))) (a b : ℕ) (h : a ≤ b) :=
  ((pbcDerivedScalarAdjunction (reductionCoefficientMap X d b a h)).homEquiv _ _).symm
    ((completedReductionTargetTransition g d a b h).app K)

/-- Equal-index restriction is the identity, fixed sectionwise.
Source: blueprint unit clause (blueprint: lemma-weil-pbc-completed-pullback-reduction).
Proof: the equal-index quotient is identity. Forgetting the restricted action leaves
every section unchanged, defining inverse natural maps whose section maps are identities. -/
theorem completedReductionOrdinaryRestrictionUnit_exists (T : Scheme.{u}) (a : ℕ) :
    ∃! e : SheafOfModules.restrictScalars.{u + 1}
        ((adicLisseForget T).map (reductionCoefficientMap T d a a (le_refl a))) ≅ 𝟭 _,
      ∀ (M : pbcModules T (reductionCoefficient T d a))
        (U : T.ProEtᵒᵖ) (x : M.val.obj U), (e.hom.app M).val.app U x = x := by
  classical
  have hφ : (adicLisseForget T).map
      (reductionCoefficientMap T d a a (le_refl a)) = 𝟙 _ := by
    rw [reductionCoefficientMap_id, CategoryTheory.Functor.map_id]
  let e : SheafOfModules.restrictScalars.{u + 1}
      ((adicLisseForget T).map (reductionCoefficientMap T d a a (le_refl a))) ≅ 𝟭 _ :=
    NatIso.ofComponents (fun M ↦
      (SheafOfModules.fullyFaithfulForget _).preimageIso
        (PresheafOfModules.isoMk
          (fun U ↦ ModuleCat.restrictScalarsId'App _ (by rw [hφ]; rfl) (M.val.obj U))
          (by intros; rfl))) (by intros; rfl)
  refine ⟨e, ?_, ?_⟩
  · intro M U x
    rfl
  · intro e' he'
    apply Iso.ext
    apply NatTrans.ext
    funext M
    apply SheafOfModules.hom_ext
    apply PresheafOfModules.hom_ext
    intro U
    ext x
    exact he' M U x

/-- The sectionwise identity comparison for equal-index restriction.
Source: blueprint unit clause (blueprint: lemma-weil-pbc-completed-pullback-reduction). -/
def completedReductionRestrictionUnit (T : Scheme.{u}) (a : ℕ) :
    pbcDerivedRestrict (reductionCoefficientMap T d a a (le_refl a)) ≅ 𝟭 _ :=
  letI := HasDerivedCategory.standard
    (pbcModules T (reductionCoefficient T d a))
  Functor.mapDerivedCategoryNatIso
    (completedReductionOrdinaryRestrictionUnit_exists d T a).exists.choose ≪≫
      Functor.mapDerivedCategoryIdIso _

/-- The canonical equal-index scalar-extension unitor, from the normalized adjunction.
Source: blueprint unit clause (blueprint: lemma-weil-pbc-completed-pullback-reduction). -/
def completedReductionUnit (T : Scheme.{u}) (a : ℕ)
    (M : DerivedCategory
      (pbcModules T (reductionCoefficient T d a))) :=
  (reductionDerivedChange T (reductionCoefficientMap T d a a (le_refl a))).map
      ((completedReductionRestrictionUnit d T a).inv.app M) ≫
    (pbcDerivedScalarAdjunction (reductionCoefficientMap T d a a (le_refl a))).counit.app M

/-- Reduction of completed pullback, including the actual projection-induced arrows,
functoriality, transition maps, normalization, quotient cocycle and equal-index unit.
The parameter n denotes the positive level n+1; representatives are arbitrary.
No boundedness, nonempty scheme, nonzero ring, or nonempty generator tuple is required.

Source: blueprint order 1262; Stacks Tag 099N (5)
(blueprint: lemma-weil-pbc-completed-pullback-reduction).

Proof:
1. Restrict to constant A-coefficients using lem-weil-pbc-constant-completion-equivalence.
The defining pulled strict tower becomes the reduction tower of ordinary pullback N,
including its quotient units and finite projections; no infinite limit is pulled back.
2. Apply lem-weil-pbc-ringed-koszul-completion-reflector. Its completed value is complete.
The constant/completed comparison identifies its Koszul unit with the unit for L;
exact scalar restriction reflects invertibility, giving intrinsic completeness over A_X.
3. Use the strict-perfect coefficient package and projection-formula totalization to
commute reduction by P_a with the Koszul derived limit. On the tail m>=a the reduced
Koszul differential vanishes. The degree-zero summand is constant N_a; negative
summands have zero transition across a gap of a. The strict-tower homotopy-limit
lemma kills their derived limit, and also permits discarding the finite initial tail.
The product triangle computes the constant tower as N_a by finite partial sums.
Thus reduction of the completion unit is invertible.
4. The projection-induced arrow composed with that reduced unit is identity by the
normalized scalar adjunction: x tensor s maps to (x tensor 1)s. Hence alpha is the
inverse of the reduced unit. Natural finite comparisons give functoriality.
5. Naturality of tensoring the single completion unit with each quotient gives the
transition square. Apply scalar associativity to the same unit and invert its
reductions to obtain normalization compatibility. Associativity of scalar multiplication
in the ordinary balanced formulas gives the quotient cocycle; the identity quotient
gives the stated unitor. All maps here are the uniquely normalized maps above. -/
theorem completedPullback_reduction
    (r : ℕ) (f : Fin r → A) (hf : Ideal.span (Set.range f) = d.ideal)
    (K : DerivedCategory (pbcModules Y (pbcAdicCompletion Y d)))
    (C : CochainComplex (pbcModules Y (pbcAdicCompletion Y d)) ℤ)
    (e : DerivedCategory.Q.obj C ≅ K)
    (_hK : IsDerivedCompleteIntrinsic Y d r f hf K C e) :
    (∀ (P : CochainComplex (pbcModules X (pbcAdicCompletion X d)) ℤ)
      (eP : DerivedCategory.Q.obj P ≅ completedPullbackObject g d K),
      IsDerivedCompleteIntrinsic X d r f hf (completedPullbackObject g d K) P eP) ∧
    (∀ n : ℕ, IsIso (completedPullbackReductionArrow g d K n)) ∧
    (∀ (K' : DerivedCategory (pbcModules Y (pbcAdicCompletion Y d)))
      (C' : CochainComplex (pbcModules Y (pbcAdicCompletion Y d)) ℤ)
      (e' : DerivedCategory.Q.obj C' ≅ K')
      (_hK' : IsDerivedCompleteIntrinsic Y d r f hf K' C' e') (v : K ⟶ K') (n : ℕ),
      (reductionDerivedChange X (completedReductionProjection X d n)).map
          ((completedPullbackFunctor g d).map v) ≫ completedPullbackReductionArrow g d K' n =
        completedPullbackReductionArrow g d K n ≫
          (completedReductionFiniteTarget g d n).map v) ∧
    (∀ (a b : ℕ) (h : a ≤ b),
      IsIso (completedReductionTargetNormalization g d K a b h) ∧
      ((pbcDerivedScalarAdjunction (reductionCoefficientMap X d b a h)).homEquiv _ _
          ((completedPullbackSourceNormalization d X a b h (completedPullbackObject g d K)).hom)) ≫
            (pbcDerivedRestrict (reductionCoefficientMap X d b a h)).map
              (completedPullbackReductionArrow g d K a) =
        completedPullbackReductionArrow g d K b ≫
          (completedReductionTargetTransition g d a b h).app K) ∧
    (∀ (a b : ℕ) (h : a ≤ b),
      (reductionDerivedChange X (reductionCoefficientMap X d b a h)).map
          (completedPullbackReductionArrow g d K b) ≫
            completedReductionTargetNormalization g d K a b h =
        (completedPullbackSourceNormalization d X a b h (completedPullbackObject g d K)).hom ≫
          completedPullbackReductionArrow g d K a) ∧
    (∀ (a b c : ℕ) (hab : a ≤ b) (hbc : b ≤ c),
      (reductionDerivedChange X (reductionCoefficientMap X d b a hab)).map
          (completedReductionTargetNormalization g d K b c hbc) ≫
            completedReductionTargetNormalization g d K a b hab =
        (completedReductionQuotientAssoc d X a b c hab hbc
            ((completedReductionFiniteTarget g d c).obj K)).hom ≫
          completedReductionTargetNormalization g d K a c (hab.trans hbc)) ∧
    ∀ a : ℕ, completedReductionTargetNormalization g d K a a (le_refl a) =
      completedReductionUnit d X a ((completedReductionFiniteTarget g d a).obj K) := by
  sorry

end AlgebraicGeometry.Scheme
