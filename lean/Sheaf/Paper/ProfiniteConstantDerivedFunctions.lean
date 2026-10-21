/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NB
-/
module

public import Sheaf.Paper.CondensedModuleDerivedPushpull
public import Sheaf.CategoryTheory.CondensedInternalBarResolution
public import Sheaf.Topology.ContinuousMapCondensedRing
public import Sheaf.Topology.ContinuousMapCondensedRingMap
public import Sheaf.Paper.ProfinitePointPullback
public import WeilConjectures.CategoryTheory.ModuleObjects.MapModMonoidal
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.MapDerivedCategory
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.MapDerivedComp
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.MonoidalModule
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Coherence
public import Mathlib.Topology.Algebra.Module.ModuleTopology
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.NumberTheory.Padics.PadicNumbers
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Sheaf.Paper.CoefficientHeartStratificationDefs
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients
public import WeilConjectures.CategoryTheory.ModuleObjects.FinitelyPresentedComap


import Sheaf.CategoryTheory.InternalSectionTensorComparison
import Sheaf.Paper.ModuleObjectRingedSiteDerivedComparison
import Sheaf.AlgebraicGeometry.InternalModuleOperationsTransport
import Sheaf.Paper.CondensedPointBasisEvaluation
import Sheaf.Paper.ProEtalePointComponentsMaps
import WeilConjectures.AlgebraicGeometry.ProEtale.WeaklyContractible
import Sheaf.AlgebraicGeometry.ProEtale.SingleWContractibleCover
import Sheaf.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization
import WeilConjectures.Algebra.Homology.KInjectiveRestrictLocalized
import Sheaf.Algebra.Homology.DerivedInternalHomOfUniverses
import Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses
import Sheaf.Algebra.Homology.RingedSliceEvaluationTranspose
import Sheaf.Paper.ComponentRelativeProfiniteSite
import Sheaf.Algebra.Homology.RingedInternalHomShiftOfUniverses
import Sheaf.Paper.ProjectionMateExact

/-! # Derived continuous functions on profinite parameters

Source: Hemo--Richarz--Scholbach, Example 3.1 and Proposition 4.3(1),
and the agent-formulated profinite-function input to paragraph (3) of
blueprint main-20261015, direct-image stability
(blueprint: lem-sfb-profinite-constant-derived-functions).

The comparison is the mate of evaluation at the universal parameter. Its definition
uses the original free internal module and the total K-injective right derived functor.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open scoped CategoryTheory.Obj TensorProduct

namespace AlgebraicGeometry.ProEtale.ProfiniteFunctions

/-- A named specialization of the existing canonical condensed sheaf tensor.
The body is the published instance, cached to avoid repeatedly synthesizing the large
presheaf internal-Hom diagrams when elaborating all the compatibility squares.
Source: the item's existing internal tensor
(blueprint: lem-sfb-profinite-constant-derived-functions). -/
instance condensedSheafMonoidal :
    MonoidalCategory (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) := inferInstance

/-- The corresponding named specialization of the existing pro-etale sheaf tensor.
Its data is precisely the published monoidal instance, without a different tensor.
Source: the item's existing internal tensor
(blueprint: lem-sfb-profinite-constant-derived-functions). -/
instance schemeSheafMonoidal (X : Scheme.{u}) :
    MonoidalCategory (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) := inferInstance

variable (R : Profinite.CondensedRing.{u}) [IsCommMonObj R.X]

/-- The recorded internal condensed modules.
Source: blueprint module objects (blueprint: lem-sfb-profinite-constant-derived-functions). -/
abbrev PointModules := Profinite.CondensedAction.Modules R

/-- Internal modules over the recorded pulled-back coefficient ring.
Source: blueprint pulled-back coefficients
(blueprint: lem-sfb-profinite-constant-derived-functions). -/
abbrev Modules (X : Scheme.{u}) :=
  Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj R.X X)

/-- The recorded free internal module on the representable condensed set of parameters.
Source: the item's free-module clause
(blueprint: lem-sfb-profinite-constant-derived-functions). -/
def freeParameter (P : Profinite.{u}) : PointModules R :=
  (Profinite.CondensedAction.InternalBar.free R).obj
    (((coherentTopology Profinite.{u}).uliftYoneda.{u + 1}).obj P)

/-- The actual relative profinite test scheme.
Source: blueprint profinite test objects
(blueprint: lem-sfb-profinite-constant-derived-functions). -/
abbrev testScheme (X : Scheme.{u}) (P : Profinite.{u}) : Scheme.{u} :=
  ((profiniteToProEtOf X).obj P).left

/-- Its canonical projection.
Source: blueprint profinite test objects
(blueprint: lem-sfb-profinite-constant-derived-functions). -/
abbrev projection (X : Scheme.{u}) (P : Profinite.{u}) : testScheme X P ⟶ X :=
  ((profiniteToProEtOf X).obj P).hom

/-- Inverse image of internal modules from the condensed point, with the existing action.
Source: blueprint pulled-back coefficients
(blueprint: lem-sfb-profinite-constant-derived-functions). -/
abbrev pointPull (X : Scheme.{u}) : PointModules R ⥤ Modules R X :=
  (upperStarFromPoint X).mapMod R.X

/-- The geometric point inverse image preserves finite limits.
Source: HRS Example 3.1 (blueprint: lem-sfb-profinite-constant-derived-functions).
Proof: the inverse image is sheafification after a left Kan extension along the
finite-limit-preserving profinite-test functor; the Kan indexing categories are filtered.
Finite limits commute with these filtered colimits, and sheafification is left exact. -/
@[instance] theorem pointAbelian_preservesFiniteLimits (X : Scheme.{u}) :
    PreservesFiniteLimits (upperStarFromPoint X) := by
  sorry

/-- Point inverse image preserves colimits, as the left adjoint of the point direct image.
Source: HRS Example 3.1 (blueprint: lem-sfb-profinite-constant-derived-functions). -/
instance pointAbelian_preservesColimits (X : Scheme.{u}) :
    PreservesColimitsOfSize.{u + 1, u + 1} (upperStarFromPoint X) :=
  (pointUpperStarLowerStarAdjunction.comp
    (upperStarLowerStarAdjunction Ab.{u + 1} (toSpecZ X))).leftAdjoint_preservesColimits

/-- Point inverse image on modules preserves finite limits, as does its underlying functor.
Source: HRS Example 3.1 (blueprint: lem-sfb-profinite-constant-derived-functions). -/
instance pointPull_preservesFiniteLimits (X : Scheme.{u}) :
    PreservesFiniteLimits (pointPull R X) :=
  inferInstanceAs (PreservesFiniteLimits ((upperStarFromPoint X).mapMod R.X))

/-- Point inverse image on modules preserves finite colimits.
Source: HRS Example 3.1 (blueprint: lem-sfb-profinite-constant-derived-functions). -/
instance pointPull_preservesFiniteColimits (X : Scheme.{u}) :
    PreservesFiniteColimits (pointPull R X) :=
  inferInstanceAs (PreservesFiniteColimits ((upperStarFromPoint X).mapMod R.X))

/-- The existing strong symmetric point inverse image, with its inherited braiding law.
Source: HRS Example 3.1 (blueprint: lem-sfb-profinite-constant-derived-functions). -/
instance pointAbelian_braided (X : Scheme.{u}) : (upperStarFromPoint X).Braided where
  toMonoidal := inferInstance
  braided := Functor.LaxBraided.braided

/-- The existing monoidal transport of module objects, using the actual point functor.
Source: HRS Example 3.1 (blueprint: lem-sfb-profinite-constant-derived-functions). -/
instance pointPull_monoidal (X : Scheme.{u}) : (pointPull R X).Monoidal :=
  inferInstanceAs ((upperStarFromPoint X).mapMod R.X).Monoidal

/-- Exact point inverse image is additive.
Source: HRS Example 3.1 (blueprint: lem-sfb-profinite-constant-derived-functions).
Proof: the underlying inverse image preserves finite limits and colimits; forgetting
module actions is faithful and creates the finite biproduct diagrams. Thus it preserves
addition, defined by the diagonal, the biproduct map and the codiagonal. -/
@[instance] theorem pointPull_additive (X : Scheme.{u}) : (pointPull R X).Additive := by
  sorry

/-- The ordinary unbounded derived point inverse image.
Source: blueprint unbounded module categories
(blueprint: lem-sfb-profinite-constant-derived-functions). -/
abbrev pointPullD (X : Scheme.{u}) := (pointPull R X).mapDerivedCategory

/-- Internal Hom right derived in its second variable, with K-injective resolutions.
Source: Stacks 08J7 (blueprint: lem-sfb-profinite-constant-derived-functions). -/
abbrev functions (P : Profinite.{u}) :
    DerivedCategory (PointModules R) ⥤ DerivedCategory (PointModules R) :=
  (ihom (freeParameter R P)).rightDerivedFunctor

/-- The free generator indexed by the identity of P.
Source: the free-forgetful adjunction in the item
(blueprint: lem-sfb-profinite-constant-derived-functions). -/
def identityGenerator (P : Profinite.{u}) : (freeParameter R P).X.obj.obj (op P) :=
  (((Profinite.CondensedAction.InternalBar.freeAdjunction R).unit.app
    (((coherentTopology Profinite.{u}).uliftYoneda.{u + 1}).obj P)).hom.app (op P))
      (ULift.up (𝟙 P))

/-- The graph of the universal parameter, as a map into the relative P-test object.
Source: the exponential-law normalization
(blueprint: lem-sfb-profinite-constant-derived-functions). -/
def parameterDiagonal (X : Scheme.{u}) (P : Profinite.{u}) :
    Scheme.ProEt.mk (𝟙 (testScheme X P)) ⟶
      (profiniteToProEtOf (testScheme X P)).obj P :=
  MorphismProperty.Over.homMk
    (pullback.lift (pullback.fst _ _) (𝟙 _)
      (specULiftZIsTerminal.hom_ext _ _)) (pullback.lift_snd _ _ _)

/-- The universal parameter section is the point-adjunction unit evaluated on [id_P],
then restricted along its graph. No choice of a point of P is involved.
Source: the item's evaluation normalization
(blueprint: lem-sfb-profinite-constant-derived-functions). -/
def parameterSection (X : Scheme.{u}) (P : Profinite.{u}) :
    ((pointPull R (testScheme X P)).obj (freeParameter R P)).X.obj.obj
      (op (Scheme.ProEt.mk (𝟙 (testScheme X P)))) :=
  (((pointPull R (testScheme X P)).obj (freeParameter R P)).X.obj.map
    (parameterDiagonal X P).op)
    ((((pointUpperStarLowerStarAdjunction.comp
      (upperStarLowerStarAdjunction Ab.{u + 1} (toSpecZ (testScheme X P)))).unit.app
        (freeParameter R P).X).hom.app (op P)) (identityGenerator R P))

/-- The terminal arrow of the small pro-etale site.
Source: the item's evaluation construction
(blueprint: lem-sfb-profinite-constant-derived-functions). -/
def terminalArrow {X : Scheme.{u}} (U : X.ProEt) : U ⟶ Scheme.ProEt.mk (𝟙 X) :=
  MorphismProperty.Over.homMk U.hom (Category.comp_id U.hom)

/-- A section determines the unique map out of the regular module by multiplication.
Source: Stacks 00YV, module objects; the item's free-module evaluation
(blueprint: lem-sfb-profinite-constant-derived-functions).
Proof: on U send a scalar r to r times the restriction of s. The module axioms give
additivity and linearity; restriction maps preserve the action. These maps therefore
form an internal module morphism. Conversely a linear map sends r to r times its value
on 1, so the formula determines it uniquely on every object of the site. -/
theorem sectionMap_existsUnique (X : Scheme.{u}) (N : Modules R X)
    (s : N.X.obj.obj (op (Scheme.ProEt.mk (𝟙 X)))) :
    ∃! f : Mod.regular (condensedRingObj R.X X) ⟶ N,
      ∀ (U : X.ProEt)
        (r : (CategoryTheory.InternalAbelianSheafModule.sectionRings
          (Scheme.ProEt.topology X) (condensedRingObj R.X X)).obj (op U)),
        (f.hom.hom.app (op U)) r =
          (inferInstance : Module
            ((CategoryTheory.InternalAbelianSheafModule.sectionRings
              (Scheme.ProEt.topology X) (condensedRingObj R.X X)).obj (op U))
            (((CategoryTheory.InternalAbelianSheafModule.sectionModuleFunctor
              (Scheme.ProEt.topology X) (condensedRingObj R.X X)).obj N).val.obj
                (op U))).smul r (N.X.obj.map (terminalArrow U).op s) := by
  sorry

/-- The universal parameter as a map from the tensor unit of internal modules.
Its sectionwise scalar-multiplication formula uniquely determines this map.
Source: the item's exponential-law normalization
(blueprint: lem-sfb-profinite-constant-derived-functions). -/
def parameterGenerator (X : Scheme.{u}) (P : Profinite.{u}) :
    𝟙_ (Modules R (testScheme X P)) ⟶
      (pointPull R (testScheme X P)).obj (freeParameter R P) :=
  (sectionMap_existsUnique R (testScheme X P) _ (parameterSection R X P)).choose

/-- Evaluate a function at the universal parameter before deriving.
Source: the free-module/tensor/internal-Hom adjunction in the item
(blueprint: lem-sfb-profinite-constant-derived-functions). -/
def evaluationApp (X : Scheme.{u}) (P : Profinite.{u}) (N : PointModules R) :
    (pointPull R (testScheme X P)).obj ((ihom (freeParameter R P)).obj N) ⟶
      (pointPull R (testScheme X P)).obj N :=
  (λ_ _).inv ≫ (parameterGenerator R X P ⊗ₘ 𝟙 _) ≫
    Functor.LaxMonoidal.μ (pointPull R (testScheme X P)) _ _ ≫
      (pointPull R (testScheme X P)).map ((ihom.ev (freeParameter R P)).app N)

/-- Evaluation is natural in its module argument.
Source: the item's naturality in M
(blueprint: lem-sfb-profinite-constant-derived-functions).
Proof: apply naturality of the tensor comparison to the identity in the free-parameter
factor and the given module map in the other factor. Naturality of the internal-Hom
counit then identifies both composites with evaluation followed by the given map. -/
theorem evaluation_naturality (X : Scheme.{u}) (P : Profinite.{u})
    (N N' : PointModules R) (f : N ⟶ N') :
    (pointPull R (testScheme X P)).map ((ihom (freeParameter R P)).map f) ≫
      evaluationApp R X P N' = evaluationApp R X P N ≫
        (pointPull R (testScheme X P)).map f := by
  sorry

/-- The natural transformation evaluating at the universal parameter.
Source: the item's evaluation-adjoint normalization
(blueprint: lem-sfb-profinite-constant-derived-functions). -/
def evaluation (X : Scheme.{u}) (P : Profinite.{u}) :
    ihom (freeParameter R P) ⋙ pointPull R (testScheme X P) ⟶
      pointPull R (testScheme X P) where
  app := evaluationApp R X P
  naturality N N' f := evaluation_naturality R X P N N' f

/-- Derived evaluation, by the existing right-derived natural transformation and the
canonical comparisons for exact outer inverse image. This fixes all resolution maps.
Source: Stacks 08J7 and the item's evaluation normalization
(blueprint: lem-sfb-profinite-constant-derived-functions). -/
def derivedEvaluation (X : Scheme.{u}) (P : Profinite.{u}) :
    functions R P ⋙ pointPullD R (testScheme X P) ⟶
      pointPullD R (testScheme X P) :=
  (Functor.rightDerivedFunctorCompMapDerivedCategoryIso
    (ihom (freeParameter R P)) (pointPull R (testScheme X P))).inv ≫
      Functor.rightDerivedFunctorNatTrans (evaluation R X P) ≫
        (Functor.rightDerivedFunctorIsoMapDerivedCategory
          (pointPull R (testScheme X P))).hom

/-- Point inverse image commutes with scheme pullback by the unique linear lift of
its recorded abelian composition comparison.
Source: blueprint pulled-back coefficients and the item's normalization
(blueprint: lem-sfb-profinite-constant-derived-functions).
Proof: the underlying comparison is upperStarFromPointComp. Its monoidality identifies
the coefficient actions, hence makes the comparison and its inverse linear. Forgetting
module actions is faithful, so the displayed underlying equation proves uniqueness. -/
theorem pointComp_existsUnique {Y X : Scheme.{u}} (f : Y ⟶ X) :
    ∃! c : pointPull R X ⋙ CondensedRing.upperStar R.X f ≅ pointPull R Y,
      ∀ N : PointModules R, (c.hom.app N).hom =
        (profinitePointModuleForgetPullbackIso R.X f).hom.app ((pointPull R X).obj N) ≫
          (upperStarFromPointComp f).hom.app N.X := by
  sorry

/-- The uniquely normalized linear point composition comparison.
Source: the item's normalization (blueprint: lem-sfb-profinite-constant-derived-functions). -/
def pointComp {Y X : Scheme.{u}} (f : Y ⟶ X) :
    pointPull R X ⋙ CondensedRing.upperStar R.X f ≅ pointPull R Y :=
  (pointComp_existsUnique R f).choose

/-- Its canonical lift to the ordinary unbounded derived categories.
Source: the item's normalization (blueprint: lem-sfb-profinite-constant-derived-functions). -/
def pointCompD {Y X : Scheme.{u}} (f : Y ⟶ X) :
    pointPullD R X ⋙ (CondensedRing.upperStar R.X f).mapDerivedCategory ≅ pointPullD R Y :=
  (Functor.mapDerivedCategoryCompIso (pointPull R X)
    (CondensedRing.upperStar R.X f)).symm ≪≫
      Functor.mapDerivedCategoryNatIso (pointComp R f)

/-- The exact-pullback form of the recorded total derived adjunction.
Source: blueprint module derived pushpull
(blueprint: lem-sfb-profinite-constant-derived-functions). -/
def projectionAdjunction (X : Scheme.{u}) (P : Profinite.{u}) :
    (CondensedRing.upperStar R.X (projection X P)).mapDerivedCategory ⊣
      CondensedRing.moduleObjectDerivedPushforward R.X (projection X P) :=
  (CondensedRing.derivedUpperStarLowerStarAdjunction R.X (projection X P)).ofNatIsoLeft
    (CondensedRing.upperStar R.X (projection X P)).leftDerivedFunctorIsoMapDerivedCategory

/-- The canonical evaluation-adjoint map, in the direction before inversion.
Source: the item's construction by evaluation and transposition
(blueprint: lem-sfb-profinite-constant-derived-functions). -/
def comparisonApp (X : Scheme.{u}) (P : Profinite.{u})
    (N : DerivedCategory (PointModules R)) :
    (pointPullD R X).obj ((functions R P).obj N) ⟶
      (CondensedRing.moduleObjectDerivedPushforward R.X (projection X P)).obj
        ((pointPullD R (testScheme X P)).obj N) :=
  (projectionAdjunction R X P).homEquiv _ _
    ((pointCompD R (projection X P)).hom.app ((functions R P).obj N) ≫
      (derivedEvaluation R X P).app N)

/-- Evaluation-adjoint comparison is natural in all derived condensed modules.
Source: the item's naturality in the constant model
(blueprint: lem-sfb-profinite-constant-derived-functions).
Proof: use naturality of pointCompD and derivedEvaluation. Naturality of the Hom
bijection in projectionAdjunction carries their common equality to the displayed square.
The equation is between derived morphisms, without applying cohomology. -/
theorem comparison_naturality (X : Scheme.{u}) (P : Profinite.{u})
    (N N' : DerivedCategory (PointModules R)) (f : N ⟶ N') :
    (pointPullD R X).map ((functions R P).map f) ≫ comparisonApp R X P N' =
      comparisonApp R X P N ≫
        (CondensedRing.moduleObjectDerivedPushforward R.X (projection X P)).map
          ((pointPullD R (testScheme X P)).map f) := by
  sorry

/-- The normalized comparison as a natural transformation on unbounded derived objects.
Source: the item's normalization and naturality
(blueprint: lem-sfb-profinite-constant-derived-functions). -/
def comparison (X : Scheme.{u}) (P : Profinite.{u}) :
    functions R P ⋙ pointPullD R X ⟶
      pointPullD R (testScheme X P) ⋙
        CondensedRing.moduleObjectDerivedPushforward R.X (projection X P) where
  app := comparisonApp R X P
  naturality N N' f := comparison_naturality R X P N N' f

/-- Internal derived functions on X, before using the constant-model comparison.
Source: the item's free-module/internal-Hom normalization
(blueprint: lem-sfb-profinite-constant-derived-functions). -/
abbrev schemeFunctions (X : Scheme.{u}) (P : Profinite.{u}) :=
  (ihom ((pointPull R X).obj (freeParameter R P))).rightDerivedFunctor

/-- The canonical composition map into a right derived functor after exact inverse image.
It is the Kan-extension map induced by the existing derived units, with no assertion
that inverse image preserves K-injective objects.
Source: Stacks 08J7 (blueprint: lem-sfb-profinite-constant-derived-functions). -/
def pointHomComposition (X : Scheme.{u}) (P : Profinite.{u}) :
    (pointPull R X ⋙ ihom ((pointPull R X).obj (freeParameter R P))).rightDerivedFunctor ⟶
      pointPullD R X ⋙ schemeFunctions R X P :=
  Functor.rightDerivedDesc _
    (pointPull R X ⋙ ihom ((pointPull R X).obj (freeParameter R P))).rightDerivedFunctorUnit
    (HomotopyCategory.quasiIso (PointModules R) (ComplexShape.up ℤ)) _
    (Functor.mapDerivedCategoryCompRightDerivedFunctorUnit (pointPull R X)
      (ihom ((pointPull R X).obj (freeParameter R P))))

/-- Canonical derived internal-Hom comparison induced by monoidal point inverse image.
Source: the item's evaluation construction
(blueprint: lem-sfb-profinite-constant-derived-functions). -/
def pointHomComparison (X : Scheme.{u}) (P : Profinite.{u}) :
    functions R P ⋙ pointPullD R X ⟶ pointPullD R X ⋙ schemeFunctions R X P :=
  (Functor.rightDerivedFunctorCompMapDerivedCategoryIso
    (ihom (freeParameter R P)) (pointPull R X)).inv ≫
      Functor.rightDerivedFunctorNatTrans
        (Functor.LaxMonoidal.ihomComparison (pointPull R X) (freeParameter R P)).natTrans ≫
      pointHomComposition R X P

/-- The universal parameter, with coefficients identified by the point composition map.
Source: the item's normalization (blueprint: lem-sfb-profinite-constant-derived-functions). -/
def relativeGenerator (X : Scheme.{u}) (P : Profinite.{u}) :
    𝟙_ (Modules R (testScheme X P)) ⟶
      (CondensedRing.upperStar R.X (projection X P)).obj
        ((pointPull R X).obj (freeParameter R P)) :=
  parameterGenerator R X P ≫ (pointComp R (projection X P)).inv.app (freeParameter R P)

/-- Evaluation of internal functions on X at its universal relative parameter.
Source: the item's tensor/internal-Hom normalization
(blueprint: lem-sfb-profinite-constant-derived-functions). -/
def relativeEvaluationApp (X : Scheme.{u}) (P : Profinite.{u}) (N : Modules R X) :
    (CondensedRing.upperStar R.X (projection X P)).obj
      ((ihom ((pointPull R X).obj (freeParameter R P))).obj N) ⟶
        (CondensedRing.upperStar R.X (projection X P)).obj N :=
  (λ_ _).inv ≫ (relativeGenerator R X P ⊗ₘ 𝟙 _) ≫
    Functor.LaxMonoidal.μ (CondensedRing.upperStar R.X (projection X P)) _ _ ≫
      (CondensedRing.upperStar R.X (projection X P)).map
        ((ihom.ev ((pointPull R X).obj (freeParameter R P))).app N)

/-- Evaluation-adjoint slice comparison is natural in every X-linear map.
Source: the item's linear naturality clause
(blueprint: lem-sfb-profinite-constant-derived-functions).
Proof: naturality of internal-Hom evaluation and of the tensorator gives the equality
before transposition. The ordinary pullback/direct-image Hom bijection is natural in
its target, and therefore gives exactly the displayed equality. -/
theorem sliceComparison_naturality (X : Scheme.{u}) (P : Profinite.{u})
    (N N' : Modules R X) (f : N ⟶ N') :
    (ihom ((pointPull R X).obj (freeParameter R P))).map f ≫
      (CondensedRing.upperStarLowerStarAdjunction R.X (projection X P)).homEquiv _ _
        (relativeEvaluationApp R X P N') =
    (CondensedRing.upperStarLowerStarAdjunction R.X (projection X P)).homEquiv _ _
      (relativeEvaluationApp R X P N) ≫
        (CondensedRing.lowerStar R.X (projection X P)).map
          ((CondensedRing.upperStar R.X (projection X P)).map f) := by
  sorry

/-- The canonical underived slice comparison, with its action on all X-linear maps.
Source: the item's normalization (blueprint: lem-sfb-profinite-constant-derived-functions). -/
def sliceComparison (X : Scheme.{u}) (P : Profinite.{u}) :
    ihom ((pointPull R X).obj (freeParameter R P)) ⟶
      CondensedRing.upperStar R.X (projection X P) ⋙
        CondensedRing.lowerStar R.X (projection X P) where
  app N := (CondensedRing.upperStarLowerStarAdjunction R.X (projection X P)).homEquiv _ _
    (relativeEvaluationApp R X P N)
  naturality N N' f := sliceComparison_naturality R X P N N' f

/-- Slice restriction along the relative profinite test projection preserves K-injectives.
Source: Stacks 08FI and the item's proof step 3
(blueprint: lem-sfb-profinite-constant-derived-functions).
Proof: the projection is pro-etale, so inverse image identifies with restriction to
the localized site. Extension by zero is its exact left adjoint. Transfer a morphism
from an acyclic complex across this adjunction and use K-injectivity on X. -/
@[instance] theorem projectionPull_preservesKInjective (X : Scheme.{u}) (P : Profinite.{u}) :
    (CondensedRing.upperStar R.X (projection X P)).PreservesKInjectiveComplexes := by
  sorry

/-- The canonical derived slice comparison, independent of the constant-model theorem.
Source: the item's proof step 3 (blueprint: lem-sfb-profinite-constant-derived-functions). -/
def derivedSliceComparison (X : Scheme.{u}) (P : Profinite.{u}) :
    schemeFunctions R X P ⟶
      (CondensedRing.upperStar R.X (projection X P)).mapDerivedCategory ⋙
        CondensedRing.moduleObjectDerivedPushforward R.X (projection X P) :=
  Functor.rightDerivedFunctorNatTrans (sliceComparison R X P) ≫
    (Functor.rightDerivedFunctorCompIso (CondensedRing.upperStar R.X (projection X P))
      (CondensedRing.lowerStar R.X (projection X P))).hom ≫
    Functor.whiskerRight
      (Functor.rightDerivedFunctorIsoMapDerivedCategory
        (CondensedRing.upperStar R.X (projection X P))).hom
      (CondensedRing.lowerStar R.X (projection X P)).rightDerivedFunctor

/-- The elementary slice comparison is an isomorphism on all unbounded derived modules.
Source: the item's proof steps 2--3
(blueprint: lem-sfb-profinite-constant-derived-functions).
Proof: identify the pulled-back representable h_P with h_{X[P]} on the w-contractible
basis by the component-map bijection. Thus its free module represents sections on the
slice. Tensor-Hom adjunction identifies sliceComparison with the ordinary slice identity.
Compute both derived sides on the same K-injective resolution; slice restriction preserves
K-injectives by Stacks 08FI. The termwise identity gives the stated derived isomorphism. -/
@[instance] theorem derivedSliceComparison_isIso (X : Scheme.{u}) (P : Profinite.{u}) :
    IsIso (derivedSliceComparison R X P) := by
  sorry

/-- The two independently constructed comparisons agree by evaluation transposition.
Source: the item's normalization and proof step 4
(blueprint: lem-sfb-profinite-constant-derived-functions).
Proof: substitute the monoidal internal-Hom comparison into relative evaluation.
Its evaluation identity turns the composite into evaluation at parameterGenerator.
The point-composition coherence and the units of right derivation identify the two
mates on K-injective complexes. The universal property of right derivation gives equality. -/
theorem comparison_factorization (X : Scheme.{u}) (P : Profinite.{u}) :
    comparison R X P = pointHomComparison R X P ≫
      Functor.whiskerLeft (pointPullD R X) (derivedSliceComparison R X P) ≫
      Functor.whiskerRight (pointCompD R (projection X P)).hom
        (CondensedRing.moduleObjectDerivedPushforward R.X (projection X P)) := by
  sorry

/-- The relative free module represents sections on the relative test scheme.
This equivalence is specified uniquely by its generator formula.
Source: the item's free-module clause and proof step 2
(blueprint: lem-sfb-profinite-constant-derived-functions).
Proof: identify the pulled-back representable with the relative representable on a
w-contractible affine basis. The free-forgetful adjunction followed by sheaf Yoneda
identifies the two Hom sets. Its forward map restricts a module map to the universal
generator, which is the displayed formula. This formula also proves uniqueness. -/
theorem parameterHom_existsUnique (X : Scheme.{u}) (P : Profinite.{u}) (N : Modules R X) :
    ∃! e : (((pointPull R X).obj (freeParameter R P)) ⟶ N) ≃
      (𝟙_ (Modules R (testScheme X P)) ⟶
        (CondensedRing.upperStar R.X (projection X P)).obj N),
      ∀ f, e f = relativeGenerator R X P ≫
        (CondensedRing.upperStar R.X (projection X P)).map f := by
  sorry

/-- The canonical free-generator/slice Hom bijection.
Source: the item's free-module adjunction
(blueprint: lem-sfb-profinite-constant-derived-functions). -/
def parameterHom (X : Scheme.{u}) (P : Profinite.{u}) (N : Modules R X) :=
  (parameterHom_existsUnique R X P N).choose

/-- The free-module map induced by an actual map of relative parameter objects.
It allows parameter maps depending on the base, not only maps of profinite sets.
Source: the item's whole-family clause
(blueprint: lem-sfb-profinite-constant-derived-functions). -/
def relativeFreeMap (X : Scheme.{u}) (P P' : Profinite.{u})
    (h : testScheme X P' ⟶ testScheme X P)
    (comm : h ≫ projection X P = projection X P') :
    (pointPull R X).obj (freeParameter R P') ⟶
      (pointPull R X).obj (freeParameter R P) :=
  (parameterHom R X P' ((pointPull R X).obj (freeParameter R P))).symm
    (Functor.LaxMonoidal.ε (CondensedRing.upperStar R.X h) ≫
      (CondensedRing.upperStar R.X h).map (relativeGenerator R X P) ≫
      (CondensedRing.upperStarComp R.X h (projection X P)).inv.app _ ≫
      (CondensedRing.upperStarCongr R.X comm).hom.app _)

/-- Derived internal-Hom precomposition by a relative parameter map.
Source: the item's parameter naturality
(blueprint: lem-sfb-profinite-constant-derived-functions). -/
def schemeParameterMap (X : Scheme.{u}) (P P' : Profinite.{u})
    (h : testScheme X P' ⟶ testScheme X P)
    (comm : h ≫ projection X P = projection X P') :
    schemeFunctions R X P ⟶ schemeFunctions R X P' :=
  Functor.rightDerivedFunctorNatTrans (MonoidalClosed.pre (relativeFreeMap R X P P' h comm))

/-- Canonical derived pullback comparison for a commutative relative parameter square.
Source: the item's base-change and parameter clauses
(blueprint: lem-sfb-profinite-constant-derived-functions). -/
def squarePullIso {X Y : Scheme.{u}} (f : Y ⟶ X) (P P' : Profinite.{u})
    (h : testScheme Y P' ⟶ testScheme X P)
    (comm : h ≫ projection X P = projection Y P' ≫ f) :
    (CondensedRing.upperStar R.X f).mapDerivedCategory ⋙
        (CondensedRing.upperStar R.X (projection Y P')).mapDerivedCategory ≅
      (CondensedRing.upperStar R.X (projection X P)).mapDerivedCategory ⋙
        (CondensedRing.upperStar R.X h).mapDerivedCategory :=
  (Functor.mapDerivedCategoryCompIso (CondensedRing.upperStar R.X f)
    (CondensedRing.upperStar R.X (projection Y P'))).symm ≪≫
  Functor.mapDerivedCategoryNatIso
    ((CondensedRing.upperStarComp R.X (projection Y P') f).symm ≪≫
      CondensedRing.upperStarCongr R.X comm.symm ≪≫
      CondensedRing.upperStarComp R.X h (projection X P)) ≪≫
  Functor.mapDerivedCategoryCompIso (CondensedRing.upperStar R.X (projection X P))
    (CondensedRing.upperStar R.X h)

/-- The ordinary base-change mate in the unbounded derived category, without assuming
it invertible. This fixes the direct-image map in every naturality square.
Source: the item's base-change and whole-family clauses
(blueprint: lem-sfb-profinite-constant-derived-functions). -/
def pushSquareApp {X Y : Scheme.{u}} (f : Y ⟶ X) (P P' : Profinite.{u})
    (h : testScheme Y P' ⟶ testScheme X P)
    (comm : h ≫ projection X P = projection Y P' ≫ f)
    (N : DerivedCategory (Modules R (testScheme X P))) :
    (CondensedRing.upperStar R.X f).mapDerivedCategory.obj
      ((CondensedRing.moduleObjectDerivedPushforward R.X (projection X P)).obj N) ⟶
    (CondensedRing.moduleObjectDerivedPushforward R.X (projection Y P')).obj
      ((CondensedRing.upperStar R.X h).mapDerivedCategory.obj N) :=
  (projectionAdjunction R Y P').homEquiv _ _
    ((squarePullIso R f P P' h comm).hom.app _ ≫
      (CondensedRing.upperStar R.X h).mapDerivedCategory.map
        ((projectionAdjunction R X P).counit.app N))

/-- The parameter projection is compatible with base change on its base scheme.
Source: the item's pro-etale base-change clause
(blueprint: lem-sfb-profinite-constant-derived-functions). -/
def parameterBaseMap {X Y : Scheme.{u}} (f : Y ⟶ X) (P : Profinite.{u}) :
    testScheme Y P ⟶ testScheme X P :=
  pullback.lift (pullback.fst _ _) (projection Y P ≫ f)
    (specULiftZIsTerminal.hom_ext _ _)

/-- The canonical comparison commutes with pro-etale base change, as derived maps.
Source: the item's proof steps 4 and 6
(blueprint: lem-sfb-profinite-constant-derived-functions).
Proof: transpose the two composites under projectionAdjunction. Pullback composition
and the counit defining pushSquareApp reduce both to evaluation at the same universal
P-parameter. The slice evaluation/transposition identity gives equality before taking
any cohomology. This calculation works on affine slices and glues on general Y. -/
theorem comparison_baseChange {X Y : Scheme.{u}} (f : Y ⟶ X) [WeaklyEtale f]
    (P : Profinite.{u}) (N : DerivedCategory (PointModules R)) :
    (CondensedRing.upperStar R.X f).mapDerivedCategory.map (comparisonApp R X P N) ≫
      pushSquareApp R f P P (parameterBaseMap f P) (pullback.lift_snd _ _ _)
        ((pointPullD R (testScheme X P)).obj N) ≫
      (CondensedRing.moduleObjectDerivedPushforward R.X (projection Y P)).map
        ((pointCompD R (parameterBaseMap f P)).hom.app N) =
    (pointCompD R f).hom.app ((functions R P).obj N) ≫ comparisonApp R Y P N := by
  sorry

/-- The canonical derived slice comparison in the inverse direction.
Source: the item's proof step 3 (blueprint: lem-sfb-profinite-constant-derived-functions). -/
def sliceDelta (X : Scheme.{u}) (P : Profinite.{u}) :
    (CondensedRing.upperStar R.X (projection X P)).mapDerivedCategory ⋙
        CondensedRing.moduleObjectDerivedPushforward R.X (projection X P) ≅
      schemeFunctions R X P :=
  (asIso (derivedSliceComparison R X P)).symm

/-- Parameter pullback on the direct-image side, transposed from its derived counit.
Source: the item's whole-family clause
(blueprint: lem-sfb-profinite-constant-derived-functions). -/
def pushParameterApp (X : Scheme.{u}) (P P' : Profinite.{u})
    (h : testScheme X P' ⟶ testScheme X P)
    (comm : h ≫ projection X P = projection X P')
    (N : DerivedCategory (Modules R X)) :
    (CondensedRing.moduleObjectDerivedPushforward R.X (projection X P)).obj
      ((CondensedRing.upperStar R.X (projection X P)).mapDerivedCategory.obj N) ⟶
    (CondensedRing.moduleObjectDerivedPushforward R.X (projection X P')).obj
      ((CondensedRing.upperStar R.X (projection X P')).mapDerivedCategory.obj N) :=
  (projectionAdjunction R X P').homEquiv _ _
    ((Functor.mapDerivedCategoryNatIso
      ((CondensedRing.upperStarComp R.X h (projection X P)).symm ≪≫
        CondensedRing.upperStarCongr R.X comm)).inv.app _ ≫
    (Functor.mapDerivedCategoryCompIso
      (CondensedRing.upperStar R.X (projection X P))
      (CondensedRing.upperStar R.X h)).hom.app _ ≫
    (CondensedRing.upperStar R.X h).mapDerivedCategory.map
      ((projectionAdjunction R X P).counit.app
        ((CondensedRing.upperStar R.X (projection X P)).mapDerivedCategory.obj N)) ≫
    (Functor.mapDerivedCategoryCompIso
      (CondensedRing.upperStar R.X (projection X P))
      (CondensedRing.upperStar R.X h)).inv.app N ≫
    (Functor.mapDerivedCategoryNatIso
      ((CondensedRing.upperStarComp R.X h (projection X P)).symm ≪≫
        CondensedRing.upperStarCongr R.X comm)).hom.app N)

/-- Whole-family parameter and linear naturality, for every X-linear derived map u.
The equality lives on X itself. In particular take X to be the relative Q-test scheme:
then it is an equality over X[Q], with no passage to Q-points.
Source: the item's whole-family clause and proof step 7
(blueprint: lem-sfb-profinite-constant-derived-functions).
Proof: transpose the parameter square. The free-generator definition of relativeFreeMap
makes both sides evaluate the same relative parameter. Compose with u and use naturality
of the internal-Hom counit. Derive on the same K-injective resolution; the localization
calculation gives the equality for arbitrary unbounded objects. Finally invert the
slice comparison. This equality holds on the entire slice, including higher terms. -/
theorem sliceDelta_family_naturality (X : Scheme.{u}) (P P' : Profinite.{u})
    (h : testScheme X P' ⟶ testScheme X P)
    (comm : h ≫ projection X P = projection X P')
    (N N' : DerivedCategory (Modules R X)) (u : N ⟶ N') :
    (sliceDelta R X P).hom.app N ≫ (schemeParameterMap R X P P' h comm).app N ≫
      (schemeFunctions R X P').map u =
    pushParameterApp R X P P' h comm N ≫
      (CondensedRing.moduleObjectDerivedPushforward R.X (projection X P')).map
        ((CondensedRing.upperStar R.X (projection X P')).mapDerivedCategory.map u) ≫
      (sliceDelta R X P').hom.app N' := by
  sorry

/-- The point-side derived internal-Hom precomposition by the free map of a continuous
parameter map phi from P' to P.
Source: the item's naturality in continuous maps of profinite parameters
(blueprint: lem-sfb-profinite-constant-derived-functions). -/
def pointParameterMap {P P' : Profinite.{u}} (φ : P' ⟶ P) :
    functions R P ⟶ functions R P' :=
  Functor.rightDerivedFunctorNatTrans
    (MonoidalClosed.pre (show freeParameter R P' ⟶ freeParameter R P from
      (Profinite.CondensedAction.InternalBar.free R).map
        (((coherentTopology Profinite.{u}).uliftYoneda.{u + 1}).map φ)))

/-- The relative test-scheme map induced by a continuous parameter map.
Source: blueprint profinite test objects and the item's parameter naturality
(blueprint: lem-sfb-profinite-constant-derived-functions). -/
abbrev testSchemeMap (X : Scheme.{u}) {P P' : Profinite.{u}} (φ : P' ⟶ P) :
    testScheme X P' ⟶ testScheme X P :=
  ((profiniteToProEtOf X).map φ).left

/-- The comparison is natural in continuous maps of profinite parameters, as derived maps
on X. Since delta is the inverse of comparisonApp on the supplied constant models, this is
the item's parameter naturality of delta, with its displayed target p_X^* RHom(C_F[P],M_F).
Source: the item's parameter naturality clause and proof step 6
(blueprint: lem-sfb-profinite-constant-derived-functions).
Proof: transpose both composites under projectionAdjunction for P'. Precomposition with the
free map of phi followed by evaluation at the universal P'-parameter is evaluation at the
image of that parameter under phi, by the free-generator adjunction. That image is the
pullback, along the induced test-scheme map, of the universal P-parameter. The counit
defining pushParameterApp and the point-composition coherences identify the transpose of
the second composite with this same evaluation. Uniqueness of transposes under the derived
adjunction gives the equality of derived morphisms, without applying cohomology. -/
theorem comparison_parameterNaturality (X : Scheme.{u}) {P P' : Profinite.{u}} (φ : P' ⟶ P)
    (N : DerivedCategory (PointModules R)) :
    (pointPullD R X).map ((pointParameterMap R φ).app N) ≫ comparisonApp R X P' N =
      comparisonApp R X P N ≫
        (CondensedRing.moduleObjectDerivedPushforward R.X (projection X P)).map
          ((pointCompD R (projection X P)).inv.app N) ≫
        pushParameterApp R X P P' (testSchemeMap X φ)
          (MorphismProperty.Over.w ((profiniteToProEtOf X).map φ))
          ((pointPullD R X).obj N) ≫
        (CondensedRing.moduleObjectDerivedPushforward R.X (projection X P')).map
          ((pointCompD R (projection X P')).hom.app N) := by
  sorry

/-- The profinite test-scheme functor preserves finite products, independently of X.
Source: the item's relative test objects, proof step 2
(blueprint: lem-sfb-profinite-constant-derived-functions).
Proof: the adjunction with profinite connected components proves finite-limit preservation
for profiniteToCommRingCatOp. Spec preserves limits. Hence the composite profiniteToScheme
preserves finite products, with the canonical product comparison. -/
@[instance] theorem testSchemeFunctor_preservesFiniteLimits :
    PreservesFiniteLimits profiniteToScheme.{u} := by
  sorry

/-- The actual simultaneous continuous parameter map over X[Q]. Here Q times P'
is the categorical profinite product, canonically the topological product.
Source: the item's whole-family clause
(blueprint: lem-sfb-profinite-constant-derived-functions). -/
def familyParameterMap (X : Scheme.{u}) (Q P P' : Profinite.{u})
    (α : Q ⨯ P' ⟶ P) :
    testScheme (testScheme X Q) P' ⟶ testScheme (testScheme X Q) P :=
  pullback.lift
    (Limits.prod.lift
      (projection (testScheme X Q) P' ≫ pullback.fst _ _)
      (pullback.fst _ _) ≫
      inv (Limits.prodComparison profiniteToScheme Q P') ≫ profiniteToScheme.map α)
    (projection (testScheme X Q) P') (specULiftZIsTerminal.hom_ext _ _)

/-- The family map lies over the entire Q-test scheme.
Source: the item's whole-family clause
(blueprint: lem-sfb-profinite-constant-derived-functions).
Proof: familyParameterMap is the indicated pullback lift. Its second projection is
the relative P'-projection by the second pullback equation. -/
theorem familyParameterMap_over (X : Scheme.{u}) (Q P P' : Profinite.{u})
    (α : Q ⨯ P' ⟶ P) :
    familyParameterMap X Q P P' α ≫ projection (testScheme X Q) P =
      projection (testScheme X Q) P' := by
  sorry

section ScalarRestriction

variable (S : Profinite.CondensedRing.{u}) [IsCommMonObj S.X]
  (a : R.X ⟶ S.X) [IsMonHom a]

/-- The exact restriction of condensed module scalars.
Source: the item's scalar clause (blueprint: lem-sfb-profinite-constant-derived-functions). -/
abbrev restrictPoint : PointModules S ⥤ PointModules R := Mod.comap a

/-- The exact restriction of the pulled-back coefficient rings.
Source: the item's scalar clause (blueprint: lem-sfb-profinite-constant-derived-functions). -/
abbrev restrictScheme (X : Scheme.{u}) : Modules S X ⥤ Modules R X :=
  Mod.comap (coefficientMap a X)

/-- Scalar restriction and point pullback commute by the recorded mapMod construction.
Source: the item's scalar clause (blueprint: lem-sfb-profinite-constant-derived-functions). -/
def restrictPointPull (X : Scheme.{u}) :
    restrictPoint R S a ⋙ pointPull R X ≅ pointPull S X ⋙ restrictScheme R S a X :=
  (upperStarFromPoint X).mapModComapIso a

/-- Its exact levelwise derived comparison.
Source: the item's scalar clause (blueprint: lem-sfb-profinite-constant-derived-functions). -/
def restrictPointPullD (X : Scheme.{u}) :
    (restrictPoint R S a).mapDerivedCategory ⋙ pointPullD R X ≅
      pointPullD S X ⋙ (restrictScheme R S a X).mapDerivedCategory :=
  (Functor.mapDerivedCategoryCompIso _ _).symm ≪≫
    Functor.mapDerivedCategoryNatIso (restrictPointPull R S a X) ≪≫
    Functor.mapDerivedCategoryCompIso _ _

/-- The scalar-change comparison into a right derived functor, with no flatness hypothesis.
Source: the item's proof step 8, Stacks 08J7
(blueprint: lem-sfb-profinite-constant-derived-functions). -/
def restrictHomComposition (P : Profinite.{u}) :
    (restrictPoint R S a ⋙ ihom (freeParameter R P)).rightDerivedFunctor ⟶
      (restrictPoint R S a).mapDerivedCategory ⋙ functions R P :=
  Functor.rightDerivedDesc _
    (restrictPoint R S a ⋙ ihom (freeParameter R P)).rightDerivedFunctorUnit
    (HomotopyCategory.quasiIso (PointModules S) (ComplexShape.up ℤ)) _
    (Functor.mapDerivedCategoryCompRightDerivedFunctorUnit (restrictPoint R S a)
      (ihom (freeParameter R P)))

/-- The generator section at an arbitrary generalized parameter.
Source: the item's free-module adjunction
(blueprint: lem-sfb-profinite-constant-derived-functions). -/
def generatorAt (P T : Profinite.{u}) (b : T ⟶ P) :
    (freeParameter R P).X.obj.obj (op T) :=
  (((Profinite.CondensedAction.InternalBar.freeAdjunction R).unit.app
    (((coherentTopology Profinite.{u}).uliftYoneda.{u + 1}).obj P)).hom.app (op T))
      (ULift.up b)

/-- Restricting internal functions is uniquely characterized by the same free generators
and the unchanged underlying evaluation. This specifies actual data, not an arbitrary map.
Source: the item's proof step 8, Stacks 08J7
(blueprint: lem-sfb-profinite-constant-derived-functions).
Proof: extend the canonical free R-generator to the free S-generator using the free
adjunction. Compose restricted S-linear evaluation with this generator map. The resulting
balanced R-bilinear map transposes to the required R-linear internal-Hom map. At every
profinite T the displayed formula is its evaluation at every generalized parameter b.
The free adjunction and internal-Hom adjunction imply that these evaluations determine
the map uniquely. Naturality follows from associativity of evaluation. -/
theorem restrictHom_existsUnique (P : Profinite.{u}) :
    ∃! c : ihom (freeParameter S P) ⋙ restrictPoint R S a ⟶
      restrictPoint R S a ⋙ ihom (freeParameter R P),
      ∀ (N : PointModules S) (T : Profinite.{u}) (b : T ⟶ P)
        (z : ((ihom (freeParameter S P)).obj N).X.obj.obj (op T)),
        (((ihom.ev (freeParameter R P)).app ((restrictPoint R S a).obj N)).hom.hom.app
          (op T))
          (Profinite.CondensedAction.InternalBar.pureTensor R (freeParameter R P)
            ((ihom (freeParameter R P)).obj ((restrictPoint R S a).obj N)) T
            (generatorAt R P T b) ((c.app N).hom.hom.app (op T) z)) =
        (((ihom.ev (freeParameter S P)).app N).hom.hom.app (op T))
          (Profinite.CondensedAction.InternalBar.pureTensor S (freeParameter S P)
            ((ihom (freeParameter S P)).obj N) T (generatorAt S P T b) z) := by
  sorry

/-- The canonically evaluated restriction of internal functions.
Source: the item's scalar clause (blueprint: lem-sfb-profinite-constant-derived-functions). -/
def restrictHom (P : Profinite.{u}) := (restrictHom_existsUnique R S a P).choose

/-- Its right-derived comparison, without asserting that scalar extension is exact.
Source: the item's proof step 8 (blueprint: lem-sfb-profinite-constant-derived-functions). -/
def restrictHomD (P : Profinite.{u}) :
    functions S P ⋙ (restrictPoint R S a).mapDerivedCategory ⟶
      (restrictPoint R S a).mapDerivedCategory ⋙ functions R P :=
  (Functor.rightDerivedFunctorCompMapDerivedCategoryIso
    (ihom (freeParameter S P)) (restrictPoint R S a)).inv ≫
      Functor.rightDerivedFunctorNatTrans (restrictHom R S a P) ≫
        restrictHomComposition R S a P

/-- Canonical scalar comparison for total direct image; its direction follows the
right-derived universal property and it need not be an isomorphism.
Source: the item's proof step 8 (blueprint: lem-sfb-profinite-constant-derived-functions). -/
def restrictPushD (X : Scheme.{u}) (P : Profinite.{u}) :
    CondensedRing.moduleObjectDerivedPushforward S.X (projection X P) ⋙
      (restrictScheme R S a X).mapDerivedCategory ⟶
    (restrictScheme R S a (testScheme X P)).mapDerivedCategory ⋙
      CondensedRing.moduleObjectDerivedPushforward R.X (projection X P) :=
  (Functor.rightDerivedFunctorCompMapDerivedCategoryIso
    (CondensedRing.lowerStar S.X (projection X P)) (restrictScheme R S a X)).inv ≫
  Functor.rightDerivedFunctorNatTrans
    (CondensedRing.comapLowerStarIso a (projection X P)).hom ≫
  Functor.rightDerivedDesc _
    (restrictScheme R S a (testScheme X P) ⋙
      CondensedRing.lowerStar R.X (projection X P)).rightDerivedFunctorUnit
    (HomotopyCategory.quasiIso (Modules S (testScheme X P)) (ComplexShape.up ℤ)) _
    (Functor.mapDerivedCategoryCompRightDerivedFunctorUnit
      (restrictScheme R S a (testScheme X P)) (CondensedRing.lowerStar R.X (projection X P)))

/-- Scalar restriction commutes with the normalized comparison, as derived morphisms.
This square, together with comparison_naturality for M_E to Res M_Omega, is the scalar
compatibility square in the item; neither scalar-comparison arrow is assumed invertible.
Source: the item's proof step 8
(blueprint: lem-sfb-profinite-constant-derived-functions).
Proof: transpose both routes under the derived projection adjunction and the derived
extension/restriction adjunction. restrictHom is normalized on every generalized free
generator and restrictPushD is the mate of the recorded coefficient square. Thus both
transposes evaluate the same generator and then restrict scalars. Uniqueness of mates
and of the right-derived extension gives equality on the unbounded derived category.
Composing with the supplied module map evaluates and then sends x to 1 tensor x. -/
theorem comparison_scalarRestriction (X : Scheme.{u}) (P : Profinite.{u})
    (N : DerivedCategory (PointModules S)) :
    (pointPullD R X).map ((restrictHomD R S a P).app N) ≫
      comparisonApp R X P ((restrictPoint R S a).mapDerivedCategory.obj N) =
    (restrictPointPullD R S a X).hom.app ((functions S P).obj N) ≫
      (restrictScheme R S a X).mapDerivedCategory.map (comparisonApp S X P N) ≫
      (restrictPushD R S a X P).app ((pointPullD S (testScheme X P)).obj N) ≫
      (CondensedRing.moduleObjectDerivedPushforward R.X (projection X P)).map
        ((restrictPointPullD R S a (testScheme X P)).inv.app N) := by
  sorry

end ScalarRestriction

section ContinuousModels

variable (F : Type u) [NormedField F]

/-- The original all-continuous coefficient ring from the recorded dependency.
Source: HRS Example 3.1 (blueprint: lem-sfb-profinite-constant-derived-functions). -/
def continuousRing : Profinite.CondensedRing.{u} :=
  Mon.mk ((sheafCompose (coherentTopology Profinite.{u})
    (forget₂ RingCat.{u + 1} AddCommGrpCat.{u + 1})).obj
      (Profinite.continuousMapRingSheafOfUniverse.{u, u} F))

/-- Commutativity is the existing pointwise continuous-coefficient construction.
Source: HRS Example 3.1 (blueprint: lem-sfb-profinite-constant-derived-functions). -/
instance continuousRing_comm : IsCommMonObj (continuousRing F).X :=
  Sheaf.isCommMonObj_sheafCompose_obj (coherentTopology Profinite.{u})
    (Profinite.continuousMapRingSheafOfUniverse.{u, u} F)
    (fun S (a b : ULift.{u + 1} C(S.unop, F)) ↦ mul_comm a b)

variable (V : Type u) [AddCommGroup V] [Module F V] [TopologicalSpace V]
  [IsTopologicalAddGroup V] [ContinuousSMul F V]

/-- All continuous V-valued functions, with their additive operations and restrictions.
Source: the item's definition of M_F
(blueprint: lem-sfb-profinite-constant-derived-functions). -/
def continuousPresheaf : Profinite.{u}ᵒᵖ ⥤ Ab.{u + 1} where
  obj S := AddCommGrpCat.of (ULift.{u + 1} C(S.unop, V))
  map f := AddCommGrpCat.ofHom
    { toFun := fun a ↦ ULift.up (a.down.comp f.unop.hom.hom)
      map_zero' := rfl
      map_add' := fun _ _ ↦ rfl }
  map_id _ := rfl
  map_comp _ _ := rfl

/-- The canonical presheaf ring structure underlying the coefficient sheaf.
Source: the item's pointwise coefficient construction
(blueprint: lem-sfb-profinite-constant-derived-functions). -/
instance continuousPresheafRingMonObj : MonObj (continuousRing F).X.obj :=
  (sheafToPresheaf (coherentTopology Profinite.{u}) Ab.{u + 1}).monObjObj
    (continuousRing F).X

/-- Sectionwise scalar multiplication commutes with restriction.
Source: the item's pointwise continuous-module construction
(blueprint: lem-sfb-profinite-constant-derived-functions).
Proof: evaluate both maps on a pure tensor a tensor m and then on a point s.
Both give a(f(s)) times m(f(s)). Pure tensors generate the section tensor product. -/
theorem continuousAction_naturality (S T : Profinite.{u}ᵒᵖ) (f : S ⟶ T) :
    ((continuousRing F).X.obj.map f ⊗ₘ (continuousPresheaf V).map f) ≫
      CategoryTheory.InternalAbelianSheafModule.ordinaryAction
        (S := ULift.{u + 1} C(T.unop, F)) (N := ULift.{u + 1} C(T.unop, V)) =
    CategoryTheory.InternalAbelianSheafModule.ordinaryAction
      (S := ULift.{u + 1} C(S.unop, F)) (N := ULift.{u + 1} C(S.unop, V)) ≫
        (continuousPresheaf V).map f := by
  sorry

/-- The actual pointwise scalar action on presheaves.
Source: the item's definition of M_F
(blueprint: lem-sfb-profinite-constant-derived-functions). -/
def continuousAction : (continuousRing F).X.obj ⊗ continuousPresheaf V ⟶
    continuousPresheaf V where
  app S := CategoryTheory.InternalAbelianSheafModule.ordinaryAction
    (S := ULift.{u + 1} C(S.unop, F)) (N := ULift.{u + 1} C(S.unop, V))
  naturality S T f := continuousAction_naturality F V S T f

/-- The action has the ordinary unital and associative module laws.
Source: the item's pointwise module construction
(blueprint: lem-sfb-profinite-constant-derived-functions).
Proof: test the first equality on an integer tensor m, and the second on
(a tensor b) tensor m. They are the pointwise identities 1 times m = m and
(ab) times m = a times (b times m). The reconstructed coefficient multiplication is
pointwise multiplication, by the ring-sheaf monoid construction and its counit. -/
theorem continuousAction_laws :
    (CategoryTheory.MonObj.one (X := (continuousRing F).X.obj) ▷
      continuousPresheaf V) ≫ continuousAction F V = (λ_ _).hom ∧
    (CategoryTheory.MonObj.mul (X := (continuousRing F).X.obj) ▷
      continuousPresheaf V) ≫ continuousAction F V =
        (α_ _ _ _).hom ≫ (continuousRing F).X.obj ◁ continuousAction F V ≫
          continuousAction F V := by
  sorry

/-- The presheaf module with precisely the pointwise continuous-function action.
Source: the item's definition of M_F
(blueprint: lem-sfb-profinite-constant-derived-functions). -/
def continuousPresheafModule :
    Mod (Profinite.{u}ᵒᵖ ⥤ Ab.{u + 1}) (continuousRing F).X.obj where
  X := continuousPresheaf V
  mod :=
    { smul := continuousAction F V
      one_smul := (continuousAction_laws F V).1
      mul_smul := (continuousAction_laws F V).2 }

/-- Continuous functions satisfy descent for the coherent profinite topology.
Source: HRS Example 3.1 (blueprint: lem-sfb-profinite-constant-derived-functions).
Proof: a surjection of compact Hausdorff spaces is a quotient map. A matching family
therefore descends to a unique continuous function. Finite disjoint unions give products,
including the empty product. Addition and scalar multiplication descend pointwise. -/
theorem continuousPresheaf_isSheaf :
    Presheaf.IsSheaf (coherentTopology Profinite.{u}) (continuousPresheaf V) := by
  sorry

/-- M_F is constructed by the existing internal-module sheafification functor from the
presheaf Q mapsto C(Q,V). The preceding descent theorem identifies its sections with
all continuous functions, including those with infinitely many values.
Source: the item's definition of M_F
(blueprint: lem-sfb-profinite-constant-derived-functions). -/
def continuousModule : PointModules (continuousRing F) :=
  (CategoryTheory.InternalAbelianSheafModule.sheafModuleReflector
    (coherentTopology Profinite.{u}) (continuousRing F).X).obj
      (continuousPresheafModule F V)

/-- The scalar counit mate in the module sheafification construction is invertible.
Source: the item's continuous-model construction, HRS Example 3.1
(blueprint: lem-sfb-profinite-constant-derived-functions).
Proof: the inverse Hom bijection sends the identity on the underlying presheaf of R
to the counit at R. Sheaf inclusion is fully faithful, so that counit is invertible. -/
@[instance] theorem continuousCounitMate_isIso :
    IsIso (((sheafificationAdjunction (coherentTopology Profinite.{u}) Ab.{u + 1}).homEquiv
      (continuousRing F).X.obj (continuousRing F).X).symm (𝟙 (continuousRing F).X.obj)) := by
  sorry

/-- The scalar counit mate preserves the canonical coefficient monoid structure.
Source: the item's continuous-model construction, HRS Example 3.1
(blueprint: lem-sfb-profinite-constant-derived-functions).
Proof: the mate of the identity is the counit of the monoidal sheafification adjunction.
The counit is monoidal, hence its component is a morphism of monoid objects. -/
@[instance] theorem continuousCounitMate_isMonHom :
    IsMonHom (((sheafificationAdjunction (coherentTopology Profinite.{u}) Ab.{u + 1}).homEquiv
      (continuousRing F).X.obj (continuousRing F).X).symm (𝟙 (continuousRing F).X.obj)) := by
  sorry

/-- The actual sheafification-unit map from continuous functions to the constructed model.
Source: the item's M_F, HRS Example 3.1
(blueprint: lem-sfb-profinite-constant-derived-functions). -/
def continuousModuleUnit : continuousPresheaf V ⟶ (continuousModule F V).X.obj :=
  let adj := sheafificationAdjunction (coherentTopology Profinite.{u}) Ab.{u + 1}
  let ψ := adj.counit.app (continuousRing F).X
  letI : IsMonHom ψ := inferInstance
  letI : IsIso ((adj.homEquiv (continuousRing F).X.obj (continuousRing F).X).symm
    (𝟙 (continuousRing F).X.obj)) := continuousCounitMate_isIso F
  letI : IsMonHom ((adj.homEquiv (continuousRing F).X.obj (continuousRing F).X).symm
    (𝟙 (continuousRing F).X.obj)) := continuousCounitMate_isMonHom F
  let e := adj.modAdjunction
    (A := (continuousRing F).X.obj) (B := (continuousRing F).X)
    (𝟙 (continuousRing F).X.obj)
  (e.unit.app (continuousPresheafModule F V)).hom ≫
    ((Mod.comapId (continuousRing F).X.obj).hom.app _).hom

/-- The continuous-function model has exactly its original sections.
Source: HRS Example 3.1 and the item's all-continuous clause
(blueprint: lem-sfb-profinite-constant-derived-functions).
Proof: continuousPresheaf_isSheaf makes the underlying sheafification unit invertible.
The coefficient counit is invertible, and the module reflector uses extension along
that counit. Its comparison with the original sheafification unit therefore proves
this unit invertible. No topology is completed and no sections are discarded. -/
@[instance] theorem continuousModuleUnit_isIso : IsIso (continuousModuleUnit F V) := by
  sorry

/-- Identify the model's actual sections with all continuous functions.
Source: the item's all-continuous clause
(blueprint: lem-sfb-profinite-constant-derived-functions). -/
def modelSection (T : Profinite.{u}) :
    (continuousModule F V).X.obj.obj (op T) → ULift.{u + 1} C(T, V) :=
  (inv (continuousModuleUnit F V)).app (op T)

end ContinuousModels

section ScalarModels

variable (E F : Type u) [Field E] [NormedField F] [Algebra E F]
  (M : Type u) [AddCommGroup M] [Module E M]

/-- The actual scalar extension F tensor_E M, with a separate type name so that its
specified finite-dimensional product topology does not overwrite any tensor topology.
Source: the item's definition of M_F
(blueprint: lem-sfb-profinite-constant-derived-functions). -/
def ScalarModel := F ⊗[E] M

/-- The inherited additive group on scalar extension.
Source: the item's definition of M_F
(blueprint: lem-sfb-profinite-constant-derived-functions). -/
instance scalarModelAddCommGroup : AddCommGroup (ScalarModel E F M) :=
  inferInstanceAs (AddCommGroup (F ⊗[E] M))

/-- The inherited F-vector-space structure on scalar extension.
Source: the item's definition of M_F
(blueprint: lem-sfb-profinite-constant-derived-functions). -/
instance scalarModelModule : Module F (ScalarModel E F M) :=
  inferInstanceAs (Module F (F ⊗[E] M))

/-- The canonical vector-space topology, equal to the finite product norm topology
in every finite basis. It requires no completeness of F.
Source: the item's finite-dimensional product topology
(blueprint: lem-sfb-profinite-constant-derived-functions). -/
instance scalarModelTopology : TopologicalSpace (ScalarModel E F M) :=
  moduleTopology F (ScalarModel E F M)

/-- The declared topology is the module topology.
Source: the item's finite-dimensional product topology
(blueprint: lem-sfb-profinite-constant-derived-functions). -/
instance scalarModelIsModuleTopology : IsModuleTopology F (ScalarModel E F M) := ⟨rfl⟩

/-- Its additive operations are continuous.
Source: the item's finite-dimensional product topology
(blueprint: lem-sfb-profinite-constant-derived-functions). -/
instance scalarModelIsTopologicalAddGroup : IsTopologicalAddGroup (ScalarModel E F M) :=
  IsModuleTopology.topologicalAddGroup F (ScalarModel E F M)

/-- Its F-action is continuous.
Source: the item's finite-dimensional product topology
(blueprint: lem-sfb-profinite-constant-derived-functions). -/
instance scalarModelContinuousSMul : ContinuousSMul F (ScalarModel E F M) := inferInstance

/-- The supplied constant condensed model Q mapsto C(Q,F tensor_E M).
Source: the item's definition of M_F
(blueprint: lem-sfb-profinite-constant-derived-functions). -/
abbrev constantModel : PointModules (continuousRing F) :=
  continuousModule F (ScalarModel E F M)

/-- Its degree-zero object in the ordinary unbounded derived category.
Source: the item's M_F[0]
(blueprint: lem-sfb-profinite-constant-derived-functions). -/
abbrev constantModelD : DerivedCategory (PointModules (continuousRing F)) :=
  (DerivedCategory.singleFunctor (PointModules (continuousRing F)) 0).obj (constantModel E F M)

end ScalarModels

section ContinuousScalarMap

variable (E Ω : Type u) [NormedField E] [NormedField Ω] [NormedAlgebra E Ω]

/-- The recorded postcomposition morphism C_E to C_Omega, retaining every section.
Source: def-sfb-continuous-map-condensed-ring-map and the item's scalar clause
(blueprint: lem-sfb-profinite-constant-derived-functions). -/
def coefficientInclusion : (continuousRing E).X ⟶ (continuousRing Ω).X :=
  Profinite.continuousMapRingObjMapOfUniverse.{u, u} (algebraMap E Ω)
    (continuous_algebraMap E Ω)

/-- The inclusion is a morphism of the original coefficient ring objects.
Source: def-sfb-continuous-map-condensed-ring-map
(blueprint: lem-sfb-profinite-constant-derived-functions). -/
instance coefficientInclusion_isMonHom : IsMonHom (coefficientInclusion E Ω) :=
  Sheaf.isMonHom_sheafCompose_map (coherentTopology Profinite.{u})
    (Profinite.continuousMapRingSheafMapOfUniverse.{u, u} (algebraMap E Ω)
      (continuous_algebraMap E Ω))

variable (M : Type u) [AddCommGroup M] [Module E M]

/-- The specified map E tensor_E M to Omega tensor_E M, before taking functions.
Source: the item's x mapsto 1 tensor x clause
(blueprint: lem-sfb-profinite-constant-derived-functions). -/
def scalarModelInclusion (x : ScalarModel E E M) : ScalarModel E Ω M :=
  TensorProduct.map (Algebra.linearMap E Ω) (LinearMap.id : M →ₗ[E] M) x

/-- The canonical map of continuous models is uniquely determined on every section.
Source: the item's scalar clause and proof step 8
(blueprint: lem-sfb-profinite-constant-derived-functions).
Proof: in finite bases the displayed linear map has the scalar inclusion in each
coordinate, so it is continuous. Postcomposition therefore gives a natural additive
map of the continuous-function presheaves. Pointwise scalar multiplication proves its
E-linearity after scalar restriction. Sheafification gives the indicated map, and the
continuousModuleUnit isomorphisms give exactly this section formula. Those isomorphisms
and pointwise equality of continuous maps prove uniqueness. Under E tensor_E M = M,
the tensor formula is m mapsto 1 tensor m. -/
theorem scalarConstantMap_existsUnique [FiniteDimensional E M] :
    ∃! f : constantModel E E M ⟶
      (restrictPoint (continuousRing E) (continuousRing Ω) (coefficientInclusion E Ω)).obj
        (constantModel E Ω M),
      ∀ (T : Profinite.{u}) (x : (constantModel E E M).X.obj.obj (op T)) (q : T),
        (modelSection Ω (ScalarModel E Ω M) T ((f.hom.hom.app (op T)) x)).down q =
          scalarModelInclusion E Ω M
            ((modelSection E (ScalarModel E E M) T x).down q) := by
  sorry

/-- The specified scalar map, with the uniquely normalized all-continuous sections.
Source: the item's scalar clause (blueprint: lem-sfb-profinite-constant-derived-functions). -/
def scalarConstantMap [FiniteDimensional E M] : constantModel E E M ⟶
    (restrictPoint (continuousRing E) (continuousRing Ω) (coefficientInclusion E Ω)).obj
      (constantModel E Ω M) :=
  (scalarConstantMap_existsUnique E Ω M).choose

/-- Its degree-zero derived map with the exact scalar-restriction transport.
Source: the item's scalar clause (blueprint: lem-sfb-profinite-constant-derived-functions). -/
def scalarConstantMapD [FiniteDimensional E M] : constantModelD E E M ⟶
    (restrictPoint (continuousRing E) (continuousRing Ω) (coefficientInclusion E
      Ω)).mapDerivedCategory.obj (constantModelD E Ω M) :=
  (DerivedCategory.singleFunctor (PointModules (continuousRing E)) 0).map
    (scalarConstantMap E Ω M) ≫
    ((restrictPoint (continuousRing E) (continuousRing Ω) (coefficientInclusion E
      Ω)).mapDerivedCategorySingleFunctor 0).inv.app (constantModel E Ω M)

end ContinuousScalarMap




/-- The evaluation-adjoint comparison is invertible for the supplied continuous models.
The first alternative in hF is F = E, invariant under an E-algebra identification;
the second is the specified normed algebraic closure. No completeness of F is assumed.
Source: HRS Example 3.1 and Proposition 4.3(1), blueprint paragraph (3)
(blueprint: lem-sfb-profinite-constant-derived-functions).

Step 1. Write Lambda=C_F, A=Lambda[P], N=M_F[0] and B=p_X^*Lambda. Work interchangeably with
internal modules and their section-ring module sheaves: the exact equivalence preserves
underlying sheaves, tensor and its derived model, and takes the right-adjoint internal Hom to
K-injective derived sheaf Hom with the same evaluation. It likewise transports the entire
direct-image functor and its derived adjunction. On the condensed-point site the same exact
monoidal equivalence identifies internal and sectionwise modules; preservation of K-flat and
K-injective resolutions follows by transporting their defining Hom/tensor acyclicity tests. Thus
no change of coefficient category or completion is involved. Dependencies: def-weil-pbc-
internal-abelian-sheaf-module-equivalence, lem-pe-internal-section-tensor-comparison, lem-sfb-
module-object-ringed-site-derived-comparison, lem-sfb-internal-module-operations-transport.

Step 2. There is a canonical identification p_X^{-1}h_P=h_{X[P]}. Indeed, on a geometrically
w-contractible affine test V both sides are C(pi_0V,P), with the same restrictions; geometric
w-contractibility implies the site evaluation criterion needed by the two cited evaluation
statements. Such affines cover every affine test by the single-cover theorem; arbitrary tests
have affine open covers. Consequently the identifications determine an equality of sheaves.
Pullback also takes A to B[h_{X[P]}]: for any B-module T, the pullback adjunction and the free-
module adjunction identify maps from either object to T with maps h_Pto
p_{X*}(operatorname{Forget}T), since module direct image has that underlying sheaf. Yoneda gives
the isomorphism, normalized on generators. Similarly rho_P^*p_X^*N=p_{X[P]}^*N by composition of
the condensed-point pullbacks. Dependencies: lem-weil-pbc-condensed-point-basis-evaluation, lem-
weil-pbc-proetale-point-components-maps, lem-weil-pbc-source-affine-wcontractible-evaluation,
det-pe-hypercover-single-cover, lem-weil-pbc-profinite-point-pullback.

Step 3. The small pro-etale site of X[P] is the slice X_{mathrm{proet}}/X[P]; use only clause
(1) of the localization node. Put U=X[P] and take a K-injective resolution p_X^*Nto J. The free-
generator adjunction, applied on each slice over V, identifies mathcal Hom_B(B[h_U],J)(V) with
J(Vtimes_XU), degree by degree and with the same differential. By preservation of K-injectives
under localization, J|_U is K-injective and resolves p_{X[P]}^*N. Thus the identical complex
mathcal Hom_B(B[h_U],J)=rho_{P*}(J|_U) computes both Rmathcal Hom_B(p_X^*A,p_X^*N) and
R(rho_P)_*p_{X[P]}^*N. This is the canonical derived identification, natural in the object, the
parameter maps and further localization because its degreewise maps evaluate the same free
generator. Dependencies: lem-weil-proetale-weakly-etale-localization, lem-pur-kinjective-
restrict-localized, def-pur-derived-internal-hom.

Step 4. Pull back the evaluation Rmathcal Hom_Lambda(A,N)otimes_Lambda^{mathbf L}Ato N along
p_X, using its exact inverse image and canonical derived tensor comparison. Transposition
defines
beta_X:p_X^*Rmathcal Hom_Lambda(A,N)to Rmathcal Hom_B(p_X^*A,p_X^*N).
This defines a morphism before any assertion that it is invertible. Under restriction to a slice
it is the same evaluation-adjoint morphism: the cited slice evaluation/transposition identities
identify the two transposes. In particular its restriction to a test W is beta_W, using the
cartesian coefficient identification for p_W. Dependencies: lem-weil-pbc-profinite-point-
pullback, lem-weil-pbc-ringed-topoi-derived-tensor-pullback, lem-weil-pbc-ringed-slice-
evaluation-transpose.

Step 5. Let Wto X be a geometrically w-contractible affine test and put S=pi_0W. The component
morphism gives p_W^*=pi_W^*q_S^*. Restriction q_S^* from the profinite site to its slice over S
commutes with derived internal Hom for arbitrary unbounded complexes. The component theorem then
identifies
pi_W^*q_S^*Rmathcal Hom_Lambda(A,N) with Rmathcal Hom_{p_W^*Lambda}(p_W^*A,p_W^*N).
Both arrows are normalized by evaluation, so their composite is precisely the restriction of
beta_X constructed in step 4. Hence beta_X|_W is invertible. Every affine test has such a cover
by the single-cover theorem. The cone therefore has all cohomology sheaves zero locally and
hence globally; beta_X is invertible. Compose its inverse with step 3 to obtain delta_{X,P,M_F}
in the direction stated in the item. Dependencies: lem-zl-component-relative-profinite-site,
lem-weil-pbc-ringed-internal-hom-exact-restriction, lem-sfb-wcontractible-component-derived-hom,
det-pe-hypercover-single-cover.

Step 6. The slice identification evaluates a free generator, and beta_X is the transpose of
pulled-back evaluation. Thus the inverse composite has exactly the specified degree-zero
exponential-law normalization, sending a section on V[P] to its corresponding P-indexed
function. Uniqueness of transposes gives naturality in N and in maps h_{P'}to h_P, hence in M
and continuous maps P'to P. The same argument on a slice, with the slice evaluation identities,
gives pro-etale base change. If a base-changed scheme is not affine, this equality holds on its
affine open cover and glues. These are equalities of the derived morphisms, since they are
obtained by transposing identical evaluation morphisms. Dependencies: def-pur-derived-internal-
hom, lem-weil-pbc-ringed-slice-evaluation-transpose, lem-weil-pbc-profinite-point-pullback.

Step 7. Choose bases only to check the remaining linear-map clause. The supplied constant models
are B^r and B^s, since continuous functions into a finite product are products of continuous
functions. On every slice an arbitrary map between them is a matrix of sections of B; all
comparison maps above are B-linear and respect finite sums. They therefore commute with this
matrix, including matrices not pulled back from the condensed point. This description is
independent of the checking bases. Over X[Q], repeat the construction in that slice. A
continuous alpha:Qtimes P'to P induces a map of parameter objects over X[Q]. Transposing the two
proposed composites gives the same evaluation morphism there: for a local family f, it sends
(q,p') to u(q)(f(q,alpha(q,p'))). This notation describes evaluation on the entire parameter
object, not evaluation only at its points. The equality follows from the free-generator
adjunction and associativity of composition, so it holds over X[Q], including all higher derived
terms by the same transposition identity. Dependencies: lem-weil-pbc-ringed-slice-evaluation-
transpose, def-pur-derived-internal-hom.

Step 8. Finally apply the coefficient map C_Eto C_Omega and the module map
M_Etooperatorname{Res}M_Omega, xmapsto1otimes x. The free-generator coefficient-extension
identification sends the generator [a] to [a]. The canonical coefficient-comparison arrows for
internal Hom and direct image are mates of these evaluation/module maps. After scalar
restriction both composites in the requested square transpose to the identical map, evaluating a
function and then applying xmapsto1otimes x. Hence their mates agree. This argument uses the
derived extension/restriction adjunction (K-flat tensor for extension) and does not assert that
scalar extension is exact or that the scalar-comparison arrows themselves are isomorphisms. All
operations used the original sheaves C(Q,F) and C(Q,Fotimes_E M); no finite-subextension-valued
or completed model has entered. Dependencies: lem-weil-pbc-ringed-topoi-derived-tensor-pullback,
lem-weil-pbc-ringed-projection-mate-exact.
-/
theorem comparison_isIso (p l : ℕ) [Fact p.Prime] [Fact l.Prime] (hpl : p ≠ l)
    (k : Type u) [Field k] [CharP k p]
    (E : Type u) [NormedField E] [NormedAlgebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (F : Type u) [NormedField F] [NormedAlgebra E F]
    (hF : Nonempty (E ≃ₐ[E] F) ∨ IsAlgClosure E F)
    (X : Scheme.{u}) [IsAffine X] (s : X ⟶ Scheme.Spec.obj (op (CommRingCat.of k)))
    (P : Profinite.{u}) (M : Type u) [AddCommGroup M] [Module E M]
    [FiniteDimensional E M] :
    IsIso (comparisonApp (continuousRing F) X P (constantModelD E F M)) := by
  sorry

/-- The canonical isomorphism in the node's stated direction, obtained by inverting
its explicitly defined evaluation-adjoint comparison. This inverse has no choice of map.
Source: blueprint paragraph (3), the item's displayed isomorphism
(blueprint: lem-sfb-profinite-constant-derived-functions). -/
def delta (p l : ℕ) [Fact p.Prime] [Fact l.Prime] (hpl : p ≠ l)
    (k : Type u) [Field k] [CharP k p]
    (E : Type u) [NormedField E] [NormedAlgebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (F : Type u) [NormedField F] [NormedAlgebra E F]
    (hF : Nonempty (E ≃ₐ[E] F) ∨ IsAlgClosure E F)
    (X : Scheme.{u}) [IsAffine X] (s : X ⟶ Scheme.Spec.obj (op (CommRingCat.of k)))
    (P : Profinite.{u}) (M : Type u) [AddCommGroup M] [Module E M]
    [FiniteDimensional E M] :
    (CondensedRing.moduleObjectDerivedPushforward (continuousRing F).X (projection X P)).obj
      ((pointPullD (continuousRing F) (testScheme X P)).obj (constantModelD E F M)) ≅
    (pointPullD (continuousRing F) X).obj
      ((functions (continuousRing F) P).obj (constantModelD E F M)) :=
  letI := comparison_isIso p l hpl k E F hF X s P M
  (asIso (comparisonApp (continuousRing F) X P (constantModelD E F M))).symm

/-- The internal-Hom part of the comparison is invertible on the same supplied models.
Source: the item's proof steps 4--5
(blueprint: lem-sfb-profinite-constant-derived-functions).
Proof: comparison_factorization expresses comparison as this map followed by the
slice isomorphism and the point-composition isomorphism. comparison_isIso proves the
composite invertible. Cancel the two isomorphisms to obtain this assertion. -/
theorem pointHomComparison_constant_isIso (p l : ℕ) [Fact p.Prime] [Fact l.Prime] (hpl : p ≠ l)
    (k : Type u) [Field k] [CharP k p]
    (E : Type u) [NormedField E] [NormedAlgebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (F : Type u) [NormedField F] [NormedAlgebra E F]
    (hF : Nonempty (E ≃ₐ[E] F) ∨ IsAlgClosure E F)
    (X : Scheme.{u}) [IsAffine X] (s : X ⟶ Scheme.Spec.obj (op (CommRingCat.of k)))
    (P : Profinite.{u}) (M : Type u) [AddCommGroup M] [Module E M]
    [FiniteDimensional E M] :
    IsIso ((pointHomComparison (continuousRing F) X P).app (constantModelD E F M)) := by
  sorry

/-- The independently normalized point-to-scheme internal-Hom comparison on a supplied
model. It provides the canonical interpretation of arbitrary X-linear coefficient maps
on the right-hand side, without defining them by conjugation with delta.
Source: the item's linear naturality clause
(blueprint: lem-sfb-profinite-constant-derived-functions). -/
def pointHomIso (p l : ℕ) [Fact p.Prime] [Fact l.Prime] (hpl : p ≠ l)
    (k : Type u) [Field k] [CharP k p]
    (E : Type u) [NormedField E] [NormedAlgebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (F : Type u) [NormedField F] [NormedAlgebra E F]
    (hF : Nonempty (E ≃ₐ[E] F) ∨ IsAlgClosure E F)
    (X : Scheme.{u}) [IsAffine X] (s : X ⟶ Scheme.Spec.obj (op (CommRingCat.of k)))
    (P : Profinite.{u}) (M : Type u) [AddCommGroup M] [Module E M]
    [FiniteDimensional E M] :
    (pointPullD (continuousRing F) X).obj
      ((functions (continuousRing F) P).obj (constantModelD E F M)) ≅
    (schemeFunctions (continuousRing F) X P).obj
      ((pointPullD (continuousRing F) X).obj (constantModelD E F M)) :=
  letI := pointHomComparison_constant_isIso p l hpl k E F hF X s P M
  asIso ((pointHomComparison (continuousRing F) X P).app (constantModelD E F M))

/-- The inverse comparison is normalized by the universal evaluation, already in the
unbounded derived category. On degree zero this is precisely the exponential law.
Source: the item's normalization and proof step 6
(blueprint: lem-sfb-profinite-constant-derived-functions).
Proof: the inverse of delta is comparisonApp. Apply the inverse Hom bijection of the
derived projection adjunction to its definition. It cancels its forward Hom bijection,
leaving pointCompD followed by derivedEvaluation. In degree zero these evaluate the
free generator at the universal P-coordinate; transposing sends a section on V[P]
to its P-indexed function, with every continuous section retained. -/
theorem delta_normalization (p l : ℕ) [Fact p.Prime] [Fact l.Prime] (hpl : p ≠ l)
    (k : Type u) [Field k] [CharP k p]
    (E : Type u) [NormedField E] [NormedAlgebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (F : Type u) [NormedField F] [NormedAlgebra E F]
    (hF : Nonempty (E ≃ₐ[E] F) ∨ IsAlgClosure E F)
    (X : Scheme.{u}) [IsAffine X] (s : X ⟶ Scheme.Spec.obj (op (CommRingCat.of k)))
    (P : Profinite.{u}) (M : Type u) [AddCommGroup M] [Module E M]
    [FiniteDimensional E M] :
    ((projectionAdjunction (continuousRing F) X P).homEquiv _ _).symm
      (delta p l hpl k E F hF X s P M).inv =
    (pointCompD (continuousRing F) (projection X P)).hom.app
      ((functions (continuousRing F) P).obj (constantModelD E F M)) ≫
        (derivedEvaluation (continuousRing F) X P).app (constantModelD E F M) := by
  sorry

/-- Delta is the inverse point/internal-Hom comparison followed by the independent
slice identity. This identifies the linear and whole-family naturalities of sliceDelta
with those of the isomorphism displayed in the item.
Source: the item's proof steps 3--7
(blueprint: lem-sfb-profinite-constant-derived-functions).
Proof: invert comparison_factorization. Its three factors are isomorphisms by
comparison_isIso, derivedSliceComparison_isIso and pointHomComparison_constant_isIso.
The inverse of the point-composition factor gives the first displayed direct-image map;
the inverse of the slice factor is sliceDelta; the last inverse is pointHomIso.inv. -/
theorem delta_factorization (p l : ℕ) [Fact p.Prime] [Fact l.Prime] (hpl : p ≠ l)
    (k : Type u) [Field k] [CharP k p]
    (E : Type u) [NormedField E] [NormedAlgebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (F : Type u) [NormedField F] [NormedAlgebra E F]
    (hF : Nonempty (E ≃ₐ[E] F) ∨ IsAlgClosure E F)
    (X : Scheme.{u}) [IsAffine X] (s : X ⟶ Scheme.Spec.obj (op (CommRingCat.of k)))
    (P : Profinite.{u}) (M : Type u) [AddCommGroup M] [Module E M]
    [FiniteDimensional E M] :
    (delta p l hpl k E F hF X s P M).hom =
      (CondensedRing.moduleObjectDerivedPushforward (continuousRing F).X (projection X P)).map
        ((pointCompD (continuousRing F) (projection X P)).inv.app (constantModelD E F M)) ≫
      (sliceDelta (continuousRing F) X P).hom.app
        ((pointPullD (continuousRing F) X).obj (constantModelD E F M)) ≫
      (pointHomIso p l hpl k E F hF X s P M).inv := by
  sorry

/-- Whole-family equality explicitly specialized to the simultaneous map alpha on Q times P'.
All coefficient maps u live on X[Q], and the equality is a derived equality there.
Together with delta_factorization this is the item's whole-family naturality for the
supplied constant models, using the independently normalized internal-Hom interpretation.
Source: the item's proof step 7
(blueprint: lem-sfb-profinite-constant-derived-functions).
Proof: apply sliceDelta_family_naturality on X[Q] to familyParameterMap and its projection
identity. The displayed equality is on that entire slice. Evaluating on a generalized
free parameter gives u(q)(f(q,alpha(q,p'))), as a continuous family. No assertion that
points of Q detect derived morphisms is used. -/
theorem delta_wholeFamily (X : Scheme.{u}) (Q P P' : Profinite.{u}) (α : Q ⨯ P' ⟶ P)
    (N N' : DerivedCategory (Modules R (testScheme X Q))) (u : N ⟶ N') :
    (sliceDelta R (testScheme X Q) P).hom.app N ≫
      (schemeParameterMap R (testScheme X Q) P P' (familyParameterMap X Q P P' α)
        (familyParameterMap_over X Q P P' α)).app N ≫
      (schemeFunctions R (testScheme X Q) P').map u =
    pushParameterApp R (testScheme X Q) P P' (familyParameterMap X Q P P' α)
      (familyParameterMap_over X Q P P' α) N ≫
      (CondensedRing.moduleObjectDerivedPushforward R.X (projection (testScheme X Q) P')).map
        ((CondensedRing.upperStar R.X (projection (testScheme X Q) P')).mapDerivedCategory.map u) ≫
      (sliceDelta R (testScheme X Q) P').hom.app N' := by
  sorry

/-- The specified scalar map also commutes with the normalized comparison. Combined
with comparison_scalarRestriction (at coefficientInclusion and constantModelD E Omega M),
this is precisely the comparison after scalar restriction with M_E to M_Omega.
Source: the item's proof step 8
(blueprint: lem-sfb-profinite-constant-derived-functions).
Proof: comparison is a natural transformation on the full unbounded derived category.
Apply its naturality to scalarConstantMapD. Its section formula is the specified
x mapsto 1 tensor x by scalarConstantMap_existsUnique. The coefficient square is
comparison_scalarRestriction, whose maps were constructed independently using evaluation
and the right-derived units. Consequently the two squares paste to the required scalar
compatibility; no exactness of coefficient extension is asserted. -/
theorem comparison_scalarModel (E Ω : Type u) [NormedField E] [NormedField Ω]
    [NormedAlgebra E Ω] (M : Type u) [AddCommGroup M] [Module E M] [FiniteDimensional E M]
    (X : Scheme.{u}) (P : Profinite.{u}) :
    (pointPullD (continuousRing E) X).map
      ((functions (continuousRing E) P).map (scalarConstantMapD E Ω M)) ≫
      comparisonApp (continuousRing E) X P
        ((restrictPoint (continuousRing E) (continuousRing Ω) (coefficientInclusion E
          Ω)).mapDerivedCategory.obj (constantModelD E Ω M)) =
    comparisonApp (continuousRing E) X P (constantModelD E E M) ≫
      (CondensedRing.moduleObjectDerivedPushforward (continuousRing E).X (projection X P)).map
        ((pointPullD (continuousRing E) (testScheme X P)).map (scalarConstantMapD E Ω M)) := by
  sorry

end AlgebraicGeometry.ProEtale.ProfiniteFunctions
