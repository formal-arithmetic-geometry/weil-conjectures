/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.DerivedNakayamaResolution
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
public import Mathlib.RingTheory.Ideal.Quotient.Index
public import WeilConjectures.AlgebraicGeometry.ContinuousCoefficientCommRing
public import WeilConjectures.AlgebraicGeometry.ContinuousCoefficientUniverse
public import Mathlib.Topology.Category.Profinite.EffectiveEpi
public import WeilConjectures.CategoryTheory.RingObjects.ContinuousMap
public import Mathlib.Condensed.TopComparison
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Tensor
public import Mathlib.Topology.Algebra.Ring.Ideal
public import Mathlib.Algebra.Homology.DerivedCategory.ShortExact
public import WeilConjectures.CategoryTheory.Right.RightDerivedFunctorOfQuasiIsoResolutions
public import WeilConjectures.SixFunctors.ProEtale.Adic.PadicIntSheafLinear
public import WeilConjectures.CategoryTheory.Sites.MonObj
public import Mathlib.Algebra.Homology.ShortComplex.Ab
public import WeilConjectures.NumberTheory.Padics.IntegersCosetBasis
public import Mathlib.Topology.Bases
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Topology.LocallyConstant.Basic
public import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.TensorMappingCone
public import WeilConjectures.CategoryTheory.Monoidal.Closed.UnitEnd
public import Mathlib.CategoryTheory.Center.Linear
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Shapes.Kernels
public import WeilConjectures.NumberTheory.Padics.ContinuousUniformizerDivision
public import Mathlib.Topology.Algebra.Order.Field
public import WeilConjectures.Mathlib.CategoryTheory.Functor.Flat
public import Mathlib.CategoryTheory.Abelian.DiagramLemmas.KernelCokernelComp
public import Mathlib.CategoryTheory.Sites.Sheafification
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Sheaf
public import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Shift
public import WeilConjectures.NumberTheory.Padics.ExtensionIntegersDvr
public import Mathlib.Algebra.Order.AbsoluteValue.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import Mathlib.NumberTheory.Padics.PadicNumbers
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.Localization.FractionRing
public import WeilConjectures.NumberTheory.Padics.ExtensionIntegersDvrCore
public import Mathlib.Analysis.Normed.Algebra.Ultra
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.NumberTheory.Padics.ProperSpace
public import Mathlib.Topology.Algebra.Valued.LocallyCompact
public import WeilConjectures.NumberTheory.Padics.ExtensionIntegersDvrFactorization
public import WeilConjectures.NumberTheory.Padics.ExtensionIntegersDvrFactorizationUnique
public import WeilConjectures.Mathlib.RingTheory.OrderOfVanishing.Noetherian
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
public import WeilConjectures.CategoryTheory.SixFunctors.ModuleObjects
public import WeilConjectures.AlgebraicGeometry.Coefficient.CoefficientHeartCommonStratification
public import WeilConjectures.AlgebraicGeometry.IsConstructibleEtaleModuleSheaf
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleSiteComparisonSupplement
public import WeilConjectures.AlgebraicGeometry.ProEtaleInverseImage
public import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous
public import Mathlib.CategoryTheory.Sites.Equivalence
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.Defs
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Category.ModuleCat.AB
public import Mathlib.Algebra.Category.ModuleCat.Sheaf
public import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import WeilConjectures.CategoryTheory.Adjunction.LiftsGroupRingObjects
public import Mathlib.CategoryTheory.Monoidal.CommGrp_
public import Mathlib.CategoryTheory.Monoidal.Ring
public import Mathlib.CategoryTheory.Adjunction.Limits
public import WeilConjectures.CategoryTheory.Adjunction.LiftedCommRingBranch
public import WeilConjectures.CategoryTheory.Sites.WeaklyContractible
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LowerShriek
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.Topology.KrullDimension

public import WeilConjectures.AlgebraicGeometry.BaseChangeConventions
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Hom
import all WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.LocallyClosedGeneratorTensorIntersection
import all WeilConjectures.AlgebraicGeometry.DerivedNakayamaResolution
import all WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
import all WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
import all Mathlib.RingTheory.Ideal.Quotient.Index
import all WeilConjectures.AlgebraicGeometry.ContinuousCoefficientCommRing
import all WeilConjectures.AlgebraicGeometry.ContinuousCoefficientUniverse
import all Mathlib.Topology.Category.Profinite.EffectiveEpi
import all WeilConjectures.CategoryTheory.RingObjects.ContinuousMap
import all Mathlib.Condensed.TopComparison
import all WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Tensor
import all Mathlib.Topology.Algebra.Ring.Ideal
import all Mathlib.Algebra.Homology.DerivedCategory.ShortExact
import all WeilConjectures.CategoryTheory.Right.RightDerivedFunctorOfQuasiIsoResolutions
import all WeilConjectures.SixFunctors.ProEtale.Adic.PadicIntSheafLinear
import all WeilConjectures.CategoryTheory.Sites.MonObj
import all Mathlib.Algebra.Homology.ShortComplex.Ab
import all WeilConjectures.NumberTheory.Padics.IntegersCosetBasis
import all Mathlib.Topology.Bases
import all Mathlib.Topology.MetricSpace.Pseudo.Defs
import all Mathlib.Analysis.SpecificLimits.Basic
import all Mathlib.Topology.LocallyConstant.Basic
import all WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.TensorMappingCone
import all WeilConjectures.CategoryTheory.Monoidal.Closed.UnitEnd
import all Mathlib.CategoryTheory.Center.Linear
import all Mathlib.CategoryTheory.Limits.FunctorCategory.Shapes.Kernels
import all WeilConjectures.NumberTheory.Padics.ContinuousUniformizerDivision
import all Mathlib.Topology.Algebra.Order.Field
import all WeilConjectures.Mathlib.CategoryTheory.Functor.Flat
import all Mathlib.CategoryTheory.Abelian.DiagramLemmas.KernelCokernelComp
import all Mathlib.CategoryTheory.Sites.Sheafification
import all WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
import all WeilConjectures.CategoryTheory.GrothendieckAbelian.Sheaf
import all WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Shift
import all WeilConjectures.NumberTheory.Padics.ExtensionIntegersDvr
import all Mathlib.Algebra.Order.AbsoluteValue.Basic
import all Mathlib.LinearAlgebra.FiniteDimensional.Basic
import all Mathlib.NumberTheory.Padics.PadicNumbers
import all Mathlib.RingTheory.DiscreteValuationRing.Basic
import all Mathlib.RingTheory.Localization.FractionRing
import all WeilConjectures.NumberTheory.Padics.ExtensionIntegersDvrCore
import all Mathlib.Analysis.Normed.Algebra.Ultra
import all Mathlib.Analysis.Normed.Module.FiniteDimension
import all Mathlib.NumberTheory.Padics.ProperSpace
import all Mathlib.Topology.Algebra.Valued.LocallyCompact
import all WeilConjectures.NumberTheory.Padics.ExtensionIntegersDvrFactorization
import all WeilConjectures.NumberTheory.Padics.ExtensionIntegersDvrFactorizationUnique
import all WeilConjectures.Mathlib.RingTheory.OrderOfVanishing.Noetherian
import all WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
import all WeilConjectures.CategoryTheory.ProEtaleCoefficients.RegularScalarExtensionMultiplication
import all WeilConjectures.AlgebraicGeometry.Coefficient.CoefficientHeartLisseExtensionConstructible
import all WeilConjectures.AlgebraicGeometry.FiniteDiscreteOrdinary.FiniteDiscreteEncodingConstructibility
import all WeilConjectures.AlgebraicGeometry.FiniteDiscreteOrdinary.FiniteDiscreteEncodingPullbackFixed
import WeilConjectures.CategoryTheory.ModuleObjects.ProperBaseChange.IntegralReductionTensor
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients
import WeilConjectures.AlgebraicGeometry.ConstructibleEtaleModuleSheafComparison
import WeilConjectures.SixFunctors.ProEtale.ConstructibleSheaf
import WeilConjectures.AlgebraicGeometry.Proper.ProperTorsionDirectImageBound
import WeilConjectures.AlgebraicGeometry.ProEtaleAbelianEvaluationColimits
import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
import Mathlib.AlgebraicGeometry.Sites.Proetale
import Mathlib.CategoryTheory.Sites.ConstantSheaf
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleWeaklyContractibleEvaluationColimitsSupplement
import Mathlib.Algebra.Category.Grp.Abelian
import Mathlib.CategoryTheory.Sites.Limits
import Mathlib.CategoryTheory.Sites.Abelian
import Mathlib.CategoryTheory.Sites.PreservesSheafification
import Mathlib.CategoryTheory.Sites.EpiMono
import Mathlib.CategoryTheory.Sites.LocallySurjective
import Mathlib.Algebra.Category.Grp.EpiMono
import Mathlib.Algebra.Category.Grp.AB
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Injective
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.GlobalSections
import WeilConjectures.SixFunctors.ProEtale.Comparison
import WeilConjectures.SixFunctors.ProEtale.Comparison.ForgetUpperStar
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusExact
import WeilConjectures.AlgebraicGeometry.TorsionSheafCharacterizations
import WeilConjectures.AlgebraicGeometry.FieldBaseChangeDimension
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import WeilConjectures.ProEtaleCoefficients.DerivedNakayamaResolution

/-!
# Torsion reductions of locally closed integral lattices

Source: blueprint main-20261015, sec-six-functors-basics/sk-lem-proper-heart-bound,
`sk-lem-proper-heart-bound-torsion.md` (blueprint: det-proper-heart-bound-torsion).
The ordinary relative tensor with the actual quotient module is the canonical quotient
by the uniformizer power. The scalar equations in the origin predicate retain its module
structure when comparing with fixed finite-coefficient sheaves.
-/

@[expose] public noncomputable section

set_option linter.unusedVariables false
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory MonObj Opposite
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

variable (ℓ : ℕ) [Fact ℓ.Prime] (E : Type u) [Field E]
  [Algebra (Padic ℓ) E] [FiniteDimensional (Padic ℓ) E]

/-- Multiplication by an actual integral scalar on the continuous condensed integer sheaf.
Source: blueprint torsion reduction, coefficient convention
(blueprint: det-proper-heart-bound-torsion). -/
def torsionIntegerMultiply (b : Padic.coefficientExtensionIntegers ℓ E) :
    End (DerivedNakayama.integerRing ℓ E) :=
  letI := (Padic.coefficientExtensionAbsoluteValue ℓ E).toNormedField
  ⟨{
    app := fun S ↦ AddCommGrpCat.ofHom
      (AddMonoidHom.mulLeft (ULift.up (ContinuousMap.const S.unop b)))
    naturality := fun _ _ _ ↦ rfl }⟩

/-- The underlying additive scalar endomorphism, using the pulled-back scalar and the
specified internal module action. Source: blueprint torsion reduction, coefficient convention
(blueprint: det-proper-heart-bound-torsion). -/
def torsionScalar {X : Scheme.{u}}
    (M : pulledBackModuleObjects (DerivedNakayama.integerRing ℓ E) X)
    (b : Padic.coefficientExtensionIntegers ℓ E) : End M.X :=
  (λ_ M.X).inv ≫
    ((η[condensedRingObj (DerivedNakayama.integerRing ℓ E) X] ≫
      (upperStarFromPoint X).map (torsionIntegerMultiply ℓ E b)) ▷ M.X) ≫ Mod.act M.X

/-- The actual locally closed extension, with the chosen open--closed factorization.
Source: blueprint torsion statement, a_! = i_* u_!
(blueprint: det-proper-heart-bound-torsion). -/
abbrev torsionLocallyClosedExtension {S Sbar X : Scheme.{u}}
    (j : S ⟶ Sbar) [IsOpenImmersion j] (i : Sbar ⟶ X) :=
  CondensedRing.openImmersionLowerShriek (DerivedNakayama.integerRing ℓ E) j ⋙
    CondensedRing.lowerStar (DerivedNakayama.integerRing ℓ E) i

/-- The canonical quotient L / pi^n L, as ordinary relative tensor with O_E / pi^n.
Source: blueprint torsion statement, Q_n in the reduction paragraph
(blueprint: det-proper-heart-bound-torsion). -/
abbrev torsionQuotient (S : Scheme.{u}) (n : ℕ) :=
  (tensoringRight (Mod (Sheaf (Scheme.ProEt.topology S) Ab.{u + 1})
    (condensedRingObj (DerivedNakayama.integerRing ℓ E) S))).obj
    ((DerivedNakayama.pullback ℓ E S).obj (DerivedNakayama.quotientModule ℓ E n))

/-- Scalar multiplication on a fixed-coefficient module sheaf, with the given scalar action.
Source: blueprint torsion statement, finite discrete coefficients
(blueprint: det-proper-heart-bound-torsion). -/
def torsionFixedScalar {C : Type (u + 1)} [Category.{u} C]
    {J : GrothendieckTopology C} {B : Type (u + 1)} [CommRing B]
    (G : Sheaf J (ModuleCat.{u + 1} B)) (b : B) : End G :=
  ⟨{
    app := fun U ↦ ModuleCat.ofHom (b • LinearMap.id)
    naturality := fun _ _ f ↦ by
      ext m
      exact ((G.obj.map f).hom.map_smul b m).symm }⟩

/-- A finite-coefficient presentation, linear for every integral scalar, and its constructible
etale origin. The quotient action is locally generated by constant scalars, so the displayed
scalar equation says precisely that the comparison is a module isomorphism, including for
nonconstant local sections of the finite constant ring.
Source: blueprint torsion statement, classical constructibility
(blueprint: det-proper-heart-bound-torsion). -/
def TorsionClassicalOrigin (X : Scheme.{u}) (n : ℕ) (hn : 1 ≤ n)
    (N : pulledBackModuleObjects (DerivedNakayama.integerRing ℓ E) X) : Prop :=
  letI : Finite (Padic.coefficientExtensionRing ℓ E n) :=
    Padic.finite_coefficientExtensionRing ℓ E n hn
  ∃ G : Sheaf (Scheme.ProEt.topology X)
      (ModuleCat.{u + 1} (ULift.{u + 1, u} (Padic.coefficientExtensionRing ℓ E n))),
    ∃ e : (sheafCompose (Scheme.ProEt.topology X)
      (forget₂ (ModuleCat.{u + 1}
        (ULift.{u + 1, u} (Padic.coefficientExtensionRing ℓ E n))) Ab.{u + 1})).obj G ≅ N.X,
      (∀ b : Padic.coefficientExtensionIntegers ℓ E,
        e.hom ≫ torsionScalar ℓ E N b =
          (sheafCompose (Scheme.ProEt.topology X)
            (forget₂ (ModuleCat.{u + 1}
              (ULift.{u + 1, u} (Padic.coefficientExtensionRing ℓ E n))) Ab.{u + 1})).map
                (torsionFixedScalar G
                  (ULift.up (Ideal.Quotient.mk (Padic.coefficientExtensionIdeal ℓ E n) b))) ≫
            e.hom) ∧
      ∃ F : Sheaf X.smallEtaleTopology
          (ModuleCat.{u + 1} (ULift.{u + 1, u} (Padic.coefficientExtensionRing ℓ E n))),
        Scheme.IsConstructibleEtaleModuleSheaf F ∧
          Nonempty ((comparisonUpperStar
            (ModuleCat.{u + 1} (ULift.{u + 1, u} (Padic.coefficientExtensionRing ℓ E n)))
              X).obj F ≅ G)

section Reduction

open CondensedRing

attribute [local irreducible] DerivedCategory.monoidalClosed Mod.monoidalClosed
  upperStarFromPoint CondensedRing.upperStar CondensedRing.upperStarComp
  Mod.monoidalCategoryStruct ObjectProperty.flat

private def pointPullbackIso {S X : Scheme.{u}} (a : S ⟶ X)
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (P : Mod (Sheaf (coherentTopology Profinite.{u})
      Ab.{u + 1}) Λ) :
    (CondensedRing.upperStar Λ a).obj (((upperStarFromPoint X).mapMod Λ).obj P) ≅
      ((upperStarFromPoint S).mapMod Λ).obj P := by
  unfold CondensedRing.upperStar
  let φ := condensedPullbackHom Λ a
  let N := ((upperStarFromPoint S).mapMod Λ).obj P
  let e := (Functor.mapModCompIso (upperStarFromPoint X)
    (upperStar Ab.{u + 1} a) (upperStarFromPointComp a).hom Λ).app P
  exact (Mod.extendScalars φ).mapIso e ≪≫
    (Mod.extendScalarsIsoComapInv φ).app ((Mod.comap φ).obj N) ≪≫
    (Mod.comapEquivalenceOfIsIso φ).unitIso.symm.app N

attribute [local irreducible] generatorExtension generatorRestriction
  tensorRestrictionIso pointPullbackIso
attribute [local instance] generatorRestriction_isIso

private theorem projection_exists
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {S X : Scheme.{u}}
    [IsLocallyNoetherian X] [CompactSpace X]
    {a : S ⟶ X} [IsImmersion a] (A : GeneratorFactorization a)
    (B : Mod (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) Λ)
    (L : pulledBackModuleObjects Λ S) :
    ∃ e : ((generatorExtension Λ A).obj L ⊗ ((upperStarFromPoint X).mapMod Λ).obj B) ≅
      (generatorExtension Λ A).obj (L ⊗ ((upperStarFromPoint S).mapMod Λ).obj B),
      (CondensedRing.upperStar Λ a).map e.hom ≫ (generatorRestriction Λ A).app _ =
      (tensorRestrictionIso (CondensedRing.upperStar Λ a)
        ((asIso (generatorRestriction Λ A)).app L) (pointPullbackIso a Λ B)).hom := by
  have hs : universallySupported Λ a
      ((generatorExtension Λ A).obj L ⊗ ((upperStarFromPoint X).mapMod Λ).obj B) :=
    supported_tensor_left Λ a _ _ (fun g hg ↦ generatorExtension_support Λ A g hg L)
  exact normalized_comparison_of_essImage (generatorExtension Λ A)
    (CondensedRing.upperStar Λ a) (generatorExtension_fullyFaithful Λ A)
    (asIso (generatorRestriction Λ A)) _ _
    ⟨_, generatorExtension_reconstruct Λ A _ hs⟩
    (tensorRestrictionIso (CondensedRing.upperStar Λ a)
      ((asIso (generatorRestriction Λ A)).app L) (pointPullbackIso a Λ B))

section Projection

private def projectionIso
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ] {S X : Scheme.{u}}
  [IsLocallyNoetherian X] [CompactSpace X]
  {a : S ⟶ X} [IsImmersion a] (A : GeneratorFactorization a)
  (B : Mod (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) Λ)
    (L : pulledBackModuleObjects Λ S) :=
  Classical.choose (projection_exists Λ (a := a) A B L)

private theorem projectionIso_normalized
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ] {S X : Scheme.{u}}
  [IsLocallyNoetherian X] [CompactSpace X]
  {a : S ⟶ X} [IsImmersion a] (A : GeneratorFactorization a)
  (B : Mod (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) Λ)
    (L : pulledBackModuleObjects Λ S) :
    (CondensedRing.upperStar Λ a).map (projectionIso Λ A B L).hom ≫
        (generatorRestriction Λ A).app _ =
      (tensorRestrictionIso (CondensedRing.upperStar Λ a)
        ((asIso (generatorRestriction Λ A)).app L) (pointPullbackIso a Λ B)).hom :=
  Classical.choose_spec (projection_exists Λ (a := a) A B L)

private theorem projectionIso_natural
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ] {S X : Scheme.{u}}
  [IsLocallyNoetherian X] [CompactSpace X]
  {a : S ⟶ X} [IsImmersion a] (A : GeneratorFactorization a)
  (B : Mod (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) Λ)
    {L L' : pulledBackModuleObjects Λ S}
    (f : L ⟶ L') :
    ((generatorExtension Λ A).map f ⊗ₘ 𝟙 (((upperStarFromPoint X).mapMod Λ).obj B)) ≫
        (projectionIso Λ A B L').hom =
      (projectionIso Λ A B L).hom ≫ (generatorExtension Λ A).map
        (f ⊗ₘ 𝟙 (((upperStarFromPoint S).mapMod Λ).obj B)) := by
  let R := CondensedRing.upperStar Λ a
  let F := generatorExtension Λ A
  apply restrict_hom_injective_of_iso F R (generatorExtension_fullyFaithful Λ A)
    (asIso (generatorRestriction Λ A)) (projectionIso Λ A B L) (Iso.refl _)
  apply (cancel_mono ((generatorRestriction Λ A).app _)).1
  have hn := (generatorRestriction Λ A).naturality
    (f ⊗ₘ 𝟙 (((upperStarFromPoint S).mapMod Λ).obj B))
  dsimp only [Functor.comp_map, Functor.id_map] at hn
  simp only [R, Functor.map_comp, Category.assoc]
  have ht := tensorRestrictionIso_natural R
    ((asIso (generatorRestriction Λ A)).app L) (pointPullbackIso a Λ B)
    ((asIso (generatorRestriction Λ A)).app L') (pointPullbackIso a Λ B)
    ((generatorExtension Λ A).map f) (𝟙 _)
    f (𝟙 _) ((generatorRestriction Λ A).naturality f)
    (by rw [R.map_id, Category.id_comp, Category.comp_id])
  have h1 := congrArg (fun t ↦ R.map
    ((generatorExtension Λ A).map f ⊗ₘ
      𝟙 (((upperStarFromPoint X).mapMod Λ).obj B)) ≫ t)
    (projectionIso_normalized Λ A B L')
  have h2 := congrArg (fun t ↦ R.map (projectionIso Λ A B L).hom ≫ t) hn
  let fs := ((tensoringRight
    (Mod (Sheaf (Scheme.ProEt.topology S) Ab.{u + 1}) (condensedRingObj Λ S))).obj
      (((upperStarFromPoint S).mapMod Λ).obj B)).map f
  have h3 := congrArg (fun t ↦ t ≫ fs) (projectionIso_normalized Λ A B L)
  dsimp only [fs, Functor.flip_obj_map, curriedTensor_map_app] at h3
  simp only [Category.assoc, tensorHom_id] at h1 h2 h3 ht
  simpa only [R, tensorHom_id] using h1.trans (ht.trans (h3.symm.trans h2.symm))

private def flatProjectionIso
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ] {S X : Scheme.{u}}
  [IsLocallyNoetherian X] [CompactSpace X]
  {a : S ⟶ X} [IsImmersion a] (A : GeneratorFactorization a)
  (B : Mod (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) Λ)
    (L : ObjectProperty.FullSubcategory (IsLisseCoefficientModule Λ (X := S))) :=
  singleTensorIsoComp
    (D := Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
    (hBraided := Mod.braidedCategory) (hClosed := Mod.monoidalClosed)
    (hFlatResolution := coefficientModule_flatResolution Λ X)
    ((generatorExtension Λ A).obj L.obj) (((upperStarFromPoint X).mapMod Λ).obj B) _
    (generatorExtension_flat Λ A L.obj L.property) (projectionIso Λ A B L.obj)

private theorem flatProjectionIso_natural
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ] {S X : Scheme.{u}}
  [IsLocallyNoetherian X] [CompactSpace X]
  {a : S ⟶ X} [IsImmersion a] (A : GeneratorFactorization a)
  (B : Mod (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) Λ)
    {L L' : ObjectProperty.FullSubcategory (IsLisseCoefficientModule Λ (X := S))}
    (f : L ⟶ L') :
    ((DerivedCategory.singleFunctor _ 0).map ((generatorExtension Λ A).map f.hom) ⊗ₘ
      𝟙 ((DerivedCategory.singleFunctor _ 0).obj
        (((upperStarFromPoint X).mapMod Λ).obj B))) ≫
        (flatProjectionIso Λ A B L').hom =
      (flatProjectionIso Λ A B L).hom ≫ (DerivedCategory.singleFunctor _ 0).map
        ((generatorExtension Λ A).map
          (f.hom ⊗ₘ 𝟙 (((upperStarFromPoint S).mapMod Λ).obj B))) := by
  have h := singleTensorIso_comp_natural
    (D := Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
    (hBraided := Mod.braidedCategory) (hClosed := Mod.monoidalClosed)
    (hFlatResolution := coefficientModule_flatResolution Λ X)
    (generatorExtension_flat Λ A L.obj L.property)
    (generatorExtension_flat Λ A L'.obj L'.property)
    ((generatorExtension Λ A).map f.hom) (𝟙 _)
    ((generatorExtension Λ A).map
      (f.hom ⊗ₘ 𝟙 (((upperStarFromPoint S).mapMod Λ).obj B)))
    (projectionIso Λ A B L.obj) (projectionIso Λ A B L'.obj)
    (projectionIso_natural Λ A B f.hom)
  rw [(DerivedCategory.singleFunctor _ 0).map_id] at h
  exact h

private def reductionProjectionIso
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {S X : Scheme.{u}}
    [IsLocallyNoetherian X] [CompactSpace X]
    {a : S ⟶ X} [IsImmersion a] (A : GeneratorFactorization a)
    (B : Mod (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) Λ) :
    ObjectProperty.ι (IsLisseCoefficientModule Λ (X := S)) ⋙ generatorExtension Λ A ⋙
        DerivedCategory.singleFunctor _ 0 ⋙ (CondensedRing.derivedTensor Λ X).flip.obj
          ((DerivedCategory.singleFunctor _ 0).obj (((upperStarFromPoint X).mapMod Λ).obj B)) ≅
      ObjectProperty.ι (IsLisseCoefficientModule Λ (X := S)) ⋙
        (tensoringRight _).obj (((upperStarFromPoint S).mapMod Λ).obj B) ⋙
          generatorExtension Λ A ⋙ DerivedCategory.singleFunctor _ 0 := by
  refine NatIso.ofComponents (flatProjectionIso Λ A B) ?_
  intro L L' f
  unfold CondensedRing.derivedTensor
  simpa only [Functor.comp_map, ObjectProperty.ι_map, Functor.flip_obj_map,
    curriedTensor_map_app, tensorHom_id] using
      flatProjectionIso_natural Λ A B f

private theorem scalarExtension_free
    {T : Scheme.{u}} {R B : Sheaf (Scheme.ProEt.topology T) Ab.{u + 1}}
    [MonObj R] [MonObj B] [IsCommMonObj R] [IsCommMonObj B]
    (φ : R ⟶ B) [IsMonHom φ] (M : Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1}) R)
    (hM : Mod.IsFree R M) : Mod.IsFree B ((Mod.extendScalars φ).obj M) := by
  obtain ⟨r, ⟨e⟩⟩ := hM
  exact ⟨r, ⟨(Mod.extendScalars φ).mapIso e ≪≫
    (Mod.extendScalars φ).mapBiproduct (fun _ : Fin r ↦ Mod.regular R) ≪≫
      biproduct.mapIso (fun _ ↦ CategoryTheory.regularIso (Scheme.ProEt.topology T) R B φ)⟩⟩

private theorem scalarExtension_lisse
    (Λ Λ' : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [MonObj Λ'] [IsCommMonObj Λ] [IsCommMonObj Λ']
    (c : Λ ⟶ Λ') [IsMonHom c] (T : Scheme.{u})
    (M : pulledBackModuleObjects Λ T) (hM : IsLisseCoefficientModule Λ M) :
    IsLisseCoefficientModule Λ' ((Mod.extendScalars (coefficientMap c T)).obj M) := by
  obtain ⟨C, hC⟩ := hM
  refine ⟨C, fun a ↦ ?_⟩
  obtain ⟨r, ⟨e⟩⟩ := scalarExtension_free (coefficientMap c (C.X a)) _ (hC a)
  exact ⟨r, ⟨((pullIso c (C.f a)).symm.app M) ≪≫ e⟩⟩

private def ordinaryQuotientRestrictionIso
    (T : Scheme.{u}) (n : ℕ) (M : pulledBackModuleObjects (DerivedNakayama.integerRing ℓ E) T) :
    (Mod.comap (coefficientMap (DerivedNakayama.reductionRing ℓ E n) T)).obj
      ((Mod.extendScalars (coefficientMap (DerivedNakayama.reductionRing ℓ E n) T)).obj M) ≅
        (torsionQuotient ℓ E T n).obj M := by
  let c := DerivedNakayama.reductionRing ℓ E n
  let F := upperStarFromPoint T
  let e : (Mod.comap (coefficientMap c T)).obj
      (Mod.regular (condensedRingObj (DerivedNakayama.quotientRing ℓ E n) T)) ≅
        (DerivedNakayama.pullback ℓ E T).obj (DerivedNakayama.quotientModule ℓ E n) :=
    (Mod.comap (coefficientMap c T)).mapIso
      (mapRegularIso F (DerivedNakayama.quotientRing ℓ E n)).symm ≪≫
    (F.mapModComapIso c).symm.app _
  exact (Mod.extendComapTensorIso (coefficientMap c T)).app M ≪≫
    tensorIso e (Iso.refl M) ≪≫ β_ _ _

private theorem finiteExtension_stratified
    {S Sbar X : Scheme.{u}} [IsNoetherian X]
    (j : S ⟶ Sbar) [IsOpenImmersion j] (i : Sbar ⟶ X) [IsClosedImmersion i]
    (n : ℕ) (L : pulledBackModuleObjects (DerivedNakayama.integerRing ℓ E) S)
    (hL : IsLisseCoefficientModule (DerivedNakayama.integerRing ℓ E) L) :
    IsFiniteConstantStratified (DerivedNakayama.quotientRing ℓ E n) X
      ((CondensedRing.lowerStar (DerivedNakayama.quotientRing ℓ E n) i).obj
        ((CondensedRing.openImmersionLowerShriek (DerivedNakayama.quotientRing ℓ E n) j).obj
          ((Mod.extendScalars (coefficientMap (DerivedNakayama.reductionRing ℓ E n) S)).obj
            L))) := by
  have : TopologicalSpace.NoetherianSpace Sbar := i.isEmbedding.isInducing.noetherianSpace
  have : TopologicalSpace.NoetherianSpace S :=
    j.isEmbedding.isInducing.noetherianSpace
  apply stratified_closedPush
  apply stratified_openExtension
  apply stratified_of_finiteModel
  apply lisse_finiteModel
  exact scalarExtension_lisse _ _ (DerivedNakayama.reductionRing ℓ E n) S L hL

private def finiteExtensionRestrictionIso
    {S Sbar X : Scheme.{u}}
    (j : S ⟶ Sbar) [IsOpenImmersion j] (i : Sbar ⟶ X) (n : ℕ)
    (L : pulledBackModuleObjects (DerivedNakayama.integerRing ℓ E) S) :
    (Mod.comap (coefficientMap (DerivedNakayama.reductionRing ℓ E n) X)).obj
      ((CondensedRing.lowerStar (DerivedNakayama.quotientRing ℓ E n) i).obj
        ((CondensedRing.openImmersionLowerShriek (DerivedNakayama.quotientRing ℓ E n) j).obj
          ((Mod.extendScalars (coefficientMap (DerivedNakayama.reductionRing ℓ E n) S)).obj
            L))) ≅
      (torsionLocallyClosedExtension ℓ E j i).obj ((torsionQuotient ℓ E S n).obj L) :=
  (comapLowerStarIso (DerivedNakayama.reductionRing ℓ E n) i).app _ ≪≫
    (CondensedRing.lowerStar (DerivedNakayama.integerRing ℓ E) i).mapIso
      ((comapOpenImmersionLowerShriekIso (DerivedNakayama.reductionRing ℓ E n) j).app _ ≪≫
        (CondensedRing.openImmersionLowerShriek (DerivedNakayama.integerRing ℓ E) j).mapIso
          (ordinaryQuotientRestrictionIso ℓ E S n L))

private theorem ordinaryStratified_constructible
    (A : Type u) [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
    (T : Scheme.{u})
    (G : Sheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} (ULift.{u + 1} A)))
    (hG : FiniteDiscreteOrdinary.ordinaryStratified A T G) :
    ProEtale.IsConstructible (ULift.{u + 1} A) G := by
  obtain ⟨S, hS⟩ := hG
  refine ⟨S, fun a ↦ ?_⟩
  obtain ⟨C, hC⟩ := hS a
  refine ⟨ULift.{u + 1} C.I₀, fun b ↦ C.X b.down, fun b ↦ C.f b.down, ?_, ?_⟩
  · have he : Presieve.ofArrows (fun b : ULift.{u + 1} C.I₀ ↦ C.X b.down)
        (fun b ↦ C.f b.down) = C.presieve₀ := by
      refine le_antisymm (fun _ _ ⟨b⟩ ↦ ⟨b.down⟩) fun _ _ ⟨b⟩ ↦ ?_
      exact @Presieve.ofArrows.mk _ _ _ (ULift.{u + 1} C.I₀)
        (fun b ↦ C.X b.down) (fun b ↦ C.f b.down) (ULift.up b)
    rw [he]
    exact C.mem₀
  · intro b
    exact hC b.down

attribute [local irreducible] projectionIso

end Projection

end Reduction

section Origin

open CondensedRing

private local instance (n : ℕ) : TopologicalSpace (Padic.coefficientExtensionRing ℓ E n) :=
  letI := (Padic.coefficientExtensionAbsoluteValue ℓ E).toNormedField
  inferInstance

private local instance (n : ℕ) : IsTopologicalRing (Padic.coefficientExtensionRing ℓ E n) :=
  letI := (Padic.coefficientExtensionAbsoluteValue ℓ E).toNormedField
  inferInstance

private def scalarIntegerMap (A : Type u) [CommRing A] (b : A) :
    𝟙_ Ab.{u + 1} ⟶ AddCommGrpCat.of (ULift.{u + 1} A) :=
  AddCommGrpCat.ofHom
    { toFun z := z.down • (ULift.up b)
      map_zero' := by simp
      map_add' x y := by simp [add_mul] }

attribute [local irreducible] Mod.monoidalCategoryStruct Mod.monoidalClosed

private theorem point_scalar_constant (n : ℕ)
    (b : Padic.coefficientExtensionIntegers ℓ E) :
    η[DerivedNakayama.integerRing ℓ E] ≫ torsionIntegerMultiply ℓ E b ≫
      DerivedNakayama.reductionRing ℓ E n =
    Functor.LaxMonoidal.ε (constantSheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) ≫
      (constantSheaf (coherentTopology Profinite.{u}) Ab.{u + 1}).map
        (scalarIntegerMap (Padic.coefficientExtensionRing ℓ E n)
          (Ideal.Quotient.mk (Padic.coefficientExtensionIdeal ℓ E n) b)) ≫
      (((sheafificationAdjunction (coherentTopology Profinite.{u}) Ab.{u + 1}).homEquiv
        _ (DerivedNakayama.quotientRing ℓ E n)).symm
          (FiniteDiscreteOrdinary.pointConstants (Padic.coefficientExtensionRing ℓ E n))) := by
  let := (Padic.coefficientExtensionAbsoluteValue ℓ E).toNormedField
  let J := coherentTopology Profinite.{u}
  have hc : Functor.LaxMonoidal.ε (constantSheaf J Ab.{u + 1}) = 𝟙 _ := by
    change 𝟙 _ ≫ (presheafToSheaf J Ab.{u + 1}).map (𝟙 _) = 𝟙 _
    exact (Category.id_comp _).trans ((presheafToSheaf J Ab.{u + 1}).map_id _)
  let U := sheafToPresheaf J Ab.{u + 1}
  let g := scalarIntegerMap (Padic.coefficientExtensionRing ℓ E n)
    (Ideal.Quotient.mk (Padic.coefficientExtensionIdeal ℓ E n) b)
  apply ((sheafificationAdjunction J Ab.{u + 1}).homEquiv _ _).injective
  change Functor.LaxMonoidal.ε U ≫
      U.map (η[DerivedNakayama.integerRing ℓ E] ≫ torsionIntegerMultiply ℓ E b ≫
        DerivedNakayama.reductionRing ℓ E n) = _
  simp only [Functor.map_comp, ← Category.assoc]
  erw [Sheaf.ε_sheafToPresheaf_comp_map_one_sheafCompose]
  rw [hc, Category.id_comp]
  change _ = (sheafificationAdjunction J Ab.{u + 1}).homEquiv _ _
    ((presheafToSheaf J Ab.{u + 1}).map
      ((Functor.const Profinite.{u}ᵒᵖ).map g) ≫ _)
  rw [Adjunction.homEquiv_naturality_left, Equiv.apply_symm_apply]
  ext S z
  apply ULift.ext
  apply ContinuousMap.ext
  intro x
  dsimp only [U, g, scalarIntegerMap, torsionIntegerMultiply,
    DerivedNakayama.reductionRing, DerivedNakayama.reductionRingSheaf,
    FiniteDiscreteOrdinary.pointConstants]
  simp only [NatTrans.comp_app, AddCommGrpCat.comp_apply]
  rw [Functor.one_compForget₂_app]
  erw [AddCommGrpCat.ringMonObj_one_apply]
  with_unfolding_all
    change Ideal.Quotient.mk (Padic.coefficientExtensionIdeal ℓ E n)
      (b * (z.down : Padic.coefficientExtensionIntegers ℓ E)) =
    z.down • Ideal.Quotient.mk (Padic.coefficientExtensionIdeal ℓ E n) b
  simp [map_mul, mul_comm, zsmul_eq_mul]

attribute [local irreducible] upperStarFromPoint torsionIntegerMultiply

private theorem scalar_constant (T : Scheme.{u}) (n : ℕ)
    (b : Padic.coefficientExtensionIntegers ℓ E) :
    η[condensedRingObj (DerivedNakayama.integerRing ℓ E) T] ≫
      (upperStarFromPoint T).map (torsionIntegerMultiply ℓ E b) ≫
      coefficientMap (DerivedNakayama.reductionRing ℓ E n) T =
    Functor.LaxMonoidal.ε (constantSheaf (Scheme.ProEt.topology T) Ab.{u + 1}) ≫
      (constantSheaf (Scheme.ProEt.topology T) Ab.{u + 1}).map
        (scalarIntegerMap (Padic.coefficientExtensionRing ℓ E n)
          (Ideal.Quotient.mk (Padic.coefficientExtensionIdeal ℓ E n) b)) ≫
      FiniteDiscreteOrdinary.canonicalAbelianMap
        (Padic.coefficientExtensionRing ℓ E n) T := by
  let := (Padic.coefficientExtensionAbsoluteValue ℓ E).toNormedField
  let F := upperStarFromPoint T
  let P := constantSheaf (coherentTopology Profinite.{u}) Ab.{u + 1}
  let Q := constantSheaf (Scheme.ProEt.topology T) Ab.{u + 1}
  let g := scalarIntegerMap (Padic.coefficientExtensionRing ℓ E n)
    (Ideal.Quotient.mk (Padic.coefficientExtensionIdeal ℓ E n) b)
  let ψ := ((sheafificationAdjunction (coherentTopology Profinite.{u}) Ab.{u + 1}).homEquiv
    _ (DerivedNakayama.quotientRing ℓ E n)).symm
      (FiniteDiscreteOrdinary.pointConstants (Padic.coefficientExtensionRing ℓ E n))
  have hnat := (constantSchemeIso T).hom.naturality g
  change Q.map g ≫ (constantSchemeIso T).hom.app _ =
    (constantSchemeIso T).hom.app _ ≫ F.map (P.map g) at hnat
  have hu := NatTrans.IsMonoidal.unit (τ := (constantSchemeIso T).hom)
  change Functor.LaxMonoidal.ε Q ≫ (constantSchemeIso T).hom.app _ =
    Functor.LaxMonoidal.ε F ≫ F.map (Functor.LaxMonoidal.ε P) at hu
  change Functor.LaxMonoidal.ε F ≫ F.map η[DerivedNakayama.integerRing ℓ E] ≫
      F.map (torsionIntegerMultiply ℓ E b) ≫ F.map (DerivedNakayama.reductionRing ℓ E n) =
    Functor.LaxMonoidal.ε Q ≫ Q.map g ≫ (constantSchemeIso T).hom.app _ ≫ F.map ψ
  erw [reassoc_of% hnat, reassoc_of% hu]
  simp only [← F.map_comp]
  congr 1
  exact congrArg F.map (point_scalar_constant ℓ E n b)

private theorem constant_scalar_section (T : Scheme.{u}) (n : ℕ)
    (b : Padic.coefficientExtensionIntegers ℓ E) (V : T.ProEtᵒᵖ) :
    sfbRegularSection (Scheme.ProEt.topology T) _
      (η[condensedRingObj (DerivedNakayama.integerRing ℓ E) T] ≫
        (upperStarFromPoint T).map (torsionIntegerMultiply ℓ E b) ≫
        coefficientMap (DerivedNakayama.reductionRing ℓ E n) T) V =
      ((toSheafify (Scheme.ProEt.topology T)
        ((Functor.const T.ProEtᵒᵖ).obj
          (AddCommGrpCat.of (ULift.{u + 1} (Padic.coefficientExtensionRing ℓ E n)))) ≫
        (FiniteDiscreteOrdinary.canonicalAbelianMap
          (Padic.coefficientExtensionRing ℓ E n) T).hom).app V).hom
        (ULift.up (Ideal.Quotient.mk (Padic.coefficientExtensionIdeal ℓ E n) b)) := by
  rw [scalar_constant]
  unfold sfbRegularSection
  let J := Scheme.ProEt.topology T
  let A := Padic.coefficientExtensionRing ℓ E n
  let a := Ideal.Quotient.mk (Padic.coefficientExtensionIdeal ℓ E n) b
  let g := scalarIntegerMap A a
  have hc : Functor.LaxMonoidal.ε (constantSheaf J Ab.{u + 1}) = 𝟙 _ := by
    change 𝟙 _ ≫ (presheafToSheaf J Ab.{u + 1}).map (𝟙 _) = 𝟙 _
    exact (Category.id_comp _).trans ((presheafToSheaf J Ab.{u + 1}).map_id _)
  rw [hc, Category.id_comp]
  change (FiniteDiscreteOrdinary.canonicalAbelianMap A T).hom.app V
      (((constantSheaf J Ab.{u + 1}).map g).hom.app V
        ((toSheafify J ((Functor.const T.ProEtᵒᵖ).obj (𝟙_ Ab.{u + 1}))).app V
          (ULift.up (1 : ℤ)))) =
    (FiniteDiscreteOrdinary.canonicalAbelianMap A T).hom.app V
      ((toSheafify J ((Functor.const T.ProEtᵒᵖ).obj
        (AddCommGrpCat.of (ULift.{u + 1} A)))).app V (ULift.up a))
  apply congrArg ((FiniteDiscreteOrdinary.canonicalAbelianMap A T).hom.app V)
  have h := toSheafify_naturality J
    ((Functor.const T.ProEtᵒᵖ).map g)
  have he := congrArg (fun t ↦ (t.app V).hom (ULift.up (1 : ℤ))) h
  change ((constantSheaf J Ab.{u + 1}).map g).hom.app V
      ((toSheafify J ((Functor.const T.ProEtᵒᵖ).obj (𝟙_ Ab.{u + 1}))).app V
        (ULift.up (1 : ℤ))) =
    (toSheafify J ((Functor.const T.ProEtᵒᵖ).obj
      (AddCommGrpCat.of (ULift.{u + 1} A)))).app V (ULift.up a)
  change (toSheafify J ((Functor.const T.ProEtᵒᵖ).obj
      (AddCommGrpCat.of (ULift.{u + 1} A)))).app V (g.hom (ULift.up (1 : ℤ))) =
    ((constantSheaf J Ab.{u + 1}).map g).hom.app V
      ((toSheafify J ((Functor.const T.ProEtᵒᵖ).obj (𝟙_ Ab.{u + 1}))).app V
        (ULift.up (1 : ℤ))) at he
  have hg : g.hom (ULift.up (1 : ℤ)) = ULift.up a := by simp [g, scalarIntegerMap]
  rw [hg] at he
  exact he.symm

attribute [local irreducible] FiniteDiscreteOrdinary.canonicalAbelianMap

private theorem scalar_encoded (T : Scheme.{u}) (n : ℕ)
    (e : FiniteDiscreteOrdinary.Encoding (Padic.coefficientExtensionRing ℓ E n) T)
    (M : FiniteDiscreteOrdinary.Internal (Padic.coefficientExtensionRing ℓ E n) T)
    (b : Padic.coefficientExtensionIntegers ℓ E) :
    torsionScalar ℓ E
      ((Mod.comap (coefficientMap (DerivedNakayama.reductionRing ℓ E n) T)).obj M) b =
      (sheafCompose (Scheme.ProEt.topology T)
        (forget₂ (ModuleCat.{u + 1}
          (ULift.{u + 1} (Padic.coefficientExtensionRing ℓ E n))) Ab.{u + 1})).map
        (torsionFixedScalar ((FiniteDiscreteOrdinary.sectionEncoding _ T e.ringIso ⋙
          FiniteDiscreteOrdinary.fixedRestriction _ T).obj M)
          (ULift.up (Ideal.Quotient.mk (Padic.coefficientExtensionIdeal ℓ E n) b))) := by
  apply Sheaf.hom_ext
  apply NatTrans.ext
  funext V
  apply AddCommGrpCat.hom_ext
  apply AddMonoidHom.ext
  intro m
  change _ = (show M.X.obj.obj V from
    (ULift.up (Ideal.Quotient.mk (Padic.coefficientExtensionIdeal ℓ E n) b) :
      ULift.{u + 1} (Padic.coefficientExtensionRing ℓ E n)) •
    (show ((FiniteDiscreteOrdinary.sectionEncoding _ T e.ringIso ⋙
      FiniteDiscreteOrdinary.fixedRestriction _ T).obj M).obj.obj V from m))
  rw [FiniteDiscreteOrdinary.encoding_smul]
  change (((λ_ M.X).inv ≫
    ((η[condensedRingObj (DerivedNakayama.integerRing ℓ E) T] ≫
      (upperStarFromPoint T).map (torsionIntegerMultiply ℓ E b)) ▷ M.X) ≫
      (coefficientMap (DerivedNakayama.reductionRing ℓ E n) T ▷ M.X) ≫
      Mod.act M.X).hom.app V).hom m = _
  rw [← comp_whiskerRight_assoc]
  change (Mod.act M.X).hom.app V
    (((λ_ M.X).inv ≫ _ ▷ M.X).hom.app V m) = _
  rw [left_section]
  simp only [Category.assoc]
  erw [constant_scalar_section]
  rfl

private theorem torsionScalar_naturality {T : Scheme.{u}}
    {M N : pulledBackModuleObjects (DerivedNakayama.integerRing ℓ E) T}
    (f : M ⟶ N) (b : Padic.coefficientExtensionIntegers ℓ E) :
    f.hom ≫ torsionScalar ℓ E N b = torsionScalar ℓ E M b ≫ f.hom := by
  simp only [torsionScalar, Category.assoc]
  rw [leftUnitor_inv_naturality_assoc, whisker_exchange_assoc, ← Mod.act_hom]

private theorem origin_extension
    {S Sbar X : Scheme.{u}} [IsNoetherian X]
    (j : S ⟶ Sbar) [IsOpenImmersion j] (i : Sbar ⟶ X) [IsClosedImmersion i]
    (n : ℕ) (hn : 1 ≤ n)
    (L : pulledBackModuleObjects (DerivedNakayama.integerRing ℓ E) S)
    (hL : IsLisseCoefficientModule (DerivedNakayama.integerRing ℓ E) L) :
    TorsionClassicalOrigin ℓ E X n hn
      ((torsionLocallyClosedExtension ℓ E j i).obj ((torsionQuotient ℓ E S n).obj L)) := by
  let := (Padic.coefficientExtensionAbsoluteValue ℓ E).toNormedField
  let A := Padic.coefficientExtensionRing ℓ E n
  let : Finite A := Padic.finite_coefficientExtensionRing ℓ E n hn
  let : DiscreteTopology A := DerivedNakayama.quotientDiscrete ℓ E n
  let M : FiniteDiscreteOrdinary.Internal A X :=
    (CondensedRing.lowerStar (DerivedNakayama.quotientRing ℓ E n) i).obj
      ((CondensedRing.openImmersionLowerShriek (DerivedNakayama.quotientRing ℓ E n) j).obj
        ((Mod.extendScalars (coefficientMap (DerivedNakayama.reductionRing ℓ E n) S)).obj L))
  obtain ⟨enc⟩ := FiniteDiscreteOrdinary.encoding_exists A X
  let G := (FiniteDiscreteOrdinary.sectionEncoding A X enc.ringIso ⋙
    FiniteDiscreteOrdinary.fixedRestriction A X).obj M
  let e : (sheafCompose (Scheme.ProEt.topology X)
      (forget₂ (ModuleCat.{u + 1} (ULift.{u + 1} A)) Ab.{u + 1})).obj G ≅
      ((torsionLocallyClosedExtension ℓ E j i).obj
        ((torsionQuotient ℓ E S n).obj L)).X :=
    (Mod.forget _).mapIso (finiteExtensionRestrictionIso ℓ E j i n L)
  refine ⟨G, e, ?_, ?_⟩
  · intro b
    change (finiteExtensionRestrictionIso ℓ E j i n L).hom.hom ≫ _ = _
    exact (torsionScalar_naturality ℓ E
      (finiteExtensionRestrictionIso ℓ E j i n L).hom b).trans
        (congrArg (fun t ↦ t ≫ (finiteExtensionRestrictionIso ℓ E j i n L).hom.hom)
          (scalar_encoded ℓ E X n enc M b))
  · have hM := finiteExtension_stratified ℓ E j i n L hL
    have hG : FiniteDiscreteOrdinary.ordinaryStratified A X G := by
      simpa only [enc.ordinary_functor, enc.fixed_functor] using
        (FiniteDiscreteOrdinary.stratified_comparison A X enc M).1 hM
    obtain ⟨F, hF, eF⟩ := exists_isConstructibleSheaf_iso_comparisonUpperStar_obj
      (ULift.{u + 1} A) (ordinaryStratified_constructible A X G hG)
    exact ⟨F, (Scheme.isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf F).2 hF, eF⟩

private def localizationSectionsIso {T X : Scheme.{u}} (r : T ⟶ X) [WeaklyEtale r] :
    upperStar Ab.{u + 1} r ⋙ Sheaf.Γ (Scheme.ProEt.topology T) Ab.{u + 1} ≅
      (sheafSections (Scheme.ProEt.topology X) Ab.{u + 1}).obj
        (op (Scheme.ProEt.mk r)) := by
  refine Functor.isoWhiskerRight
    (upperStarIsoLocalizationRestriction Ab.{u + 1} r inferInstance) _ ≪≫
    Functor.isoWhiskerLeft _
      (Sheaf.ΓNatIsoSheafSections _ _ (Scheme.ProEt.isTerminalMkId T)) ≪≫ ?_
  let e : (MorphismProperty.Over.map ⊤ (inferInstance : WeaklyEtale r)).obj
      (Scheme.ProEt.mk (𝟙 T)) ≅ Scheme.ProEt.mk r :=
    MorphismProperty.Over.isoMk (Iso.refl _) (by exact Category.id_comp _)
  exact (NatIso.ofComponents (fun _ ↦ Iso.refl _) (by intros; rfl)) ≪≫
    (sheafSections (Scheme.ProEt.topology X) Ab.{u + 1}).mapIso e.symm.op

private def directImageSectionsIso {X Y : Scheme.{u}} (p : X ⟶ Y) (V : Y.ProEt) :
    lowerStar Ab.{u + 1} p ⋙
      (sheafSections (Scheme.ProEt.topology Y) Ab.{u + 1}).obj (op V) ≅
    (sheafSections (Scheme.ProEt.topology X) Ab.{u + 1}).obj
      (op (Scheme.ProEt.mk (pullback.fst p V.hom))) := by
  let e : (MorphismProperty.Over.pullback @WeaklyEtale ⊤ p).obj V ≅
      Scheme.ProEt.mk (pullback.fst p V.hom) :=
    MorphismProperty.Over.isoMk (pullbackSymmetry V.hom p) (by simp)
  exact (NatIso.ofComponents (fun _ ↦ Iso.refl _) (by intros; rfl)) ≪≫
    (sheafSections (Scheme.ProEt.topology X) Ab.{u + 1}).mapIso e.symm.op

private theorem proper_torsion_vanishing
    {X Y : Scheme.{u}} (p : X ⟶ Y) [IsProper p] (d : ℕ)
    (hd : ∀ y : Y, topologicalKrullDim (p.fiber y) ≤ (d : WithBot ℕ∞))
    (V : Y.ProEt) [IsAffine V.left]
    (hV : (Scheme.ProEt.topology Y).IsWeaklyContractible.{u + 1} V)
    (F : Sheaf X.smallEtaleTopology Ab.{u + 1})
    (hF : Scheme.IsTorsionAbelianSheaf F)
    (G : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
    (e : (comparisonUpperStar Ab.{u + 1} X).obj F ≅ G)
    (q : ℤ) (hq : 2 * (d : ℤ) < q) :
    IsZero ((DerivedCategory.homologyFunctor Ab.{u + 1} q).obj
      ((rightDerivedGlobalSections Ab.{u + 1} (pullback p V.hom)).obj
        ((DerivedCategory.singleFunctor _ 0).obj
          ((upperStar Ab.{u + 1} (pullback.fst p V.hom)).obj G)))) := by
  let r := pullback.fst p V.hom
  let U := upperStar Ab.{u + 1} r
  let Γ := Sheaf.Γ (Scheme.ProEt.topology (pullback p V.hom)) Ab.{u + 1}
  let ev := (sheafSections (Scheme.ProEt.topology Y) Ab.{u + 1}).obj (op V)
  let P := lowerStar Ab.{u + 1} p
  have : ev.Additive := ⟨by intros; rfl⟩
  have : Γ.Additive := inferInstance
  let ν := comparisonUpperStar Ab.{u + 1} Y
  have hWC : ∀ (F G : Sheaf (Scheme.ProEt.topology Y) (Type (u + 1)))
      (f : F ⟶ G), Epi f → Function.Surjective (f.hom.app (op V)) := by
    intro F G f hf
    exact hV f ((Sheaf.isLocallySurjective_iff_epi f).2 hf)
  obtain ⟨hev, _⟩ := Scheme.ProEt.affine_weaklyContractible_abelian_evaluation_colimits
    Y V hWC
  have : ev.PreservesHomology := hev
  have : PreservesFiniteLimits ev := Functor.preservesFiniteLimits_of_preservesHomology ev
  have : PreservesFiniteColimits ev := Functor.preservesFiniteColimits_of_preservesHomology ev
  have : U.PreservesInjectiveObjects := by
    constructor
    intro I hI
    let := hI
    exact injective_upperStar_obj_of_weaklyEtale Ab.{u + 1} r I
  have : P.PreservesInjectiveObjects :=
    Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms
      (upperStarLowerStarAdjunction Ab.{u + 1} p)
  let K := (DerivedCategory.Plus.singleFunctor _ 0).obj G
  let eΓ : Γ.rightDerivedFunctorPlus.obj
      ((DerivedCategory.Plus.singleFunctor _ 0).obj (U.obj G)) ≅
      ev.mapDerivedCategoryPlus.obj (P.rightDerivedFunctorPlus.obj K) :=
    Γ.rightDerivedFunctorPlus.mapIso ((U.mapDerivedCategoryPlusSingleFunctor 0).app G).symm ≪≫
    Γ.rightDerivedFunctorPlus.mapIso
      (U.rightDerivedFunctorPlusIsoMapDerivedCategoryPlus.app K).symm ≪≫
    (Functor.rightDerivedFunctorPlusCompIso U Γ).symm.app K ≪≫
    (Functor.rightDerivedFunctorPlusNatIso
      (localizationSectionsIso r ≪≫ (directImageSectionsIso p V).symm)).app K ≪≫
    (Functor.rightDerivedFunctorPlusCompIso P ev).app K ≪≫
    ev.rightDerivedFunctorPlusIsoMapDerivedCategoryPlus.app _
  obtain ⟨ec⟩ := nonempty_iso_comparisonUpperStar_comp_rightDerivedLowerStar Ab.{u + 1} p
  have het := Etale.isZero_higherDirectImage_of_isProper_of_fiber_dimension_le
    p d hd F hF q hq
  have hpro : IsZero ((DerivedCategory.Plus.homologyFunctor _ q).obj
      (P.rightDerivedFunctorPlus.obj K)) := by
    exact (ν.map_isZero het).of_iso
      ((DerivedCategory.Plus.homologyFunctor _ q).mapIso
          (P.rightDerivedFunctorPlus.mapIso
            (((comparisonUpperStar Ab.{u + 1} X).mapDerivedCategoryPlusSingleFunctor 0).app F ≪≫
              (DerivedCategory.Plus.singleFunctor _ 0).mapIso e)).symm ≪≫
        (DerivedCategory.Plus.homologyFunctor _ q).mapIso
          (ec.app ((DerivedCategory.Plus.singleFunctor _ 0).obj F)).symm ≪≫
        ((ν.mapDerivedCategoryPlusHomologyFunctorIso q).app _).symm)
  have hsec : IsZero ((DerivedCategory.Plus.homologyFunctor Ab.{u + 1} q).obj
      (Γ.rightDerivedFunctorPlus.obj
        ((DerivedCategory.Plus.singleFunctor _ 0).obj (U.obj G)))) := by
    exact (ev.map_isZero hpro).of_iso
      ((DerivedCategory.Plus.homologyFunctor _ q).mapIso eΓ ≪≫
        ((ev.mapDerivedCategoryPlusHomologyFunctorIso q).app _).symm)
  exact hsec.of_iso ((DerivedCategory.homologyFunctor Ab.{u + 1} q).mapIso
    (Γ.rightDerivedFunctorPlusCompatibility.app
      ((DerivedCategory.Plus.singleFunctor _ 0).obj (U.obj G)))).symm

private theorem finite_module_torsion (B : Type (u + 1)) [CommRing B] [Finite B]
    {X : Scheme.{u}} (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} B)) :
    Scheme.IsTorsionAbelianSheaf
      ((sheafCompose X.smallEtaleTopology (forget₂ (ModuleCat.{u + 1} B) Ab.{u + 1})).obj F) := by
  apply (Scheme.isTorsionAbelianSheaf_characterizations _).1.mpr
  apply Sheaf.IsTorsion.of_forall_isAddTorsion
  intro U x
  refine isOfFinAddOrder_iff_nsmul_eq_zero.2 ⟨Nat.card B, Nat.card_pos, ?_⟩
  change Nat.card B • (show F.obj.obj U from x) = 0
  calc
    Nat.card B • (show F.obj.obj U from x) =
        (Nat.card B • (1 : B)) • (show F.obj.obj U from x) := by
      simp [Nat.cast_smul_eq_nsmul]
    _ = 0 := by rw [card_nsmul_eq_zero', zero_smul]

/-- The natural reduction isomorphism, its degree-zero constructible etale origin, and the
2d vanishing bound over every affine categorically weakly contractible pro-etale object.
Source: blueprint main-20261015, sk-lem-proper-heart-bound-torsion; Stacks Tags 099Y,
09AF, 095U, 09A6 and 0991 (blueprint: det-proper-heart-bound-torsion).

Proof:
1. The locally closed extension preserves flat lisse integral modules. Its normalized
   tensor projection isomorphism, followed by the flat single-object tensor comparison,
   gives a natural derived reduction isomorphism.
2. Scalar extension of a finite free module is finite free. Over the finite discrete
   quotient ring, the quotient therefore has finite constant local models. Extension
   along the open and closed immersions preserves a finite constructible stratification.
3. The normalized finite-discrete encoding identifies these internal local models with
   finite locally constant ordinary module sheaves. Its action on constant scalars is
   the actual quotient of each integral scalar. The constructible comparison theorem
   supplies the required etale module sheaf with its full scalar compatibility.
4. Invariance of finite-type dimension under field extension turns the given geometric
   fibre bound into the ordinary fibre bound. The proper torsion direct-image theorem
   applies to the underlying abelian etale sheaf, killed by the order of its finite ring.
5. The qcqs etale/pro-etale direct-image comparison transfers the higher direct-image
   vanishing to Y's pro-etale site. Evaluation at V is exact by categorical weak
   contractibility and affineness.
6. Sections at V after direct image are sections over X times_Y V. The restriction to
   this weakly etale localization preserves injectives. The bounded-below derived
   composition isomorphisms, exact evaluation and compatibility with the unbounded
   derived functor give the asserted cohomology vanishing. -/
theorem properHeartBoundTorsion
    (k : Type u) [Field k] (hchar : ringChar k ≠ 0) (hell : ringChar k ≠ ℓ)
    {X Y S Sbar : Scheme.{u}} [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))] [LocallyOfFiniteType (X ↘ Spec (.of k))]
    [QuasiCompact (X ↘ Spec (.of k))]
    [IsSeparated (Y ↘ Spec (.of k))] [LocallyOfFiniteType (Y ↘ Spec (.of k))]
    [QuasiCompact (Y ↘ Spec (.of k))]
    (p : X ⟶ Y) [p.IsOver (Spec (.of k))] [IsProper p] (d : ℕ)
    (hd : ∀ y : Y, topologicalKrullDim
      (pullback p (Spec.map (CommRingCat.ofHom
        (algebraMap (Y.residueField y) (AlgebraicClosure (Y.residueField y)))) ≫
          Y.fromSpecResidueField y) : Scheme.{u}) ≤ (d : WithBot ℕ∞))
    (V : Y.ProEt) [IsAffine V.left]
    (hV : (Scheme.ProEt.topology Y).IsWeaklyContractible.{u + 1} V)
    (j : S ⟶ Sbar) [IsOpenImmersion j] (i : Sbar ⟶ X) [IsClosedImmersion i]
    (n : ℕ) (hn : 1 ≤ n) :
    Nonempty (
      ObjectProperty.ι (IsLisseCoefficientModule (DerivedNakayama.integerRing ℓ E)
        (X := S)) ⋙ torsionLocallyClosedExtension ℓ E j i ⋙
        DerivedCategory.singleFunctor _ 0 ⋙ DerivedNakayama.reductionFunctor ℓ E X n ≅
      ObjectProperty.ι (IsLisseCoefficientModule (DerivedNakayama.integerRing ℓ E)
        (X := S)) ⋙ torsionQuotient ℓ E S n ⋙
        torsionLocallyClosedExtension ℓ E j i ⋙ DerivedCategory.singleFunctor _ 0) ∧
    ∀ L : ObjectProperty.FullSubcategory
        (IsLisseCoefficientModule (DerivedNakayama.integerRing ℓ E) (X := S)),
      TorsionClassicalOrigin ℓ E X n hn
        ((torsionLocallyClosedExtension ℓ E j i).obj ((torsionQuotient ℓ E S n).obj L.obj)) ∧
      ∀ q : ℤ, (2 * d : ℤ) < q →
        IsZero ((DerivedCategory.homologyFunctor Ab.{u + 1} q).obj
          ((rightDerivedGlobalSections Ab.{u + 1} (pullback p V.hom)).obj
            ((DerivedCategory.singleFunctor _ 0).obj
              ((Scheme.proEtaleSheafInverseImage (pullback.fst p V.hom) Ab.{u + 1}).obj
                (((torsionLocallyClosedExtension ℓ E j i).obj
                  ((torsionQuotient ℓ E S n).obj L.obj)).X))))) := by
  have : IsLocallyNoetherian X :=
    LocallyOfFiniteType.isLocallyNoetherian (X ↘ Spec (.of k))
  have : CompactSpace X :=
    QuasiCompact.compactSpace_of_compactSpace (X ↘ Spec (.of k))
  let A : GeneratorFactorization (j ≫ i) :=
    .inr ⟨Sbar, j, i, rfl, inferInstance, inferInstance⟩
  constructor
  · refine ⟨?_⟩
    simpa only [generatorExtension, A, torsionLocallyClosedExtension, torsionQuotient,
      DerivedNakayama.reductionFunctor, DerivedNakayama.pullback, CondensedRing.derivedTensor] using
      reductionProjectionIso (DerivedNakayama.integerRing ℓ E) A
        (DerivedNakayama.quotientModule ℓ E n)
  · intro L
    have : IsNoetherian X := ⟨⟩
    have hN := origin_extension ℓ E j i n hn L.obj L.property
    refine ⟨hN, ?_⟩
    obtain ⟨G, eG, _, F, _, ⟨eF⟩⟩ := hN
    let B := ULift.{u + 1} (Padic.coefficientExtensionRing ℓ E n)
    let forgetX := sheafCompose (Scheme.ProEt.topology X)
      (forget₂ (ModuleCat.{u + 1} B) Ab.{u + 1})
    let FAb := (sheafCompose X.smallEtaleTopology
      (forget₂ (ModuleCat.{u + 1} B) Ab.{u + 1})).obj F
    let eAb : (comparisonUpperStar Ab.{u + 1} X).obj FAb ≅
        ((torsionLocallyClosedExtension ℓ E j i).obj
          ((torsionQuotient ℓ E S n).obj L.obj)).X :=
      (sheafComposeForget₂CompComparisonUpperStarIso B X).app F ≪≫
        forgetX.mapIso eF ≪≫ eG
    have hf (y : Y) : topologicalKrullDim (p.fiber y) ≤ (d : WithBot ℕ∞) := by
      have he := topologicalKrullDim_pullback_eq_of_field
        (k := Y.residueField y) (pullback.snd p (Y.fromSpecResidueField y))
        (Spec.map (CommRingCat.ofHom
          (algebraMap (Y.residueField y) (AlgebraicClosure (Y.residueField y)))))
      have hi := IsHomeomorph.topologicalKrullDim_eq _
        (pullbackLeftPullbackSndIso p (Y.fromSpecResidueField y)
          (Spec.map (CommRingCat.ofHom
            (algebraMap (Y.residueField y)
              (AlgebraicClosure (Y.residueField y)))))).hom.homeomorph.isHomeomorph
      exact (he.symm.trans hi).le.trans (hd y)
    intro q hq
    have : Finite B := by
      have := Padic.finite_coefficientExtensionRing ℓ E n hn
      infer_instance
    exact proper_torsion_vanishing p d hf V hV FAb (finite_module_torsion B F) _ eAb q hq

attribute [local irreducible] ordinaryQuotientRestrictionIso finiteExtensionRestrictionIso

end Origin

open CondensedRing

attribute [local irreducible] localizationSectionsIso directImageSectionsIso

end AlgebraicGeometry.ProEtale
