/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.DeligneLaumon.CondensedLisseDualityDefs
import WeilConjectures.DeligneLaumon.CondensedDualCohomologyObjects
import WeilConjectures.DeligneLaumon.CondensedTateLineTrivializations
import all WeilConjectures.AlgebraicGeometry.FiniteEtaleLocallyFreeModels
import all WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs
import all WeilConjectures.CategoryTheory.ModuleObjects.Free
import all Mathlib.AlgebraicGeometry.Morphisms.Etale
import all Mathlib.AlgebraicGeometry.Morphisms.Finite
import all WeilConjectures.AlgebraicGeometry.FiniteEtaleEtaleLocalSplit
import all WeilConjectures.AlgebraicGeometry.SplitProEtaleModuleProductMap
import all Mathlib.CategoryTheory.Limits.Shapes.Products
import all WeilConjectures.AlgebraicGeometry.ProfinitePointPullback
import all WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import all WeilConjectures.AlgebraicGeometry.ProEtaleInverseImage
import all WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
import all WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
import all Mathlib.AlgebraicGeometry.Sites.Proetale
import all Mathlib.CategoryTheory.Sites.ConstantSheaf
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import all Mathlib.Algebra.Homology.DerivedCategory.Basic
import all WeilConjectures.CategoryTheory.RingedSiteModules
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous
import all Mathlib.CategoryTheory.Sites.Equivalence
import all WeilConjectures.CategoryTheory.SiteInverseImageTensor
import all WeilConjectures.CategoryTheory.Adjunction.LiftsGroupRingObjects
import all Mathlib.CategoryTheory.Monoidal.CommGrp_
import all Mathlib.CategoryTheory.Monoidal.Ring
import all Mathlib.CategoryTheory.Adjunction.Limits
import all WeilConjectures.CategoryTheory.Adjunction.LiftedCommRingBranch
import all WeilConjectures.CategoryTheory.Monoidal.Conjugate
import all WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate
import all WeilConjectures.CategoryTheory.Sites.MonObj
import all WeilConjectures.AlgebraicGeometry.SplitProEtaleAbelianProductMap
import all Mathlib.Algebra.Category.Grp.AB
import all WeilConjectures.Mathlib.CategoryTheory.Adjunction.Unique
import all WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Defs
import all WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Iso
import all WeilConjectures.Mathlib.AlgebraicGeometry.PullbackCarrier
import all Mathlib.AlgebraicGeometry.Limits
import all WeilConjectures.AlgebraicGeometry.CondensedConstructibleSerre
import all WeilConjectures.ConstructibleSheaf.ProEtaleModule.Def
import all WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.Compatibility
import all WeilConjectures.NumberTheory.Padics.FiniteCoefficientFields
import all Mathlib.NumberTheory.Padics.PadicNumbers
import all Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import all Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import all Mathlib.Algebra.Field.ULift
import all Mathlib.CategoryTheory.Sites.EpiMono
import all WeilConjectures.ConstructibleSheaf.Refinement
import all WeilConjectures.AlgebraicGeometry.CondensedFieldLfpLocalTriviality
import all WeilConjectures.AlgebraicGeometry.CondensedFieldContinuousRealization
import all WeilConjectures.AlgebraicGeometry.ProEtaleModuleConstructiblePullback
import all WeilConjectures.ConstructibleSheaf.Pullback
import all WeilConjectures.AlgebraicGeometry.ContinuousCoefficientUniverse
import all Mathlib.Topology.Category.Profinite.EffectiveEpi
import all WeilConjectures.CategoryTheory.RingObjects.ContinuousMap
import all Mathlib.Condensed.TopComparison
import all WeilConjectures.RingTheory.Spectrum.Prime.LocallyConstant
import all WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
import all Mathlib.Topology.NoetherianSpace
import all WeilConjectures.AlgebraicGeometry.ProEtalePointComponentsMaps
import all WeilConjectures.AlgebraicGeometry.ProfiniteTestObjectFunctor
import all WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
import all Mathlib.Topology.Category.Profinite.AsLimit
import all Mathlib.Topology.Category.Profinite.CofilteredLimit
import all Mathlib.Topology.Connected.TotallyDisconnected
import all WeilConjectures.Topology.SpectralSpace.ConnectedComponent
import all WeilConjectures.AlgebraicGeometry.ProEtaleSheafificationWcontractibleSections
import all WeilConjectures.AlgebraicGeometry.PointLanAffineEvaluation
import all Mathlib.CategoryTheory.Functor.KanExtension.Pointwise
import all Mathlib.CategoryTheory.Whiskering
import all Mathlib.Algebra.Category.Ring.Basic
import all WeilConjectures.AlgebraicGeometry.PointLanFiniteProducts
import all WeilConjectures.AlgebraicGeometry.Sites.ProEtaleFiniteCoproductEvaluation
import all WeilConjectures.AlgebraicGeometry.FiniteCoproductLfpQcqs
import all WeilConjectures.AlgebraicGeometry.Sites.ProEtaleFiniteCoproductSections
import all WeilConjectures.AlgebraicGeometry.ProEtaleAffineContractibleExtension
import all WeilConjectures.AlgebraicGeometry.ProEtale.WeaklyContractible
import all WeilConjectures.AlgebraicGeometry.ProEtaleAffineWeaklyContractibleCover
import all Mathlib.Analysis.Normed.Module.FiniteDimension
import all Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
import all WeilConjectures.AlgebraicGeometry.LocallyClosedStratification
import all WeilConjectures.AlgebraicGeometry.CondensedFieldPresentationCorank
import all WeilConjectures.AlgebraicGeometry.CondensedFieldPresentationMatrix
import all Mathlib.LinearAlgebra.Matrix.Rank
import all WeilConjectures.AlgebraicGeometry.CondensedFieldPresentationEvaluation
import all Mathlib.Algebra.Category.ModuleCat.Basic
import all WeilConjectures.AlgebraicGeometry.CondensedFieldRegularModuleScalars
import all WeilConjectures.AlgebraicGeometry.CondensedFieldEvaluationFunctors
import all WeilConjectures.AlgebraicGeometry.GeometricFieldProEtaleEvaluation
import all WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale
import all WeilConjectures.Mathlib.CategoryTheory.Adjunction.Reflective
import all WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import all WeilConjectures.AlgebraicGeometry.GeometricFieldProfiniteDenseSubsite
import all WeilConjectures.AlgebraicGeometry.ProEtale.Comparison.Affine
import all WeilConjectures.CategoryTheory.DenseSubsiteModuleRestriction
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
import all Mathlib.CategoryTheory.Sites.CartesianMonoidal
import all Mathlib.Algebra.Category.Ring.Limits
import all Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import all Mathlib.Algebra.Category.ModuleCat.ChangeOfRingsExact
import all WeilConjectures.AlgebraicGeometry.InternalModuleAbEquivalence
import all WeilConjectures.CategoryTheory.RingObjects.Ab
import all Mathlib.CategoryTheory.Monoidal.Mod
import all WeilConjectures.Mathlib.CategoryTheory.Monoidal.Mod
import all WeilConjectures.AlgebraicGeometry.CondensedFieldGeometricRegularCoefficient
import all WeilConjectures.AlgebraicGeometry.ContinuousChartSchemeNaturality
import all WeilConjectures.AlgebraicGeometry.IntegralMatrixAnalyticData
import all WeilConjectures.AlgebraicGeometry.ContinuousCoefficientRealizations
import all WeilConjectures.AlgebraicGeometry.ContinuousIntegralCoefficientData
import all WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients
import all WeilConjectures.CategoryTheory.ModuleObjects.DerivedCategory
import all Mathlib.Analysis.Normed.Algebra.Ultra
import all Mathlib.Topology.Algebra.Valued.NormedValued
import all Mathlib.Topology.Algebra.Ring.Ideal
import all Mathlib.Topology.ContinuousMap.Compact
import all Mathlib.NumberTheory.Padics.ProperSpace
import all WeilConjectures.Mathlib.Algebra.Homology.ShortComplex.Exact
import all Mathlib.CategoryTheory.Abelian.ShortExact
import all WeilConjectures.AlgebraicGeometry.IntegralScalarContractive
import all Mathlib.Data.Matrix.Basic
import all WeilConjectures.AlgebraicGeometry.IntegralRegularCoefficientPullback
import all Mathlib.Algebra.Category.ModuleCat.Biproducts
import all Mathlib.Algebra.Category.ModuleCat.Kernels
import all Mathlib.AlgebraicGeometry.PullbackCarrier
import all WeilConjectures.AlgebraicGeometry.CondensedFieldRankDescent
import all Mathlib.AlgebraicGeometry.Morphisms.Flat
import all Mathlib.Topology.LocallyConstant.Basic
import all Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
import all WeilConjectures.AlgebraicGeometry.ContinuousFieldCokernelLocalFree
import all WeilConjectures.AlgebraicGeometry.ContinuousFieldPresentationNormalForm
import all WeilConjectures.AlgebraicGeometry.ContinuousFieldMatrixSheafNormalForm
import all WeilConjectures.AlgebraicGeometry.ContinuousFieldMatrixElimination
import all Mathlib.Logic.Equiv.Set
import all Mathlib.Data.Fintype.Basic
import all Mathlib.Topology.ContinuousMap.Algebra
import all Mathlib.Analysis.Normed.Field.Lemmas
import all Mathlib.LinearAlgebra.Matrix.SchurComplement
import all WeilConjectures.Mathlib.LinearAlgebra.Matrix.Rank
import all WeilConjectures.Mathlib.LinearAlgebra.Matrix.SchurComplement
import all WeilConjectures.AlgebraicGeometry.CondensedQbarLfpLocalTriviality
import all WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic
import all WeilConjectures.AlgebraicGeometry.CondensedQbarLfpMatrixRefinement
import all WeilConjectures.AlgebraicGeometry.CondensedQbarFunctionPresentations
import all Mathlib.LinearAlgebra.Matrix.ToLin
import all WeilConjectures.AlgebraicGeometry.CondensedQbarFunctionCoefficients
import all WeilConjectures.AlgebraicGeometry.CondensedQbarCoefficientConstruction
import all WeilConjectures.CategoryTheory.RingObjects.Condensed.FiniteSubextension
import all WeilConjectures.CategoryTheory.Monoidal.Mod.EvaluationPairing
import all WeilConjectures.AlgebraicGeometry.CondensedQbarScalarPullback
import all WeilConjectures.AlgebraicGeometry.CondensedQbarFieldFiberExtension
import all WeilConjectures.AlgebraicGeometry.CondensedQbarFieldEvaluationLinearity
import all WeilConjectures.CategoryTheory.Sites.PushforwardMonoidal
import all WeilConjectures.AlgebraicGeometry.CondensedQbarFieldCoefficientSquare
import all WeilConjectures.AlgebraicGeometry.CondensedQbarFieldPointCoefficientValue
import all WeilConjectures.AlgebraicGeometry.CondensedCoefficientPointUnitPasting
import all WeilConjectures.AlgebraicGeometry.CondensedQbarLfpCoverComposition

/-! # The bounded lisse cohomology calculation with a supplied purity isomorphism -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale.CondensedLisseDual
variable (ell : ℕ) [Fact ell.Prime]

/-- The cohomology comparison alone implies lisse preservation and zero detection.
Source: Step 2 of `thm-a1-curve-perverse-heart`, finite free linear algebra
(blueprint: lem-per-condensed-lisse-cohomology-formula).

Proof: evaluate the comparison at a lisse complex. The ordinary dual twisted by
the Tate line is lisse and detects zero, by its local unit bases and finite free
double duality. Transport those two assertions along the evaluated comparison.
-/
theorem cohomology_lisse_vanishing (c : PurityTransport.Coefficient ell)
    {k : Type u} [Field k] (hEll : IsUnit (ell : k))
    (A : ∀ T : Space k, AdjointData ell c T)
    (cohom : CohomologyComparisons ell c A) :
    DualLisse ell c A ∧ DualVanishing ell c A := by
  have hInv (T : Space k) : ∀ x : T.scheme, Invertible (ell : T.scheme.residueField x) :=
    fun x ↦ (by simpa using hEll.map (T.map.residueFieldAlgebraMap x) :
      IsUnit (ell : T.scheme.residueField x)).invertible
  have hp (T : Space k) (M : (lisseProperty ell c T.scheme).FullSubcategory) (a : ℤ) := by
    let := hInv T
    exact PurityTransport.linear_dual_twist_properties ell c T.scheme T.dim.val
      ((DerivedCategory.homologyFunctor (Modules ell c T.scheme)
        (-2 * (T.dim.val : ℤ) - a)).obj M.obj) (M.property.2 _)
  constructor
  · intro T M a
    exact CondensedRing.locFree_iso ((cohom T a).app (op M)) (hp T M a).1
  · intro T M a
    let e := (cohom T a).app (op M)
    exact ⟨fun h ↦ (hp T M a).2.mp (h.of_iso e.symm),
      fun h ↦ ((hp T M a).2.mpr h).of_iso e⟩

/-- The natural dual-cohomology calculation, conditional on the chosen smooth purity.
This assertion constructs neither a geometric adjoint nor coherent open orientations.
Source: Step 2 of `thm-a1-curve-perverse-heart`, the bounded lisse calculation and
its evaluation-defined restriction square
(blueprint: lem-per-condensed-lisse-cohomology-formula).

Proof: a lisse cohomology sheaf is locally finite free, so is dualizable in the
native category of modules over the pulled-back condensed coefficient ring.
Apply `DerivedCategory.nonempty_ihom_single_unit` for a sheaf in one degree.
Its ordinary internal dual is lisse of the same finite rank, including rank zero.
The objectwise untwisted formula is proved in
`CondensedRing.nonempty_ihom_unit_homology_of_lisse`. For the natural untwisted
formula in degree a, put j = -a. The functorial maps
truncLE j M -> M and truncLE j M -> H^j(M)[-j] give, after contravariant
internal Hom and degree-a cohomology, a natural zigzag from H^a D(M) to
H^a D(truncLE j M) and from H^a D(H^j(M)[-j]) to that middle object.
The upper truncation has cohomology only in degrees at least j+1, so its
dual has cohomology only in degrees at most a-1. The remaining lower truncation
has cohomology only in degrees at most j-1, so its dual has
cohomology only in degrees at least a+1. The proved objectwise formula gives
these vanishings also when one truncation is zero. The two exact sequences
therefore make both displayed edge maps isomorphisms. Define the single-degree
identification by the ordinary evaluation pairing and the monoidal single-functor
comparison, so uniqueness of its transpose proves naturality in the sheaf.
Invert the second edge map and compose with this single-degree identification.
Both truncations preserve boundedness and lisse cohomology. Their indices depend
only on a, not on objectwise bounds, so the construction is a natural
isomorphism on the entire full lisse subcategory. No splitting of M is used.

Postcompose internal Hom with the supplied purity isomorphism. Its target is the
Tate line in degree shift `2d`. This line is locally free of rank one; tensoring
with it is exact and invertible. The tensor-Hom comparison for perfect objects
and the homology shift formula turn the untwisted edge maps into the displayed
natural isomorphisms in degree `-2d-a` with twist `d`. Dualizing a finite free
module and twisting by a line both detect zero on a trivializing cover, proving
the vanishing equivalence as well as the lisse assertion.

For any normalized open orientation, the target-variable map in `restrictionMap`
agrees, after purity, with the prescribed derived Tate pullback. Naturality of
the evaluation-defined internal-Hom comparison and the exact inverse-image
homology comparison makes the single-degree square commute with the ordinary
map `coefficientLinearPull`. Functorial truncation and its long exact sequence
carry this commuting square through the same truncation zigzag. This gives the
stated `CohomologyEquivariant` equality for every supplied coordinate, including
semilinear automorphisms and their Frobenius descent data. Invertibility of ell
covers characteristic zero as well as positive characteristic different from ell.
-/
theorem lisse_cohomology_formula (k : Type u) [Field k] [PerfectField k]
    (hEll : IsUnit (ell : k))
    (A : ∀ T : Space k, AdjointData ell PurityTransport.Coefficient.closure T)
    (p : PurityComparisons ell PurityTransport.Coefficient.closure A) :
    ∃ cohom : CohomologyComparisons ell PurityTransport.Coefficient.closure A,
      ∀ e : OpenDualizingComparisons ell PurityTransport.Coefficient.closure A,
        OpenNormalized ell PurityTransport.Coefficient.closure A p e →
          CohomologyEquivariant ell PurityTransport.Coefficient.closure A cohom e := by sorry

end AlgebraicGeometry.ProEtale.CondensedLisseDual
