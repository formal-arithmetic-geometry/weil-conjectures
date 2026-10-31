/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Topology.ProfiniteCondensedRing
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic
public import WeilConjectures.ConstructibleSheaf.ProEtaleModule.DerivedCategory
public import Mathlib.CategoryTheory.Monoidal.Mon
public import WeilConjectures.AlgebraicGeometry.BoundedConstructibleConeCounterexample
public import WeilConjectures.AlgebraicGeometry.CondensedModuleDerivedPushpull
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.FieldTheory.IsAlgClosed.Basic
import WeilConjectures.ConstructibleSheaf.ProEtaleModule.Def
import WeilConjectures.CategoryTheory.ModuleObjects.Free
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs
import all WeilConjectures.AlgebraicGeometry.CondensedConstructibleSerre
import all WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.Compatibility
import all WeilConjectures.NumberTheory.Padics.FiniteCoefficientFields
import all Mathlib.NumberTheory.Padics.PadicNumbers
import all Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import all Mathlib.Algebra.Field.ULift
import all Mathlib.CategoryTheory.Sites.EpiMono
import all WeilConjectures.ConstructibleSheaf.Refinement
import all WeilConjectures.AlgebraicGeometry.CondensedFieldLfpLocalTriviality
import all WeilConjectures.AlgebraicGeometry.CondensedFieldContinuousRealization
import all WeilConjectures.AlgebraicGeometry.ProEtaleModuleConstructiblePullback
import all WeilConjectures.CategoryTheory.Monoidal.Conjugate
import all WeilConjectures.ConstructibleSheaf.Pullback
import all WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Defs
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
import all WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
import all Mathlib.AlgebraicGeometry.Sites.Proetale
import all Mathlib.CategoryTheory.Sites.ConstantSheaf
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import all Mathlib.Algebra.Homology.DerivedCategory.Basic
import all Mathlib.Topology.Category.Profinite.AsLimit
import all Mathlib.CategoryTheory.Limits.Shapes.Products
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
import all Mathlib.AlgebraicGeometry.Limits
import all WeilConjectures.AlgebraicGeometry.FiniteCoproductLfpQcqs
import all WeilConjectures.AlgebraicGeometry.Sites.ProEtaleFiniteCoproductSections
import all WeilConjectures.AlgebraicGeometry.ProEtaleAffineContractibleExtension
import all WeilConjectures.AlgebraicGeometry.ProEtale.WeaklyContractible
import all WeilConjectures.CategoryTheory.Sites.MonObj
import all WeilConjectures.AlgebraicGeometry.ProEtaleAffineWeaklyContractibleCover
import all Mathlib.Analysis.Normed.Module.FiniteDimension
import all Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
import all WeilConjectures.AlgebraicGeometry.LocallyClosedStratification
import all WeilConjectures.AlgebraicGeometry.ProfinitePointPullback
import all WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import all WeilConjectures.AlgebraicGeometry.ProEtaleInverseImage
import all WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
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
import all WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate
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
import WeilConjectures.AlgebraicGeometry.NoetherianStratumDetectionSupplement
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.SepClosedPoint
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.FinitelyPresentedStalk
import Mathlib.AlgebraicGeometry.Noetherian

/-!
# Geometric pullbacks detect zero bounded constructible condensed complexes

Source: latest blueprint, sec-fourier-transform/sk-thm-inversion/
lem-fd-convolution-kernel.proof.md, Step 3.
(blueprint: lem-fd-condensed-geometric-fibre-conservativity)

Both conclusions use the whole total derived inverse image in the module-object
category on the geometric scheme, with the pulled-back condensed coefficients.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

/-- Forgetfulness detects a zero module because it is faithful. -/
private theorem fibre_module_zero_of_underlying {Y : Scheme.{u}}
    {R : Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}} [MonObj R]
    (M : Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) R)
    (h : IsZero M.X) : IsZero M := by
  exact (IsZero.iff_id_eq_zero _).2 (Mod.hom_ext _ _ (h.eq_of_src _ _))

/-- The empty-cover sheaf axiom deals with an empty trivializing chart. -/
private theorem fibre_module_zero_of_empty {Y : Scheme.{u}} [IsEmpty Y]
    {R : Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}} [MonObj R]
    (M : Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) R) : IsZero M := by
  apply fibre_module_zero_of_underlying M
  apply Sheaf.isZero_of_isZero_obj
  rintro ⟨T⟩
  have : IsEmpty T.left := ⟨fun t ↦ (inferInstance : IsEmpty Y).false (T.hom t)⟩
  exact (isZero_zero _).of_iso
    ((Scheme.ProEt.isTerminalSectionsOfIsEmpty M.X T).uniqueUpToIso
      HasZeroObject.zeroIsTerminal)

/-- Normalize inverse image by the invertible cartesian coefficient comparison. -/
private noncomputable def fibre_normalizedPullbackIso
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X Y : Scheme.{u}} (f : Y ⟶ X) :
    CondensedRing.upperStar Λ f ≅
      (upperStar Ab.{u + 1} f).mapMod (condensedRingObj Λ X) ⋙
        Mod.comap (inv (condensedPullbackHom Λ f)) :=
  Functor.isoWhiskerLeft _ (Mod.extendScalarsIsoComapInv (condensedPullbackHom Λ f))

/-- Normalized module pullback has the usual inverse image as its underlying sheaf. -/
private noncomputable def fibre_pullbackForgetIso
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X Y : Scheme.{u}} (f : Y ⟶ X) :
    CondensedRing.upperStar Λ f ⋙ Mod.forget (condensedRingObj Λ Y) ≅
      Mod.forget (condensedRingObj Λ X) ⋙ upperStar Ab.{u + 1} f :=
  Functor.isoWhiskerRight (fibre_normalizedPullbackIso Λ f) _

/-- Reflection at a geometric point detects vanishing of the coefficient itself. -/
private theorem fibre_regular_zero
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (Ω : Type u) [Field Ω] [IsAlgClosed Ω]
    (h : IsZero (Mod.regular (condensedRingObj Λ (Spec (.of Ω)))))
    (Y : Scheme.{u}) : IsZero (Mod.regular (condensedRingObj Λ Y)) := by
  have hcoeff : IsZero ((upperStarFromPoint (Spec (.of Ω))).obj Λ) :=
    (Mod.forget _).map_isZero h
  have hΛ : IsZero Λ :=
    IsZero.of_full_of_faithful_of_isZero (upperStarFromPoint (Spec (.of Ω))) Λ hcoeff
  exact fibre_module_zero_of_underlying _ ((upperStarFromPoint Y).map_isZero hΛ)

/-- The regular summand detects a finite free module through a functor preserving
monomorphisms, provided vanishing of the regular object is reflected. -/
private theorem fibre_free_zero_generic
    {C D : Type*} [Category C] [Category D] [Abelian C] [MonoidalCategory C]
    [MonoidalPreadditive C] {R : C} [MonObj R]
    [PreservesFiniteColimits (MonoidalCategory.tensorLeft R)] [HasZeroMorphisms D]
    (F : Mod C R ⥤ D) [F.PreservesMonomorphisms] (M : Mod C R)
    (hfree : Mod.IsFree R M) (hM : IsZero (F.obj M))
    (hreflect : IsZero (F.obj (Mod.regular R)) → IsZero (Mod.regular R)) : IsZero M := by
  classical
  obtain ⟨n, ⟨e⟩⟩ := hfree
  rcases n with _ | n
  · have hz : IsZero (Mod.finiteFree R 0) := by
      rw [IsZero.iff_id_eq_zero]
      exact biproduct.hom_ext' _ _ fun j ↦ j.elim0
    exact hz.of_iso e
  · let i : Mod.regular R ⟶ M :=
      biproduct.ι (fun _ : Fin (n + 1) ↦ Mod.regular R) ⟨0, Nat.zero_lt_succ n⟩ ≫ e.inv
    have : Mono i := by dsimp only [i]; infer_instance
    have hR := hreflect (IsZero.of_mono (F.map i) hM)
    have hz : IsZero (Mod.finiteFree R (n + 1)) := by
      rw [IsZero.iff_id_eq_zero]
      apply biproduct.hom_ext
      intro j
      exact hR.eq_of_tgt _ _
    exact hz.of_iso e

section

attribute [local irreducible] CondensedRing.upperStar

/-- A specified geometric point detects zero finite free coefficient modules.
Reflect the regular summand through the geometric coefficient equivalence. -/
private theorem fibre_free_zero_at_point
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (Y : Scheme.{u})
    (M : Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y))
    (hfree : Mod.IsFree (condensedRingObj Λ Y) M)
    (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (g : Spec (.of Ω) ⟶ Y)
    (hM : IsZero ((CondensedRing.upperStar Λ g).obj M)) : IsZero M := by
  apply fibre_free_zero_generic (CondensedRing.upperStar Λ g) M hfree hM
  intro hR
  exact fibre_regular_zero Λ Ω
    (hR.of_iso (CondensedRing.upperStarObjRegularIso Λ g).symm) Y

end

/-- A nonempty chart admits the geometric point of an algebraic closure of a residue
field. Empty charts are handled by the empty-cover axiom. -/
private theorem fibre_free_zero
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (Y : Scheme.{u})
    (M : Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y))
    (hfree : Mod.IsFree (condensedRingObj Λ Y) M)
    (h : ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (g : Spec (.of Ω) ⟶ Y),
      IsZero ((CondensedRing.upperStar Λ g).obj M)) : IsZero M := by
  classical
  by_cases hY : Nonempty Y
  · obtain ⟨y⟩ := hY
    let Ω := AlgebraicClosure (Y.residueField y)
    let g : Spec (.of Ω) ⟶ Y :=
      Spec.map (CommRingCat.ofHom (algebraMap (Y.residueField y) Ω)) ≫
        Y.fromSpecResidueField y
    exact fibre_free_zero_at_point Λ Y M hfree Ω g (h Ω g)
  · let : IsEmpty Y := not_nonempty_iff.mp hY
    exact fibre_module_zero_of_empty M

section

attribute [local irreducible] CondensedRing.upperStar CondensedRing.upperStarComp
  fibre_normalizedPullbackIso fibre_pullbackForgetIso

/-- Transport local finite presentation through the cartesian scalar comparison. -/
private theorem fibre_lfp_normalize
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X Y : Scheme.{u}} (f : Y ⟶ X)
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
    (h : IsLocallyFinitelyPresented ((upperStar Ab.{u + 1} f).obj (condensedRingObj Λ X))
      (((upperStar Ab.{u + 1} f).mapMod (condensedRingObj Λ X)).obj M)) :
    IsLocallyFinitelyPresented (condensedRingObj Λ Y) ((CondensedRing.upperStar Λ f).obj M) :=
  lfp_of_iso (lfp_comap (inv (condensedPullbackHom Λ f)) h)
    ((fibre_normalizedPullbackIso Λ f).app M).symm

/-- Transport finite freeness through the same invertible coefficient map. -/
private theorem fibre_free_normalize
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X Y : Scheme.{u}} (f : Y ⟶ X)
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
    (h : Mod.IsFree ((upperStar Ab.{u + 1} f).obj (condensedRingObj Λ X))
      (((upperStar Ab.{u + 1} f).mapMod (condensedRingObj Λ X)).obj M)) :
    Mod.IsFree (condensedRingObj Λ Y) ((CondensedRing.upperStar Λ f).obj M) :=
  free_of_iso (free_comap (inv (condensedPullbackHom Λ f)) h)
    ((fibre_normalizedPullbackIso Λ f).app M).symm

/-- Vanishing along a triple composite gives vanishing of the iterated pullback. -/
private theorem fibre_zero_triple
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X Y Z W : Scheme.{u}}
    (i : Y ⟶ X) (f : Z ⟶ Y) (g : W ⟶ Z)
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
    (h : IsZero ((CondensedRing.upperStar Λ (g ≫ f ≫ i)).obj M)) :
    IsZero ((CondensedRing.upperStar Λ g).obj
      ((CondensedRing.upperStar Λ f).obj ((CondensedRing.upperStar Λ i).obj M))) :=
  h.of_iso ((CondensedRing.upperStarComp Λ g (f ≫ i)).app M ≪≫
    (CondensedRing.upperStar Λ g).mapIso ((CondensedRing.upperStarComp Λ f i).app M)).symm

/-- Forget a vanishing iterated module pullback along a chart of a stratum. -/
private theorem fibre_zero_underlying_composite
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X Y Z : Scheme.{u}} (i : Y ⟶ X) (f : Z ⟶ Y)
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
    (h : IsZero ((CondensedRing.upperStar Λ f).obj
      ((CondensedRing.upperStar Λ i).obj M))) :
    IsZero ((upperStar Ab.{u + 1} (f ≫ i)).obj M.X) :=
  ((Mod.forget _).map_isZero
    (h.of_iso ((CondensedRing.upperStarComp Λ f i).app M))).of_iso
      ((fibre_pullbackForgetIso Λ (f ≫ i)).app M).symm

/-- Detect a trivialized chart and forget the resulting zero module. -/
private theorem fibre_chart_zero
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X Y Z : Scheme.{u}} (i : Y ⟶ X) (f : Z ⟶ Y)
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
    (hfree : Mod.IsFree (condensedRingObj Λ Z)
      ((CondensedRing.upperStar Λ f).obj ((CondensedRing.upperStar Λ i).obj M)))
    (h : ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (g : Spec (.of Ω) ⟶ X),
      IsZero ((CondensedRing.upperStar Λ g).obj M)) :
    IsZero ((upperStar Ab.{u + 1} (f ≫ i)).obj M.X) := by
  apply fibre_zero_underlying_composite Λ i f M
  apply fibre_free_zero Λ _ _ hfree
  intro Ω _ _ g
  exact fibre_zero_triple Λ i f g M (h Ω (g ≫ f ≫ i))

/-- A fixed collection of finite free stratum charts detects the original module. -/
private theorem fibre_stratified_zero
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (X : Scheme.{u}) [IsNoetherian X]
    (S : Scheme.Stratification X)
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
    (C : ∀ a : Fin S.n, Scheme.Cover.{u} Scheme.proetalePrecoverage (S.domain a))
    (hC : ∀ a j, Mod.IsFree (condensedRingObj Λ ((C a).X j))
      ((CondensedRing.upperStar Λ ((C a).f j)).obj
        ((CondensedRing.upperStar Λ (S.immersion a)).obj M)))
    (h : ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (g : Spec (.of Ω) ⟶ X),
      IsZero ((CondensedRing.upperStar Λ g).obj M)) : IsZero M := by
  apply fibre_module_zero_of_underlying M
  apply Scheme.proEtale_isZero_of_stratum_cover X S C M.X
  intro a j
  exact fibre_chart_zero Λ (S.immersion a) ((C a).f j) M (hC a j) h

/-- Trivialize on the constructible strata and use finite-stratum sheaf detection. -/
private theorem fibre_constructible_zero
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    (htriv : ∀ (Y : Scheme.{u}) [TopologicalSpace.NoetherianSpace Y]
      (N : Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y)),
      IsLocallyFinitelyPresented (condensedRingObj Λ Y) N →
      ∃ C : Scheme.Cover.{u} Scheme.proetalePrecoverage Y, ∀ j,
        Mod.IsFree ((upperStar Ab.{u + 1} (C.f j)).obj (condensedRingObj Λ Y))
          (((upperStar Ab.{u + 1} (C.f j)).mapMod (condensedRingObj Λ Y)).obj N))
    (X : Scheme.{u}) [IsNoetherian X]
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
    (hM : IsConstructibleModuleObject (condensedRingObj Λ X) M)
    (h : ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (g : Spec (.of Ω) ⟶ X),
      IsZero ((CondensedRing.upperStar Λ g).obj M)) : IsZero M := by
  classical
  obtain ⟨S, hS⟩ := hM
  have (a : Fin S.n) : TopologicalSpace.NoetherianSpace (S.domain a) :=
    (S.immersion a).isEmbedding.isInducing.noetherianSpace
  let N (a : Fin S.n) := (CondensedRing.upperStar Λ (S.immersion a)).obj M
  have hN (a : Fin S.n) : IsLocallyFinitelyPresented
      (condensedRingObj Λ (S.domain a)) (N a) :=
    fibre_lfp_normalize Λ (S.immersion a) M (hS a)
  choose C hC using fun a ↦ htriv (S.domain a) (N a) (hN a)
  apply fibre_stratified_zero Λ X S M C _ h
  intro a j
  exact fibre_free_normalize Λ ((C a).f j) (N a) (hC a j)

end

/-- Exact pullback commutes naturally with cohomology, for the actual left derived
functor appearing in the statement. -/
private noncomputable def fibre_homologyIso
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X Y : Scheme.{u}} (g : Y ⟶ X) (n : ℤ) :
    DerivedCategory.homologyFunctor _ n ⋙ CondensedRing.upperStar Λ g ≅
      CondensedRing.moduleObjectDerivedPullback Λ g ⋙ DerivedCategory.homologyFunctor _ n :=
  (CondensedRing.upperStar Λ g).mapDerivedCategoryHomologyFunctorIso n ≪≫
    Functor.isoWhiskerRight
      (CondensedRing.leftDerivedUpperStarIsoMapDerivedCategory Λ g).symm _

/-- Geometric derived inverse images jointly detect zero objects and isomorphisms
between bounded constructible complexes for the two stated condensed coefficient rings.
The finite field has cardinality `p ^ a`; `hΛ` includes all p-th roots of unity in the
finite-subextension case. No finite-type hypothesis is imposed on a geometric point.

Source: latest blueprint, lem-fd-convolution-kernel.proof.md, Step 3.
(blueprint: lem-fd-condensed-geometric-fibre-conservativity)

Proof plan, following the DAG node verbatim:

1. A finite-type scheme over the field $k_0$ is Noetherian
[lem-weil-pbc-finite-type-over-noetherian]. Each stratum is topologically Noetherian because its
immersion is an embedding. Unpack stratified local finite presentation
[def-sfb-constructible-module, def-sfb-locally-finitely-presented]. The invertible cartesian
coefficient map [sk-prop-sfb-cartesian-coefficients] identifies raw restriction with the ordinary
coefficient-module pullback; transport local finite presentation through its inverse scalar
restriction.

2. For finite intermediate-field coefficients use `finite_lf` from the constructible Serre proof
[lem-weil-pbc-condensed-constructible-serre], which transports the local-triviality theorem
[lem-weil-pbc-condensed-lfp-local-triviality] across a universe lift. For the algebraic-closure
coefficients use `algcl_lf` from the same proof, which invokes the Qbar local-triviality theorem
[lem-weil-pbc-condensed-qbar-lfp-local-triviality]. Thus every normalized stratum restriction has
a pro-etale cover whose further normalized pullbacks are finite free
[def-sfb-finitely-presented-module].

3. A finite free coefficient module $M$ on a chart $Y$ is zero if all its geometric pullbacks
vanish. Rank zero is the empty biproduct. If $Y$ is empty, the empty-cover sheaf axiom makes every
underlying abelian sheaf zero. Otherwise choose a point $y$, an algebraic closure $\Omega$ of its
residue field [def-weil-algebraic-closure], and $g:\operatorname{Spec}\Omega\to Y$. The first
regular summand of a free module of rank $n+1$ is a split subobject of $M$; exact pullback
preserves this monomorphism, its target vanishes, so its source, the regular coefficient module on
$\operatorname{Spec}\Omega$, vanishes. The separably-closed-point equivalence
[lem-pe-point-module-pullback-equivalence] makes `upperStarFromPoint` fully faithful, hence
reflects vanishing of $\Lambda$; pulling $\Lambda$ back to $Y$ makes the regular module on $Y$,
hence $M$, zero.

4. Apply step 3 on every member of each stratum cover. Pullback composition
[det-def-sfb-module-pushforward-pullback] transports the vanishing hypothesis to those members, and
the normalized pullback/forgetful comparison identifies vanishing there with vanishing of the
underlying abelian inverse image along the composite chart-to-$X$ map. Noetherian finite-stratum
cover detection [lem-weil-pbc-noetherian-stratum-detection] makes the underlying sheaf zero, and
faithfulness of the forgetful functor makes the module zero.

5. For every scheme morphism $g$ the coefficient pullback is exact; its total left derived functor
[det-def-sfb-module-derived-pushpull] is canonically isomorphic to its termwise functor
[lem-weil-pbc-exact-functor-derived-factorization], which commutes naturally with cohomology
[lem-sp-exact-functor-preserves-homology]: $g^*H^n(-)\cong H^n(Lg^*(-))$.

6. If every $Lg^*K$ vanishes for bounded constructible $K$ [det-def-sfb-bounded-constructible], step
5 makes every $g^*H^n(K)$ zero, step 4 gives $H^n(K)=0$ for all $n$, and the derived cohomology
criterion [lem-weil-pbc-unbounded-derived-iso-cohomology] makes $K$ zero. Conversely the exact
termwise functor preserves zero objects.

7. For $v:K\to K'$, step 5 transfers invertibility of every $Lg^*v$ to every $g^*H^n(v)$. The
constructible Serre theorem [lem-weil-pbc-condensed-constructible-serre] makes kernel and cokernel
of $H^n(v)$ constructible; exact pullback identifies their pullbacks with kernel and cokernel of an
isomorphism, which vanish, so step 4 makes them zero and $H^n(v)$ is invertible. The cohomology
criterion makes $v$ invertible; the converse holds for every functor. -/
theorem condensed_geometric_pullback_conservativity
    (p ℓ a : ℕ) [Fact p.Prime] [Fact ℓ.Prime] (hne : p ≠ ℓ) (ha : 1 ≤ a)
    (k₀ : Type u) [Field k₀] [Finite k₀] [CharP k₀ p] (hk₀ : Nat.card k₀ = p ^ a)
    (Λ : Profinite.CondensedRing.{u}) [IsCommMonObj Λ.X]
    (hΛ : (∃ E : PadicAlgCl.FiniteIntermediateField ℓ,
      (∀ z : PadicAlgCl ℓ, z ^ p = 1 → z ∈ E.1) ∧
        Λ = Mon.mk (Profinite.continuousMapRingObj E.1)) ∨
      Λ = Mon.mk (Profinite.padicAlgClRingObj ℓ))
    (X : Scheme.{u}) [X.Over (Spec (.of k₀))]
    [IsSeparated (X ↘ Spec (.of k₀))]
    [LocallyOfFiniteType (X ↘ Spec (.of k₀))] [QuasiCompact (X ↘ Spec (.of k₀))] :
    (∀ K : BoundedConstructible (condensedRingObj Λ.X X),
      IsZero K.obj ↔ ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω]
        (g : Spec (.of Ω) ⟶ X),
        IsZero ((CondensedRing.moduleObjectDerivedPullback Λ.X g).obj K.obj)) ∧
    (∀ K K' : BoundedConstructible (condensedRingObj Λ.X X), ∀ (v : K.obj ⟶ K'.obj),
      IsIso v ↔ ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω]
        (g : Spec (.of Ω) ⟶ X),
        IsIso ((CondensedRing.moduleObjectDerivedPullback Λ.X g).map v)) := by
  classical
  have _ := hne
  have _ := ha
  have _ := hk₀
  have : IsNoetherian X :=
    { toIsLocallyNoetherian := LocallyOfFiniteType.isLocallyNoetherian
        (X ↘ Spec (.of k₀))
      toCompactSpace := QuasiCompact.compactSpace_of_compactSpace (X ↘ Spec (.of k₀)) }
  have htriv : ∀ (Y : Scheme.{u}) [TopologicalSpace.NoetherianSpace Y]
      (N : Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ.X Y)),
      IsLocallyFinitelyPresented (condensedRingObj Λ.X Y) N →
      ∃ C : Scheme.Cover.{u} Scheme.proetalePrecoverage Y, ∀ j,
        Mod.IsFree ((upperStar Ab.{u + 1} (C.f j)).obj (condensedRingObj Λ.X Y))
          (((upperStar Ab.{u + 1} (C.f j)).mapMod (condensedRingObj Λ.X Y)).obj N) := by
    rcases hΛ with ⟨E, _, rfl⟩ | rfl
    · exact finite_lf ℓ E
    · exact algcl_lf ℓ
  have hdetect := fibre_constructible_zero Λ.X htriv X
  have hkc (M N : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ.X X)) (f : M ⟶ N)
      (hM : IsConstructibleModuleObject (condensedRingObj Λ.X X) M)
      (hN : IsConstructibleModuleObject (condensedRingObj Λ.X X) N) :
      IsConstructibleModuleObject (condensedRingObj Λ.X X) (kernel f) ∧
      IsConstructibleModuleObject (condensedRingObj Λ.X X) (cokernel f) := by
    rcases hΛ with ⟨E, _, rfl⟩ | rfl
    · exact (isConstructibleModuleObject_serre_padicSubfield X ℓ E).1 M N f hM hN
    · exact (isConstructibleModuleObject_serre_padicAlgCl X ℓ).1 M N f hM hN
  constructor
  · intro K
    constructor
    · intro hK Ω _ _ g
      exact ((CondensedRing.upperStar Λ.X g).mapDerivedCategory.map_isZero hK).of_iso
        ((CondensedRing.leftDerivedUpperStarIsoMapDerivedCategory Λ.X g).app K.obj)
    · intro hK
      apply DerivedCategory.isZero_of_forall_isZero_homology
      intro n
      apply hdetect _ (K.property.2 n)
      intro Ω _ _ g
      exact ((DerivedCategory.homologyFunctor _ n).map_isZero (hK Ω g)).of_iso
        ((fibre_homologyIso Λ.X g n).app K.obj)
  · intro K K' v
    constructor
    · intro hv Ω _ _ g
      let := hv
      infer_instance
    · intro hv
      rw [DerivedCategory.isIso_iff]
      intro n
      let w := (DerivedCategory.homologyFunctor _ n).map v
      have hw (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (g : Spec (.of Ω) ⟶ X) :
          IsIso ((CondensedRing.upperStar Λ.X g).map w) := by
        have := hv Ω g
        exact (NatIso.isIso_map_iff (fibre_homologyIso Λ.X g n) v).2
          (by dsimp; infer_instance)
      obtain ⟨hk, hc⟩ := hkc _ _ w (K.property.2 n) (K'.property.2 n)
      have hkzero : IsZero (kernel w) := by
        apply hdetect _ hk
        intro Ω _ _ g
        have := hw Ω g
        exact (isZero_kernel_of_mono ((CondensedRing.upperStar Λ.X g).map w)).of_iso
          (PreservesKernel.iso (CondensedRing.upperStar Λ.X g) w)
      have hczero : IsZero (cokernel w) := by
        apply hdetect _ hc
        intro Ω _ _ g
        have := hw Ω g
        exact (isZero_cokernel_of_epi ((CondensedRing.upperStar Λ.X g).map w)).of_iso
          (PreservesCokernel.iso (CondensedRing.upperStar Λ.X g) w)
      let := Preadditive.mono_of_isZero_kernel w hkzero
      let := Preadditive.epi_of_isZero_cokernel w hczero
      exact isIso_of_mono_of_epi w

end AlgebraicGeometry.ProEtale
