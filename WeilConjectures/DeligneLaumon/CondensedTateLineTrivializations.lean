/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SecSmoothPurity.TransportTensor
public import WeilConjectures.AlgebraicGeometry.CoefficientHeartStratificationDefs
import WeilConjectures.DeligneLaumon.CondensedDualSingle
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
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.IntegralLisseDerivedAux
import WeilConjectures.PoincareDuality.IntegralTateBasis
import all WeilConjectures.CategoryTheory.ModuleObjects.ScalarExtensionMonoidal
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LocallyFreeTensor

/-! # Simultaneous local bases for all positive condensed Tate powers -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale.PurityTransport
open CondensedRing

private theorem normalized_unit
    (R : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj R] [IsCommMonObj R] {X Y : Scheme.{u}} (f : X ⟶ Y)
    (M : Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj R Y))
    (e : ((upperStar Ab.{u + 1} f).mapMod (condensedRingObj R Y)).obj M ≅ 𝟙_ _) :
    Nonempty ((CondensedRing.upperStar R f).obj M ≅ 𝟙_ _) := by
  exact ⟨(Mod.extendScalars (condensedPullbackHom R f)).mapIso e ≪≫
    Mod.unitComparisonIso (condensedPullbackHom R f)⟩

private theorem extended_unit
    {R S : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
    [MonObj R] [IsCommMonObj R] [MonObj S] [IsCommMonObj S]
    (a : R ⟶ S) [IsMonHom a] {X Y : Scheme.{u}} (f : X ⟶ Y)
    (M : Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj R Y))
    (e : (CondensedRing.upperStar R f).obj M ≅ 𝟙_ _) :
    Nonempty ((CondensedRing.upperStar S f).obj
      ((Mod.extendScalars (coefficientMap a Y)).obj M) ≅ 𝟙_ _) := by
  exact ⟨(CondensedRing.pullIso a f).symm.app M ≪≫
    (Mod.extendScalars (coefficientMap a X)).mapIso e ≪≫
      Mod.unitComparisonIso (coefficientMap a X)⟩

private theorem powers_unit {C D : Type (u + 2)} [Category C] [Category D]
    [MonoidalCategory C] [MonoidalCategory D] (F : C ⥤ D) [F.Monoidal]
    (L : C) (e : F.obj L ≅ 𝟙_ D) (d : ℕ) :
    Nonempty (F.obj (Nat.rec (𝟙_ C) (fun _ P ↦ P ⊗ L) d) ≅ 𝟙_ D) := by
  induction d with
  | zero => exact ⟨(Functor.Monoidal.εIso F).symm⟩
  | succ d hd =>
    obtain ⟨ed⟩ := hd
    exact ⟨(Functor.Monoidal.μIso F _ _).symm ≪≫ tensorIso ed e ≪≫ λ_ (𝟙_ _)⟩

private theorem line_eq_rec (ell : ℕ) [Fact ell.Prime] (c : Coefficient ell)
    (X : Scheme.{u}) (d : ℕ) :
    c.line ell X d = Nat.rec (𝟙_ _) (fun _ P ↦ P ⊗ c.firstLine ell X) d := by
  induction d with
  | zero => rfl
  | succ d hd => exact congrArg (fun P ↦ P ⊗ c.firstLine ell X) hd

/-- One pro-etale cover trivializes every positive Tate power for each presentation.
Source: Step 2 of `thm-a1-curve-perverse-heart`, the Tate-line rank-one calculation
(blueprint: lem-per-condensed-tate-line-trivializations).

Proof: invertibility in every residue field gives invertibility in global sections.
Take the existing compatible integral-root basis cover. Extension along the
coefficient pullback map converts its raw module trivializations into normalized
integral ones. The scalar-pull comparison then identifies the pullback of the
coefficient first line with extension of the integral trivialization. Scalar
extension sends the unit to the unit. On this same cover, monoidal inverse image
and induction identify each tensor power with the unit, using the inverse unit
constraint at power zero and the left unitor in the successor step. Thus neither
a choice of a different cover for each power nor a characteristic assumption is
hidden; the empty scheme and power zero are included.
-/
theorem line_locally_unit (ell : ℕ) [Fact ell.Prime] (c : Coefficient ell)
    (X : Scheme.{u}) [∀ x : X, Invertible (ell : X.residueField x)] :
    ∃ C : Scheme.Cover.{u} Scheme.proetalePrecoverage X, ∀ i : C.I₀, ∀ d : ℕ,
      Nonempty ((CondensedRing.upperStar (c.obj ell) (C.f i)).obj (c.line ell X d) ≅
        𝟙_ _) := by
  classical
  have hInv : IsUnit (ell : Γ(X, ⊤)) := by
    apply X.toRingedSpace.isUnit_of_isUnit_germ
    intro x hx
    change IsUnit ((X.presheaf.germ ⊤ x hx).hom (ell : Γ(X, ⊤)))
    rw [map_natCast]
    apply (isUnit_map_iff (IsLocalRing.residue (X.presheaf.stalk x)) _).mp
    simpa only [map_natCast] using isUnit_of_invertible (ell : X.residueField x)
  obtain ⟨C, hC⟩ := tateModule_locally_trivial X ell hInv
  refine ⟨C, fun i ↦ ?_⟩
  obtain ⟨e⟩ := hC i
  obtain ⟨ei⟩ := normalized_unit (Profinite.continuousMapRingObj ℤ_[ell])
    (C.f i) (tateModule X ell) e
  obtain ⟨efirst⟩ := extended_unit (c.integralMap ell) (C.f i) (tateModule X ell) ei
  intro d
  rw [line_eq_rec]
  exact powers_unit (CondensedRing.upperStar (c.obj ell) (C.f i))
    (c.firstLine ell X) efirst d

/-- The ordinary lisse dual twisted by a positive Tate power is lisse and detects zero.
Source: Step 2 of `thm-a1-curve-perverse-heart`, finite free duals and Tate powers
(blueprint: lem-per-condensed-tate-line-trivializations).

Proof: ordinary lisse duality and double duality give lisse preservation and zero
detection before twisting. The preceding cover makes every Tate power the unit.
On this cover the tensor product is isomorphic to the pulled-back ordinary dual.
Local freeness descends by refining its finite-free covers. Vanishing descends
because inverse images on a cover jointly detect zero. Conversely tensoring a
zero object gives zero. These arguments require no uniform rank and include
zero rank, zero power and the empty scheme.
-/
theorem linear_dual_twist_properties (ell : ℕ) [Fact ell.Prime] (c : Coefficient ell)
    (X : Scheme.{u}) [∀ x : X, Invertible (ell : X.residueField x)]
    (d : ℕ)
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj (c.obj ell) X))
    (hM : IsLisseCoefficientModule (c.obj ell) M) :
    IsLisseCoefficientModule (c.obj ell) (((ihom M).obj (𝟙_ _)) ⊗ c.line ell X d) ∧
      (IsZero (((ihom M).obj (𝟙_ _)) ⊗ c.line ell X d) ↔ IsZero M) := by
  obtain ⟨hd, hz⟩ := CondensedRing.lisse_dual_properties (c.obj ell) M hM
  obtain ⟨C, hC⟩ := line_locally_unit ell c X
  let D := (ihom M).obj (𝟙_ _)
  let L := c.line ell X d
  have e (i : C.I₀) :
      Nonempty ((CondensedRing.upperStar (c.obj ell) (C.f i)).obj (D ⊗ L) ≅
        (CondensedRing.upperStar (c.obj ell) (C.f i)).obj D) := by
    obtain ⟨ei⟩ := hC i d
    exact ⟨(Functor.Monoidal.μIso (CondensedRing.upperStar (c.obj ell) (C.f i)) _ _).symm ≪≫
      tensorIso (Iso.refl _) ei ≪≫ ρ_ _⟩
  have hl : IsLisseCoefficientModule (c.obj ell) (D ⊗ L) := by
    apply locFree_of_cover (D ⊗ L) C
    intro i
    exact locFree_iso (e i).some (locFree_pullback (c.obj ell) (C.f i) D hd)
  refine ⟨hl, ?_⟩
  constructor
  · intro h
    apply hz.mp
    apply CondensedRing.isZero_of_forall_isZero_upperStar_cover C
    intro i
    exact ((CondensedRing.upperStar (c.obj ell) (C.f i)).map_isZero h).of_iso (e i).some.symm
  · intro h
    exact (tensorRight L).map_isZero (hz.mpr h)

end AlgebraicGeometry.ProEtale.PurityTransport
