/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.DeligneLaumon.CondensedDualSingle
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
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Hom
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.LocallyFreeDualizable
import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.ClosedTriangulated
import WeilConjectures.SixFunctors.Etale.Derived.LisseFieldDual

/-! # Objectwise cohomology of bounded native duals -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
universe v u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open CategoryTheory.Pretriangulated
open scoped CategoryTheory.Obj
namespace DerivedCategory
variable {A : Type u} [Category.{v} A] [Abelian A] [IsGrothendieckAbelian.{v} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [MonoidalClosed A] [BraidedCategory A]
  [HasDerivedCategory.{v} A] [Abelian.HasFunctorialFlatResolution A]

private abbrev du : (DerivedCategory A)ᵒᵖ ⥤ DerivedCategory A :=
  MonoidalClosed.internalHom.flip.obj (𝟙_ _)

omit [IsGrothendieckAbelian.{v} A] [BraidedCategory A] [HasDerivedCategory.{v} A]
  [Abelian.HasFunctorialFlatResolution A] in
private theorem ihom_isZero {E : A} (hz : IsZero E) (F : A) :
    IsZero ((ihom E).obj F) := by
  rw [IsZero.iff_id_eq_zero]
  apply MonoidalClosed.uncurry_injective
  have ht : IsZero (E ⊗ (ihom E).obj F) := by
    rw [IsZero.iff_id_eq_zero, ← id_whiskerRight, hz.eq_of_src (𝟙 E) 0,
      MonoidalPreadditive.zero_whiskerRight]
  exact ht.eq_of_src _ _

private theorem dualHom_isZero (C : DerivedCategory A) (q : ℤ)
    (h : Nonempty ((homologyFunctor A q).obj (du.obj (op C)) ≅
      (ihom ((homologyFunctor A (-q)).obj C)).obj (𝟙_ _)))
    (hz : IsZero ((homologyFunctor A (-q)).obj C)) :
    IsZero ((homologyFunctor A q).obj (du.obj (op C))) :=
  (ihom_isZero hz _).of_iso h.some

private theorem dualHom_map {C Y : DerivedCategory A} (f : C ⟶ Y) (q : ℤ)
    [IsIso ((homologyFunctor A q).map (du.map f.op))]
    [IsIso ((homologyFunctor A (-q)).map f)]
    (hY : Nonempty ((homologyFunctor A q).obj (du.obj (op Y)) ≅
      (ihom ((homologyFunctor A (-q)).obj Y)).obj (𝟙_ _))) :
    Nonempty ((homologyFunctor A q).obj (du.obj (op C)) ≅
      (ihom ((homologyFunctor A (-q)).obj C)).obj (𝟙_ _)) :=
  ⟨(asIso ((homologyFunctor A q).map (du.map f.op))).symm ≪≫ hY.some ≪≫
    ((MonoidalClosed.internalHom).mapIso
      (asIso ((homologyFunctor A (-q)).map f)).op).app (𝟙_ _)⟩

private theorem dualHom_map' {X C : DerivedCategory A} (f : X ⟶ C) (q : ℤ)
    [IsIso ((homologyFunctor A q).map (du.map f.op))]
    [IsIso ((homologyFunctor A (-q)).map f)]
    (hX : Nonempty ((homologyFunctor A q).obj (du.obj (op X)) ≅
      (ihom ((homologyFunctor A (-q)).obj X)).obj (𝟙_ _))) :
    Nonempty ((homologyFunctor A q).obj (du.obj (op C)) ≅
      (ihom ((homologyFunctor A (-q)).obj C)).obj (𝟙_ _)) :=
  ⟨asIso ((homologyFunctor A q).map (du.map f.op)) ≪≫ hX.some ≪≫
    ((MonoidalClosed.internalHom).mapIso
      (asIso ((homologyFunctor A (-q)).map f)).symm.op).app (𝟙_ _)⟩

private theorem dualHom_step {X C Y : DerivedCategory A}
    (f : X ⟶ C) (g : C ⟶ Y) (δ : Y ⟶ X⟦(1 : ℤ)⟧)
    (ht : Triangle.mk f g δ ∈ distTriang _) (m : ℤ)
    (hXz : ∀ q, m < q → IsZero ((homologyFunctor A q).obj X))
    (hYz : ∀ q, q ≠ m + 1 → IsZero ((homologyFunctor A q).obj Y))
    (hf : ∀ q, q ≤ m → IsIso ((homologyFunctor A q).map f))
    (hg : ∀ q, m + 1 ≤ q → IsIso ((homologyFunctor A q).map g))
    (hXd : ∀ q, Nonempty ((homologyFunctor A q).obj (du.obj (op X)) ≅
      (ihom ((homologyFunctor A (-q)).obj X)).obj (𝟙_ _)))
    (hYd : ∀ q, Nonempty ((homologyFunctor A q).obj (du.obj (op Y)) ≅
      (ihom ((homologyFunctor A (-q)).obj Y)).obj (𝟙_ _))) (q : ℤ) :
    Nonempty ((homologyFunctor A q).obj (du.obj (op C)) ≅
      (ihom ((homologyFunctor A (-q)).obj C)).obj (𝟙_ _)) := by
  obtain ⟨w, hw⟩ := exists_distinguished_ihom_pre (Triangle.mk f g δ) ht (𝟙_ _)
  by_cases hq : q ≤ -(m + 1)
  · have : IsIso ((homologyFunctor A q).map (du.map g.op)) :=
      isIso_homologyMap_mor₁_of_isZero _ hw (q - 1) q (by omega)
        (dualHom_isZero X _ (hXd _) (hXz _ (by omega)))
        (dualHom_isZero X _ (hXd _) (hXz _ (by omega)))
    have := hg (-q) (by omega)
    exact dualHom_map g q (hYd q)
  · have : IsIso ((homologyFunctor A q).map (du.map f.op)) :=
      isIso_homologyMap_mor₂_of_isZero _ hw q (q + 1) rfl
        (dualHom_isZero Y _ (hYd _) (hYz _ (by omega)))
        (dualHom_isZero Y _ (hYd _) (hYz _ (by omega)))
    have := hf (-q) (by omega)
    exact dualHom_map' f q (hXd q)

private theorem dualHom_concentrated (C : DerivedCategory A) (a : ℤ)
    (hC : ∀ q, IsDualizable ((homologyFunctor A q).obj C))
    (hz : ∀ q, q ≠ a → IsZero ((homologyFunctor A q).obj C)) :
    ∀ q, Nonempty ((homologyFunctor A q).obj (du.obj (op C)) ≅
      (ihom ((homologyFunctor A (-q)).obj C)).obj (𝟙_ _)) := by
  have : C.IsGE a := (isGE_iff C a).mpr (fun q hq ↦ hz q hq.ne)
  have : C.IsLE a := (isLE_iff C a).mpr (fun q hq ↦ hz q hq.ne')
  obtain ⟨E, ⟨e⟩⟩ := C.exists_iso_singleFunctor_obj_of_isGE_of_isLE a
  let eE : (homologyFunctor A a).obj C ≅ E :=
    (homologyFunctor A a).mapIso e ≪≫ (singleFunctorCompHomologyFunctorIso A a).app E
  obtain ⟨eD⟩ := nonempty_ihom_single_unit E ((hC a).of_iso eE) a
  let e' : du.obj (op C) ≅ (singleFunctor A (-a)).obj ((ihom E).obj (𝟙_ _)) :=
    du.mapIso e.symm.op ≪≫ eD
  intro q
  by_cases hq : q = -a
  · subst hq
    rw [neg_neg]
    exact ⟨(homologyFunctor A (-a)).mapIso e' ≪≫
      (singleFunctorCompHomologyFunctorIso A (-a)).app _ ≪≫
      ((MonoidalClosed.internalHom).mapIso eE.op).app (𝟙_ _)⟩
  · refine ⟨IsZero.iso ?_ (ihom_isZero (hz _ (by omega)) _)⟩
    refine IsZero.of_iso ?_ ((homologyFunctor A q).mapIso e')
    obtain hq | hq := lt_or_gt_of_ne hq
    · exact isZero_of_isGE _ (-a) q hq
    · exact isZero_of_isLE _ (-a) q hq

/-- The objectwise, untwisted bounded dual-cohomology formula for any native
coefficient category. Source: `lem-fin-lisse-field-dual`, bounded induction in
Step 2 of `thm-a1-curve-perverse-heart`
(blueprint: lem-per-condensed-dual-cohomology-objects).

Proof: induction on the length `n` of the cohomological interval. At length zero
identify the complex with its sole cohomology in that degree and apply the
single-degree dual calculation. At the successor step use the truncation triangle
with lower part in degrees at most `a+n` and upper part concentrated in degree
`a+n+1`. The long exact sequence identifies the cohomology of each truncation
with that of the original complex in its range. Apply induction to the lower
part and the single-degree case to the upper part. Internal Hom reverses the
triangle. For degree `q ≤ -(a+n+1)` the lower-part contribution in the dual
sequence vanishes, and otherwise the upper-part contribution vanishes. The two
resulting edge isomorphisms give the assertion. Zero cohomology is dualizable,
so the induction includes empty intervals and the zero complex. This statement
only asserts objectwise isomorphisms; functorial comparisons are a further step.
-/
theorem nonempty_ihom_unit_homology (n : ℕ) : ∀ (C : DerivedCategory A) (a : ℤ),
    (∀ q, IsDualizable ((homologyFunctor A q).obj C)) →
    (∀ q, q < a ∨ a + n < q → IsZero ((homologyFunctor A q).obj C)) →
    ∀ q, Nonempty ((homologyFunctor A q).obj ((ihom C).obj (𝟙_ _)) ≅
      (ihom ((homologyFunctor A (-q)).obj C)).obj (𝟙_ _)) := by
  induction n with
  | zero =>
    intro C a hC hz
    exact dualHom_concentrated C a hC fun q hq ↦ hz q (by omega)
  | succ n ih =>
    intro C a hC hz
    obtain ⟨X, Y, hX, hY, f, g, δ, ht⟩ :=
      (TStructure.t (C := A)).exists_triangle C (a + n) (a + n + 1) rfl
    have hXz : ∀ q, a + n < q → IsZero ((homologyFunctor A q).obj X) :=
      (isLE_iff X (a + n)).mp ⟨hX⟩
    have hYz : ∀ q, q < a + n + 1 → IsZero ((homologyFunctor A q).obj Y) :=
      (isGE_iff Y (a + n + 1)).mp ⟨hY⟩
    have hf (q : ℤ) (hq : q ≤ a + n) : IsIso ((homologyFunctor A q).map f) :=
      isIso_homologyMap_mor₁_of_isZero _ ht (q - 1) q (by omega)
        (hYz _ (by omega)) (hYz _ (by omega))
    have hg (q : ℤ) (hq : a + n + 1 ≤ q) : IsIso ((homologyFunctor A q).map g) :=
      isIso_homologyMap_mor₂_of_isZero _ ht q (q + 1) rfl
        (hXz _ (by omega)) (hXz _ (by omega))
    have hXl (q : ℤ) : IsDualizable ((homologyFunctor A q).obj X) := by
      by_cases hq : q ≤ a + n
      · have := hf q hq
        exact (hC q).of_iso (asIso ((homologyFunctor A q).map f)).symm
      · exact ⟨hasRightDualOfIsZero (hXz q (by omega))⟩
    have hYl (q : ℤ) : IsDualizable ((homologyFunctor A q).obj Y) := by
      by_cases hq : a + n + 1 ≤ q
      · have := hg q hq
        exact (hC q).of_iso (asIso ((homologyFunctor A q).map g))
      · exact ⟨hasRightDualOfIsZero (hYz q (by omega))⟩
    have hXz' (q : ℤ) (hq : q < a ∨ a + n < q) :
        IsZero ((homologyFunctor A q).obj X) := by
      obtain hq | hq := hq
      · have := hf q (by omega)
        exact (hz q (.inl hq)).of_iso (asIso ((homologyFunctor A q).map f))
      · exact hXz q hq
    have hYz' (q : ℤ) (hq : q ≠ a + n + 1) :
        IsZero ((homologyFunctor A q).obj Y) := by
      obtain hq | hq := lt_or_gt_of_ne hq
      · exact hYz q hq
      · have := hg q (by omega)
        exact (hz q (.inr (by omega))).of_iso (asIso ((homologyFunctor A q).map g)).symm
    exact dualHom_step f g δ ht (a + n) hXz hYz' hf hg
      (ih X a hXl hXz') (dualHom_concentrated Y (a + n + 1) hYl hYz')

end DerivedCategory

namespace AlgebraicGeometry.ProEtale.CondensedRing

/-- Objectwise cohomology of an untwisted bounded native lisse dual.
Source: Step 2, the bounded lisse cohomology calculation
(blueprint: lem-per-condensed-dual-cohomology-objects).

Proof: the lower and upper bounds give an interval of natural-number length
`max (b-a) 0`. Each lisse cohomology module is locally free under the raw
module inverse-image convention, hence dualizable. Apply the bounded induction
above. It includes arbitrary condensed commutative coefficients and the empty
scheme; neither a field-valued section ring nor positive characteristic is used.
-/
theorem nonempty_ihom_unit_homology_of_lisse
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X : Scheme.{u}}
    (C : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ X))) (hb : DerivedCategory.TStructure.t.bounded C)
    (hl : ∀ n : ℤ, IsLisseCoefficientModule Λ
      ((DerivedCategory.homologyFunctor _ n).obj C)) (q : ℤ) :
    Nonempty ((DerivedCategory.homologyFunctor _ q).obj ((ihom C).obj (𝟙_ _)) ≅
      (ihom ((DerivedCategory.homologyFunctor _ (-q)).obj C)).obj (𝟙_ _)) := by
  obtain ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ := hb
  have hd (n : ℤ) : IsDualizable ((DerivedCategory.homologyFunctor _ n).obj C) := by
    have hraw : IsLocallyFree (condensedRingObj Λ X)
        ((DerivedCategory.homologyFunctor _ n).obj C) := by
      obtain ⟨U, hU⟩ := hl n
      exact ⟨U, fun i ↦ (freeAt_iff_standard Λ (U.f i) _).mpr (hU i)⟩
    exact hraw.isDualizable
  apply DerivedCategory.nonempty_ihom_unit_homology (Int.toNat (b - a)) C a hd
  intro n hn
  obtain hn | hn := hn
  · exact (DerivedCategory.isGE_iff C a).mp ha n hn
  · apply (DerivedCategory.isLE_iff C b).mp hb n
    omega

end AlgebraicGeometry.ProEtale.CondensedRing
