/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Vector.VectorPurityScalarSingle
public import WeilConjectures.Algebra.Homology.DerivedChangeOfRingsCochainModel
public import WeilConjectures.Algebra.Homology.DerivedChangeOfRingsIndependentCoefficients
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
public import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
public import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.Limits.EssentiallySmall
public import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived
public import Mathlib.CategoryTheory.Adjunction.Additive
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
public import WeilConjectures.FromJoel.Algebra.Homology.BifunctorSingle
public import WeilConjectures.FromJoel.Algebra.Homology.ShortComplex.HomologicalComplex
public import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
public import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
public import Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
public import Mathlib.RingTheory.Flat.CategoryTheory
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.CategoryTheory.Limits.Final
public import WeilConjectures.Algebra.Homology.SheafRingDerivedCoefficientAdjunction
public import WeilConjectures.Algebra.Homology.Site.SiteTensorFunctorialitySupplement
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction
public import WeilConjectures.Algebra.Homology.SheafRingCoefficientOrdinaryAdjunction
public import WeilConjectures.Algebra.Homology.SheafRingDerivedHomComparison
public import WeilConjectures.CategoryTheory.DerivedCategory.ResolvingClassEssentialConstancy
public import WeilConjectures.CategoryTheory.DerivedCategory.DerivedAdjunctionCompatibility
public import Mathlib.CategoryTheory.MorphismProperty.Comma
public import Mathlib.CategoryTheory.Functor.Derived.LeftDerived
public import Mathlib.CategoryTheory.Functor.Derived.RightDerived
public import WeilConjectures.CategoryTheory.DerivedCategory.EssentiallyConstantInd
public import Mathlib.CategoryTheory.Filtered.Basic
public import Mathlib.CategoryTheory.Limits.Cones
public import WeilConjectures.CategoryTheory.DerivedCategory.EssentiallyConstantPro
public import Mathlib.Algebra.Homology.DerivedCategory.Fractions
public import Mathlib.CategoryTheory.Functor.Derived.Adjunction
public import Mathlib.CategoryTheory.Functor.KanExtension.Preserves
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedPointwiseKanBridge
public import WeilConjectures.Algebra.Homology.QuasiIsoSaturatedTriangulated
public import Mathlib.CategoryTheory.Functor.Derived.PointwiseRightDerived
public import WeilConjectures.AlgebraicGeometry.FiniteEtaleTwistLine
public import WeilConjectures.AlgebraicGeometry.FiniteEtaleTateTwist
public import WeilConjectures.AlgebraicGeometry.Sites.Kummer
public import Mathlib.Algebra.Module.ZMod
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
public import Mathlib.CategoryTheory.Sites.Monoidal
public import WeilConjectures.AlgebraicGeometry.EtaleConstantRingModuleEquivalence
public import WeilConjectures.ConstructibleSheaf.Defs
public import WeilConjectures.EtaleCohomology.TateTwist.Sheaf
public import WeilConjectures.ConstructibleSheaf.Pullback
public import WeilConjectures.Algebra.Homology.CanonicalTensorPullbackOfUniverses.RingedTopoiCanonicalTensorPullbackOfUniverses
public import WeilConjectures.AlgebraicGeometry.FiniteSmoothPurity.FiniteSmoothCoefficientArrows
public import WeilConjectures.AlgebraicGeometry.Finite.Tate.FiniteTateSiteDescent
public import WeilConjectures.SmoothPurity.PurityFiniteSetting.Tate.FiniteTateScalarSourceData
import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Homology.BifunctorShift
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.CategoryTheory.Sites.Equivalence
import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import Mathlib.CategoryTheory.Limits.EssentiallySmall
import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
import WeilConjectures.Algebra.Homology.Site.SiteTensorFunctorialitySupplement
import WeilConjectures.Mathlib.Algebra.Homology.Monoidal
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import all Mathlib.Algebra.Homology.DerivedCategory.Basic
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import WeilConjectures.SmoothPurity.PurityFiniteSetting.Tate.FiniteTateScalarSourceExistence
import all WeilConjectures.AlgebraicGeometry.EtaleFiniteTwistPullbackRest
import all Mathlib.AlgebraicGeometry.Sites.Etale
import all Mathlib.AlgebraicGeometry.Scheme
import all WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
import all WeilConjectures.AlgebraicGeometry.FiniteEtaleTateSheaf
import all WeilConjectures.AlgebraicGeometry.FiniteEtaleTateTwist
import all WeilConjectures.AlgebraicGeometry.Sites.Kummer
import all Mathlib.Algebra.Module.ZMod
import all Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
import all Mathlib.CategoryTheory.Sites.Monoidal
import all WeilConjectures.AlgebraicGeometry.EtaleConstantRingModuleEquivalence
import all WeilConjectures.CategoryTheory.RingedSiteModules
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHom
import all WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.TensorColimits
import all WeilConjectures.AlgebraicGeometry.EtaleSheaves
import all WeilConjectures.AlgebraicGeometry.DerivedCategories
import all WeilConjectures.AlgebraicGeometry.RingedTopoiDerivedPullback
import all WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Flat
import all WeilConjectures.CategoryTheory.AlgebraicInverseImage
import all Mathlib.Algebra.Category.ModuleCat.Sheaf
import all Mathlib.Algebra.Category.Ring.Limits
import all Mathlib.Algebra.Category.Grp.Limits
import all Mathlib.CategoryTheory.Sites.Whiskering
import all Mathlib.CategoryTheory.Sites.Equivalence
import all Mathlib.CategoryTheory.Functor.Derived.LeftDerived
import all WeilConjectures.Algebra.Homology.KFlatResolution
import all WeilConjectures.Algebra.Homology.ChangeOfRingsKFlatQuasiIso
import all WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
import all WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import all Mathlib.Algebra.Category.Grp.FilteredColimits
import all Mathlib.Algebra.Homology.BifunctorShift
import all Mathlib.Algebra.Homology.QuasiIso
import all Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import all Mathlib.CategoryTheory.Limits.EssentiallySmall
import all WeilConjectures.AlgebraicGeometry.KFlatRingedToposPullback
import all WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import all WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import all Mathlib.CategoryTheory.Limits.ExactFunctor
import all WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import all Mathlib.Algebra.Homology.HomologicalComplex
import all Mathlib.Algebra.Homology.Additive
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.RingedToposFlatPullback
import all WeilConjectures.CategoryTheory.AlgebraicInverseImageOfUniverses
import all Mathlib.CategoryTheory.Types.Basic
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatAlgebraicInverseImageOfUniverses
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatEquationalCriterionOfUniverses
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatLocalRelationsOfUniverses
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
import all WeilConjectures.CategoryTheory.Sites.WeakSheafifyAddCommGrpLeftExact
import all Mathlib.Algebra.Category.ModuleCat.Presheaf.Submodule
import all Mathlib.LinearAlgebra.TensorProduct.Vanishing
import all Mathlib.RingTheory.TensorProduct.DirectLimitFG
import all Mathlib.LinearAlgebra.TensorProduct.Finiteness
import all Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import all Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
import all WeilConjectures.CategoryTheory.Sites.InverseImageLocalFamilies
import all Mathlib.CategoryTheory.Sites.Sheaf
import all Mathlib.CategoryTheory.Sites.LocallyBijective
import all Mathlib.CategoryTheory.Sites.Limits
import all Mathlib.CategoryTheory.Adjunction.Limits
import all Mathlib.CategoryTheory.Limits.Types.Pullbacks
import all Mathlib.CategoryTheory.Functor.EpiMono
import all Mathlib.CategoryTheory.Limits.Types.Equalizers
import all Mathlib.CategoryTheory.Limits.Preserves.Shapes.Equalizers
import all Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.ScalarTensorComparisonOfUniverses
import all Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
import all Mathlib.Algebra.Homology.HomotopyCategory.MappingCone
import all Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import all WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
import all WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import all WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
import all Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import all Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import all WeilConjectures.Algebra.Homology.RingedToposAdaptedFlatResolution
import all WeilConjectures.Algebra.Homology.RingedToposPullbackFilteredColimits
import all WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import all Mathlib.CategoryTheory.Sites.PreservesSheafification
import all Mathlib.CategoryTheory.Limits.Preserves.Limits
import all WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import all Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import all Mathlib.RingTheory.Flat.CategoryTheory
import all Mathlib.CategoryTheory.ObjectProperty.ColimitsOfShape
import all Mathlib.Algebra.Homology.Embedding.CochainComplex
import all Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import all Mathlib.Algebra.Category.Grp.AB
import all WeilConjectures.Algebra.Homology.RingedToposAcyclicKFlatPullback
import all WeilConjectures.Algebra.Homology.BoundedFlatIndependentCoefficients
import all Mathlib.CategoryTheory.Monoidal.Preadditive
import all WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import all Mathlib.CategoryTheory.Monoidal.Closed.Basic
import all WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import all Mathlib.CategoryTheory.Sites.EpiMono
import all Mathlib.CategoryTheory.Adjunction.Additive
import all Mathlib.Algebra.Category.Grp.EpiMono
import all Mathlib.Algebra.Category.Grp.Abelian
import all Mathlib.CategoryTheory.Sites.Abelian
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.MonoidalClosed
import all WeilConjectures.Algebra.Homology.Site.SiteDerivedTensorDescent
import all WeilConjectures.SixFunctors.Etale.UpperLowerStar.Coherence
import all WeilConjectures.SixFunctors.Etale.UpperLowerStar.Monoidal
import all WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal
import all WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal.TensorShiftIso
import all WeilConjectures.SixFunctors.Etale.UpperLowerStar.FlatModuleCat
import all Mathlib.CategoryTheory.Abelian.Refinements
import all Mathlib.Algebra.Homology.ShortComplex.Exact
import all WeilConjectures.AlgebraicGeometry.Scalar.ScalarPullbackIsoUniqueness

/-! # Unique normalized finite Tate scalar comparisons -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.defeqAttrib.useBackward false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.Functor
attribute [local irreducible] Functor.leftAdjoint Functor.rightAdjoint
  Functor.leftDerivedFunctor Functor.mapDerivedCategory
  ProEtale.pbcFixedScalarExtension Etale.upperStar Etale.lowerStar
namespace WeilConjectures.PurityFiniteSetting
variable {A B : Type (u + 1)} [CommRing A] [CommRing B]

attribute [local instance 20000] Etale.sheafMonoidalCategory
attribute [local irreducible] purityScalarSingleMap purityScalarUnitMap
  finiteTateScalarZeroIso finiteTateScalarLineMap finiteTateScalarSourceMap
  IsFiniteTateScalarBalancing IsFiniteTateScalarLineNormalized
  IsFiniteTateScalarSourceInvertible IsFiniteTateScalarSourceUnitNormalized
  IsFiniteTateScalarSourceZeroNormalized

private theorem balancing_unique
    (φ : A →+* B) (N : ℕ) (hA : (N : A) = 0) (hB : (N : B) = 0)
    (X : Scheme.{u})
    (β γ : ∀ r : ℕ,
      (Etale.purityScalarSheaf φ X).obj (Scheme.finiteEtaleTateTwist X N A hA r) ≅
        Scheme.finiteEtaleTateTwist X N B hB r)
    (hβ : IsFiniteTateScalarBalancing φ N hA hB X β)
    (hγ : IsFiniteTateScalarBalancing φ N hA hB X γ) : β = γ := by
  unfold IsFiniteTateScalarBalancing at hβ hγ
  have h1 : (β 1).hom = (γ 1).hom := by
    apply (Etale.purityScalarSheafAdjunction φ X).homEquiv _ _ |>.injective
    apply (Scheme.lineHomEquiv X N A hA _).injective
    ext U z
    simp only [Scheme.lineHomEquiv_generator]
    have hb := hβ.1 1 U 1 1 (fun _ ↦ z)
    have hg := hγ.1 1 U 1 1 (fun _ ↦ z)
    simp only [one_smul, map_one, one_mul, Scheme.finiteTateEtalePowerGenerator] at hb hg
    exact hb.trans hg.symm
  funext r
  apply Iso.ext
  induction r with
  | zero => exact hβ.2.1.trans hγ.2.1.symm
  | succ r hr =>
    cases r with
    | zero => exact h1
    | succ r => rw [hβ.2.2 r, hγ.2.2 r, hr, h1]

private theorem single_map_eq (φ : A →+* B) (X : Scheme.{u})
    (M : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)) :
    purityScalarSingleMap φ X M = Etale.FiniteSmoothPurity.scalarSingleMap φ X M := by
  rfl
private theorem single_from_rep_isIso
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D]
    (F : C ⥤ D) [F.Additive] (E : DerivedCategory C ⥤ DerivedCategory D)
    (rep : ∀ P : CochainComplex C ℤ, E.obj (DerivedCategory.Q.obj P) ⟶
      DerivedCategory.Q.obj ((F.mapHomologicalComplex (.up ℤ)).obj P))
    (M : C) [IsIso (rep ((CochainComplex.singleFunctor C 0).obj M))] :
    IsIso (puritySingleFromRepresentativeMap F E rep M) := by
  unfold puritySingleFromRepresentativeMap
  infer_instance

private theorem single_map_iso (φ : A →+* B) (X : Scheme.{u})
    (M : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A))
    (hM : exactFunctor _ _ (tensorRight M)) : IsIso (purityScalarSingleMap φ X M) := by
  have hflat : ObjectProperty.flat M := by
    refine ⟨?_, hM⟩
    exact (exactFunctor _ _).prop_of_iso
      (BraidedCategory.tensorLeftIsoTensorRight M).symm hM
  have hP := (CochainComplex.kFlat_single_obj_iff_flat M (0 : ℤ)).2 hflat
  have := Etale.scalarRepresentative_isIso φ X
    ((CochainComplex.singleFunctor _ 0).obj M) hP
  have hrep : Etale.scalarAdjunctionRepresentativeMap (Etale.purityScalarSheaf φ X)
      (Sheaf.restrictScalars X.smallEtaleTopology φ) (Etale.purityScalarSheafAdjunction φ X)
      (Etale.purityScalarExtension φ X)
      (Etale.purityScalarAdjunction φ X) = Etale.scalarExtensionRepresentative φ X := by
    funext P
    unfold Etale.scalarExtensionRepresentative Etale.purityScalarAdjunction
      Etale.scalarAdjunctionRepresentativeMap
    with_unfolding_all rfl
  unfold purityScalarSingleMap
  rw [CategoryTheory.purityAdjunctionSingleMap_eq_representative]
  unfold purityRepresentativeSingleMap
  rw [hrep]
  exact single_from_rep_isIso (Etale.purityScalarSheaf φ X)
    (Etale.purityScalarExtension φ X) (Etale.scalarExtensionRepresentative φ X) M

/-- All ordinary balancing maps, uniquely fixed on local scalar/root generators;
flat-single computation; the unit, tensor-power and shift normalizations; and the
source isomorphism for every unbounded input, with its two endpoint unit equations.
The generator equation includes an arbitrary new scalar b, so it says precisely
(a tensor z) tensor b maps to phi(a)b tensor z in degree one. At degree zero it is
ordinary coefficient multiplication. Higher-degree generators are the existing
ordered root tensors, and the successor equation fixes the actual tensor powers.

Source: sk-prop-an, cor-pur-vector-bundle-purity.proof.md, paragraph 2;
Stacks 06YN, 06YY, 07A6, 07A4, 06YS, 0G7E, 03PK and 03RV
(blueprint: lem-pur-finite-tate-scalar-source-normalization).

Proof:
1. Flatness makes the single complex K-flat: tensoring an acyclic complex with M[0]
   is termwise exact tensoring by M (def-pc-flat-sheaf-modules, def-pc-kflat-complex).
   Its identity resolution computes scalar extension (lem-pur-derived-change-of-rings).
2. The normalized adjunct of x maps to x tensor 1 is the identity on the ordinary
   extended tensor (lem-pur-sheaf-ring-derived-coefficient-adjunction). Thus the actual
   scalar/single map equals the representative comparison and is invertible.
3. On the coefficient unit, multiply a tensor b to phi(a)b, with inverse b maps to
   1 tensor b. Balancing proves both identities and identifies the published unit.
4. The Tate sheaves are flat (lem-asd-finite-etale-twist-line). Construct balancing
   sectionwise; its inverse inserts 1 in each old coefficient factor. Both maps
   commute with restrictions and sheafification (def-pur-sheaf-tensor-product).
   The generator formulas determine each map uniquely, including the zero power.
5. The scalar tensorator is ordinary balancing on K-flat representatives
   (lem-weil-pbc-ringed-topoi-derived-tensor-pullback). It gives the displayed power
   equation. Scalar extension commutes termwise with shifts; localize this comparison.
   Every shift is even, so the regrouping introduces no sign.
6. Compose the tensorator, the inverse scalar/pullback comparison, and the shifted
   line map. Each is invertible, for every unbounded K; only the unbounded introductory
   comparison of lem-pur-etale-scalar-mate-projection is used.
7. Use the published scalar tensor-unit and scalar/pullback-unit coherence. Naturality
   transports the left tensor-unit equation along the specified single/unit maps.
   Cancel the pullback comparison and use its naturality to transport the coefficient
   unit square along the same maps. This gives the coefficient-unit source equation.
   Transport the existing scalar right-unit equation along the degree-zero line
   normalization to obtain the zero-power source equation. All comparisons remain
   the published ones, and no flatness of B over A is used. -/
theorem finite_tate_scalar_source_normalization [Finite A] [Finite B]
    (φ : A →+* B) (N : ℕ) (hN : 0 < N)
    (hA : (N : A) = 0) (hB : (N : B) = 0)
    (X : Scheme.{u}) (hX : ∀ x : X, IsUnit (N : X.presheaf.stalk x)) :
    (∀ M : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A),
      exactFunctor _ _ (tensorRight M) →
        purityScalarSingleMap φ X M = Etale.FiniteSmoothPurity.scalarSingleMap φ X M ∧
        IsIso (purityScalarSingleMap φ X M)) ∧
    ∃! β : ∀ r : ℕ,
        (Etale.purityScalarSheaf φ X).obj (Scheme.finiteEtaleTateTwist X N A hA r) ≅
          Scheme.finiteEtaleTateTwist X N B hB r,
      IsFiniteTateScalarBalancing φ N hA hB X β ∧
      IsFiniteTateScalarLineNormalized φ N hA hB X β ∧
      IsFiniteTateScalarSourceInvertible φ N hA hB X β ∧
      IsFiniteTateScalarSourceUnitNormalized φ N hA hB X β ∧
      IsFiniteTateScalarSourceZeroNormalized φ N hA hB X β := by
  constructor
  · intro M hM
    exact ⟨single_map_eq φ X M, single_map_iso φ X M hM⟩
  · obtain ⟨β, hβ⟩ := finite_tate_scalar_source_normalization_exists φ N hN hA hB X hX
    refine ⟨β, hβ, ?_⟩
    intro γ hγ
    exact balancing_unique φ N hA hB X γ β hγ.1 hβ.1

end WeilConjectures.PurityFiniteSetting
