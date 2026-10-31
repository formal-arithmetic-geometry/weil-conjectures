/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CoordinateProductPresentations
public import WeilConjectures.CategoryTheory.Monoidal.Instances.DerivedCategoryBraided
import WeilConjectures.CategoryTheory.Monoidal.Braided.Adjunction
import WeilConjectures.SixFunctors.ProEtale.Comparison.Flat
import WeilConjectures.SixFunctors.ProEtale.Comparison.Monoidal
import WeilConjectures.AlgebraicGeometry.FiniteEtaleTwistLine
import WeilConjectures.AlgebraicGeometry.FiniteEtaleTateTwist
import WeilConjectures.AlgebraicGeometry.Sites.Kummer
import Mathlib.Algebra.Module.ZMod
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
import Mathlib.CategoryTheory.Sites.Monoidal
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import WeilConjectures.AlgebraicGeometry.EtaleConstantRingModuleEquivalence
import WeilConjectures.CategoryTheory.RingedSiteModules
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import WeilConjectures.ConstructibleSheaf.Defs
import WeilConjectures.EtaleCohomology.TateTwist.Sheaf
import WeilConjectures.ConstructibleSheaf.Pullback
import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import WeilConjectures.AlgebraicGeometry.EtaleEvenShiftCanonicalSelfSymmetry
import WeilConjectures.AlgebraicGeometry.EtaleCoordinateTraceData
import WeilConjectures.AlgebraicGeometry.DerivedCategories
import WeilConjectures.ConstructibleSheaf.LisseRankOne
import WeilConjectures.SixFunctors.Etale.Derived.LowerStarProjection
import WeilConjectures.SixFunctors.Etale.Derived.TensorStructure
import WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.Proper
import WeilConjectures.AlgebraicGeometry.BaseChangeMapAbelianAndSets
import WeilConjectures.SixFunctors.BaseChange.DerivedUnbounded
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.AB
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.GroupTheory.Torsion
import WeilConjectures.AlgebraicGeometry.ProperUnboundedBaseChangeModN
import WeilConjectures.AlgebraicGeometry.TorsionAssembly
import WeilConjectures.SixFunctors.BaseChange.Derived
import WeilConjectures.AlgebraicGeometry.TorsionEtaleSheaf
import WeilConjectures.AlgebraicGeometry.TorsionSheafCharacterizations
import WeilConjectures.SixFunctors.BaseChange.DerivedForget
import WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.AbTorsionSheaf
import WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine
import WeilConjectures.SixFunctors.Etale.Derived.DirectImageVanishingTorsion
import WeilConjectures.SixFunctors.BaseChange.DerivedUnboundedFac
import WeilConjectures.AlgebraicGeometry.ProperUnboundedBaseChangeForgetful
import Mathlib.Data.ZMod.Basic
import WeilConjectures.AlgebraicGeometry.UnboundedCoefficientForgetfulAux
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.DerivedBaseChange
import WeilConjectures.AlgebraicGeometry.UnboundedAbelianExchangeComparison
import WeilConjectures.AlgebraicGeometry.ChosenCartesianSquare
import Mathlib.AlgebraicGeometry.Pullbacks
import WeilConjectures.SixFunctors.BaseChange.Square
import WeilConjectures.AlgebraicGeometry.KInjectiveResolutions
import WeilConjectures.AlgebraicGeometry.EtaleSheaves
import WeilConjectures.AlgebraicGeometry.ExactUnboundedExchange
import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStar
import WeilConjectures.AlgebraicGeometry.ModuleAbelianDerivedDirectImageComparison
import WeilConjectures.AlgebraicGeometry.ModuleAbelianKInjectiveDirectImageAcyclic
import WeilConjectures.AlgebraicGeometry.EtaleModuleAbelianRingedPresentation
import WeilConjectures.CategoryTheory.RingedToposMorphismSupplement
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
import Mathlib.CategoryTheory.Category.ULift
import Mathlib.CategoryTheory.Sites.CartesianMonoidal
import Mathlib.CategoryTheory.Sites.Equivalence
import WeilConjectures.AlgebraicGeometry.ModuleSheafConstantRingEquivalence
import WeilConjectures.CategoryTheory.ContinuousRingedToposModuleDirectImage
import WeilConjectures.CategoryTheory.GeometricModuleConstruction
import Mathlib.Algebra.Category.Ring.Limits
import WeilConjectures.CategoryTheory.RingedToposRingData
import WeilConjectures.CategoryTheory.AdjunctionRingOperations
import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
import Mathlib.CategoryTheory.Adjunction.Basic
import Mathlib.CategoryTheory.Monoidal.CommGrp_
import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Mod
import WeilConjectures.CategoryTheory.RestrictionRingedToposModuleDirectImageSupplement
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
import WeilConjectures.CategoryTheory.RingedToposDerivedPushforwardComposition
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
import Mathlib.CategoryTheory.Functor.Derived.RightDerived
import WeilConjectures.CategoryTheory.RingedSiteKInjectiveResolutionsSupplement
import WeilConjectures.Mathlib.Algebra.Homology.GrothendieckAbelian
import Mathlib.CategoryTheory.Localization.DerivabilityStructure.Derives
import WeilConjectures.Algebra.Homology.KFlatSupplement
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Flat
import WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Defs
import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution
import Mathlib.Algebra.Homology.DerivedCategory.Fractions
import WeilConjectures.Algebra.Homology.KFlatResolution
import WeilConjectures.CategoryTheory.RingedToposKFlatPullback
import WeilConjectures.CategoryTheory.AlgebraicInverseImage
import Mathlib.Algebra.Category.ModuleCat.Sheaf
import Mathlib.Algebra.Category.Grp.Limits
import Mathlib.CategoryTheory.Sites.Whiskering
import WeilConjectures.CategoryTheory.GeometricModuleTransport
import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
import Mathlib.CategoryTheory.Adjunction.Limits
import WeilConjectures.CategoryTheory.GeometricRingTransport
import Mathlib.CategoryTheory.Sites.Limits
import WeilConjectures.CategoryTheory.SheavesAlgebraicStructuresRingCore
import WeilConjectures.CategoryTheory.SheafRingObjectReconstruction
import WeilConjectures.CategoryTheory.Adjunction.FiniteProductRingFunctor
import WeilConjectures.CategoryTheory.ModulePullbackPushforwardAdjunctionSupplement
import WeilConjectures.AlgebraicGeometry.KFlatRingedToposPullback
import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Homology.BifunctorShift
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import Mathlib.CategoryTheory.Limits.EssentiallySmall
import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import Mathlib.CategoryTheory.Limits.ExactFunctor
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import Mathlib.Algebra.Homology.HomologicalComplex
import Mathlib.Algebra.Homology.Additive
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.RingedToposFlatPullback
import WeilConjectures.CategoryTheory.AlgebraicInverseImageOfUniverses
import Mathlib.CategoryTheory.Types.Basic
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatAlgebraicInverseImageOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatEquationalCriterionOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatLocalRelationsOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
import WeilConjectures.CategoryTheory.Sites.WeakSheafifyAddCommGrpLeftExact
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Submodule
import Mathlib.LinearAlgebra.TensorProduct.Vanishing
import Mathlib.RingTheory.TensorProduct.DirectLimitFG
import Mathlib.LinearAlgebra.TensorProduct.Finiteness
import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
import WeilConjectures.CategoryTheory.Sites.InverseImageLocalFamilies
import Mathlib.CategoryTheory.Sites.Sheaf
import Mathlib.CategoryTheory.Sites.LocallyBijective
import Mathlib.CategoryTheory.Limits.Types.Pullbacks
import Mathlib.CategoryTheory.Functor.EpiMono
import Mathlib.CategoryTheory.Limits.Types.Equalizers
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Equalizers
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.ScalarTensorComparisonOfUniverses
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
import Mathlib.Algebra.Homology.HomotopyCategory.MappingCone
import Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import WeilConjectures.Algebra.Homology.RingedToposAdaptedFlatResolution
import WeilConjectures.Algebra.Homology.RingedToposPullbackFilteredColimits
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.CategoryTheory.Sites.PreservesSheafification
import Mathlib.CategoryTheory.Limits.Preserves.Limits
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import Mathlib.RingTheory.Flat.CategoryTheory
import Mathlib.CategoryTheory.ObjectProperty.ColimitsOfShape
import Mathlib.Algebra.Homology.Embedding.CochainComplex
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.Algebra.Category.Grp.AB
import WeilConjectures.Algebra.Homology.RingedToposAcyclicKFlatPullback
import WeilConjectures.Algebra.Homology.BoundedFlatIndependentCoefficients
import Mathlib.CategoryTheory.Monoidal.Preadditive
import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import Mathlib.CategoryTheory.Monoidal.Closed.Basic
import WeilConjectures.AlgebraicGeometry.RingedTopoiDerivedPullback
import Mathlib.CategoryTheory.Functor.Derived.LeftDerived
import WeilConjectures.Algebra.Homology.ChangeOfRingsKFlatQuasiIsoSupplement
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
import Mathlib.CategoryTheory.Sites.EpiMono
import Mathlib.CategoryTheory.Adjunction.Additive
import Mathlib.Algebra.Category.Grp.EpiMono
import Mathlib.Algebra.Category.Grp.Abelian
import Mathlib.CategoryTheory.Sites.Abelian
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.MonoidalClosed
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp
import WeilConjectures.AlgebraicGeometry.ModuleAbelianUnderivedExchange
import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate
import WeilConjectures.AlgebraicGeometry.EtaleDerivedTensorSymmetrySupplement
import WeilConjectures.AlgebraicGeometry.ProperTorsionProjectionFormula
import WeilConjectures.SixFunctors.Etale.Derived.Coefficients
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.FlatModuleCat
import WeilConjectures.SixFunctors.Etale.Derived.Kunneth.ProperProjectionFormula
import Mathlib.Tactic.SuppressCompilation

/-! # Symmetry of the shifted coordinate Tate line

Source: literature/blueprint/latest/blueprint/sec-smooth-purity/sk-prop-an/
cor-pur-affine-space-zero-section-purity.proof.md, ordered exterior product and even shifts
(blueprint: lem-pur-coordinate-shifted-line-symmetry).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 2048
attribute [local instance] CategoryTheory.Sheaf.monoidalCategory
  CategoryTheory.Sheaf.braidedCategory DerivedCategory.braidedCategory'
universe u v
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open AlgebraicGeometry WeilConjectures
namespace AlgebraicGeometry.ProEtale.AffineZeroPurity
open AffineSpacePurity AffineLinePurity

private theorem finite_line_self_braiding (A : Type (u + 1)) [CommRing A]
    (N : ℕ) (hN : 0 < N) (hA : (N : A) = 0) (X : Scheme.{u})
    (hX : IsUnit (N : Γ(X, ⊤))) :
    (β_ (Scheme.finiteEtaleTateLine X N A hA)
      (Scheme.finiteEtaleTateLine X N A hA)).hom = 𝟙 _ := by
  let T := PurityFiniteSetting.functorialCupTwistProducts A N hN hA
  have h := T.symmetry X hX 1 1
  simp only [eqToHom_refl, Category.comp_id] at h
  dsimp only [Scheme.finiteEtaleTateSheaf, Scheme.finiteEtaleTateTwist] at h
  apply (cancel_mono (T.product X hX 1 1).hom).mp
  erw [Category.id_comp]
  exact h

private theorem self_braiding_of_iso {C : Type*} [Category C] [MonoidalCategory C]
    [BraidedCategory C] {L M : C} (e : L ≅ M)
    (h : (β_ M M).hom = 𝟙 _) : (β_ L L).hom = 𝟙 _ := by
  apply (cancel_mono (e.hom ⊗ₘ e.hom)).mp
  rw [← BraidedCategory.braiding_naturality, h]
  simp only [Category.comp_id, Category.id_comp]

private theorem derived_even_single_braiding
    {C : Type*} [Category.{v + 1} C] [Abelian C] [IsGrothendieckAbelian.{v + 1} C]
    [MonoidalCategory C] [MonoidalPreadditive C] [SymmetricCategory C]
    [MonoidalClosed C]
    [Abelian.HasFunctorialFlatResolution C]
    (L : C) (hflat : ObjectProperty.flat L) (h : (β_ L L).hom = 𝟙 _) :
    (β_ (((DerivedCategory.singleFunctor C 0).obj L)⟦(2 : ℤ)⟧)
      (((DerivedCategory.singleFunctor C 0).obj L)⟦(2 : ℤ)⟧)).hom = 𝟙 _ := by
  have h' := Etale.CoordinateTrace.evenShiftCanonicalSelfSymmetry L hflat h 1
  change (β_ (((DerivedCategory.singleFunctor C 0).obj L)⟦(2 * 1 : ℤ)⟧)
    (((DerivedCategory.singleFunctor C 0).obj L)⟦(2 * 1 : ℤ)⟧)).hom = 𝟙 _ at h'
  exact h'

private theorem compared_line_self_braiding
    (A : Type (u + 1)) [CommRing A] (N : ℕ) (hN : 0 < N) (hA : (N : A) = 0)
    (X : Scheme.{u}) (hX : IsUnit (N : Γ(X, ⊤))) :
    (β_ ((comparisonUpperStar (ModuleCat.{u + 1} A) X).obj
      (Scheme.finiteEtaleTateLine X N A hA))
      ((comparisonUpperStar (ModuleCat.{u + 1} A) X).obj
      (Scheme.finiteEtaleTateLine X N A hA))).hom = 𝟙 _ := by
  let : (comparisonLowerStar (ModuleCat.{u + 1} A) X).LaxMonoidal :=
    laxMonoidal_comparisonLowerStar (ModuleCat.{u + 1} A) X
  let : (comparisonUpperStar (ModuleCat.{u + 1} A) X).OplaxMonoidal :=
    oplaxMonoidal_comparisonUpperStar (ModuleCat.{u + 1} A) X
  let : (comparisonLowerStar (ModuleCat.{u + 1} A) X).LaxBraided :=
    { __ := laxMonoidal_comparisonLowerStar (ModuleCat.{u + 1} A) X
      braided L M := by
        unfold comparisonLowerStar
        exact Functor.LaxBraided.braided L M }
  let L := Scheme.finiteEtaleTateLine X N A hA
  have h := (comparisonAdjunction (ModuleCat.{u + 1} A) X).leftAdjointOplaxMonoidal_δ_braiding
    L L
  change Functor.OplaxMonoidal.δ (comparisonUpperStar (ModuleCat.{u + 1} A) X) L L ≫
      (β_ ((comparisonUpperStar (ModuleCat.{u + 1} A) X).obj L)
        ((comparisonUpperStar (ModuleCat.{u + 1} A) X).obj L)).hom =
      (comparisonUpperStar (ModuleCat.{u + 1} A) X).map (β_ L L).hom ≫
        Functor.OplaxMonoidal.δ (comparisonUpperStar (ModuleCat.{u + 1} A) X) L L at h
  apply (cancel_epi (Functor.OplaxMonoidal.δ
    (comparisonUpperStar (ModuleCat.{u + 1} A) X) L L)).mp
  dsimp only [L] at h
  rw [finite_line_self_braiding A N hN hA X hX, CategoryTheory.Functor.map_id,
    Category.id_comp] at h
  dsimp only [L]
  erw [Category.comp_id]
  exact h


/-- Self-braiding of the compared rank-one Tate line shifted by two.
Source: ordered exterior product of rank-one classes, affine-space purity proof.
(blueprint: lem-pur-coordinate-shifted-line-symmetry).

Proof: etale locally a primitive root trivializes the unshifted Tate line.
The tensor square is generated by the square of this local generator, fixed by
braiding, so the unshifted self-braiding is identity by sheaf descent. The exact
single and site-comparison functors preserve this equation through their
canonical monoidal comparisons. The shift braiding formula contributes
(-1)^(2*2)=1. Conjugating by the tensor-shift comparison proves the stated
identity on the literal compared shifted line. -/
theorem coordinate_shifted_line_self_braiding (P : PurityFiniteSetting.{u}) (n : ℕ)
    (X : Scheme.{u}) (aX : X ⟶ Spec (.of P.field.k)) :
    (β_ (shiftedLine (setting P n) X) (shiftedLine (setting P n) X)).hom =
      𝟙 _ := by
  let S := setting P n
  let A := Ring S
  let N := S.coefficients.l ^ (S.level + 1)
  have hN : 0 < N := pow_pos (Fact.out : S.coefficients.l.Prime).pos _
  have hA : (N : A) = 0 := annihilates S
  have hX : IsUnit (N : Γ(X, ⊤)) := exponentUnit S X aX
  let F := comparisonUpperStar (ModuleCat.{u + 1} A) X
  let L := Scheme.finiteEtaleTateLine X N A hA
  have hInv : ∀ x : X, IsUnit (N : X.presheaf.stalk x) := fun x ↦ by
    simpa only [map_natCast] using hX.map (X.presheaf.germ ⊤ x (by trivial)).hom
  have hfL : ObjectProperty.flat L :=
    (ObjectProperty.flat_iff_preservesFiniteLimits _).2
      (Scheme.finite_etale_torsion_twist_line X N hN hInv A hA 1).2.2.1
  let : IsNoetherianRing A := isNoetherian_of_finite A A
  have hfR : ObjectProperty.flat (F.obj L) := flat_comparisonUpperStar_obj hfL
  have hbR := compared_line_self_braiding A N hN hA X hX
  let e : shiftedLine S X ≅
      ((DerivedCategory.singleFunctor _ 0).obj (F.obj L))⟦(2 : ℤ)⟧ :=
    (F.mapDerivedCategory.commShiftIso (2 : ℤ)).app
        ((DerivedCategory.singleFunctor _ 0).obj L) ≪≫
      (shiftFunctor _ (2 : ℤ)).mapIso ((F.mapDerivedCategorySingleFunctor 0).app L)
  exact self_braiding_of_iso e (derived_even_single_braiding _ hfR hbR)

end AlgebraicGeometry.ProEtale.AffineZeroPurity
