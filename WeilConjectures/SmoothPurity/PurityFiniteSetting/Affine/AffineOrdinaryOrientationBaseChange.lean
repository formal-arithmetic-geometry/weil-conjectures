/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurityFiniteSetting.Diagonal.DiagonalDncChartNormalization
import WeilConjectures.SmoothPurity.PurityFiniteSetting.SmoothPurityMap
import WeilConjectures.SixFunctors.Etale.Derived.Invertible
import WeilConjectures.SmoothPurity.PurityFiniteSetting.Diagonal.PurityDiagonalDualizingData
import WeilConjectures.AlgebraicGeometry.FiniteSmoothPurity.FiniteSmoothPurityMaps
import WeilConjectures.AlgebraicGeometry.FiniteRingSectionDeformation.FiniteRingSectionDeformation
import WeilConjectures.AlgebraicGeometry.Finite.Smooth.FiniteSmoothGammaConstructions
import WeilConjectures.AlgebraicGeometry.NoetherianSectionSpecialization.NoetherianEtaleSectionSpecialization
import WeilConjectures.Compactification.FiniteFieldDatum.FiniteFieldFiberSupplement
import WeilConjectures.AlgebraicGeometry.BaseChangeConventions
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import WeilConjectures.AlgebraicGeometry.Vector.VectorBundleIntegrationCharts
import WeilConjectures.SmoothPurity.PurityFiniteSetting.Vector.VectorPurityNormalization
import WeilConjectures.Compactification.BaseChange
import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteTwistTransportUniqueness
import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteP1Arrows
import WeilConjectures.AlgebraicGeometry.Ordinary.OrdinaryFiniteP1KummerSupplement
import WeilConjectures.AlgebraicGeometry.Relative.RelativeKummerExchangeGeneratorsSupplement
import WeilConjectures.AlgebraicGeometry.Etale.EtaleSinglePullbackComparisonsSupplement
import WeilConjectures.AlgebraicGeometry.EtaleFiniteTwistPullback
import Mathlib.AlgebraicGeometry.Sites.Etale
import Mathlib.AlgebraicGeometry.Scheme
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
import WeilConjectures.AlgebraicGeometry.FiniteEtaleTateSheaf
import WeilConjectures.AlgebraicGeometry.FiniteEtaleTateTwist
import WeilConjectures.AlgebraicGeometry.Sites.Kummer
import Mathlib.Algebra.Module.ZMod
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
import Mathlib.CategoryTheory.Sites.Monoidal
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import WeilConjectures.AlgebraicGeometry.EtaleConstantRingModuleEquivalence
import WeilConjectures.CategoryTheory.RingedSiteModules
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHom
import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.TensorColimits
import WeilConjectures.AlgebraicGeometry.EtaleSheaves
import WeilConjectures.AlgebraicGeometry.DerivedCategories
import WeilConjectures.AlgebraicGeometry.RingedTopoiDerivedPullback
import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Flat
import WeilConjectures.CategoryTheory.AlgebraicInverseImage
import Mathlib.Algebra.Category.ModuleCat.Sheaf
import Mathlib.Algebra.Category.Ring.Limits
import Mathlib.Algebra.Category.Grp.Limits
import Mathlib.CategoryTheory.Sites.Whiskering
import Mathlib.CategoryTheory.Sites.Equivalence
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Mathlib.CategoryTheory.Functor.Derived.LeftDerived
import WeilConjectures.Algebra.Homology.KFlatResolution
import WeilConjectures.Algebra.Homology.ChangeOfRingsKFlatQuasiIso
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Homology.BifunctorShift
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import Mathlib.CategoryTheory.Limits.EssentiallySmall
import WeilConjectures.AlgebraicGeometry.KFlatRingedToposPullback
import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
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
import Mathlib.CategoryTheory.Sites.Limits
import Mathlib.CategoryTheory.Adjunction.Limits
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
import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import Mathlib.CategoryTheory.Sites.EpiMono
import Mathlib.CategoryTheory.Adjunction.Additive
import Mathlib.Algebra.Category.Grp.EpiMono
import Mathlib.Algebra.Category.Grp.Abelian
import Mathlib.CategoryTheory.Sites.Abelian
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.MonoidalClosed
import WeilConjectures.Algebra.Homology.Site.SiteDerivedTensorDescent
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Coherence
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Monoidal
import WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal
import WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal.TensorShiftIso
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.FlatModuleCat
import WeilConjectures.AlgebraicGeometry.EtaleFiniteTwistPullbackBase
import WeilConjectures.ConstructibleSheaf.Defs
import WeilConjectures.EtaleCohomology.TateTwist.Sheaf
import WeilConjectures.AlgebraicGeometry.FiniteEtaleTateLinePullback
import WeilConjectures.EtaleCohomology.TateTwist.RootsOfUnityPullback
import WeilConjectures.AlgebraicGeometry.FiniteEtaleTateTensorFamily
import WeilConjectures.CategoryTheory.NormalizedSignedTensorPowers
import WeilConjectures.CategoryTheory.Monoidal.IntTensorFamily
import WeilConjectures.CategoryTheory.IntTensorFamilyIso
import Mathlib.CategoryTheory.Monoidal.Braided.Basic
import WeilConjectures.AlgebraicGeometry.FiniteEtaleTateLocalLine
import WeilConjectures.AlgebraicGeometry.Sites.SmallEtaleRepresentablePresheafSheaf
import WeilConjectures.ConstructibleSheaf.Pullback
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.LocallyTrivialInverse
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Surjective
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.MonoidalComp
import WeilConjectures.SixFunctors.Etale.Derived.ProjectionFormula.Unit
import WeilConjectures.AlgebraicGeometry.EtaleFiniteTwistPullbackRest
import Mathlib.CategoryTheory.Abelian.Refinements
import Mathlib.Algebra.Homology.ShortComplex.Exact
import WeilConjectures.AlgebraicGeometry.ProperProjectionFormula
import WeilConjectures.SixFunctors.Etale.Derived.LowerStarProjection
import WeilConjectures.CategoryTheory.Monoidal.EtaleDerivedTensorSymmetrySupplement
import WeilConjectures.SixFunctors.Etale.Derived.ProjectionFormula
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.Topology.Defs.Filter
import WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact
import WeilConjectures.SixFunctors.Etale.Derived.Tensor
import WeilConjectures.AlgebraicGeometry.ExactUnboundedExchange
import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStar
import WeilConjectures.SixFunctors.BaseChange.Square
import WeilConjectures.SixFunctors.Etale.Derived.Shift
import WeilConjectures.SixFunctors.Etale.Derived.ReductionConservative
import Mathlib.CategoryTheory.Adjunction.Whiskering
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import WeilConjectures.CategoryTheory.DerivedCategory.FlatModel
public import WeilConjectures.AlgebraicGeometry.SmoothPurityBaseChange.FiniteOrientationCartesianTransport
public import WeilConjectures.SmoothPurity.OrdinaryFiniteTwistTransportUniqueness
public import WeilConjectures.SmoothPurity.PurityFiniteSetting.Diagonal.DiagonalOrdinaryReesEquation

/-! # Base change for ordinary affine diagonal orientations -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option maxRecDepth 8192
universe u v w
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry
namespace WeilConjectures.PurityFiniteSetting

attribute [local implicit_reducible] diagonalTwistEtale diagonalOrdinaryDualizing

private theorem derived_unit_eq (C : Type u) [Category.{v} C] [Abelian C]
    [IsGrothendieckAbelian.{v} C] [MonoidalCategory C] [MonoidalPreadditive C]
    [SymmetricCategory C] [MonoidalClosed C] [Abelian.HasFunctorialFlatResolution C]
    [HasDerivedCategory.{w} C] :
    DerivedCategory.singleFunctorObjUnitIso C = Iso.refl _ := by
  have hc (K : CochainComplex C ℤ) :
      (DerivedCategory.quotientCompQhIso C).symm.app K = Iso.refl _ := by
    apply Iso.ext
    rfl
  have hq : Functor.Monoidal.εIso (HomotopyCategory.quotient C (.up ℤ)) =
      Iso.refl _ := by
    apply Iso.ext
    rfl
  let := DerivedCategory.isIso_ε_Qh C
  have hε : asIso (Functor.LaxMonoidal.ε (DerivedCategory.Qh (C := C))) =
      Iso.refl _ := by
    apply Iso.ext
    rfl
  have hs (K : C) : (DerivedCategory.singleFunctorIsoCompQ C 0).app K =
      Iso.refl _ := rfl
  simp only [DerivedCategory.singleFunctorObjUnitIso, hs, hc, hq, hε,
    Iso.refl_symm]
  erw [Functor.mapIso_refl, Iso.refl_trans, Iso.refl_trans]
  apply Iso.ext
  exact Category.id_comp _

private theorem coefficient_unit_eq (A : Type (u + 1)) [CommRing A] (Y : Scheme.{u}) :
    smoothPurityUnitIso A Y = Iso.refl _ := by
  change Etale.singleFunctorObjUnitIso (ModuleCat.{u + 1} A) Y = Iso.refl _
  have h := derived_unit_eq (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} A))
  simpa only [DerivedCategory.singleFunctorObjUnitIso, smoothPurityUnitIso,
    Etale.singleFunctorObjUnitIso, Etale.singleFunctorObjIsoQh, Etale.ordinaryFiniteUnit,
    Etale.ordinaryFiniteDegreeZero,
    Etale.ordinaryFiniteConstant,
    Iso.trans_assoc] using h

private theorem unit_eq (P : PurityFiniteSetting.{u}) {X Y : Scheme.{u}}
    (f : X ⟶ Y) [HasCompactification f] :
    P.chartDualizingUnit f = Iso.refl _ := by
  simp only [chartDualizingUnit, coefficient_unit_eq, Iso.refl_symm]
  erw [Functor.mapIso_refl]
  rfl

private theorem rees_normalization (P : PurityFiniteSetting.{u})
    {X Y : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y]
    (d : ℕ) (f : X ⟶ Y) [HasCompactification f]
    [IsSeparated f] [QuasiCompact f] [LocallyOfFiniteType f]
    [SmoothOfRelativeDimension d f]
    (aY : Y ⟶ Spec (.of P.field.k))
    [IsSeparated aY] [LocallyOfFiniteType aY] [QuasiCompact aY]
    (G : Etale.FiniteRingSectionDeformation.Geometry d
      (pullback.fst f f) (pullback.diagonal f))
    (e : Etale.dualizingComplex P.Coefficient f ≅
      P.diagonalTwistEtale X d)
    (he : P.DiagonalOrientationNormalization d f aY e) :
    Etale.FiniteSmoothPurity.OrientationNormalized P.Coefficient P.diagonalExponent
      (pow_pos P.coefficients.prime.out.pos P.level) P.diagonalExponent_annihilates
      f d G (P.diagonalExponent_isUnit (f ≫ aY)) e := by
  let _ := G
  let hN : 0 < P.diagonalExponent :=
    pow_pos P.coefficients.prime.out.pos P.level
  let hX : IsUnit (P.diagonalExponent : Γ(X, ⊤)) :=
    P.diagonalExponent_isUnit (f ≫ aY)
  obtain ⟨κ, hκ, _⟩ :=
    AlgebraicGeometry.Etale.FiniteRingSectionDeformation.existsUnique_normalized
      P.diagonalExponent hN P.Coefficient P.diagonalExponent_annihilates hX d
      (pullback.fst f f) (pullback.diagonal f) (pullback.diagonal_fst f)
  let q := AlgebraicGeometry.Etale.FiniteSmoothPurity.reesConeComparison
      (pullback.diagonal f) ≪≫
    AlgebraicGeometry.Etale.FiniteRingSectionDeformation.coneBundleIso d
      (pullback.fst f f) (pullback.diagonal f)
  have hq : q.hom ≫ VectorBundleZeroSection.π X d
      (ConormalGradedAlgebra.piece (pullback.diagonal f) 1) =
      Scheme.Hom.normalConeProj (pullback.fst f f) (pullback.diagonal f) := by
    dsimp [q]
    rw [Category.assoc,
      (AlgebraicGeometry.Etale.FiniteRingSectionDeformation.coneBundleIso_spec d
        (pullback.fst f f) (pullback.diagonal f) (pullback.diagonal_fst f)).1,
      (AlgebraicGeometry.Etale.FiniteSmoothPurity.reesConeComparison_spec
        (pullback.diagonal f)).1]
    exact Scheme.Hom.purityNormalProjection_eq _ _ (pullback.diagonal_fst f)
  have sq : IsPullback q.hom
      (Scheme.Hom.normalConeProj (pullback.fst f f) (pullback.diagonal f))
      (VectorBundleZeroSection.π X d
        (ConormalGradedAlgebra.piece (pullback.diagonal f) 1)) (𝟙 X) :=
    IsPullback.of_horiz_isIso ⟨by simpa using hq⟩
  exact ⟨κ, hκ, sq, by
    exact diagonalOrdinaryReesEquation P d f aY G e κ hκ sq he⟩

private theorem forward_orientation {C D : Type*} [Category C] [Category D]
    (F : C ⥤ D) {K L : C} {K' L' : D} (o : K ≅ L) (o' : K' ≅ L')
    (β : F.obj K ⟶ K') (t : F.obj L ⟶ L')
    (h : F.map o.inv ≫ β = t ≫ o'.inv) :
    F.map o.hom ≫ t = β ≫ o'.hom := by
  apply (cancel_epi (F.map o.inv)).mp
  simp only [← Functor.map_comp_assoc, Iso.inv_hom_id]
  rw [← Category.assoc, h, Category.assoc, Iso.inv_hom_id, Category.comp_id,
    F.map_id, Category.id_comp]

/-- On a Cartesian square of affine finite-type schemes, the ordinary diagonal
orientation commutes with the recorded dualizing base-change mate and normalized Tate
pullback. Source: latest blueprint, composition proof Step 1, base-change clause.
(blueprint: lem-pur-affine-ordinary-orientation-base-change).

Proof: all four structure maps are separated and their sources are Noetherian. Apply
finite section deformation to each closed diagonal. The Rees cone comparison followed
by the conormal symmetric-algebra comparison is an isomorphism over the source; this
constructs the normalization square. The fixed-witness diagonal Rees equation then
makes the chosen chart orientations OrientationNormalized. Apply Cartesian transport
of normalized finite orientations to this supplied square. Uniqueness of normalized
Tate transport identifies its coefficient comparison with the specified one. The
coefficient-unit comparisons in chartOrdinaryBaseChange are identities: their factors
are the identity quotient/derived unit comparisons. Finally multiply the inverse
orientation equation by the two orientations to obtain the forward equation. This
argument applies unchanged in rank zero and for empty affine schemes. -/
theorem affine_ordinary_orientation_baseChange (P : PurityFiniteSetting.{u})
    {X Y X' Y' : Scheme.{u}} [IsAffine X] [IsAffine Y] [IsAffine X'] [IsAffine Y']
    (d : ℕ) (f : X ⟶ Y)
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [SmoothOfRelativeDimension d f]
    (aY : Y ⟶ Spec (.of P.field.k)) [LocallyOfFiniteType aY] [QuasiCompact aY]
    (b : Y' ⟶ Y) [LocallyOfFiniteType b] [QuasiCompact b]
    (f' : X' ⟶ Y') [IsSeparated f'] [LocallyOfFiniteType f'] [QuasiCompact f']
    [SmoothOfRelativeDimension d f']
    (j : X' ⟶ X) (sq : IsPullback j f' f b)
    (t : Etale.OrdinaryFiniteTwistTransport P.Coefficient P.diagonalExponent
      P.diagonalExponent_annihilates) :
    letI := Dnc.compactifiable P f aY
    letI := Dnc.compactifiable P f' (b ≫ aY)
    (Etale.ordinaryFinitePullback P.Coefficient j).map
        (P.chartOrdinaryOrientation d f aY).hom ≫
      (Etale.vectorIntegrationBaseCoefficientPullback P.Coefficient P.diagonalExponent
        P.diagonalExponent_annihilates t j (P.diagonalExponent_isUnit (f ≫ aY)) d).hom =
      (P.chartOrdinaryBaseChange d f aY b f' j sq).hom ≫
        (P.chartOrdinaryOrientation d f' (b ≫ aY)).hom := by
  let := P.noetherian aY
  let := P.noetherian (f ≫ aY)
  let := P.noetherian (b ≫ aY)
  let := P.noetherian (f' ≫ b ≫ aY)
  let := Dnc.compactifiable P f aY
  let := Dnc.compactifiable P f' (b ≫ aY)
  let Xo : Over (Spec (.of P.field.k)) := Over.mk (f ≫ aY)
  let Yo : Over (Spec (.of P.field.k)) := Over.mk aY
  let Xo' : Over (Spec (.of P.field.k)) := Over.mk (f' ≫ b ≫ aY)
  let Yo' : Over (Spec (.of P.field.k)) := Over.mk (b ≫ aY)
  let : IsSeparated Xo.hom := inferInstanceAs (IsSeparated (f ≫ aY))
  let : LocallyOfFiniteType Xo.hom := inferInstanceAs (LocallyOfFiniteType (f ≫ aY))
  let : QuasiCompact Xo.hom := inferInstanceAs (QuasiCompact (f ≫ aY))
  let : IsNoetherian Xo.left := inferInstanceAs (IsNoetherian X)
  let : IsSeparated Yo.hom := inferInstanceAs (IsSeparated (aY))
  let : LocallyOfFiniteType Yo.hom := inferInstanceAs (LocallyOfFiniteType (aY))
  let : QuasiCompact Yo.hom := inferInstanceAs (QuasiCompact (aY))
  let : IsNoetherian Yo.left := inferInstanceAs (IsNoetherian Y)
  let : IsSeparated Xo'.hom := inferInstanceAs (IsSeparated (f' ≫ b ≫ aY))
  let : LocallyOfFiniteType Xo'.hom := inferInstanceAs (LocallyOfFiniteType (f' ≫ b ≫ aY))
  let : QuasiCompact Xo'.hom := inferInstanceAs (QuasiCompact (f' ≫ b ≫ aY))
  let : IsNoetherian Xo'.left := inferInstanceAs (IsNoetherian X')
  let : IsSeparated Yo'.hom := inferInstanceAs (IsSeparated (b ≫ aY))
  let : LocallyOfFiniteType Yo'.hom := inferInstanceAs (LocallyOfFiniteType (b ≫ aY))
  let : QuasiCompact Yo'.hom := inferInstanceAs (QuasiCompact (b ≫ aY))
  let : IsNoetherian Yo'.left := inferInstanceAs (IsNoetherian Y')
  let fo : Xo ⟶ Yo := Over.homMk f
  let bo : Yo' ⟶ Yo := Over.homMk b
  let fo' : Xo' ⟶ Yo' := Over.homMk f'
  let jo : Xo' ⟶ Xo := Over.homMk j (by
    dsimp [Xo, Xo']
    rw [← Category.assoc, sq.w, Category.assoc])
  let : IsSeparated fo.left := inferInstanceAs (IsSeparated f)
  let : QuasiCompact fo.left := inferInstanceAs (QuasiCompact f)
  let : HasCompactification fo.left := inferInstanceAs (HasCompactification f)
  let : SmoothOfRelativeDimension d fo.left :=
    inferInstanceAs (SmoothOfRelativeDimension d f)
  let G := Etale.FiniteRingSectionDeformation.geometry d
    (pullback.fst f f) (pullback.diagonal f) (pullback.diagonal_fst f)
  let G' := Etale.FiniteRingSectionDeformation.geometry d
    (pullback.fst f' f') (pullback.diagonal f') (pullback.diagonal_fst f')
  let o := P.chartOrdinaryOrientation d f aY
  let o' := P.chartOrdinaryOrientation d f' (b ≫ aY)
  have ho := rees_normalization P d f aY G o (P.chartOrdinaryOrientation_spec d f aY).1
  have ho' := rees_normalization P d f' (b ≫ aY) G' o'
    (P.chartOrdinaryOrientation_spec d f' (b ≫ aY)).1
  have h := ProEtale.SmoothPurityBaseChange.finite_orientation_cartesian_transport
    P.field P.coefficients.l P.coefficients.different Xo Yo Xo' Yo'
    fo bo jo fo' sq d P.level P.level_pos P.Coefficient P.diagonalExponent_annihilates
    G G' (P.diagonalExponent_isUnit (f ≫ aY))
    (P.diagonalExponent_isUnit (f' ≫ b ≫ aY)) o o' ho ho'
  have ht := Etale.ordinaryFiniteTwistTransport_unique P.Coefficient P.diagonalExponent
    P.diagonalExponent_annihilates
    (purityTwistTransport P.Coefficient P.diagonalExponent
      (pow_pos P.coefficients.prime.out.pos P.level) P.diagonalExponent_annihilates) t
  dsimp only [diagonalExponent] at ht
  rw [ht] at h
  have hb : (P.chartOrdinaryBaseChange d f aY b f' j sq).hom =
      Etale.dualizingComplexBaseChangeMap P.Coefficient sq := by
    simp only [chartOrdinaryBaseChange, unit_eq, Iso.refl_symm, Iso.trans_refl]
    erw [Functor.mapIso_refl, Iso.refl_trans]
    rfl
  erw [hb]
  exact forward_orientation (Etale.ordinaryFinitePullback P.Coefficient j) o o' _ _ h

end WeilConjectures.PurityFiniteSetting
