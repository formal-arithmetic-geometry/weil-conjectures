/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SectionComparisonArrows.SectionComparisonArrows
public import WeilConjectures.AlgebraicGeometry.Affine.Space.AffineSpaceAmbientAdjunction
public import WeilConjectures.AlgebraicGeometry.Etale.EtaleAmbientAdjointLocality
public import WeilConjectures.AlgebraicGeometry.EtaleFiniteTwistPullback
public import Mathlib.AlgebraicGeometry.Sites.Etale
public import Mathlib.AlgebraicGeometry.Scheme
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
public import WeilConjectures.AlgebraicGeometry.FiniteEtaleTateSheaf
public import WeilConjectures.AlgebraicGeometry.FiniteEtaleTateTwist
public import WeilConjectures.AlgebraicGeometry.Sites.Kummer
public import Mathlib.Algebra.Module.ZMod
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
public import Mathlib.CategoryTheory.Sites.Monoidal
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import WeilConjectures.AlgebraicGeometry.EtaleConstantRingModuleEquivalence
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHom
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.TensorColimits
public import WeilConjectures.AlgebraicGeometry.EtaleSheaves
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import WeilConjectures.AlgebraicGeometry.RingedTopoiDerivedPullback
public import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Flat
public import WeilConjectures.CategoryTheory.AlgebraicInverseImage
public import Mathlib.Algebra.Category.ModuleCat.Sheaf
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.Algebra.Category.Grp.Limits
public import Mathlib.CategoryTheory.Sites.Whiskering
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.CategoryTheory.Functor.Derived.LeftDerived
public import WeilConjectures.Algebra.Homology.KFlatResolution
public import WeilConjectures.Algebra.Homology.ChangeOfRingsKFlatQuasiIso
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
public import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.Limits.EssentiallySmall
public import WeilConjectures.AlgebraicGeometry.KFlatRingedToposPullback
public import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
public import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
public import Mathlib.Algebra.Homology.HomologicalComplex
public import Mathlib.Algebra.Homology.Additive
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.RingedToposFlatPullback
public import WeilConjectures.CategoryTheory.AlgebraicInverseImageOfUniverses
public import Mathlib.CategoryTheory.Types.Basic
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatAlgebraicInverseImageOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatEquationalCriterionOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatLocalRelationsOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
public import WeilConjectures.CategoryTheory.Sites.WeakSheafifyAddCommGrpLeftExact
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Submodule
public import Mathlib.LinearAlgebra.TensorProduct.Vanishing
public import Mathlib.RingTheory.TensorProduct.DirectLimitFG
public import Mathlib.LinearAlgebra.TensorProduct.Finiteness
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
public import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
public import WeilConjectures.CategoryTheory.Sites.InverseImageLocalFamilies
public import Mathlib.CategoryTheory.Sites.Sheaf
public import Mathlib.CategoryTheory.Sites.LocallyBijective
public import Mathlib.CategoryTheory.Sites.Limits
public import Mathlib.CategoryTheory.Adjunction.Limits
public import Mathlib.CategoryTheory.Limits.Types.Pullbacks
public import Mathlib.CategoryTheory.Functor.EpiMono
public import Mathlib.CategoryTheory.Limits.Types.Equalizers
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Equalizers
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.ScalarTensorComparisonOfUniverses
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
public import Mathlib.Algebra.Homology.HomotopyCategory.MappingCone
public import Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
public import WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
public import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
public import WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
public import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
public import WeilConjectures.Algebra.Homology.RingedToposAdaptedFlatResolution
public import WeilConjectures.Algebra.Homology.RingedToposPullbackFilteredColimits
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Mathlib.CategoryTheory.Sites.PreservesSheafification
public import Mathlib.CategoryTheory.Limits.Preserves.Limits
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
public import Mathlib.RingTheory.Flat.CategoryTheory
public import Mathlib.CategoryTheory.ObjectProperty.ColimitsOfShape
public import Mathlib.Algebra.Homology.Embedding.CochainComplex
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.Algebra.Category.Grp.AB
public import WeilConjectures.Algebra.Homology.RingedToposAcyclicKFlatPullback
public import WeilConjectures.Algebra.Homology.BoundedFlatIndependentCoefficients
public import Mathlib.CategoryTheory.Monoidal.Preadditive
public import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
public import Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
public import Mathlib.CategoryTheory.Sites.EpiMono
public import Mathlib.CategoryTheory.Adjunction.Additive
public import Mathlib.Algebra.Category.Grp.EpiMono
public import Mathlib.Algebra.Category.Grp.Abelian
public import Mathlib.CategoryTheory.Sites.Abelian
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.MonoidalClosed
public import WeilConjectures.Algebra.Homology.Site.SiteDerivedTensorDescent
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Coherence
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Monoidal
public import WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal
public import WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal.TensorShiftIso
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.FlatModuleCat
public import WeilConjectures.AlgebraicGeometry.EtaleFiniteTwistPullbackBase
public import WeilConjectures.ConstructibleSheaf.Defs
public import WeilConjectures.EtaleCohomology.TateTwist.Sheaf
public import WeilConjectures.AlgebraicGeometry.FiniteEtaleTateLinePullback
public import WeilConjectures.EtaleCohomology.TateTwist.RootsOfUnityPullback
public import WeilConjectures.AlgebraicGeometry.FiniteEtaleTateTensorFamily
public import WeilConjectures.CategoryTheory.NormalizedSignedTensorPowers
public import WeilConjectures.CategoryTheory.Monoidal.IntTensorFamily
public import WeilConjectures.CategoryTheory.IntTensorFamilyIso
public import Mathlib.CategoryTheory.Monoidal.Braided.Basic
public import WeilConjectures.AlgebraicGeometry.FiniteEtaleTateLocalLine
public import WeilConjectures.AlgebraicGeometry.Sites.SmallEtaleRepresentablePresheafSheaf
public import WeilConjectures.ConstructibleSheaf.Pullback
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.LocallyTrivialInverse
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Surjective
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.MonoidalComp
public import WeilConjectures.SixFunctors.Etale.Derived.ProjectionFormula.Unit
public import WeilConjectures.AlgebraicGeometry.EtaleFiniteTwistPullbackRest
public import Mathlib.CategoryTheory.Abelian.Refinements
public import Mathlib.Algebra.Homology.ShortComplex.Exact

/-! # Counit-normalized local section comparison formulas

Source: main-20261015, sec-smooth-purity/sk-thm-dnc, opening and Local construction
(blueprint: def-trf-section-local-comparison-data).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.Etale.SectionLocalDualizingComparisons
open SectionComparisonArrows

/-- Units pull back along every scheme morphism.
Source: sk-thm-dnc, domain checks (blueprint: def-trf-section-local-comparison-data).
Proof: apply the global-sections ring map to the unit N; ring homomorphisms preserve
units and natural-number casts, including on the empty scheme. -/
theorem invertibleOnSource (N : ℕ) {X T : Scheme.{u}} (v : X ⟶ T)
    (hT : IsUnit (N : Γ(T, ⊤))) : IsUnit (N : Γ(X, ⊤)) := by
  simpa only [map_natCast] using hT.map v.appTop.hom

/-- The degree-zero finite Tate sheaf with its even shift.
Source: sk-thm-dnc, Local construction
(blueprint: def-trf-section-local-comparison-data). -/
def tateObject (A : Type (u + 1)) [CommRing A] (N : ℕ) (hA : (N : A) = 0)
    (T : Scheme.{u}) (d : ℕ) : DerivedCategoryModule A T :=
  ((_root_.DerivedCategory.singleFunctor _ 0).obj
    (Scheme.finiteEtaleTateTwist T N A hA d))⟦2 * (d : ℤ)⟧

/-- Tate pullback, using the root-normalized comparison, degree-zero localization and shifts.
Source: sk-thm-dnc, Local construction (blueprint: def-trf-section-local-comparison-data).
-/
@[irreducible]
def tatePullback (A : Type (u + 1)) [CommRing A] (N : ℕ) (hN : 0 < N)
    (hA : (N : A) = 0) {T T' : Scheme.{u}} (v : T' ⟶ T)
    (hT : IsUnit (N : Γ(T, ⊤))) (hT' : IsUnit (N : Γ(T', ⊤))) (d : ℕ) :
    (upperStar (ModuleCat.{u + 1} A) v).leftDerivedFunctor.obj (tateObject A N hA T d) ≅
      tateObject A N hA T' d :=
  ((upperStar (ModuleCat.{u + 1} A) v).leftDerivedFunctor.commShiftIso
    (2 * (d : ℤ))).app _ ≪≫
      (shiftFunctor _ (2 * (d : ℤ))).mapIso
        ((singleFunctorCompLeftDerivedUpperStarIso (ModuleCat.{u + 1} A) v).app _ ≪≫
          (_root_.DerivedCategory.singleFunctor _ 0).mapIso
            ((Scheme.finiteEtaleTwistPullbackData A N hN hA).c v hT hT' (d : ℤ)))

/-- The explicit right functor in the ordinary affine-space adjunction.
Source: sk-thm-dnc, Local construction
(blueprint: def-trf-section-local-comparison-data). -/
def affineRight (A : Type (u + 1)) [CommRing A] (N : ℕ) (hA : (N : A) = 0)
    (T : Scheme.{u}) (d : ℕ) :
    DerivedCategoryModule A T ⥤ DerivedCategoryModule A (AffineSpace (ULift.{u} (Fin d)) T) :=
  ((upperStar (ModuleCat.{u + 1} A) (AffineSpace (ULift.{u} (Fin d)) T ↘ T)).mapDerivedCategory ⋙
    derivedTensorRight (ModuleCat.{u + 1} A) (AffineSpace (ULift.{u} (Fin d)) T)
      ((_root_.DerivedCategory.singleFunctor _ 0).obj
        (Scheme.finiteEtaleTateTwist (AffineSpace (ULift.{u} (Fin d)) T) N A hA d))) ⋙
    shiftFunctor _ (2 * (d : ℤ))

/-- Compare the chosen affine-space right adjoint with the explicit affine adjunction,
using uniqueness respecting counits, and remove the inverse-image coefficient unit.
Source: sk-thm-dnc, Local construction
(blueprint: def-trf-section-local-comparison-data). -/
@[irreducible]
def affineDualizingIso (A : Type (u + 1)) [CommRing A] [Finite A]
    (N : ℕ) (_hN : 0 < N) (hA : (N : A) = 0)
    (T : Scheme.{u}) [IsNoetherian T] (_hT : IsUnit (N : Γ(T, ⊤))) (d : ℕ)
    (adj : rightDerivedLowerShriek (ModuleCat.{u + 1} A)
      (AffineSpace (ULift.{u} (Fin d)) T ↘ T) ⊣ affineRight A N hA T d) :
    dualizingComplex A
      (AffineSpace (ULift.{u} (Fin d)) T ↘ T) ≅
        tateObject A N hA (AffineSpace (ULift.{u} (Fin d)) T) d :=
  ((rightDerivedUpperShriekAdjunction A
      (AffineSpace (ULift.{u} (Fin d)) T ↘ T)).rightAdjointUniq
        adj).app
          (𝟙_ _) ≪≫
    (shiftFunctor _ (2 * (d : ℤ))).mapIso
      ((derivedTensorRight (ModuleCat.{u + 1} A) (AffineSpace (ULift.{u} (Fin d)) T)
          ((_root_.DerivedCategory.singleFunctor _ 0).obj
            (Scheme.finiteEtaleTateTwist (AffineSpace (ULift.{u} (Fin d)) T) N A hA d))).mapIso
        ((leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A)
          (AffineSpace (ULift.{u} (Fin d)) T ↘ T)).symm.app (𝟙_ _) ≪≫
            leftDerivedUpperStarUnitIso (ModuleCat.{u + 1} A)
              (AffineSpace (ULift.{u} (Fin d)) T ↘ T)) ≪≫
        derivedTensorLeftUnitor (ModuleCat.{u + 1} A) _ _)

/-- Pull the affine comparison to a section and use canonical Tate pullback.
Source: sk-thm-dnc, Local construction
(blueprint: def-trf-section-local-comparison-data). -/
@[irreducible]
def affineSectionIso (A : Type (u + 1)) [CommRing A] [Finite A]
    (N : ℕ) (hN : 0 < N) (hA : (N : A) = 0)
    (T : Scheme.{u}) [IsNoetherian T] (hT : IsUnit (N : Γ(T, ⊤))) (d : ℕ)
    (r : T ⟶ AffineSpace (ULift.{u} (Fin d)) T)
    (adj : rightDerivedLowerShriek (ModuleCat.{u + 1} A)
      (AffineSpace (ULift.{u} (Fin d)) T ↘ T) ⊣ affineRight A N hA T d) :
    sectionInvariant A (AffineSpace (ULift.{u} (Fin d)) T ↘ T) r ≅ tateObject A N hA T d :=
  (upperStar (ModuleCat.{u + 1} A) r).leftDerivedFunctor.mapIso
      (affineDualizingIso A N hN hA T hT d adj) ≪≫
    tatePullback A N hN hA r
      (invertibleOnSource N (AffineSpace (ULift.{u} (Fin d)) T ↘ T) hT) hT d

/-- Finite-type sources over a Noetherian scheme are Noetherian.
Source: sk-thm-dnc, domain checks (blueprint: def-trf-section-local-comparison-data).
Proof: local finite type preserves local Noetherianity, and quasi-compactness over
quasi-compact T makes the source quasi-compact. Apply IsNoetherian.mk. -/
theorem noetherianSource {X T : Scheme.{u}} [IsNoetherian T] (v : X ⟶ T)
    [LocallyOfFiniteType v] [QuasiCompact v] : IsNoetherian X := by
  exact isNoetherian_of_locallyOfFiniteType v

/-- Restriction to compatible sections of the unique counit-compatible locality comparison.
Source: sk-thm-dnc, Local construction
(blueprint: def-trf-section-local-comparison-data). -/
@[irreducible]
def sectionLocality (A : Type (u + 1)) [CommRing A] [Finite A]
    {U X T : Scheme.{u}} [IsNoetherian U] [IsNoetherian X] [IsNoetherian T]
    (v : U ⟶ X) [Etale v] [IsSeparated v] [LocallyOfFiniteType v] [QuasiCompact v]
    (f : X ⟶ T) [HasCompactification f] (f' : U ⟶ T) [HasCompactification f']
    (w : v ≫ f = f') (r : T ⟶ X) (r' : T ⟶ U) (hr : r' ≫ v = r) :
    sectionInvariant A f r ≅ sectionInvariant A f' r' := by
  subst f'
  let l := (existsUnique_etaleAmbientAdjointLocalityIso A v f
    (HasCompactification.compactification f) (HasCompactification.compactification (v ≫ f))
    (rightDerivedUpperShriek A f)
    (rightDerivedUpperShriek A (v ≫ f))
    (rightDerivedUpperShriekAdjunction A f)
    (rightDerivedUpperShriekAdjunction A (v ≫ f))).exists.choose
  exact (leftDerivedUpperStarComp (ModuleCat.{u + 1} A) r' v r hr.symm).app _ ≪≫
    (upperStar (ModuleCat.{u + 1} A) r').leftDerivedFunctor.mapIso
      ((leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) v).app _ ≪≫
        l.app (𝟙_ _))

/-- Section-chart identification: invert the counit-normalized locality map, then apply
its standard affine-space adjunction. No orientation of a fibre is supplied.
Source: sk-thm-dnc, Local construction
(blueprint: def-trf-section-local-comparison-data). -/
@[irreducible]
def chartMap (A : Type (u + 1)) [CommRing A] [Finite A]
    (N : ℕ) (hN : 0 < N) (hA : (N : A) = 0)
    {X T : Scheme.{u}} [IsNoetherian X] [IsNoetherian T]
    (hT : IsUnit (N : Γ(T, ⊤))) (d : ℕ) (f : X ⟶ T) [HasCompactification f]
    (r : T ⟶ X) (e : X ⟶ AffineSpace (ULift.{u} (Fin d)) T)
    [Etale e] [IsSeparated e] [LocallyOfFiniteType e] [QuasiCompact e]
    (w : e ≫ (AffineSpace (ULift.{u} (Fin d)) T ↘ T) = f)
    (adj : rightDerivedLowerShriek (ModuleCat.{u + 1} A)
      (AffineSpace (ULift.{u} (Fin d)) T ↘ T) ⊣ affineRight A N hA T d) :
    sectionInvariant A f r ⟶ tateObject A N hA T d :=
  letI : IsNoetherian (AffineSpace (ULift.{u} (Fin d)) T) :=
    noetherianSource (AffineSpace (ULift.{u} (Fin d)) T ↘ T)
  (sectionLocality A e (AffineSpace (ULift.{u} (Fin d)) T ↘ T) f w
    (r ≫ e) r rfl).inv ≫ (affineSectionIso A N hN hA T hT d (r ≫ e) adj).hom

/-- The raw local comparison from the two chart identifications and Tate pullback.
Source: sk-thm-dnc, Local construction, composition of identifications
(blueprint: def-trf-section-local-comparison-data). -/
@[irreducible]
def rawComparison (A : Type (u + 1)) [CommRing A] (N : ℕ) (hN : 0 < N)
    (hA : (N : A) = 0) (T : Scheme.{u}) (hT : IsUnit (N : Γ(T, ⊤))) (d : ℕ)
    (C : DerivedCategoryModule A T)
    (F : DerivedCategoryModule A (AffineSpace (ULift.{u} (Fin 1)) T))
    (c : C ≅ tateObject A N hA T d)
    (f : F ≅ tateObject A N hA (AffineSpace (ULift.{u} (Fin 1)) T) d) :
    F ≅ (upperStar (ModuleCat.{u + 1} A)
      (AffineSpace (ULift.{u} (Fin 1)) T ↘ T)).leftDerivedFunctor.obj C :=
  f ≪≫ (tatePullback A N hN hA (AffineSpace (ULift.{u} (Fin 1)) T ↘ T) hT
    (invertibleOnSource N (AffineSpace (ULift.{u} (Fin 1)) T ↘ T) hT) d).symm ≪≫
      (upperStar (ModuleCat.{u + 1} A)
        (AffineSpace (ULift.{u} (Fin 1)) T ↘ T)).leftDerivedFunctor.mapIso c.symm

/-- Restriction at one, including the specified inverse-image section compositor.
Source: sk-thm-dnc, correction at one
(blueprint: def-trf-section-local-comparison-data). -/
@[irreducible]
def restrictionAtOne (A : Type (u + 1)) [CommRing A] (T : Scheme.{u})
    {C : DerivedCategoryModule A T}
    {F : DerivedCategoryModule A (AffineSpace (ULift.{u} (Fin 1)) T)}
    (l : F ≅ (upperStar (ModuleCat.{u + 1} A)
      (AffineSpace (ULift.{u} (Fin 1)) T ↘ T)).leftDerivedFunctor.obj C) :
    (upperStar (ModuleCat.{u + 1} A)
      (AffineSpace.oneSection (ULift.{u} (Fin 1)) T)).leftDerivedFunctor.obj F ≅ C :=
  (upperStar (ModuleCat.{u + 1} A)
    (AffineSpace.oneSection (ULift.{u} (Fin 1)) T)).leftDerivedFunctor.mapIso l ≪≫
      (leftDerivedUpperStarCompSectionIso (ModuleCat.{u + 1} A)
        (AffineSpace.oneSection (ULift.{u} (Fin 1)) T)
        (AffineSpace (ULift.{u} (Fin 1)) T ↘ T)
        (AffineSpace.oneSection_comp_over (ULift.{u} (Fin 1)) T)).app C

/-- The discrepancy h = (i1*lambda) theta^(-1), in composition order.
Source: sk-thm-dnc, correction at one
(blueprint: def-trf-section-local-comparison-data). -/
@[irreducible]
def discrepancy (A : Type (u + 1)) [CommRing A] (T : Scheme.{u})
    {C : DerivedCategoryModule A T}
    {F : DerivedCategoryModule A (AffineSpace (ULift.{u} (Fin 1)) T)}
    (l : F ≅ (upperStar (ModuleCat.{u + 1} A)
      (AffineSpace (ULift.{u} (Fin 1)) T ↘ T)).leftDerivedFunctor.obj C)
    (theta : (upperStar (ModuleCat.{u + 1} A)
      (AffineSpace.oneSection (ULift.{u} (Fin 1)) T)).leftDerivedFunctor.obj F ≅ C) : C ≅ C :=
  theta.symm ≪≫ restrictionAtOne A T l

/-- The normalization is lambda followed by a*(h^(-1)).
Source: sk-thm-dnc, correction at one
(blueprint: def-trf-section-local-comparison-data). -/
@[irreducible]
def normalizedComparison (A : Type (u + 1)) [CommRing A] (T : Scheme.{u})
    {C : DerivedCategoryModule A T}
    {F : DerivedCategoryModule A (AffineSpace (ULift.{u} (Fin 1)) T)}
    (l : F ≅ (upperStar (ModuleCat.{u + 1} A)
      (AffineSpace (ULift.{u} (Fin 1)) T ↘ T)).leftDerivedFunctor.obj C)
    (theta : (upperStar (ModuleCat.{u + 1} A)
      (AffineSpace.oneSection (ULift.{u} (Fin 1)) T)).leftDerivedFunctor.obj F ≅ C) :
    F ≅ (upperStar (ModuleCat.{u + 1} A)
      (AffineSpace (ULift.{u} (Fin 1)) T ↘ T)).leftDerivedFunctor.obj C :=
  l ≪≫ (upperStar (ModuleCat.{u + 1} A)
    (AffineSpace (ULift.{u} (Fin 1)) T ↘ T)).leftDerivedFunctor.mapIso
      (discrepancy A T l theta).symm

/-- Restrict the actual theta to the local affine base, using only inverse-image compositors.
Source: sk-thm-dnc, correction at one
(blueprint: def-trf-section-local-comparison-data). -/
@[irreducible]
def restrictedTheta (A : Type (u + 1)) [CommRing A] [Finite A]
    {V S T : Scheme.{u}} (g : V ⟶ S) [HasCompactification g] [QuasiCompact g]
    (s : S ⟶ V) [IsClosedImmersion s] (hs : s ≫ g = 𝟙 S)
    [HasCompactification (Scheme.Hom.deformationSpaceProj g s)] (b : T ⟶ S) :
    (upperStar (ModuleCat.{u + 1} A)
      (AffineSpace.oneSection (ULift.{u} (Fin 1)) T)).leftDerivedFunctor.obj
        ((upperStar (ModuleCat.{u + 1} A)
          (AffineSpace.map (ULift.{u} (Fin 1)) b)).leftDerivedFunctor.obj (family A g s)) ⟶
      (upperStar (ModuleCat.{u + 1} A) b).leftDerivedFunctor.obj (sectionInvariant A g s) :=
  ((leftDerivedUpperStarComp (ModuleCat.{u + 1} A)
    (AffineSpace.oneSection (ULift.{u} (Fin 1)) T)
    (AffineSpace.map (ULift.{u} (Fin 1)) b)).app _).inv ≫
      ((leftDerivedUpperStarComp (ModuleCat.{u + 1} A) b
        (AffineSpace.oneSection (ULift.{u} (Fin 1)) S)
        (AffineSpace.oneSection (ULift.{u} (Fin 1)) T ≫
          AffineSpace.map (ULift.{u} (Fin 1)) b)
        (AffineSpace.oneSection_comp_map b)).app _).hom ≫
      (upperStar (ModuleCat.{u + 1} A) b).leftDerivedFunctor.map (atOne A g s hs)
end AlgebraicGeometry.Etale.SectionLocalDualizingComparisons
