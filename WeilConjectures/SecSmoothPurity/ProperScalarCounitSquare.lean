/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProEtaleFiniteModulesSupplement
public import WeilConjectures.Algebra.Homology.SheafRingDerivedCoefficientAdjunction
public import WeilConjectures.Algebra.Homology.DerivedChangeOfRingsIndependentCoefficients
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
public import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
public import WeilConjectures.Algebra.Homology.KFlatSupplement
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
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.SiteTensorFunctorialitySupplement
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
public import WeilConjectures.CategoryTheory.RingedSiteModules
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
public import WeilConjectures.AlgebraicGeometry.ProEtaleConstantRingOperations
public import WeilConjectures.AlgebraicGeometry.ProEtaleRingSheafChangeAdjunctionSupplement
public import WeilConjectures.AlgebraicGeometry.ProEtaleDirectImageRestrictionOfScalars
public import WeilConjectures.CategoryTheory.RingedToposDerivedPushforwardComposition
public import WeilConjectures.CategoryTheory.RingedToposMorphismSupplement
public import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
public import WeilConjectures.CategoryTheory.RingedSiteKInjectiveResolutionsSupplement
public import WeilConjectures.Mathlib.Algebra.Homology.GrothendieckAbelian
public import Mathlib.CategoryTheory.Localization.DerivabilityStructure.Derives
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Flat
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Defs
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution
public import WeilConjectures.Algebra.Homology.KFlatResolution
public import WeilConjectures.CategoryTheory.RingedToposKFlatPullback
public import WeilConjectures.CategoryTheory.AlgebraicInverseImage
public import Mathlib.Algebra.Category.ModuleCat.Sheaf
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.Algebra.Category.Grp.Limits
public import Mathlib.CategoryTheory.Sites.Whiskering
public import WeilConjectures.CategoryTheory.GeometricModuleConstruction
public import WeilConjectures.CategoryTheory.RingedToposRingData
public import WeilConjectures.CategoryTheory.AdjunctionRingOperations
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
public import Mathlib.CategoryTheory.Adjunction.Basic
public import Mathlib.CategoryTheory.Sites.CartesianMonoidal
public import Mathlib.CategoryTheory.Monoidal.CommGrp_
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Mod
public import WeilConjectures.CategoryTheory.GeometricModuleTransport
public import Mathlib.CategoryTheory.Adjunction.Limits
public import WeilConjectures.CategoryTheory.GeometricRingTransport
public import Mathlib.CategoryTheory.Sites.Limits
public import WeilConjectures.CategoryTheory.SheavesAlgebraicStructuresRingCore
public import WeilConjectures.CategoryTheory.SheafRingObjectReconstruction
public import WeilConjectures.CategoryTheory.Adjunction.FiniteProductRingFunctor
public import WeilConjectures.CategoryTheory.ModulePullbackPushforwardAdjunctionSupplement
public import WeilConjectures.AlgebraicGeometry.KFlatRingedToposPullback
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
public import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
public import WeilConjectures.CategoryTheory.Sites.InverseImageLocalFamilies
public import Mathlib.CategoryTheory.Sites.Sheaf
public import Mathlib.CategoryTheory.Sites.LocallyBijective
public import Mathlib.CategoryTheory.Limits.Types.Pullbacks
public import Mathlib.CategoryTheory.Functor.EpiMono
public import Mathlib.CategoryTheory.Limits.Types.Equalizers
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Equalizers
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.ScalarTensorComparisonOfUniverses
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
public import Mathlib.Algebra.Homology.HomotopyCategory.MappingCone
public import Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
public import WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
public import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
public import WeilConjectures.Algebra.Homology.RingedToposAdaptedFlatResolution
public import WeilConjectures.Algebra.Homology.RingedToposPullbackFilteredColimits
public import Mathlib.CategoryTheory.Sites.PreservesSheafification
public import Mathlib.CategoryTheory.Limits.Preserves.Limits
public import Mathlib.CategoryTheory.ObjectProperty.ColimitsOfShape
public import Mathlib.Algebra.Homology.Embedding.CochainComplex
public import WeilConjectures.Algebra.Homology.RingedToposAcyclicKFlatPullback
public import WeilConjectures.Algebra.Homology.BoundedFlatIndependentCoefficients
public import Mathlib.CategoryTheory.Monoidal.Preadditive
public import WeilConjectures.AlgebraicGeometry.RingedTopoiDerivedPullback
public import WeilConjectures.Algebra.Homology.ChangeOfRingsKFlatQuasiIsoSupplement
public import Mathlib.CategoryTheory.Sites.EpiMono
public import Mathlib.Algebra.Category.Grp.EpiMono
public import Mathlib.Algebra.Category.Grp.Abelian
public import Mathlib.CategoryTheory.Sites.Abelian
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.MonoidalClosed
public import WeilConjectures.AlgebraicGeometry.RingedTopoiCanonicalTensorPullbackOfUniverses
public import WeilConjectures.SecSmoothPurity.DirectImageScalarOperations
public import WeilConjectures.AlgebraicGeometry.FourCornersSupplement

/-!
# Direct-image restriction and the scalar counit square

Source: Stacks Project, Cohomology on Sites, Tags 07A6, 0D6D and 0D6E;
blueprint det-sp-tower-gluing, Levels paragraph
(blueprint: lem-sp-proper-scalar-counit-square).

The scalar extension, geometric adjunction and balanced pullback comparison are the
published canonical constructions. The direct-image comparison below specializes the
normalized ring-sheaf comparison, in the inverse direction. The theorem identifies its
resolution normalization and states both counit equations on the entire unbounded category.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 2048

universe u

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme

private noncomputable def scalarSquareDerivedUnit
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D] [Abelian.HasKInjectiveResolutions C]
    (F : C ⥤ D) [F.Additive] (K : CochainComplex C ℤ) :
    DerivedCategory.Q.obj ((F.mapHomologicalComplex (.up ℤ)).obj K) ⟶
      F.rightDerivedFunctor.obj (DerivedCategory.Q.obj K) :=
  (DerivedCategory.quotientCompQhIso _).inv.app _ ≫
    F.rightDerivedFunctorUnit.app ((HomotopyCategory.quotient _ _).obj K) ≫
    F.rightDerivedFunctor.map ((DerivedCategory.quotientCompQhIso _).hom.app K)

private theorem scalarSquareDerivedUnit_eq_inv
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D] [Abelian.HasKInjectiveResolutions C]
    (F : C ⥤ D) [F.Additive] (K : CochainComplex C ℤ) [K.IsKInjective] :
    scalarSquareDerivedUnit F K = (F.rightDerivedFunctorObjQIso K).inv := by
  simp only [scalarSquareDerivedUnit, Functor.rightDerivedFunctorObjQIso,
    Iso.trans_inv, Iso.symm_inv, Iso.app_inv, Iso.app_hom, Functor.mapIso_inv,
    asIso_hom, Category.assoc]

private theorem scalarSquareDerivedUnit_eq_homotopyUnit
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D] [Abelian.HasKInjectiveResolutions C]
    (F : C ⥤ D) [F.Additive] (K : CochainComplex C ℤ) :
    scalarSquareDerivedUnit F K =
      F.rightDerivedFunctorUnit.app ((HomotopyCategory.quotient _ _).obj K) := by
  change 𝟙 _ ≫ F.rightDerivedFunctorUnit.app
      ((HomotopyCategory.quotient _ _).obj K) ≫
      F.rightDerivedFunctor.map (𝟙 (DerivedCategory.Q.obj K)) = _
  erw [F.rightDerivedFunctor.map_id, Category.id_comp, Category.comp_id]

private theorem scalarSquareDerivedUnit_naturality
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D] [Abelian.HasKInjectiveResolutions C]
    (F : C ⥤ D) [F.Additive] {K L : CochainComplex C ℤ} (j : K ⟶ L) :
    DerivedCategory.Q.map ((F.mapHomologicalComplex (.up ℤ)).map j) ≫
        scalarSquareDerivedUnit F L =
      scalarSquareDerivedUnit F K ≫ F.rightDerivedFunctor.map (DerivedCategory.Q.map j) := by
  have hh := F.rightDerivedFunctorUnit.naturality ((HomotopyCategory.quotient _ _).map j)
  change DerivedCategory.Q.map ((F.mapHomologicalComplex (.up ℤ)).map j) ≫
      F.rightDerivedFunctorUnit.app ((HomotopyCategory.quotient _ _).obj L) =
    F.rightDerivedFunctorUnit.app ((HomotopyCategory.quotient _ _).obj K) ≫
      F.rightDerivedFunctor.map (DerivedCategory.Q.map j) at hh
  simpa only [scalarSquareDerivedUnit_eq_homotopyUnit] using hh

namespace AlgebraicGeometry.ProEtale

/-- Exact termwise scalar restriction along the specified constant-ring map.
Source: Stacks Tags 03DA and 07A6
(blueprint: lem-sp-proper-scalar-counit-square). -/
abbrev directImageScalarRestriction {A B : Type u} [CommRing A] [CommRing B]
    (φ : A →+* B) (T : Scheme.{u}) :
    T.proEtaleDerivedCategory B ⥤ T.proEtaleDerivedCategory A :=
  (proEtaleRingRestrictScalars (proEtaleConstantRingMap (T := T) φ)).mapDerivedCategory

/-- The representative-normalized extension/restriction adjunction already used by the
canonical balancing comparison. Source: Stacks Tag 07A6
(blueprint: lem-sp-proper-scalar-counit-square). -/
abbrev directImageScalarAdjunction {A B : Type u} [CommRing A] [CommRing B]
    (φ : A →+* B) (T : Scheme.{u}) :
    directImageScalarExtension φ T ⊣ directImageScalarRestriction φ T :=
  proEtaleRingDerivedExtensionAdjunction (proEtaleConstantRingMap (T := T) φ)

/-- The comparison D is the inverse of the normalized ring-sheaf comparison d.
The coefficient-square proof is the naturality of the constant-section map, so no
extra coefficient compatibility is assumed. Source: Stacks Tag 0D6E
(blueprint: lem-sp-proper-scalar-counit-square). -/
def directImageScalarRestrictionIso {A B : Type u} [CommRing A] [CommRing B]
    (φ : A →+* B) {Z Y : Scheme.{u}} (h : Z ⟶ Y) :
    directImageScalarRestriction φ Z ⋙ directImageConstantPush A h ≅
      directImageConstantPush B h ⋙ directImageScalarRestriction φ Y :=
  (proEtaleRingRestrictionDerivedDirectImage h
    (proEtaleConstantRing Y A) (proEtaleConstantRing Y B)
    (proEtaleConstantRing Z A) (proEtaleConstantRing Z B)
    (proEtaleConstantRingMap (T := Y) φ) (proEtaleConstantRingMap (T := Z) φ)
    (proEtaleConstantRingComparison h A) (proEtaleConstantRingComparison h B)
    (proEtaleConstantInverseImageMap_naturality h
      (CommRingCat.ofHom (RingHom.ulift φ))).symm).symm

set_option maxHeartbeats 1000000 in
-- The four adjunctions and representative identifications require substantial elaboration.
/-- The proper scalar counit square, which in fact needs no properness.
The already defined natural transformation `directImageScalarComparison` is gamma.
The first clause gives its defining geometric transpose, the second its naturality,
the third the compatibility of the composite adjunctions and the scalar counit square.
The final clause identifies D with the direct-image restriction comparison on every
K-injective representative, using the same composition normalization kappa.

Source: Stacks Tags 07A6, 0D6D and 0D6E; blueprint det-sp-tower-gluing, Levels
(blueprint: lem-sp-proper-scalar-counit-square).

Proof:
1. The geometric Hom bijection defines gamma uniquely by transposing
   chi followed by T_Z(e^A). Its unit formula and naturality of chi and e^A
   give the first two clauses (def-weil-pbc-proetale-operations).
2. Apply lem-weil-pbc-ring-sheaf-change-adjunction to the B-geometric counit.
   The triangle identity gives r_Z(e^B) after b inverse equal to e^A followed
   by P_A(d), with precisely the specified d. Constant-section naturality
   supplies the coefficient square (prop-weil-pbc-proetale-constant-ring-map).
3. On a flat-term K-flat resolution P of r_Y(H), the scalar counit is the
   B-linear extension of P to H, x tensor b mapping to b g(x).
   Pullback preserves these resolutions (lem-weil-pbc-ringed-pullback-preserves-kflat).
   The balanced chi inverse and the scalar counit after pullback give the same
   extension. Sheaf tensor universality and localization prove the counit equality
   (lem-pur-sheaf-ring-derived-coefficient-adjunction and
   lem-weil-pbc-ringed-topoi-derived-tensor-pullback).
4. Substitute that equality in the composite-adjunction counit formula
   (def-weil-pbc-composite-adjunction). Naturality of the scalar counit and step 2
   give the displayed composite-adjunction equation.
5. Geometrically transpose both sides of the scalar square. Step 4, naturality
   of chi and cancellation of d with D give T_Z(e^A) followed by chi on both
   sides. Injectivity of the geometric Hom bijection gives the scalar square.
6. Write the two coefficient factorizations as identity-topos coefficient
   morphisms. The normalization of lem-weil-pbc-ringed-topoi-derived-pushforward-composition
   gives d as kappa for the first factorization times inverse kappa for the second.
   For a K-injective J and a resolution j of its restriction, the first factor
   is the class of h_*(j); the exact restriction comparisons cancel in the second.
   Inverting gives exactly lem-weil-proetale-direct-image-restriction-of-scalars,
   expressed by the final equality with the canonical Q and resolution factors.
   No restriction-preservation of K-injectivity, flatness or boundedness is used. -/
theorem properScalarCounitSquare
    {A B : Type u} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) {Z Y : Scheme.{u}} (h : Z ⟶ Y) :
    (∀ N : Z.proEtaleDerivedCategory A,
      (proEtaleConstantRingDerivedPullback B h).map
          ((directImageScalarComparison φ h).app N) ≫
        (directImageConstantAdjunction B h).counit.app
          ((directImageScalarExtension φ Z).obj N) =
      (directImageScalarPullbackIso φ h).hom.app ((directImageConstantPush A h).obj N) ≫
        (directImageScalarExtension φ Z).map
          ((directImageConstantAdjunction A h).counit.app N)) ∧
    (∀ (N N' : Z.proEtaleDerivedCategory A) (v : N ⟶ N'),
      (directImageScalarExtension φ Y).map ((directImageConstantPush A h).map v) ≫
          (directImageScalarComparison φ h).app N' =
        (directImageScalarComparison φ h).app N ≫
          (directImageConstantPush B h).map ((directImageScalarExtension φ Z).map v)) ∧
    (∀ H : Z.proEtaleDerivedCategory B,
      ((directImageScalarPullbackIso φ h).inv.app
          ((directImageScalarRestriction φ Y).obj ((directImageConstantPush B h).obj H)) ≫
        (proEtaleConstantRingDerivedPullback B h).map
          ((directImageScalarAdjunction φ Y).counit.app ((directImageConstantPush B h).obj H)) ≫
        (directImageConstantAdjunction B h).counit.app H =
      (directImageScalarExtension φ Z).map
          ((proEtaleConstantRingDerivedPullback A h).map
            ((directImageScalarRestrictionIso φ h).inv.app H)) ≫
        (directImageScalarExtension φ Z).map
          ((directImageConstantAdjunction A h).counit.app
            ((directImageScalarRestriction φ Z).obj H)) ≫
        (directImageScalarAdjunction φ Z).counit.app H) ∧
      ((directImageScalarExtension φ Y).map
          ((directImageScalarRestrictionIso φ h).hom.app H) ≫
        (directImageScalarAdjunction φ Y).counit.app ((directImageConstantPush B h).obj H) =
      (directImageScalarComparison φ h).app ((directImageScalarRestriction φ Z).obj H) ≫
        (directImageConstantPush B h).map ((directImageScalarAdjunction φ Z).counit.app H))) ∧
    (∀ (J : CochainComplex (Z.proEtaleRingModules (proEtaleConstantRing Z B)) ℤ)
      [J.IsKInjective]
      (I : CochainComplex (Z.proEtaleRingModules (proEtaleConstantRing Z A)) ℤ)
      [I.IsKInjective]
      (j : ((proEtaleRingRestrictScalars
        (proEtaleConstantRingMap (T := Z) φ)).mapHomologicalComplex (.up ℤ)).obj J ⟶ I)
      [QuasiIso j],
      QuasiIso (((proEtaleConstantRingPushforward A h).mapHomologicalComplex (.up ℤ)).map j) ∧
      (directImageScalarRestrictionIso φ h).hom.app (DerivedCategory.Q.obj J) ≫
          (directImageScalarRestriction φ Y).map
            ((proEtaleConstantRingPushforward B h).rightDerivedFunctorObjQIso J).hom ≫
          (proEtaleRingRestrictScalars
            (proEtaleConstantRingMap (T := Y) φ)).mapDerivedCategoryFactors.hom.app
              (((proEtaleConstantRingPushforward B h).mapHomologicalComplex (.up ℤ)).obj J) ≫
          DerivedCategory.Q.map
            ((NatIso.mapHomologicalComplex
              (proEtaleRingRestrictionDirectImage h
                (proEtaleConstantRing Y A) (proEtaleConstantRing Y B)
                (proEtaleConstantRing Z A) (proEtaleConstantRing Z B)
                (proEtaleConstantRingMap (T := Y) φ) (proEtaleConstantRingMap (T := Z) φ)
                (proEtaleConstantRingComparison h A) (proEtaleConstantRingComparison h B)
                (proEtaleConstantInverseImageMap_naturality h
                  (CommRingCat.ofHom (RingHom.ulift φ))).symm) (.up ℤ)).hom.app J) ≫
          DerivedCategory.Q.map
            (((proEtaleConstantRingPushforward A h).mapHomologicalComplex (.up ℤ)).map j) =
        (directImageConstantPush A h).map
            ((proEtaleRingRestrictScalars
              (proEtaleConstantRingMap (T := Z) φ)).mapDerivedCategoryFactors.hom.app J) ≫
          (directImageConstantPush A h).map (DerivedCategory.Q.map j) ≫
          ((proEtaleConstantRingPushforward A h).rightDerivedFunctorObjQIso I).hom) := by
  let av := directImageScalarAdjunction φ Y
  let au := directImageScalarAdjunction φ Z
  let ar := directImageConstantAdjunction A h
  let az := directImageConstantAdjunction B h
  let b := proEtaleRingRestrictionDerivedPullback h
    (proEtaleConstantRing Y A) (proEtaleConstantRing Y B)
    (proEtaleConstantRing Z A) (proEtaleConstantRing Z B)
    (proEtaleConstantRingMap (T := Y) φ) (proEtaleConstantRingMap (T := Z) φ)
    (proEtaleConstantRingComparison h A) (proEtaleConstantRingComparison h B)
    (proEtaleConstantInverseImageMap_naturality h
      (CommRingCat.ofHom (RingHom.ulift φ))).symm
  let d := (directImageScalarRestrictionIso φ h).symm
  let χ := directImageScalarPullbackIso φ h
  let α := TwoSquare.mk _ _ _ _ b.inv
  have hmate : (mateEquiv az ar α).natTrans = d.hom := by
    apply NatTrans.ext
    funext N
    have hh := (proEtaleRingSheafChangeAdjunction h
      (proEtaleConstantRing Y A) (proEtaleConstantRing Y B)
      (proEtaleConstantRing Z A) (proEtaleConstantRing Z B)
      (proEtaleConstantRingMap (T := Y) φ) (proEtaleConstantRingMap (T := Z) φ)
      (proEtaleConstantRingComparison h A) (proEtaleConstantRingComparison h B)
      (proEtaleConstantInverseImageMap_naturality h
        (CommRingCat.ofHom (RingHom.ulift φ))).symm).2.2
      ((directImageConstantPush B h).obj N) N (az.counit.app N)
    have hid : az.homEquiv _ _ (az.counit.app N) = 𝟙 _ := by
      rw [← az.homEquiv_symm_id N]
      exact (az.homEquiv _ _).apply_symm_apply _
    change ar.homEquiv _ _ (b.inv.app _ ≫
      (directImageScalarRestriction φ Z).map (az.counit.app N)) =
        (directImageScalarRestriction φ Y).map
          (az.homEquiv _ _ (az.counit.app N)) ≫ d.hom.app N at hh
    rw [hid, CategoryTheory.Functor.map_id, Category.id_comp] at hh
    rw [← hh]
    simp only [α, mateEquiv_apply, TwoSquare.mk, TwoSquare.natTrans, NatTrans.comp_app,
      Functor.comp_obj, Functor.comp_map, Functor.rightUnitor_inv_app,
      Functor.whiskerLeft_app, Functor.whiskerRight_app, Functor.associator_hom_app,
      Functor.associator_inv_app, Functor.leftUnitor_hom_app, Category.id_comp,
      Adjunction.homEquiv_unit, Functor.map_comp]
    erw [Category.comp_id]
  have hm : mateEquiv av au χ.inv = α := (mateEquiv av au).apply_symm_apply α
  have hc : conjugateEquiv (av.comp az) (ar.comp au) χ.inv = d.hom := by
    rw [← iterated_mateEquiv_conjugateEquiv av au ar az χ.inv, hm, hmate]
  have he (H : Z.proEtaleDerivedCategory B) :
      χ.inv.app ((directImageScalarRestriction φ Y).obj
          ((directImageConstantPush B h).obj H)) ≫
        (proEtaleConstantRingDerivedPullback B h).map
          (av.counit.app ((directImageConstantPush B h).obj H)) ≫ az.counit.app H =
      (directImageScalarExtension φ Z).map
          ((proEtaleConstantRingDerivedPullback A h).map (d.hom.app H)) ≫
        (directImageScalarExtension φ Z).map
          (ar.counit.app ((directImageScalarRestriction φ Z).obj H)) ≫ au.counit.app H := by
    have hh := conjugateEquiv_counit (av.comp az) (ar.comp au) χ.inv H
    rw [hc] at hh
    simpa only [Adjunction.comp_counit_app, Functor.comp_map, Functor.comp_obj,
      Category.assoc] using hh.symm
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro N
    exact mateEquiv_counit ar az χ.hom N
  · intro N N' v
    exact (directImageScalarComparison φ h).naturality v
  · intro H
    refine ⟨he H, ?_⟩
    apply (az.homEquiv _ _).symm.injective
    simp only [Adjunction.homEquiv_counit, Functor.map_comp, Category.assoc]
    rw [az.counit_naturality]
    have hg := mateEquiv_counit ar az χ.hom ((directImageScalarRestriction φ Z).obj H)
    change (proEtaleConstantRingDerivedPullback B h).map
        ((directImageScalarComparison φ h).app ((directImageScalarRestriction φ Z).obj H)) ≫
          az.counit.app _ = _ at hg
    rw [reassoc_of% hg]
    have ht := congrArg (fun t ↦ χ.hom.app _ ≫ t) (he H)
    simp only [Iso.hom_inv_id_app_assoc] at ht
    rw [ht]
    have hn := χ.hom.naturality ((directImageScalarRestrictionIso φ h).hom.app H)
    dsimp only [Functor.comp_map] at hn
    rw [reassoc_of% hn]
    rw [← Functor.map_comp_assoc, ← Functor.map_comp]
    simp only [d, Iso.symm_hom, Iso.hom_inv_id_app]
    erw [(proEtaleConstantRingDerivedPullback A h).map_id,
      (directImageScalarExtension φ Z).map_id, Category.id_comp]
  · intro J hJ I hI j hj
    let F := proEtaleConstantRingPushforward A h
    let G := proEtaleConstantRingPushforward B h
    let rY := proEtaleRingRestrictScalars (proEtaleConstantRingMap (T := Y) φ)
    let rZ := proEtaleRingRestrictScalars (proEtaleConstantRingMap (T := Z) φ)
    let c := proEtaleRingRestrictionDirectImage h
      (proEtaleConstantRing Y A) (proEtaleConstantRing Y B)
      (proEtaleConstantRing Z A) (proEtaleConstantRing Z B)
      (proEtaleConstantRingMap (T := Y) φ) (proEtaleConstantRingMap (T := Z) φ)
      (proEtaleConstantRingComparison h A) (proEtaleConstantRingComparison h B)
      (proEtaleConstantInverseImageMap_naturality h
        (CommRingCat.ofHom (RingHom.ulift φ))).symm
    have hu := (Classical.choose_spec
      (proEtaleRingRestrictionDerivedDirectImage_existsUnique h
        (proEtaleConstantRing Y A) (proEtaleConstantRing Y B)
        (proEtaleConstantRing Z A) (proEtaleConstantRing Z B)
        (proEtaleConstantRingMap (T := Y) φ) (proEtaleConstantRingMap (T := Z) φ)
        (proEtaleConstantRingComparison h A) (proEtaleConstantRingComparison h B)
        (proEtaleConstantInverseImageMap_naturality h
          (CommRingCat.ofHom (RingHom.ulift φ))).symm)).1 J
    change rY.mapDerivedCategory.map (scalarSquareDerivedUnit G J) ≫
        d.hom.app (DerivedCategory.Q.obj J) ≫
        F.rightDerivedFunctor.map (rZ.mapDerivedCategoryFactors.hom.app J) =
      rY.mapDerivedCategoryFactors.hom.app
          ((G.mapHomologicalComplex (.up ℤ)).obj J) ≫
        DerivedCategory.Q.map
          ((NatIso.mapHomologicalComplex c (.up ℤ)).hom.app J) ≫
        scalarSquareDerivedUnit F ((rZ.mapHomologicalComplex (.up ℤ)).obj J) at hu
    rw [scalarSquareDerivedUnit_eq_inv G J] at hu
    have hunit : IsIso
        (scalarSquareDerivedUnit F ((rZ.mapHomologicalComplex (.up ℤ)).obj J)) := by
      have hh : IsIso
          (rY.mapDerivedCategoryFactors.hom.app
              ((G.mapHomologicalComplex (.up ℤ)).obj J) ≫
            DerivedCategory.Q.map
              ((NatIso.mapHomologicalComplex c (.up ℤ)).hom.app J) ≫
            scalarSquareDerivedUnit F ((rZ.mapHomologicalComplex (.up ℤ)).obj J)) := by
        rw [← hu]
        infer_instance
      have hh' := IsIso.of_isIso_comp_left
        (rY.mapDerivedCategoryFactors.hom.app
          ((G.mapHomologicalComplex (.up ℤ)).obj J))
        (DerivedCategory.Q.map ((NatIso.mapHomologicalComplex c (.up ℤ)).hom.app J) ≫
          scalarSquareDerivedUnit F ((rZ.mapHomologicalComplex (.up ℤ)).obj J))
      exact IsIso.of_isIso_comp_left
        (DerivedCategory.Q.map ((NatIso.mapHomologicalComplex c (.up ℤ)).hom.app J)) _
    have hn := scalarSquareDerivedUnit_naturality F j
    rw [scalarSquareDerivedUnit_eq_inv F I] at hn
    have hmap : IsIso (DerivedCategory.Q.map
        ((F.mapHomologicalComplex (.up ℤ)).map j)) := by
      have hh : IsIso (DerivedCategory.Q.map
          ((F.mapHomologicalComplex (.up ℤ)).map j) ≫
            (F.rightDerivedFunctorObjQIso I).inv) := by
        rw [hn]
        infer_instance
      exact IsIso.of_isIso_comp_right _ (F.rightDerivedFunctorObjQIso I).inv
    refine ⟨(DerivedCategory.isIso_Q_map_iff_quasiIso _ _).mp hmap, ?_⟩
    change d.inv.app (DerivedCategory.Q.obj J) ≫
        rY.mapDerivedCategory.map (G.rightDerivedFunctorObjQIso J).hom ≫
        rY.mapDerivedCategoryFactors.hom.app ((G.mapHomologicalComplex (.up ℤ)).obj J) ≫
        DerivedCategory.Q.map ((NatIso.mapHomologicalComplex c (.up ℤ)).hom.app J) ≫
        DerivedCategory.Q.map ((F.mapHomologicalComplex (.up ℤ)).map j) =
      F.rightDerivedFunctor.map (rZ.mapDerivedCategoryFactors.hom.app J) ≫
        F.rightDerivedFunctor.map (DerivedCategory.Q.map j) ≫
        (F.rightDerivedFunctorObjQIso I).hom
    apply (cancel_mono (F.rightDerivedFunctorObjQIso I).inv).1
    simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
    rw [hn]
    have hh := congrArg (fun t ↦ d.inv.app (DerivedCategory.Q.obj J) ≫
      rY.mapDerivedCategory.map (G.rightDerivedFunctorObjQIso J).hom ≫ t ≫
        F.rightDerivedFunctor.map (DerivedCategory.Q.map j)) hu
    simp only [Category.assoc, ← Functor.map_comp_assoc, Iso.hom_inv_id] at hh
    erw [CategoryTheory.Functor.map_id, Category.id_comp, Iso.inv_hom_id_app_assoc] at hh
    exact hh.symm

end AlgebraicGeometry.ProEtale
