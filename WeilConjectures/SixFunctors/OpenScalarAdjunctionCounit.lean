/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SecSmoothPurity.OpenScalarExchange
public import WeilConjectures.AlgebraicGeometry.IntrinsicDerivedOpenAdjunction
public import WeilConjectures.AlgebraicGeometry.SfIntrinsicCompactSupport
public import WeilConjectures.AlgebraicGeometry.ConstructibleExceptionalAdjunctionCoefficients
public import WeilConjectures.AlgebraicGeometry.FiniteTorAmplitudeSites
public import WeilConjectures.AlgebraicGeometry.SfDerivedDirectImage
public import WeilConjectures.Algebra.Homology.OrdinaryDerivedChangeOfRings
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
public import WeilConjectures.AlgebraicGeometry.CanonicalOriginCompactSupportComposition
public import WeilConjectures.AlgebraicGeometry.FiniteComparisonClassAdjunction
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LocalizeConstructible
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Stalk
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LowerStarComp
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.OpenLowerShriek
public import Mathlib.CategoryTheory.Adjunction.Mates

import WeilConjectures.AlgebraicGeometry.FiniteCoefficientFlatModel
import WeilConjectures.AlgebraicGeometry.KFlatRingedToposPullback
import WeilConjectures.CategoryTheory.RingedSiteModules
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import WeilConjectures.CategoryTheory.AlgebraicInverseImage
import Mathlib.Algebra.Category.ModuleCat.Sheaf
import Mathlib.Algebra.Category.Ring.Limits
import Mathlib.Algebra.Category.Grp.Limits
import Mathlib.CategoryTheory.Sites.Whiskering
import Mathlib.CategoryTheory.Sites.Equivalence
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import WeilConjectures.Algebra.Homology.KFlatSupplement
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
import WeilConjectures.AlgebraicGeometry.SfPreservationClass
import WeilConjectures.AlgebraicGeometry.ProEtaleConstructibleOrigin
import WeilConjectures.AlgebraicGeometry.SpecifiedExceptionalClassHom
import WeilConjectures.AlgebraicGeometry.ProEtaleRingSheafChangeAdjunctionSupplement
import WeilConjectures.AlgebraicGeometry.KFlatScalarComparisonNormalization
import WeilConjectures.SixFunctors.OpenScalarTensorNormalization
import WeilConjectures.SixFunctors.OpenScalarAdjunctionCounitScalarAux
import Mathlib.CategoryTheory.Adjunction.Unique

/-! # Open scalar adjunction and the locally closed exceptional counit

Source: Weil blueprint, `lem-coef-finite-closed-shriek`, proof paragraph 3
(blueprint: lem-coef-open-scalar-adjunction-counit).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096
set_option linter.unusedVariables false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme WeilConjectures
namespace AlgebraicGeometry.ProEtale.CoefOpenCounit

/-- The actual compact-support functor, with its compactification instance fixed by `c`.
Source: blueprint locally closed factorization, proof paragraph 3
(blueprint: lem-coef-open-scalar-adjunction-counit). -/
abbrev lower (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f) :=
  @rightDerivedLowerShriek (ModuleCat.{u + 1} A) _ _ _ X Y f c.hasCompactification

/-- The recorded comparison-transported exceptional functor with the same instance.
Source: blueprint locally closed factorization, proof paragraph 3
(blueprint: lem-coef-open-scalar-adjunction-counit). -/
abbrev upper (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f) :=
  letI := c.hasCompactification
  rightDerivedUpperShriek A f

/-- The actual exceptional counit on its bounded-below domain; finite type over the
field supplies the quasi-compact target, rather than an extra hypothesis.
Source: blueprint locally closed factorization, proof paragraph 3
(blueprint: lem-coef-open-scalar-adjunction-counit). -/
def counit (A : Type (u + 1)) [CommRing A] [Finite A]
    (k : Type u) [Field k] {X Y : Scheme.{u}}
    [Y.Over (Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
    {f : X ⟶ Y} [QuasiCompact f] (c : Compactification f)
    (M : _root_.DerivedCategory (Sheaf (ProEt.topology Y) (ModuleCat.{u + 1} A)))
    (hM : _root_.DerivedCategory.TStructure.t.plus M) :
    (lower A c).obj ((upper A c).obj M) ⟶ M :=
  letI := c.hasCompactification
  letI : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace (Y ↘ Spec (.of k))
  rightDerivedUpperShriekCounit f M hM

/-- The open special compactification removes the derived identity direct image.
Source: blueprint locally closed factorization, proof paragraph 3
(blueprint: lem-coef-open-scalar-adjunction-counit). -/
def openCandidate (A : Type (u + 1)) [CommRing A] [Finite A]
    {V X : Scheme.{u}} (j : V ⟶ X) [IsOpenImmersion j] :
    rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A)
        (Compactification.ofIsOpenImmersion j) ≅
      (openImmersionLowerShriek (ModuleCat.{u + 1} A) j).mapDerivedCategory :=
  Functor.isoWhiskerLeft _ (rightDerivedLowerStarId (ModuleCat.{u + 1} A) X) ≪≫
    Functor.rightUnitor _

/-- The closed special compactification removes extension along the identity.
Source: blueprint locally closed factorization, proof paragraph 3
(blueprint: lem-coef-open-scalar-adjunction-counit). -/
def closedCandidate (A : Type (u + 1)) [CommRing A] [Finite A]
    {W V : Scheme.{u}} (t : W ⟶ V) [IsClosedImmersion t] :
    rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A)
        (Compactification.ofIsProper t) ≅
      (lowerStar (ModuleCat.{u + 1} A) t).rightDerivedFunctor :=
  Functor.isoWhiskerRight
      (Functor.mapDerivedCategoryNatIso (openImmersionLowerShriekIdIso
        (ModuleCat.{u + 1} A) W) ≪≫ Functor.mapDerivedCategoryIdIso _) _ ≪≫
    Functor.leftUnitor _

/-- Canonical comparison with a special compactification on the full etale-origin class.
The preimage under the published equivalence is unique and retains every ambient morphism.
Source: blueprint locally closed factorization, proof paragraph 3
(blueprint: lem-coef-open-scalar-adjunction-counit). -/
def originCandidate (A : Type (u + 1)) [CommRing A] [Finite A]
    {W X : Scheme.{u}} {f : W ⟶ X} [QuasiCompact f]
    (c d : Compactification f) :
    (DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} A) W).ι ⋙ lower A c ≅
      (DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} A) W).ι ⋙
        rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) d :=
  letI := c.hasCompactification
  let Φ := comparisonUpperStarPlusEtaleOrigin (ModuleCat.{u + 1} A) W
  (Φ.asEquivalence.congrLeft.fullyFaithfulInverse).preimageIso
    (fixedCompactSupportComparisonIso A (HasCompactification.compactification f) ≪≫
      Functor.isoWhiskerRight
        (Etale.rightDerivedLowerShriekOfCompactificationPlusιIso A
          (HasCompactification.compactification f) d)
        (comparisonUpperStar (ModuleCat.{u + 1} A) X).mapDerivedCategory ≪≫
      (fixedCompactSupportComparisonIso A d).symm)

/-- The specified closed compact-support comparison with ordinary derived direct image.
Source: blueprint locally closed factorization, proof paragraph 3
(blueprint: lem-coef-open-scalar-adjunction-counit). -/
def closedComparison (A : Type (u + 1)) [CommRing A] [Finite A]
    {W V : Scheme.{u}} (t : W ⟶ V) [IsClosedImmersion t] :
    (DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} A) W).ι ⋙
        lower A (Compactification.ofIsProper t) ≅
      (DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} A) W).ι ⋙
        (lowerStar (ModuleCat.{u + 1} A) t).rightDerivedFunctor :=
  originCandidate A (Compactification.ofIsProper t) (Compactification.ofIsProper t) ≪≫
    Functor.isoWhiskerLeft _ (closedCandidate A t)

/-- The specified open compact-support comparison with the actual termwise extension.
Source: blueprint locally closed factorization, proof paragraph 3
(blueprint: lem-coef-open-scalar-adjunction-counit). -/
def openComparison (A : Type (u + 1)) [CommRing A] [Finite A]
    {V X : Scheme.{u}} (j : V ⟶ X) [IsOpenImmersion j] [QuasiCompact j] :
    (DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} A) V).ι ⋙
        lower A (Compactification.ofIsOpenImmersion j) ≅
      (DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} A) V).ι ⋙
        (openImmersionLowerShriek (ModuleCat.{u + 1} A) j).mapDerivedCategory :=
  originCandidate A (Compactification.ofIsOpenImmersion j)
      (Compactification.ofIsOpenImmersion j) ≪≫
    Functor.isoWhiskerLeft _ (openCandidate A j)

/-- The compact-support factorization is the specified compositor followed by the
special closed and open compactification comparisons, on bounded-below etale origins.
Source: blueprint locally closed factorization, proof paragraph 3
(blueprint: lem-coef-open-scalar-adjunction-counit). -/
def factorization (A : Type (u + 1)) [CommRing A] [Finite A]
    {W V X : Scheme.{u}} (t : W ⟶ V) (j : V ⟶ X)
    [IsClosedImmersion t] [IsOpenImmersion j] [QuasiCompact j]
    (c : Compactification (t ≫ j)) :
    (DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} A) W).ι ⋙ lower A c ≅
      (DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} A) W).ι ⋙
        (lowerStar (ModuleCat.{u + 1} A) t).rightDerivedFunctor ⋙
          (openImmersionLowerShriek (ModuleCat.{u + 1} A) j).mapDerivedCategory :=
  letI := (Compactification.ofIsProper t).hasCompactification
  letI := (Compactification.ofIsOpenImmersion j).hasCompactification
  letI := c.hasCompactification
  (originCompositionAmbient A t j).symm ≪≫
    Functor.isoWhiskerLeft (originCompactSupport A t) (openComparison A j) ≪≫
    Functor.isoWhiskerRight (closedComparison A t) _

/-- The canonical etale origin of the recorded exceptional image of a bounded-below input.
Source: blueprint locally closed factorization, proof paragraph 3
(blueprint: lem-coef-open-scalar-adjunction-counit). -/
abbrev upperOrigin (A : Type (u + 1)) [CommRing A] [Finite A]
    (k : Type u) [Field k] {W X : Scheme.{u}}
    [X.Over (Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    {f : W ⟶ X} [QuasiCompact f] (c : Compactification f)
    (M : _root_.DerivedCategory (Sheaf (ProEt.topology X) (ModuleCat.{u + 1} A)))
    (hM : _root_.DerivedCategory.TStructure.t.plus M) :
    DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} A) W ((upper A c).obj M) :=
  letI := c.hasCompactification
  letI : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace (X ↘ Spec (.of k))
  plusEtaleOrigin_rightDerivedUpperShriek_obj f hM

/-- The actual closed exceptional counit expressed using ordinary derived direct image.
Source: blueprint locally closed factorization, proof paragraph 3
(blueprint: lem-coef-open-scalar-adjunction-counit). -/
def closedCounit (A : Type (u + 1)) [CommRing A] [Finite A]
    (k : Type u) [Field k] {W V : Scheme.{u}}
    [V.Over (Spec (.of k))] [QuasiCompact (V ↘ Spec (.of k))]
    (t : W ⟶ V) [IsClosedImmersion t]
    (M : _root_.DerivedCategory (Sheaf (ProEt.topology V) (ModuleCat.{u + 1} A)))
    (hM : _root_.DerivedCategory.TStructure.t.plus M) :
    (lowerStar (ModuleCat.{u + 1} A) t).rightDerivedFunctor.obj
      ((upper A (Compactification.ofIsProper t)).obj M) ⟶ M :=
  (closedComparison A t).inv.app
      ⟨_, upperOrigin A k (Compactification.ofIsProper t) M hM⟩ ≫
    counit A k (Compactification.ofIsProper t) M hM

/-- The locally closed assertion, including its full bounded-constructible domain,
actual counit, finite-Tor preservation and the domains of the two support operations.
The exactness conjunct identifies the ordinary derived closed image with termwise t_*.
Source: blueprint locally closed factorization, proof paragraph 3
(blueprint: lem-coef-open-scalar-adjunction-counit). -/
def Factored (A : Type (u + 1)) [CommRing A] [Finite A]
    (k : Type u) [Field k] {W V X : Scheme.{u}}
    [V.Over (Spec (.of k))] [X.Over (Spec (.of k))]
    [QuasiCompact (V ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    (t : W ⟶ V) (j : V ⟶ X) [IsClosedImmersion t] [IsOpenImmersion j]
    [QuasiCompact j] (c : Compactification (t ≫ j)) : Prop :=
  PreservesFiniteColimits (lowerStar (ModuleCat.{u + 1} A) t) ∧
  (∀ H : (DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} A) W).FullSubcategory,
    DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} A) V
      ((lowerStar (ModuleCat.{u + 1} A) t).rightDerivedFunctor.obj H.obj)) ∧
  (∀ H : (DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} A) V).FullSubcategory,
    DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} A) X
      ((openImmersionLowerShriek (ModuleCat.{u + 1} A) j).mapDerivedCategory.obj H.obj)) ∧
  ∃ e : (DerivedCategory.boundedConstructible (ModuleCat.{u + 1} A) X).ι ⋙ upper A c ≅
      (DerivedCategory.boundedConstructible (ModuleCat.{u + 1} A) X).ι ⋙
        (upperStar (ModuleCat.{u + 1} A) j).mapDerivedCategory ⋙
          upper A (Compactification.ofIsProper t),
    (∀ M : (DerivedCategory.boundedConstructible (ModuleCat.{u + 1} A) X).FullSubcategory,
      (factorization A t j c).hom.app
          ⟨_, upperOrigin A k c M.obj M.property.plusEtaleOrigin.plus⟩ ≫
        (openImmersionLowerShriek (ModuleCat.{u + 1} A) j).mapDerivedCategory.map
          ((lowerStar (ModuleCat.{u + 1} A) t).rightDerivedFunctor.map (e.hom.app M) ≫
            closedCounit A k t
              ((upperStar (ModuleCat.{u + 1} A) j).mapDerivedCategory.obj M.obj)
              (M.property.mapDerivedCategory_upperStar j).plusEtaleOrigin.plus) ≫
        (derivedOpenImmersionLowerShriekUpperStarAdjunction
          (ModuleCat.{u + 1} A) j).counit.app M.obj =
      counit A k c M.obj M.property.plusEtaleOrigin.plus) ∧
    (∀ (M : _root_.DerivedCategory
        (Sheaf (ProEt.topology X) (ModuleCat.{u + 1} A))),
      DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} A) X M →
      DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} A) V
          ((upperStar (ModuleCat.{u + 1} A) j).mapDerivedCategory.obj M) ∧
        DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} A) W
          ((upper A (Compactification.ofIsProper t)).obj
            ((upperStar (ModuleCat.{u + 1} A) j).mapDerivedCategory.obj M)))

/-- Specialization to the actual positive coefficient quotient; finiteness and
quasi-compactness of the open map are consequences, not extra hypotheses.
Source: blueprint locally closed factorization, proof paragraph 3
(blueprint: lem-coef-open-scalar-adjunction-counit). -/
def CoefficientFactored (k : Type u) [Field k]
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (m : ℕ) (hm : 1 ≤ m)
    {W V X : Scheme.{u}} [V.Over (Spec (.of k))] [X.Over (Spec (.of k))]
    [LocallyOfFiniteType (V ↘ Spec (.of k))]
    [QuasiCompact (V ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    (t : W ⟶ V) (j : V ⟶ X) [IsClosedImmersion t] [IsOpenImmersion j]
    (c : Compactification (t ≫ j)) : Prop :=
  letI : Finite (Padic.coefficientExtensionRing l E m) :=
    Padic.finite_coefficientExtensionRing l E m hm
  letI : IsLocallyNoetherian V :=
    LocallyOfFiniteType.isLocallyNoetherian (V ↘ Spec (.of k))
  letI : CompactSpace V := QuasiCompact.compactSpace_of_compactSpace (V ↘ Spec (.of k))
  letI : IsNoetherian V := ⟨⟩
  Factored (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E m)) k t j c

/-- The scalar/open counit identity in the ordinary unbounded B-module derived category.
Both comparisons are the published maps of the actual normalized scalar/open adjunctions.
Source: blueprint locally closed factorization, proof paragraph 3
(blueprint: lem-coef-open-scalar-adjunction-counit). -/
def ScalarCounit {A B : Type u} [CommRing A] [CommRing B]
    (φ : A →+* B) {V X : Scheme.{u}} (j : V ⟶ X) [IsOpenImmersion j] : Prop :=
  ∀ M : _root_.DerivedCategory (proEtaleRingModules X (proEtaleConstantRing X A)),
    (openScalarIso φ j).hom.app ((constantPullback (A := A) j).obj M) ≫
        (openExtension (A := B) j).map ((tensorPullbackIso φ j).inv.app M) ≫
        (proEtaleRingDerivedOpenAdjunction j
          (proEtaleConstantRing X B) (proEtaleConstantRing V B)
          (proEtaleConstantRingComparison j B)).counit.app ((scalarExtension φ X).obj M) =
      (scalarExtension φ X).map ((proEtaleRingDerivedOpenAdjunction j
        (proEtaleConstantRing X A) (proEtaleConstantRing V A)
        (proEtaleConstantRingComparison j A)).counit.app M)

/-- The geometric and finite-Tor package for one finite coefficient ring.

This is the one-coefficient component of the two-ring package below. Its proof follows
paragraph 3 of `lem-coef-finite-closed-shriek`: Noetherianity and exactness give the
closed/open origin clauses, the finite flat model and preservation-class theorem give the
finite-Tor clauses, and the normalized exceptional adjunction comparison gives the displayed
counit-compatible isomorphism.
Source: Weil blueprint, `lem-coef-finite-closed-shriek`, proof paragraph 3
(blueprint: lem-coef-open-scalar-adjunction-counit-factored-single).
-/
theorem coefficient_factored_single
    (F : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (_hl : l ≠ F.p)
    (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E]
    (m : ℕ) (hm : 1 ≤ m)
    {W V X : Scheme.{u}}
    [W.Over (Spec (.of F.k))] [V.Over (Spec (.of F.k))] [X.Over (Spec (.of F.k))]
    [LocallyOfFiniteType (W ↘ Spec (.of F.k))] [QuasiCompact (W ↘ Spec (.of F.k))]
    [LocallyOfFiniteType (V ↘ Spec (.of F.k))] [QuasiCompact (V ↘ Spec (.of F.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of F.k))] [QuasiCompact (X ↘ Spec (.of F.k))]
    [IsSeparated (W ↘ Spec (.of F.k))] [IsSeparated (V ↘ Spec (.of F.k))]
    [IsSeparated (X ↘ Spec (.of F.k))]
    (t : W ⟶ V) (j : V ⟶ X) [t.IsOver (Spec (.of F.k))]
    [j.IsOver (Spec (.of F.k))] [IsClosedImmersion t] [IsOpenImmersion j]
    (c : Compactification (t ≫ j)) :
    CoefficientFactored F.k l E m hm t j c := by
  sorry

/-- The two coefficient-domain packages in the locally closed factorization.

This is the geometric and finite-Tor portion of the proof plan. Finite type over
`F.k` supplies the Noetherian hypotheses, the exact closed image and open extension
preserve etale origins, and the bounded flat model plus the preservation-class
comparison supplies the displayed finite-Tor and counit data. The remaining
unbounded scalar calculation is isolated in `scalar_counit_aux`.
Source: Weil blueprint, `lem-coef-finite-closed-shriek`, proof paragraph 3
(blueprint: lem-coef-open-scalar-adjunction-counit-factored-aux).
-/
theorem coefficient_factored_aux
    (F : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (_hl : l ≠ F.p)
    (E L : Type u) [Field E] [Field L]
    [Algebra (Padic l) E] [Algebra (Padic l) L]
    [FiniteDimensional (Padic l) E] [FiniteDimensional (Padic l) L]
    (m n : ℕ) (hm : 1 ≤ m) (hn : 1 ≤ n)
    (φ : Padic.coefficientExtensionRing l E m →+* Padic.coefficientExtensionRing l L n)
    {W V X : Scheme.{u}}
    [W.Over (Spec (.of F.k))] [V.Over (Spec (.of F.k))] [X.Over (Spec (.of F.k))]
    [LocallyOfFiniteType (W ↘ Spec (.of F.k))] [QuasiCompact (W ↘ Spec (.of F.k))]
    [LocallyOfFiniteType (V ↘ Spec (.of F.k))] [QuasiCompact (V ↘ Spec (.of F.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of F.k))] [QuasiCompact (X ↘ Spec (.of F.k))]
    [IsSeparated (W ↘ Spec (.of F.k))] [IsSeparated (V ↘ Spec (.of F.k))]
    [IsSeparated (X ↘ Spec (.of F.k))]
    (t : W ⟶ V) (j : V ⟶ X) [t.IsOver (Spec (.of F.k))]
    [j.IsOver (Spec (.of F.k))] [IsClosedImmersion t] [IsOpenImmersion j]
    (c : Compactification (t ≫ j)) :
    CoefficientFactored F.k l E m hm t j c ∧
      CoefficientFactored F.k l L n hn t j c := by
  exact ⟨coefficient_factored_single F l _hl E m hm t j c,
    coefficient_factored_single F l _hl L n hn t j c⟩

/-- Open scalar adjunction and the factored actual exceptional counit.
Source: Weil blueprint, lem-coef-finite-closed-shriek, proof paragraph 3
(blueprint: lem-coef-open-scalar-adjunction-counit).

Proof plan:
1. Finite type over the field makes W,V,X Noetherian. Use the special closed and open
compactifications, closed direct-image exactness, and thm-sf-comp-composition to obtain
factorization and preservation of the full bounded-below etale-origin class.
2. Restrict the constructible strata and a bounded flat model to V. Exact pullback preserves
flat terms and K-flatness, so the same Tor interval works. Apply thm-sf-preservation-class
to t to obtain the exceptional finite-Tor assertion. Both objects have etale origins.
3. Compose the actual open Hom equivalence and the relative exceptional Hom equivalence.
The actual exceptional inverse image of h represents this same Hom functor on the full
origin class. Unique right adjoints identify it with t^! j^*, naturally on bounded
constructible objects, and carry its counit to the pasted counit. The specified compact
support comparisons in factorization and closedCounit implement these identifications.
4. On entire ordinary derived categories the scalar adjunction is normalized by the pure
unit x ↦ x tensor 1. Restriction commutes with open inverse image by the actual action
identification. The K-flat balancing comparison identifies its scalar mate with r_j.
5. Compose scalar and open adjunctions. Their right-adjoint action identification determines
the B-linear isomorphism openScalarIso by uniqueness of left adjoints, preserving their
units, hence the stated pure-unit normalization even for nonflat coefficient maps.
6. By lem-fix-open-scalar-tensor-normalization the inverse comparison is the open adjunct
of scalar extension of the A-open unit followed by r_j. The adjunct-counit identity writes
it as the B-open counit composed with extension of that map.
7. Evaluate at j_A^* M. Naturality of the B-open counit and of r_j reduces the composite
to the A-open triangle identity. Precompose by the forward scalar/open isomorphism and
cancel its inverse. This proves ScalarCounit for every unbounded M without flatness. -/
theorem open_scalar_adjunction_counit
    (F : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (_hl : l ≠ F.p)
    (E L : Type u) [Field E] [Field L]
    [Algebra (Padic l) E] [Algebra (Padic l) L]
    [FiniteDimensional (Padic l) E] [FiniteDimensional (Padic l) L]
    (m n : ℕ) (hm : 1 ≤ m) (hn : 1 ≤ n)
    (φ : Padic.coefficientExtensionRing l E m →+* Padic.coefficientExtensionRing l L n)
    {W V X : Scheme.{u}}
    [W.Over (Spec (.of F.k))] [V.Over (Spec (.of F.k))] [X.Over (Spec (.of F.k))]
    [LocallyOfFiniteType (W ↘ Spec (.of F.k))] [QuasiCompact (W ↘ Spec (.of F.k))]
    [LocallyOfFiniteType (V ↘ Spec (.of F.k))] [QuasiCompact (V ↘ Spec (.of F.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of F.k))] [QuasiCompact (X ↘ Spec (.of F.k))]
    [IsSeparated (W ↘ Spec (.of F.k))] [IsSeparated (V ↘ Spec (.of F.k))]
    [IsSeparated (X ↘ Spec (.of F.k))]
    (t : W ⟶ V) (j : V ⟶ X) [t.IsOver (Spec (.of F.k))] [j.IsOver (Spec (.of F.k))]
    [IsClosedImmersion t] [IsOpenImmersion j]
    (c : Compactification (t ≫ j)) :
    CoefficientFactored F.k l E m hm t j c ∧
      CoefficientFactored F.k l L n hn t j c ∧ ScalarCounit φ j := by
  obtain ⟨hE, hL⟩ := coefficient_factored_aux F l _hl E L m n hm hn φ t j c
  refine ⟨hE, hL, ?_⟩
  exact scalar_counit_aux φ j

end AlgebraicGeometry.ProEtale.CoefOpenCounit
