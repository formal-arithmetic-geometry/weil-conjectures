/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SpaceAffineProjectionData
public import WeilConjectures.AlgebraicGeometry.AlgebraicSpaceMorphismProperties
public import WeilConjectures.Algebra.Homology.RingedSiteZerothHypercohomologyOfUniverses
public import WeilConjectures.CategoryTheory.RingedToposMorphismSupplement
import WeilConjectures.AlgebraicGeometry.AffineEtaleDerivedModuleRealization
import WeilConjectures.AlgebraicGeometry.SchemeZariskiEtaleQuasiCoherentEquivalence
import WeilConjectures.AlgebraicGeometry.ModulePullbackAffineSections
import WeilConjectures.AlgebraicGeometry.AlgebraicSpaceModulePullbackQuasiCoherent
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.RingTheory.Flat.Basic
import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import WeilConjectures.AlgebraicGeometry.RingedTopoiCanonicalTensorPullbackOfUniverses
import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import WeilConjectures.Algebra.Homology.KFlatSupplement
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
import Mathlib.CategoryTheory.Monoidal.Closed.Basic
import Mathlib.CategoryTheory.Limits.ExactFunctor
import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.Algebra.Category.Grp.AB
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import Mathlib.RingTheory.Flat.CategoryTheory
import WeilConjectures.AlgebraicGeometry.ProjectionMateExact
import WeilConjectures.AlgebraicGeometry.SpacePerfectLocalizingGeneration
import Mathlib.CategoryTheory.Adjunction.Limits
import WeilConjectures.Algebra.Homology.RingedDerivedClosedSymmetricMonoidal
import WeilConjectures.AlgebraicGeometry.SpaceDerivedQCohPullbackTensor
import WeilConjectures.Mathlib.CategoryTheory.Triangulated.Functor
import WeilConjectures.CategoryTheory.DerivedModuleFreeGeneration
import WeilConjectures.CategoryTheory.RingedToposDerivedPushforwardComposition
import WeilConjectures.CategoryTheory.RingedToposMorphismSupplement
import WeilConjectures.CategoryTheory.RingedSiteModules
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
import Mathlib.CategoryTheory.Functor.Derived.RightDerived
import WeilConjectures.CategoryTheory.RingedSiteKInjectiveResolutionsSupplement
import WeilConjectures.Mathlib.Algebra.Homology.GrothendieckAbelian
import Mathlib.CategoryTheory.Localization.DerivabilityStructure.Derives
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Flat
import WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Defs
import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution
import Mathlib.Algebra.Homology.DerivedCategory.Fractions
import WeilConjectures.Algebra.Homology.KFlatResolution
import WeilConjectures.CategoryTheory.RingedToposKFlatPullback
import WeilConjectures.CategoryTheory.AlgebraicInverseImage
import Mathlib.Algebra.Category.ModuleCat.Sheaf
import Mathlib.Algebra.Category.Ring.Limits
import Mathlib.Algebra.Category.Grp.Limits
import Mathlib.CategoryTheory.Sites.Whiskering
import WeilConjectures.CategoryTheory.GeometricModuleConstruction
import WeilConjectures.CategoryTheory.RingedToposRingData
import WeilConjectures.CategoryTheory.AdjunctionRingOperations
import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
import Mathlib.CategoryTheory.Adjunction.Basic
import Mathlib.CategoryTheory.Sites.CartesianMonoidal
import Mathlib.CategoryTheory.Monoidal.CommGrp_
import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Mod
import WeilConjectures.CategoryTheory.GeometricModuleTransport
import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
import WeilConjectures.CategoryTheory.GeometricRingTransport
import Mathlib.CategoryTheory.Sites.Limits
import WeilConjectures.CategoryTheory.SheavesAlgebraicStructuresRingCore
import WeilConjectures.CategoryTheory.SheafRingObjectReconstruction
import WeilConjectures.CategoryTheory.Adjunction.FiniteProductRingFunctor
import WeilConjectures.CategoryTheory.ModulePullbackPushforwardAdjunctionSupplement
import WeilConjectures.AlgebraicGeometry.KFlatRingedToposPullback
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
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
import Mathlib.CategoryTheory.Sites.PreservesSheafification
import Mathlib.CategoryTheory.Limits.Preserves.Limits
import Mathlib.CategoryTheory.ObjectProperty.ColimitsOfShape
import Mathlib.Algebra.Homology.Embedding.CochainComplex
import WeilConjectures.Algebra.Homology.RingedToposAcyclicKFlatPullback
import WeilConjectures.Algebra.Homology.BoundedFlatIndependentCoefficients
import Mathlib.CategoryTheory.Monoidal.Preadditive
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
import WeilConjectures.AlgebraicGeometry.RingedProjectionTensorComposition

/-! # The affine projection formula for a flat qcqs algebraic space

Source: Stacks Project, spaces-perfect.tex, Tag 08IN, lemma-cohomology-base-change;
flat-pullback paragraph preceding lemma-check-quasi-coherence-on-covering
(blueprint: lem-sfb-space-affine-derived-projection-formula).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
universe u w
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open WeilConjectures
namespace AlgebraicGeometry.AlgebraicSpace

/-- The affine derived projection formula, including exact scalar pullback, quasi-coherence,
its degree-zero representative, and naturality for every coefficient homomorphism.
Source: Stacks Project, spaces-perfect.tex, Tag 08IN, lemma-cohomology-base-change,
flat-pullback paragraph preceding lemma-check-quasi-coherence-on-covering
(blueprint: lem-sfb-space-affine-derived-projection-formula).

Proof:
1. On every affine étale chart Spec B the scalar functor is B tensor_A N. The
Zariski/étale quasi-coherent comparison, affine pullback sections, and preservation
of quasi-coherence by space pullback give quasi-coherence of F_N. Chartwise flatness
and flat tensor exactness give exactness, which is local on the étale site.
2. A map F_N to M is equivalent to the A-linear map n to g(1 tensor n) into
compatible sections, with inverse b tensor n to b times that section. This pins
the structural action and the ordinary adjunction. Exact derived factorization
computes pullback termwise and gives the stated canonical single comparison.
K-flat resolutions and the balanced formula b tensor (c tensor x) to bc tensor x
identify this with the composite pullback through Spec A. Derived adjunction and
tensor pullback give the displayed representative and transpose normalizations.
3. The affine étale derived-module realization identifies D(A) with D_QCoh(Spec A),
with inverse derived sections. Its tensor dictionary is the counit-defined mate,
by full faithfulness and the ordinary unit normalization.
4. The qcqs-space pushforward-right-adjoint theorem makes Rf_* preserve coproducts
on D_QCoh. Perfect localizing generation identifies these with ambient coproducts.
Tensor and pullback preserve coproducts as left adjoints; space derived pullback
and tensor preserve quasi-coherent cohomology.
5. Fix E. The exact projection-mate theorem makes its two functors exact and its
mate compatible with shifts and connecting maps. At A[0] the unit normalization
makes it the identity; hence it is invertible on every shift A[k].
6. Its isomorphism locus is closed under triangles, coproducts, isomorphisms and
retracts. On a retract use T(r) followed by the inverse at the larger object,
followed by U(i). Derived-module free generation gives every unbounded input.
7. Specialize to N[0] and apply derived sections on Spec A. The affine dictionary
and derived direct-image composition give the displayed source and target. The
projection-composition identity identifies the actual arrow with the map defined
above, including its counit. Naturality of each comparison gives simultaneous
naturality in E and every N to N'. No boundedness or flatness of N is required. -/
theorem space_affine_derived_projection_formula (A : CommRingCat.{u})
    (X : AlgebraicSpace (Spec A))
    (f : X ⟶ schemeSpace (Over.mk (𝟙 (Spec A))))
    (hflat : MapIsFlat f) (hqc : MapIsQuasiCompact f.hom.hom)
    (hqs : MapIsQuasiCompact (pullback.diagonal f.hom.hom))
    [HasDerivedCategory.{w} (ModuleCat.{u} A)] [HasDerivedCategory.{w} X.SmallModules] :
    ∃ d : AffineProjectionData A X,
      (∀ N : ModuleCat.{u} A,
        (X.smallModuleEquivalence.inverse.obj (affineScalarSheaf A X N)).IsQuasicoherent) ∧
      (∀ (E : X.DerivedQCoh) (N : ModuleCat.{u} A),
        IsIso (affineDerivedProjectionMap A X d E.obj N)) ∧
      (∀ (E E' : X.DerivedQCoh) (e : E ⟶ E')
          (N N' : ModuleCat.{u} A) (n : N ⟶ N'),
        (tensor (DerivedCategory (ModuleCat.{u} A))).map
          (Prod.mkHom ((affineProjectionRGamma A X d.G d.sections_additive).map e.hom)
            ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).map n)) ≫
          affineDerivedProjectionMap A X d E'.obj N' =
        affineDerivedProjectionMap A X d E.obj N ≫
          (affineProjectionRGamma A X d.G d.sections_additive).map
            ((affineProjectionTensor A X).map
              (Prod.mkHom e.hom ((DerivedCategory.singleFunctor X.SmallModules 0).map
                (affineScalarSheafMap A X n))))) := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
