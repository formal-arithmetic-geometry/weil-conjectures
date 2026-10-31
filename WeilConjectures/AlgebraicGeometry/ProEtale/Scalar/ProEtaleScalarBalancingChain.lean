/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProEtale.Scalar.ProEtaleScalarMateIdentifications
public import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantRingMap
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
public import WeilConjectures.Algebra.Homology.Site.SiteTensorFunctorialitySupplement
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
public import WeilConjectures.Mathlib.Algebra.Homology.Monoidal
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
public import WeilConjectures.AlgebraicGeometry.ProEtale.Finite.ProEtaleFiniteModulesSupplement
public import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantRingOperations
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
public import WeilConjectures.AlgebraicGeometry.ProEtale.Ring.ProEtaleRingSheafChangeAdjunctionSupplement
public import WeilConjectures.AlgebraicGeometry.ProEtale.Canonical.ProEtaleCanonicalTensorPullback
public import WeilConjectures.AlgebraicGeometry.AdicCoefficientDatum.FourCornersSupplement
public import WeilConjectures.AlgebraicGeometry.Stratum.StratumScalarExtension
import WeilConjectures.AlgebraicGeometry.ProEtaleInverseImage
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
import Mathlib.AlgebraicGeometry.Sites.Proetale
import Mathlib.CategoryTheory.Sites.ConstantSheaf
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import WeilConjectures.CategoryTheory.RingedSiteModules
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous
import Mathlib.CategoryTheory.Sites.Equivalence
import WeilConjectures.CategoryTheory.Site.SiteInverseImageTensor
import WeilConjectures.CategoryTheory.Adjunction.LiftsGroupRingObjects
import Mathlib.CategoryTheory.Monoidal.CommGrp_
import Mathlib.CategoryTheory.Monoidal.Ring
import Mathlib.CategoryTheory.Adjunction.Limits
import WeilConjectures.CategoryTheory.Adjunction.LiftedCommRingBranch
import Mathlib.CategoryTheory.Sites.Sheafification
import WeilConjectures.CategoryTheory.AlgebraicInverseImageOfUniverses
import WeilConjectures.CategoryTheory.AlgebraicInverseImage
import Mathlib.Algebra.Category.ModuleCat.Sheaf
import Mathlib.Algebra.Category.Ring.Limits
import Mathlib.Algebra.Category.Grp.Limits
import Mathlib.CategoryTheory.Sites.Whiskering
import Mathlib.CategoryTheory.Types.Basic
import WeilConjectures.AlgebraicGeometry.RingedTopoiInverseImageTensorComparison
import WeilConjectures.AlgebraicGeometry.RingedTopoiTensorSections
import Mathlib.Algebra.Category.Grp.FilteredColimits
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.MonoidalClosed
import WeilConjectures.Algebra.Homology.Module.ModulePullbackPushforwardAdjunctionSupplement
import Mathlib.CategoryTheory.Adjunction.Basic
import Mathlib.CategoryTheory.Limits.Preserves.Finite
import WeilConjectures.AlgebraicGeometry.RingedTopoiInverseImageTensorPairingIsIso
import WeilConjectures.AlgebraicGeometry.RingedTopoiInverseImagePairing
import Mathlib.CategoryTheory.Sites.CartesianMonoidal
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorBilinearUniversal
import WeilConjectures.CategoryTheory.GeometricModuleConstruction
import WeilConjectures.CategoryTheory.RingedToposRingData
import WeilConjectures.CategoryTheory.Ringed.RingedToposMorphismSupplement
import WeilConjectures.CategoryTheory.AdjunctionRingOperations
import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Mod
import WeilConjectures.CategoryTheory.GeometricModuleTransport
import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
import WeilConjectures.CategoryTheory.RingedToposKFlatPullback
import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Flat
import WeilConjectures.CategoryTheory.GeometricRingTransport
import Mathlib.CategoryTheory.Sites.Limits
import WeilConjectures.CategoryTheory.SheavesAlgebraicStructuresRingCore
import WeilConjectures.CategoryTheory.SheafRingObjectReconstruction
import WeilConjectures.CategoryTheory.Adjunction.FiniteProductRingFunctor
import WeilConjectures.AlgebraicGeometry.KFlatRingedToposPullback
import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
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
import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import WeilConjectures.AlgebraicGeometry.RingedTopoiDerivedPullback
import Mathlib.CategoryTheory.Functor.Derived.LeftDerived
import WeilConjectures.Algebra.Homology.KFlatResolution
import WeilConjectures.SmoothPurity.Supporting.ChangeOfRingsKFlatQuasiIsoSupplement
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
import Mathlib.CategoryTheory.Sites.EpiMono
import Mathlib.CategoryTheory.Adjunction.Additive
import Mathlib.Algebra.Category.Grp.EpiMono
import Mathlib.Algebra.Category.Grp.Abelian
import Mathlib.CategoryTheory.Sites.Abelian

/-! # Ordinary scalar balancing and its unbounded chain comparison

Source: Stacks Project, Modules on Sites, Tag 03EL, lemma-tensor-product-pullback;
Homology, Tag 012Z (blueprint: lem-sp-proetale-scalar-balancing-chain).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.ProEtale

/-- The ordinary comparison beta, oriented from restriction after B-pullback to
A-pullback after restriction. It is the inverse of the published normalized mate.
Source: Stacks 03EL (blueprint: lem-sp-proetale-scalar-balancing-chain). -/
def scalarBalancingBeta {A B : Type u} [CommRing A] [CommRing B]
    (φ : A →+* B) {X Y : Scheme.{u}} (f : X ⟶ Y) :
    proEtaleConstantRingPullback B f ⋙ scalarMateRestriction φ X ≅
      scalarMateRestriction φ Y ⋙ proEtaleConstantRingPullback A f :=
  (@asIso _ _ _ _
    (proEtaleRingRestrictionPullbackInv f
      (proEtaleConstantRing Y A) (proEtaleConstantRing Y B)
      (proEtaleConstantRing X A) (proEtaleConstantRing X B)
      (proEtaleConstantRingMap (T := Y) φ) (proEtaleConstantRingMap (T := X) φ)
      (proEtaleConstantRingComparison f A) (proEtaleConstantRingComparison f B)
      (proEtaleConstantInverseImageMap_naturality f
        (CommRingCat.ofHom (RingHom.ulift φ))).symm)
    (proEtaleRingRestrictionPullbackInv_isIso f
      (proEtaleConstantRing Y A) (proEtaleConstantRing Y B)
      (proEtaleConstantRing X A) (proEtaleConstantRing X B)
      (proEtaleConstantRingMap (T := Y) φ) (proEtaleConstantRingMap (T := X) φ)
      (proEtaleConstantRingComparison f A) (proEtaleConstantRingComparison f B)
      (proEtaleConstantInverseImageMap_naturality f
        (CommRingCat.ofHom (RingHom.ulift φ))).symm)).symm

/-- Transport t to the scalar-extension presentations, retaining the B-action on
both its source and target. This is the displayed t beta in those coordinates.
Source: Stacks 03EL (blueprint: lem-sp-proetale-scalar-balancing-chain). -/
def scalarBalancingMap {A B : Type u} [CommRing A] [CommRing B]
    (φ : A →+* B) {X Y : Scheme.{u}} (f : X ⟶ Y)
    (t : scalarMateOrdinaryTensor φ Y ⋙ proEtaleConstantRingPullback A f ≅
      proEtaleConstantRingPullback A f ⋙ scalarMateOrdinaryTensor φ X)
    (M : proEtaleRingModules Y (proEtaleConstantRing Y A)) :=
  (scalarBalancingBeta φ f).hom.app
      ((proEtaleRingExtension (proEtaleConstantRingMap (T := Y) φ)).obj M) ≫
    (proEtaleConstantRingPullback A f).map ((scalarMateOrdinaryTensorIso φ Y).hom.app M) ≫
    t.hom.app M ≫
    (scalarMateOrdinaryTensorIso φ X).inv.app ((proEtaleConstantRingPullback A f).obj M)

/-- The unit-section formula characterizing t, using images of presheaf pure tensors.
Source: Stacks 03EL (blueprint: lem-sp-proetale-scalar-balancing-chain). -/
def IsScalarBalancing {A B : Type u} [CommRing A] [CommRing B]
    (φ : A →+* B) {X Y : Scheme.{u}} (f : X ⟶ Y)
    (t : scalarMateOrdinaryTensor φ Y ⋙ proEtaleConstantRingPullback A f ≅
      proEtaleConstantRingPullback A f ⋙ scalarMateOrdinaryTensor φ X) : Prop :=
  ∀ (M : proEtaleRingModules Y (proEtaleConstantRing Y A)) (V : Y.ProEt)
    (x : M.val.obj (Opposite.op V))
    (s : (proEtaleConstantRing Y B).obj.obj (Opposite.op V)),
    (t.hom.app M).val.app (Opposite.op ((proEtaleBaseChange f).obj V))
      (((proEtaleConstantRingAdjunction A f).unit.app
        ((scalarMateOrdinaryTensor φ Y).obj M)).val.app (Opposite.op V)
          (proEtaleTensorPair Y (proEtaleConstantRing Y A) M
            (scalarMateCoefficient φ Y) (Opposite.op V) x s)) =
      proEtaleTensorPair X (proEtaleConstantRing X A)
        ((proEtaleConstantRingPullback A f).obj M) (scalarMateCoefficient φ X)
        (Opposite.op ((proEtaleBaseChange f).obj V))
        (((proEtaleConstantRingAdjunction A f).unit.app M).val.app (Opposite.op V) x)
        (((proEtaleRingDirectImageMap f (proEtaleConstantRing Y B)
          (proEtaleConstantRing X B) (proEtaleConstantRingComparison f B)).hom.app
            (Opposite.op V)) s)

/-- The coefficient square, the underlying identity comparison, and the uniquely
normalized tensor comparison, with its B-linearity and unbounded chain realization.
Source: Stacks 03EL and 012Z (blueprint: lem-sp-proetale-scalar-balancing-chain).

Proof:
1. Both coefficient composites send a constant a to phi(a); restriction, gluing and
   sheafification give the coefficient square, including the empty-source case.
2. Under the identified-coefficient inverse image beta is the identity on the
   underlying inverse-image sheaf. Equivalently its inverse carries the A-unit
   section of every restricted N to its B-unit section.
3. Apply lem-weil-pbc-algebraic-inverse-image-tensor-comparison to M and r_Y B_Y,
   then identify the second factor by c_B. Its pairing formula gives the displayed
   pure-section equation. The coefficient square makes the pairing balanced.
4. Adjunction and lem-pc-sites-sheaf-tensor-bilinear-universal show that this formula
   determines each component uniquely; they also prove naturality.
5. Transport the equality (x tensor s)b = x tensor (sb) through inverse image on
   the sheaf of triples. Finite-product preservation and the ring/module graph
   equations preserve multiplication and action for arbitrary local sections.
6. The two transported action pairings are bilinear. Apply the iterated tensor
   universal property lem-pd-sheaf-trilinear-universal to extend their equality
   on pure triples to all sections. Thus t beta is B-linear, as is its inverse.
7. Naturality on each differential gives the chain equations for t and t inverse.
   Their composites are degreewise identities, giving a natural chain isomorphism.
8. In total tensor with B[0] only bidegree (i,0) contributes to degree i. The second
   differential is zero, so the first differential is d tensor 1 with no additional
   term. The canonical signed-total comparison is the sum of the inverse ordinary
   comparisons. Its inverse, followed by the coefficient pullback induced by c_B,
   agrees with the degreewise t under the standard single-factor isomorphisms.
   No flatness, K-flatness, torsion or boundedness was used.
-/
theorem proEtaleScalarBalancingChain
    {A B : Type u} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) {X Y : Scheme.{u}} (f : X ⟶ Y) :
    ((proEtaleConstantRingComparison f A).hom ≫ proEtaleConstantRingMap (T := X) φ =
      (proEtaleSheafInverseImage f CommRingCat.{u + 1}).map
        (proEtaleConstantRingMap (T := Y) φ) ≫ (proEtaleConstantRingComparison f B).hom) ∧
    (∀ (N : proEtaleRingModules Y (proEtaleConstantRing Y B)) (V : Y.ProEt)
      (n : N.val.obj (Opposite.op V)),
      ((scalarBalancingBeta φ f).inv.app N).val.app
          (Opposite.op ((proEtaleBaseChange f).obj V))
          (((proEtaleConstantRingAdjunction A f).unit.app
            ((scalarMateRestriction φ Y).obj N)).val.app (Opposite.op V) n) =
        ((proEtaleConstantRingAdjunction B f).unit.app N).val.app (Opposite.op V) n) ∧
    ∃ t : scalarMateOrdinaryTensor φ Y ⋙ proEtaleConstantRingPullback A f ≅
        proEtaleConstantRingPullback A f ⋙ scalarMateOrdinaryTensor φ X,
      IsScalarBalancing φ f t ∧
      (∀ t' : scalarMateOrdinaryTensor φ Y ⋙ proEtaleConstantRingPullback A f ≅
          proEtaleConstantRingPullback A f ⋙ scalarMateOrdinaryTensor φ X,
        IsScalarBalancing φ f t' → t' = t) ∧
      (∀ (M : proEtaleRingModules Y (proEtaleConstantRing Y A)) (W : X.ProEtᵒᵖ)
        (b : (proEtaleConstantRing X B).obj.obj W)
        (h : ((proEtaleConstantRingPullback B f).obj
          ((proEtaleRingExtension (proEtaleConstantRingMap (T := Y) φ)).obj M)).val.obj W),
        (scalarBalancingMap φ f t M).val.app W (b • h) =
          b • (@id (((proEtaleRingExtension (proEtaleConstantRingMap (T := X) φ)).obj
            ((proEtaleConstantRingPullback A f).obj M)).val.obj W)
              ((scalarBalancingMap φ f t M).val.app W h))) ∧
      ∃ T : (scalarMateOrdinaryTensor φ Y ⋙ proEtaleConstantRingPullback A f).mapHomologicalComplex
            (.up ℤ) ≅
          (proEtaleConstantRingPullback A f ⋙ scalarMateOrdinaryTensor φ X).mapHomologicalComplex
            (.up ℤ),
        (∀ (P : CochainComplex (proEtaleRingModules Y (proEtaleConstantRing Y A)) ℤ)
          (i : ℤ), (T.hom.app P).f i = t.hom.app (P.X i) ∧
            (T.inv.app P).f i = t.inv.app (P.X i)) ∧
        (∀ (P : CochainComplex (proEtaleRingModules Y (proEtaleConstantRing Y A)) ℤ)
          (i j : ℤ),
          (scalarMateOrdinaryTensor φ Y ⋙ proEtaleConstantRingPullback A f).map
              (P.d i j) ≫ t.hom.app (P.X j) =
            t.hom.app (P.X i) ≫
              (proEtaleConstantRingPullback A f ⋙ scalarMateOrdinaryTensor φ X).map
                (P.d i j)) ∧
        ∀ P : CochainComplex (proEtaleRingModules Y (proEtaleConstantRing Y A)) ℤ,
            ((proEtaleConstantRingPullback A f).mapHomologicalComplex (.up ℤ)).map
                (CochainComplex.mapBifunctorSingle₂Iso
                  (proEtaleOrdinaryTensor Y (proEtaleConstantRing Y A))
                  (scalarMateCoefficient φ Y) P).hom ≫ T.hom.app P =
              (proEtaleTensorPullbackTotalIso f
                (proEtaleConstantRing Y A) (proEtaleConstantRing X A)
                (proEtaleConstantRingComparison f A) P (scalarMateCoefficientComplex φ Y)).inv ≫
              HomologicalComplex.mapBifunctorMap
                (𝟙 (((proEtaleConstantRingPullback A f).mapHomologicalComplex (.up ℤ)).obj P))
                (((HomologicalComplex.singleMapHomologicalComplex
                  (proEtaleConstantRingPullback A f) (.up ℤ) 0).app
                    (scalarMateCoefficient φ Y)).hom ≫
                  (CochainComplex.singleFunctor
                    (proEtaleRingModules X (proEtaleConstantRing X A)) (0 : ℤ)).map
                      (scalarMateCoefficientPullback φ f).hom)
                (proEtaleOrdinaryTensor X (proEtaleConstantRing X A)) (.up ℤ) ≫
              (CochainComplex.mapBifunctorSingle₂Iso
                (proEtaleOrdinaryTensor X (proEtaleConstantRing X A))
                (scalarMateCoefficient φ X)
                (((proEtaleConstantRingPullback A f).mapHomologicalComplex (.up ℤ)).obj P)).hom
    := by
  sorry

end AlgebraicGeometry.ProEtale
