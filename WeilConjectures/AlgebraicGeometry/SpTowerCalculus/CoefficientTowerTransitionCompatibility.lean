/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SpTowerCalculus.CoefficientTowerShriekInterfaces
import WeilConjectures.AlgebraicGeometry.SpTowerCalculus.CoefficientTowerCompactSupportStrictTransition
import WeilConjectures.AlgebraicGeometry.ProEtale.Finite.ProEtaleFiniteModulesSupplement
import WeilConjectures.Algebra.Homology.SheafRingDerivedCoefficientAdjunction
import WeilConjectures.Algebra.Homology.DerivedChangeOfRingsIndependentCoefficients
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
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
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived
import Mathlib.CategoryTheory.Adjunction.Additive
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorSingle
import WeilConjectures.FromJoel.Algebra.Homology.ShortComplex.HomologicalComplex
import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import Mathlib.CategoryTheory.Monoidal.Closed.Basic
import Mathlib.CategoryTheory.Limits.ExactFunctor
import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.Algebra.Category.Grp.AB
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import Mathlib.RingTheory.Flat.CategoryTheory
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
import WeilConjectures.Algebra.Homology.Site.SiteTensorFunctorialitySupplement
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import WeilConjectures.CategoryTheory.RingedSiteModules
import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction
import WeilConjectures.Algebra.Homology.SheafRingCoefficientOrdinaryAdjunction
import WeilConjectures.Algebra.Homology.SheafRingDerivedHomComparison
import WeilConjectures.CategoryTheory.DerivedCategory.ResolvingClassEssentialConstancy
import WeilConjectures.CategoryTheory.DerivedCategory.DerivedAdjunctionCompatibility
import Mathlib.CategoryTheory.MorphismProperty.Comma
import Mathlib.CategoryTheory.Functor.Derived.LeftDerived
import Mathlib.CategoryTheory.Functor.Derived.RightDerived
import WeilConjectures.CategoryTheory.DerivedCategory.EssentiallyConstantInd
import Mathlib.CategoryTheory.Filtered.Basic
import Mathlib.CategoryTheory.Limits.Cones
import WeilConjectures.CategoryTheory.DerivedCategory.EssentiallyConstantPro
import Mathlib.Algebra.Homology.DerivedCategory.Fractions
import Mathlib.CategoryTheory.Functor.Derived.Adjunction
import Mathlib.CategoryTheory.Functor.KanExtension.Preserves
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedPointwiseKanBridge
import WeilConjectures.Algebra.Homology.QuasiIsoSaturatedTriangulated
import Mathlib.CategoryTheory.Functor.Derived.PointwiseRightDerived
import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantRingOperations
import WeilConjectures.AlgebraicGeometry.ProEtale.Ring.ProEtaleRingSheafChangeAdjunctionSupplement
import WeilConjectures.AlgebraicGeometry.ProEtale.Direct.ProEtaleDirectImageRestrictionOfScalars
import WeilConjectures.CategoryTheory.RingedToposDerivedPushforwardComposition
import WeilConjectures.CategoryTheory.Ringed.RingedToposMorphismSupplement
import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
import WeilConjectures.CategoryTheory.RingedSiteKInjectiveResolutions
import WeilConjectures.Mathlib.Algebra.Homology.GrothendieckAbelian
import Mathlib.CategoryTheory.Localization.DerivabilityStructure.Derives
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Flat
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Defs
import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution
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
import Mathlib.CategoryTheory.Adjunction.Limits
import WeilConjectures.CategoryTheory.GeometricRingTransport
import Mathlib.CategoryTheory.Sites.Limits
import WeilConjectures.CategoryTheory.SheavesAlgebraicStructuresRingCore
import WeilConjectures.CategoryTheory.SheafRingObjectReconstruction
import WeilConjectures.CategoryTheory.Adjunction.FiniteProductRingFunctor
import WeilConjectures.Algebra.Homology.Module.ModulePullbackPushforwardAdjunctionSupplement
import WeilConjectures.AlgebraicGeometry.KFlatRingedToposPullback
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
import WeilConjectures.Algebra.Homology.ChangeOfRingsKFlatQuasiIso
import Mathlib.CategoryTheory.Sites.EpiMono
import Mathlib.Algebra.Category.Grp.EpiMono
import Mathlib.Algebra.Category.Grp.Abelian
import Mathlib.CategoryTheory.Sites.Abelian
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.MonoidalClosed
import WeilConjectures.Algebra.Homology.CanonicalTensorPullbackOfUniverses.RingedTopoiCanonicalTensorPullbackOfUniverses
import WeilConjectures.AlgebraicGeometry.Direct.DirectImageScalarOperations
import WeilConjectures.AlgebraicGeometry.AdicCoefficientDatum.FourCornersSupplement
import WeilConjectures.AlgebraicGeometry.Open.OpenScalarCounitSquare
public import WeilConjectures.AlgebraicGeometry.Proper.ProperScalarCounitSquare

/-! # Compatibility of actual tower transitions

Source: blueprint Local pairs and Levels, coefficient tower shriek calculus.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall

universe u
open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme
open WeilConjectures

private theorem coefficientSquare
    {XA XB YA YB : Type*} [Category XA] [Category XB] [Category YA] [Category YB]
    {TX : XA ⥤ XB} {RX : XB ⥤ XA} {TY : YA ⥤ YB} {RY : YB ⥤ YA}
    (ax : TX ⊣ RX) (ay : TY ⊣ RY) (FA : XA ⥤ YA) (FB : XB ⥤ YB)
    (d : RX ⋙ FA ≅ FB ⋙ RY) (b : FA ⋙ TY ⟶ TX ⋙ FB)
    (hc : ∀ L, TY.map (d.hom.app L) ≫ ay.counit.app (FB.obj L) =
      b.app (RX.obj L) ≫ FB.map (ax.counit.app L))
    {Pn : XA} {Pm : XB} {Qn : YA} {Qm : YB}
    (tP : Pn ⟶ RX.obj Pm) (tQ : Qn ⟶ RY.obj Qm)
    (θn : Qn ⟶ FA.obj Pn) (θm : Qm ⟶ FB.obj Pm)
    (rx : TX.obj Pn ⟶ Pm) (ry : TY.obj Qn ⟶ Qm)
    (hx : ax.homEquiv _ _ rx = tP) (hy : ay.homEquiv _ _ ry = tQ)
    (ht : tQ ≫ RY.map θm = θn ≫ FA.map tP ≫ d.hom.app Pm) :
    TY.map θn ≫ b.app Pn ≫ FB.map rx = ry ≫ θm := by
  have hrx : TX.map tP ≫ ax.counit.app Pm = rx := by
    calc
      _ = (ax.homEquiv Pn Pm).symm tP := (ax.homEquiv_counit _ _ _).symm
      _ = rx := by rw [← hx]; exact (ax.homEquiv _ _).symm_apply_apply rx
  have hry : TY.map tQ ≫ ay.counit.app Qm = ry := by
    calc
      _ = (ay.homEquiv Qn Qm).symm tQ := (ay.homEquiv_counit _ _ _).symm
      _ = ry := by rw [← hy]; exact (ay.homEquiv _ _).symm_apply_apply ry
  have hh := congrArg (fun t ↦ TY.map t ≫ ay.counit.app (FB.obj Pm)) ht
  simp only [Functor.map_comp, Category.assoc] at hh
  have hn : TY.map (RY.map θm) ≫ ay.counit.app (FB.obj Pm) =
      ay.counit.app Qm ≫ θm := by
    simpa only [Functor.comp_map, Functor.id_map] using ay.counit.naturality θm
  rw [hn, ← Category.assoc, hry] at hh
  rw [hc] at hh
  have hb := b.naturality tP
  dsimp only [Functor.comp_map] at hb
  rw [reassoc_of% hb] at hh
  rw [← FB.map_comp, hrx] at hh
  exact hh.symm

/-- The actual compact-support transition and its scalar-adjunction transpose.
Source: blueprint Levels, step 7; Stacks 07A6, 0D6D and 0D6E.
Proof: write each strict transition as a map to restriction of scalars. The
semilinear direct-image transition formula and the compact-support restriction
comparison express the output transition as F(t) followed by that comparison.
The scalar coordinate unit equation identifies its transpose with the recorded
reduction map. Paste the proper and open scalar counit equations, then apply
the adjunction Hom-equivalence calculation to obtain the displayed equality. This
assertion is about the actual transitions, not only their
sources and targets or their evaluations. No flatness of the quotient is used.
Identity, composition and naturality of input reduction are separate formal laws.
(blueprint: lem-route-reduction-transition-compatibility). -/
theorem reduction_transition_compatibility
    (pchar : ℕ) (hp : 0 < pchar) (hne : pchar ≠ l)
    (k : Type u) [Field k] [CharP k pchar]
    (b : SpTowerShriek.Base l E) (o : SpTowerShriek.Operations l E b)
    (q : Coordinates l E b) (z : FiniteCoordinates l E)
    (finiteData : FiniteNormalization l E k b o q z) :
    (∀ {X Y : Scheme.{u}}
    [X.Over (Spec (.of k))] [IsSeparated (X ↘ Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    [Y.Over (Spec (.of k))] [IsSeparated (Y ↘ Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of k))]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (c : Compactification f) (K : C l E b q X) {m n : ℕ} (v : m ≤ n),
    (scalarExtensionFunctor (quotient l E v) Y).map
        ((finiteData.evaluation c n).comparison.hom.app K.obj) ≫
      (reductionDirectImageComparison (quotient l E v) c.i c.g).app
        ((spDerivedCoefficientEvaluation l E X (q.abelian X) n).obj K.obj) ≫
      (reductionCompactSupport (SpTowerShriek.R l E m) c.i c.g).map
        (reduction l E X (q.abelian X) v (q.scalar X v) K.obj) =
    reduction l E Y (q.abelian Y) v (q.scalar Y v) ((F l E b o q c).obj K.obj) ≫
      (finiteData.evaluation c m).comparison.hom.app K.obj) := by
  have _ := hp
  have _ := hne
  intro X Y _ _ _ _ _ _ _ _ f _ _ _ _ c K m n v
  exact coefficientSquare
    (proEtaleRingDerivedExtensionAdjunction
      (proEtaleConstantRingMap (T := X) (quotient l E v)))
    (proEtaleRingDerivedExtensionAdjunction
      (proEtaleConstantRingMap (T := Y) (quotient l E v)))
    (reductionCompactSupport (SpTowerShriek.R l E n) c.i c.g)
    (reductionCompactSupport (SpTowerShriek.R l E m) c.i c.g)
    (intrinsicCompactSupportRestriction (quotient l E v) c.i c.g)
    (reductionDirectImageComparison (quotient l E v) c.i c.g)
    (supportScalarCounit (quotient l E v) c.i c.g)
    (intrinsicTransition l E X (q.abelian X) v (q.scalar X v) K.obj)
    (intrinsicTransition l E Y (q.abelian Y) v (q.scalar Y v)
      ((F l E b o q c).obj K.obj))
    ((finiteData.evaluation c n).comparison.hom.app K.obj)
    ((finiteData.evaluation c m).comparison.hom.app K.obj)
    (reduction l E X (q.abelian X) v (q.scalar X v) K.obj)
    (reduction l E Y (q.abelian Y) v (q.scalar Y v) ((F l E b o q c).obj K.obj))
    (reduction_homEquiv_intrinsicTransition l E X (q.abelian X) v (q.scalar X v) K.obj)
    (reduction_homEquiv_intrinsicTransition l E Y (q.abelian Y) v (q.scalar Y v)
      ((F l E b o q c).obj K.obj))
    (compactSupport_intrinsicTransition l E b o q c (finiteData.evaluation c) K.obj v)

private theorem supportScalarCounit
    {A B : Type u} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) {X Z Y : Scheme.{u}} (j : X ⟶ Z) [IsOpenImmersion j]
    (h : Z ⟶ Y) (H : proEtaleDerivedCategory X B) :
    (scalarExtensionFunctor φ Y).map
        ((intrinsicCompactSupportRestriction φ j h).hom.app H) ≫
      (proEtaleRingDerivedExtensionAdjunction
        (proEtaleConstantRingMap (T := Y) φ)).counit.app
          ((reductionCompactSupport B j h).obj H) =
    (reductionDirectImageComparison φ j h).app ((scalarRestriction φ X).obj H) ≫
      (reductionCompactSupport B j h).map
        ((proEtaleRingDerivedExtensionAdjunction
          (proEtaleConstantRingMap (T := X) φ)).counit.app H) := by
  have hp := ((properScalarCounitSquare φ h).2.2.1
    ((sfIntrinsicExtensionByZero j B).mapDerivedCategory.obj H)).2
  have ho := congr_app (openScalarCounitSquare φ j) H
  dsimp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app] at ho
  change (scalarExtensionFunctor φ Y).map
      ((directImageConstantPush A h).map ((sfOpenRestrictionDerived j φ).hom.app H) ≫
        (directImageScalarRestrictionIso φ h).hom.app _) ≫ _ = _
  simp only [Functor.map_comp, Category.assoc]
  erw [hp]
  have hn := (directImageScalarComparison φ h).naturality
    ((sfOpenRestrictionDerived j φ).hom.app H)
  dsimp only [Functor.comp_map] at hn
  erw [reassoc_of% hn]
  erw [← (directImageConstantPush B h).map_comp]
  erw [ho]
  rw [Functor.map_comp]
  exact (Category.assoc _ _ _).symm

namespace AlgebraicGeometry.ProEtale.SpTowerCalculus

set_option maxHeartbeats 2000000 in
-- The derived counit comparisons require a larger elaboration budget.
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

end AlgebraicGeometry.ProEtale.SpTowerCalculus

attribute [instance high] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
