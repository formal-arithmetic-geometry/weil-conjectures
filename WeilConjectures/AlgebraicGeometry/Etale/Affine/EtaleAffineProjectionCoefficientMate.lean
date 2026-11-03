/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Vector.VectorBundlePurity
public import WeilConjectures.AlgebraicGeometry.Reduction.ReductionExceptionalObjects
public import WeilConjectures.AlgebraicGeometry.Etale.Compact.EtaleCompactScalarCoherence
public import WeilConjectures.AlgebraicGeometry.BoundedConstructibleComplexes
public import WeilConjectures.SixFunctors.Etale.Derived.EtaleTorAmplitude
import WeilConjectures.AlgebraicGeometry.Reduction.ReductionExceptionalObjects
import WeilConjectures.AlgebraicGeometry.Affine.AffineCounitScalar
import WeilConjectures.AlgebraicGeometry.AffineIntegrationCoefficient.EtaleAffineIntegrationCoefficientEquation
import WeilConjectures.AlgebraicGeometry.Ordinary.OrdinaryFiniteP1DatumUniqueness
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
import WeilConjectures.AlgebraicGeometry.AdjunctionTransfer.EtaleProEtaleAdjunctionTransfer
import all WeilConjectures.AlgebraicGeometry.CoefficientCompatibility.EtaleProEtaleCoefficientCompatibility
public import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantModuleConstructibility
public import WeilConjectures.AlgebraicGeometry.Reduction.ReductionExceptionalChart
public import WeilConjectures.AlgebraicGeometry.Reduction.ReductionExceptionalConservativity
public import WeilConjectures.AlgebraicGeometry.Reduction.ReductionExceptionalRealization
public import WeilConjectures.AlgebraicGeometry.Reduction.ReductionSiteCoefficientPasting
public import WeilConjectures.SmoothPurity.OrdinaryFiniteTwistTransportUniqueness

/-! # The normalized affine projection coefficient mate

Source: blueprint main-20261015, sec-smooth-purity/sk-lem-sp-reduction,
sk-lem-sp-reduction-exceptional.proof.md, Charts and uniqueness of transposes
(blueprint: lem-pur-etale-affine-projection-coefficient-mate).

The existing ordered affine tower is canonically affine space by
`affineTraceAffineSpaceIso`. Positive coefficient levels are indexed by their
predecessors. The ordinary mate, scalar map, Tate reassociation and site transport
are the published constructions, with their actual counits retained.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true

universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace AlgebraicGeometry.Etale

/-- The integration-normalized purity comparison. The affine adjunction has the
specified iterated projective-line integration as counit. Transport its left functor
by the proper/open compactification comparison, then use uniqueness of right adjoints.
Source: blueprint Charts, vector-bundle integration on the trivial bundle
(blueprint: lem-pur-etale-affine-projection-coefficient-mate). -/
def affineProjectionPurityIso (A : Type (u + 1)) [CommRing A] [Finite A]
    (V : Scheme.{u}) [IsNoetherian V] (d N : ℕ) (hA : (N : A) = 0)
    (hV : IsUnit (N : Γ(V, ⊤))) (t : OrdinaryFiniteTwistTransport A N hA)
    (D : ∀ (T : Scheme.{u}) [IsNoetherian T] (hT : IsUnit (N : Γ(T, ⊤))),
      OrdinaryFiniteP1Datum A N hA t T hT) :
    affineTraceRight A N hA V d ≅
      rightDerivedUpperShriek A (affineTraceProjection V d) :=
  ((affineTraceAdjunction A N hA t D V hV d).ofNatIsoLeft
    (ProEtale.reductionEtaleAffineLeftIso A V d
      (HasCompactification.compactification (affineTraceProjection V d)))).rightAdjointUniq
        (rightDerivedUpperShriekAdjunction A
          (affineTraceProjection V d))

/-- The ordinary part of the assertion, including the domain on which the specified
coefficient projection is invertible. Every normalized P1 datum is allowed; its fields
fix the Kummer classes, trace and counit, so these are not extra orientation choices.
Source: blueprint Charts and uniqueness of transposes
(blueprint: lem-pur-etale-affine-projection-coefficient-mate). -/
def AffineProjectionCoefficientAssertion
    (A B : Type (u + 1)) [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) (V : Scheme.{u}) [IsNoetherian V] (d N : ℕ)
    (hA : (N : A) = 0) (hB : (N : B) = 0) (hV : IsUnit (N : Γ(V, ⊤))) : Prop :=
  ∀ (tA : OrdinaryFiniteTwistTransport A N hA)
    (DA : ∀ (T : Scheme.{u}) [IsNoetherian T] (hT : IsUnit (N : Γ(T, ⊤))),
      OrdinaryFiniteP1Datum A N hA tA T hT)
    (tB : OrdinaryFiniteTwistTransport B N hB)
    (DB : ∀ (T : Scheme.{u}) [IsNoetherian T] (hT : IsUnit (N : Γ(T, ⊤))),
      OrdinaryFiniteP1Datum B N hB tB T hT)
    (L : DerivedCategoryModule A V),
    DerivedCategory.isBoundedConstructible A V L →
    (∃ a b : ℤ, DerivedCategory.hasTorAmplitudeIn A V a b L) →
    IsIso (ExceptionalCoefficients.compactSupportMap φ
      (HasCompactification.compactification (affineTraceProjection V d))
      ((rightDerivedUpperShriek A
        (affineTraceProjection V d)).obj L)) ∧
    IsIso (ExceptionalCoefficients.mateMap φ (affineTraceProjection V d) L) ∧
    (scalarExtension φ (affineTraceTower V d)).map
        ((affineProjectionPurityIso A V d N hA hV tA DA).hom.app L) ≫
      ExceptionalCoefficients.mateMap φ (affineTraceProjection V d) L =
    (ProEtale.reductionEtaleAffineScalarIso φ V N hA hB hV d L).hom ≫
      (affineProjectionPurityIso B V d N hB hV tB DB).hom.app
        ((scalarExtension φ V).obj L)

private theorem affineProjectionPurityIso_counit
    (A : Type (u + 1)) [CommRing A] [Finite A]
    (V : Scheme.{u}) [IsNoetherian V] (d N : ℕ) (hA : (N : A) = 0)
    (hV : IsUnit (N : Γ(V, ⊤))) (t : OrdinaryFiniteTwistTransport A N hA)
    (D : ∀ (T : Scheme.{u}) [IsNoetherian T] (hT : IsUnit (N : Γ(T, ⊤))),
      OrdinaryFiniteP1Datum A N hA t T hT) (L : DerivedCategoryModule A V) :
    (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A)
        (HasCompactification.compactification (affineTraceProjection V d))).map
        ((affineProjectionPurityIso A V d N hA hV t D).hom.app L) ≫
      (rightDerivedUpperShriekAdjunction A
        (affineTraceProjection V d)).counit.app L =
    (ProEtale.reductionEtaleAffineLeftIso A V d
      (HasCompactification.compactification (affineTraceProjection V d))).inv.app _ ≫
        (affineTraceAdjunction A N hA t D V hV d).counit.app L := by
  let adj := (affineTraceAdjunction A N hA t D V hV d).ofNatIsoLeft
    (ProEtale.reductionEtaleAffineLeftIso A V d
      (HasCompactification.compactification (affineTraceProjection V d)))
  exact adj.rightAdjointUniq_hom_app_counit
    (rightDerivedUpperShriekAdjunction A
      (affineTraceProjection V d)) L

private theorem affineScalarCounit_allData (N : ℕ) (hN : 0 < N)
    (A : Type (u + 1)) [CommRing A] [Finite A] (hA : (N : A) = 0)
    (V : Scheme.{u}) [IsNoetherian V] (hV : IsUnit (N : Γ(V, ⊤))) (d : ℕ)
    (t : OrdinaryFiniteTwistTransport A N hA)
    (D : ∀ (T : Scheme.{u}) [IsNoetherian T] (hT : IsUnit (N : Γ(T, ⊤))),
      OrdinaryFiniteP1Datum A N hA t T hT) (L : DerivedCategoryModule A V) :
    (ProEtale.reductionEtaleAffineLeftIso A V d
      (HasCompactification.compactification (affineTraceProjection V d))).inv.app _ ≫
        (affineTraceAdjunction A N hA t D V hV d).counit.app L =
      affineScalarCompactificationCounit N hN A hA V hV d
        (HasCompactification.compactification (affineTraceProjection V d)) L := by
  obtain rfl := ordinaryFiniteTwistTransport_unique A N hA t
    (projectiveLineTraceTransport N hN A hA)
  have hD : D = projectiveLineTraceDatum N hN A hA := by
    funext T inst hT
    exact ordinaryFiniteP1Datum_unique A N hA _ T hT _ _
  rw [hD]
  rfl

private theorem normalizeCounitEquation
    {C D : Type*} [Category C] [Category D] (T : C ⥤ D)
    {A B Z : C} {W X Y : D}
    (gA : A ⟶ B) (epsA : B ⟶ Z) (zA : A ⟶ Z)
    (q : T.obj A ⟶ W) (a : W ⟶ X) (gB : X ⟶ Y)
    (epsB : Y ⟶ T.obj Z) (zB : X ⟶ T.obj Z)
    (hA : gA ≫ epsA = zA) (hB : gB ≫ epsB = zB)
    (h : q ≫ a ≫ zB = T.map zA) :
    q ≫ a ≫ gB ≫ epsB = T.map (gA ≫ epsA) := by
  rw [hB, hA]
  exact h

-- Keep the associativity calculation over abstract arrows: the scheme-specific
-- comparison constructions are large and must be used only through their equations.

private theorem normalizedMateComponent
    {CA DA CB DB : Type*} [Category CA] [Category DA] [Category CB] [Category DB]
    {FA : CA ⥤ DA} {GA HA : DA ⥤ CA} {FB : CB ⥤ DB} {GB HB : DB ⥤ CB}
    (adjA : FA ⊣ GA) (adjB : FB ⊣ GB) (γA : HA ≅ GA) (γB : HB ≅ GB)
    (S : CA ⥤ CB) (T : DA ⥤ DB) (K : DA)
    (qH : T.obj (FA.obj (HA.obj K)) ≅ FB.obj (S.obj (HA.obj K)))
    (qG : T.obj (FA.obj (GA.obj K)) ≅ FB.obj (S.obj (GA.obj K)))
    (a : S.obj (HA.obj K) ≅ HB.obj (T.obj K))
    (b : S.obj (GA.obj K) ⟶ GB.obj (T.obj K))
    (hb : FB.map b ≫ adjB.counit.app (T.obj K) =
      qG.inv ≫ T.map (adjA.counit.app K))
    (hn : T.map (FA.map (γA.hom.app K)) ≫ qG.hom =
      qH.hom ≫ FB.map (S.map (γA.hom.app K)))
    (hz : qH.hom ≫ FB.map a.hom ≫ FB.map (γB.hom.app (T.obj K)) ≫
        adjB.counit.app (T.obj K) =
      T.map (FA.map (γA.hom.app K) ≫ adjA.counit.app K)) :
    IsIso b ∧ S.map (γA.hom.app K) ≫ b = a.hom ≫ γB.hom.app (T.obj K) := by
  have he : S.map (γA.hom.app K) ≫ b = a.hom ≫ γB.hom.app (T.obj K) := by
    apply (adjB.homEquiv _ _).symm.injective
    simp only [Adjunction.homEquiv_counit, FB.map_comp, Category.assoc]
    rw [hb]
    apply (cancel_epi qH.hom).1
    rw [← Category.assoc qH.hom, ← hn]
    simp only [Category.assoc, Iso.hom_inv_id_assoc]
    simpa only [T.map_comp, Category.assoc] using hz.symm
  refine ⟨?_, he⟩
  have hf : b = S.map (γA.inv.app K) ≫ a.hom ≫ γB.hom.app (T.obj K) := by
    apply (cancel_epi (S.map (γA.hom.app K))).1
    simpa only [← S.map_comp_assoc, Iso.hom_inv_id_app, S.map_id,
      Category.id_comp, Category.assoc] using he
  rw [hf]
  infer_instance

private theorem ordinaryAffineProjectionAssertion
    (ell pchar : ℕ) [Fact ell.Prime] (hp : 0 < pchar) (hell : ell ≠ pchar)
    (k : Type u) [Field k] [CharP k pchar] (hk : Finite k ∨ IsAlgClosed k)
    (A B : Type (u + 1)) [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) (r : ℕ) (hA : ((ell ^ r : ℕ) : A) = 0)
    (hB : ((ell ^ r : ℕ) : B) = 0)
    (V : Scheme.{u}) [IsNoetherian V] [V.Over (Spec (.of k))]
    [LocallyOfFiniteType (V ↘ Spec (.of k))] [QuasiCompact (V ↘ Spec (.of k))]
    [IsSeparated (V ↘ Spec (.of k))] (hN : IsUnit ((ell ^ r : ℕ) : Γ(V, ⊤)))
    (d : ℕ) : AffineProjectionCoefficientAssertion A B φ V d (ell ^ r) hA hB hN := by
  let : IsNoetherian (affineTraceTower V d) := affineTraceNoetherian V d
  intro tA DA tB DB L hL hTor
  let c := HasCompactification.compactification (affineTraceProjection V d)
  let FA := rightDerivedLowerShriek
    (ModuleCat.{u + 1} A) (affineTraceProjection V d)
  let FB := rightDerivedLowerShriek
    (ModuleCat.{u + 1} B) (affineTraceProjection V d)
  let γA := affineProjectionPurityIso _ V d _ hA hN tA DA
  let γB := affineProjectionPurityIso _ V d _ hB hN tB DB
  let adjA := rightDerivedUpperShriekAdjunction
    A (affineTraceProjection V d)
  let adjB := rightDerivedUpperShriekAdjunction
    B (affineTraceProjection V d)
  let Q := scalarExtension φ V
  let SX := scalarExtension φ (affineTraceTower V d)
  let a := ProEtale.reductionEtaleAffineScalarIso φ V _ hA hB hN d L
  have hc := etaleCompactScalarCoherence φ (affineTraceProjection V d) c
  have hq (M : DerivedCategoryModule A
      (affineTraceTower V d)) : IsIso (ExceptionalCoefficients.compactSupportMap φ c M) :=
    hc.1 M
  have hctf : ProEtale.AdjunctionTransfer.etaleProperty
      A V L := by
    refine ⟨hL, ?_⟩
    obtain ⟨a, b, h⟩ := hTor
    exact ⟨a, b, DerivedCategory.hasTorAmplitudeIn_iff_torAmplitudeIn.mp h⟩
  obtain ⟨hV', hN', heq⟩ := affine_counit_scalar ell pchar hp (Ne.symm hell) k hk
    _ _ φ r hA hB V d c L hctf
  have hnorm : ExceptionalCoefficients.compactSupportMap φ c
      ((affineTraceRight _ _ hA V d).obj L) ≫ FB.map a.hom ≫
      FB.map (γB.hom.app (Q.obj L)) ≫ adjB.counit.app (Q.obj L) =
    Q.map (FA.map (γA.hom.app L) ≫ adjA.counit.app L) := by
    have hγA := (affineProjectionPurityIso_counit _ V d _ hA hN tA DA L).trans
      (affineScalarCounit_allData _ (pow_pos (Fact.out : ell.Prime).pos _) _ hA
        V hN d tA DA L)
    have hγB := (affineProjectionPurityIso_counit _ V d _ hB hN tB DB (Q.obj L)).trans
      (affineScalarCounit_allData _ (pow_pos (Fact.out : ell.Prime).pos _) _ hB
        V hN d tB DB (Q.obj L))
    apply normalizeCounitEquation Q (FA.map (γA.hom.app L)) (adjA.counit.app L) _
      _ (FB.map a.hom) (FB.map (γB.hom.app (Q.obj L)))
      (adjB.counit.app (Q.obj L)) _ hγA hγB
    simpa only [ProEtale.CoefficientCompatibility.etaleCoefficientMap_eq_compactScalarMap,
      compactScalarMap, a, FA, FB, Q, c, rightDerivedLowerShriek] using heq
  let qH := @asIso _ _ _ _
    (ExceptionalCoefficients.compactSupportMap φ c ((affineTraceRight _ _ hA V d).obj L))
    (hq _)
  let qG := @asIso _ _ _ _
    (ExceptionalCoefficients.compactSupportMap φ c
      ((rightDerivedUpperShriek A (affineTraceProjection V d)).obj L))
    (hq _)
  have hb : FB.map (ExceptionalCoefficients.mateMap φ (affineTraceProjection V d) L) ≫
      adjB.counit.app (Q.obj L) = qG.inv ≫ Q.map (adjA.counit.app L) := by
    have hh := (adjB.homEquiv _ _).symm_apply_apply
      (ExceptionalCoefficients.comparisonInverse φ c
        ((rightDerivedUpperShriek A (affineTraceProjection V d)).obj L) ≫
        Q.map (adjA.counit.app L))
    change FB.map (ExceptionalCoefficients.mateMap φ (affineTraceProjection V d) L) ≫
      adjB.counit.app (Q.obj L) = _ at hh
    simp only [qG, asIso_inv]
    dsimp only [ExceptionalCoefficients.comparisonInverse] at hh
    rw [dif_pos (hq _)] at hh
    exact hh
  have hn := compactScalarMap_naturality φ c (γA.hom.app L)
  change Q.map (FA.map (γA.hom.app L)) ≫ _ =
    _ ≫ FB.map (SX.map (γA.hom.app L)) at hn
  have hresult := normalizedMateComponent adjA adjB γA γB SX Q L qH qG a
    (ExceptionalCoefficients.mateMap φ (affineTraceProjection V d) L) hb
    (by simpa only [qH, qG, asIso_hom] using hn)
    (by simpa only [qH, asIso_hom, FA, FB, Q, rightDerivedLowerShriek, c] using hnorm)
  exact ⟨hq _, hresult.1, hresult.2⟩

end AlgebraicGeometry.Etale

namespace AlgebraicGeometry.ProEtale

end AlgebraicGeometry.ProEtale

namespace AlgebraicGeometry.Etale

attribute [local irreducible] ProEtale.reductionSiteScalarIso
  ProEtale.reductionSiteCompactSupportIso ProEtale.reductionDirectImageComparison
  ProEtale.reductionSite ProEtale.scalarExtensionFunctor
  ProEtale.reductionEtaleAffineScalarIso affineProjectionPurityIso

open ProEtale in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
end AlgebraicGeometry.Etale
