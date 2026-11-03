/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.VectorIntegrationSite.ProEtaleFrameIntegration

import WeilConjectures.SixFunctors.Etale.Derived.UpperStarIdCoherence
import WeilConjectures.AlgebraicGeometry.Vector.VectorBundleIntegration
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
import WeilConjectures.AlgebraicGeometry.Ordinary.OrdinaryFiniteP1DatumUniqueness
import WeilConjectures.AlgebraicGeometry.VectorIntegrationSite.OrderedIntegrationComparison
public import WeilConjectures.SmoothPurity.OrdinaryFiniteTwistTransportUniqueness

/-! # Pro-etale vector integration with local normalization
Source: main-20261015, vector-bundle integration; Stacks 09AF and 099R
(blueprint: def-pur-proetale-vector-integration).
-/
@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 2048
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.VectorIntegrationSite
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra (Padic l) E]
  [FiniteDimensional (Padic l) E] (n : ℕ)
variable (S : Scheme.{u}) [IsNoetherian S]
variable (r : ℕ)
  (hA : ((l ^ (r + 1) : ℕ) : Scheme.finiteTateCoefficient l E n) = 0)
variable (d : ℕ) (F : SheafOfModules.{u} S.ringCatSheaf) [F.IsFiniteLocallyFreeOfRank d]

set_option linter.unusedVariables false in
end AlgebraicGeometry.ProEtale.VectorIntegrationSite

namespace AlgebraicGeometry.ProEtale.VectorIntegrationSite

private theorem plus_pullback (A : Type (u + 1)) [CommRing A]
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (K : Etale.DerivedCategoryModule A Y) (hK : DerivedCategory.TStructure.t.plus K) :
    DerivedCategory.TStructure.t.plus ((Etale.ordinaryFinitePullback A f).obj K) := by
  obtain ⟨a, ha⟩ := hK
  have := ha
  apply (DerivedCategory.TStructure.t.plus).prop_of_iso
    ((Etale.leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) f).symm.app K)
  exact ⟨a, (Etale.upperStar (ModuleCat.{u + 1} A) f).isGE_mapDerivedCategory_obj K a⟩

/-- Boundedness of the actual vector coefficient follows from the locally free Tate line.
Source: finite Tate local freeness and exact inverse image
(blueprint: def-pur-proetale-vector-integration).
Proof: each shifted line has amplitude [-2,-2]. Its d-fold tensor has amplitude
[-2d,-2d], including the zero-fold constant. Exact inverse image along pi preserves
these bounds. In particular this complex is bounded below.
-/
theorem vectorCoefficient_plus (hS : IsUnit (l : Γ(S, ⊤))) :
    DerivedCategory.TStructure.t.plus
      (Etale.vectorIntegrationCoefficient (Scheme.finiteTateCoefficient l E n)
        (l ^ (r + 1)) hA S d F) := by
  let A := Scheme.finiteTateCoefficient l E n
  let N := l ^ (r + 1)
  have hN : 0 < N := pow_pos (Fact.out : l.Prime).pos _
  have hSN : IsUnit (N : Γ(S, ⊤)) := by
    simpa only [N, Nat.cast_pow] using hS.pow (r + 1)
  let t := Etale.projectiveLineTraceTransport N hN A hA
  -- Retract the affine coefficient descent along its canonical zero section.
  let z : (e : ℕ) → S ⟶ affineTraceTower S e :=
    Nat.rec (𝟙 S) (fun e s ↦ s ≫ AffineSpace.zeroSection PUnit.{u + 1} _)
  have hz : ∀ e, z e ≫ affineTraceProjection S e = 𝟙 S := by
    intro e
    induction e with
    | zero => exact Category.id_comp _
    | succ e ih =>
      change (z e ≫ AffineSpace.zeroSection PUnit.{u + 1} _) ≫
        (_ ≫ affineTraceProjection S e) = 𝟙 S
      rw [Category.assoc, ← Category.assoc (AffineSpace.zeroSection PUnit.{u + 1} _),
        AffineSpace.zeroSection_comp_over, Category.id_comp]
      exact ih
  let K := Etale.affineLinearBaseCoefficient A N hA S d
  let e := Etale.affineLinearCoefficientDescent A N hA t S hSN d
  have hb : DerivedCategory.TStructure.t.plus
      ((Etale.ordinaryFinitePullback A (affineTraceProjection S d)).obj K) :=
    (DerivedCategory.TStructure.t.plus).prop_of_iso e
      (rightTower_plus l E n S hS r hA d
        ⟨Etale.ordinaryFiniteUnit A S, ⟨0, inferInstance⟩⟩)
  have hzK := plus_pullback A (z d) _ hb
  have hK : DerivedCategory.TStructure.t.plus K :=
    (DerivedCategory.TStructure.t.plus).prop_of_iso
      ((Etale.leftDerivedUpperStarCompSectionIso (ModuleCat.{u + 1} A)
        (z d) (affineTraceProjection S d) (hz d)).app K) hzK
  exact plus_pullback A (VectorBundleZeroSection.π S d F) K hK

/-- The actual pro-etale compact-support source, at the canonical Nagata compactification.
Source: vector-bundle integration (blueprint: def-pur-proetale-vector-integration). -/
abbrev vectorSource :=
  (rightDerivedLowerShriekOfCompactification
    (ModuleCat.{u + 1} (Scheme.finiteTateCoefficient l E n))
    (Etale.vectorBundlePurityCompactification S d F)).obj
      ((comparison (Scheme.finiteTateCoefficient l E n) _).obj
        (Etale.vectorIntegrationCoefficient _ (l ^ (r + 1)) hA S d F))

/-- Canonical compact-support comparison: proper counit mate after exact open extension.
Source: Stacks 09AF and 099R (blueprint: def-pur-proetale-vector-integration). -/
@[irreducible]
def vectorSite (hS : IsUnit (l : Γ(S, ⊤))) :
    vectorSource l E n S r hA d F ≅
      (comparison (Scheme.finiteTateCoefficient l E n) S).obj
        (Etale.vectorIntegrationSource _ (l ^ (r + 1)) hA S d F) :=
  (compactSupportSiteComparison (Scheme.finiteTateCoefficient l E n)
    (Etale.vectorBundlePurityCompactification S d F)).app
      ⟨_, vectorCoefficient_plus l E n S r hA d F hS⟩

/-- Every frame restriction equals the independently formed ordered pro-etale trace.
The canonical comparison only identifies the source of the chart exchange; it contains
no integration morphism. Source: blueprint vector-bundle integration, a_i
(blueprint: def-pur-proetale-vector-integration). -/
@[irreducible]
def VectorNormalization (hS : IsUnit (l : Γ(S, ⊤)))
    (t : vectorSource l E n S r hA d F ⟶ unit (Scheme.finiteTateCoefficient l E n) S) :
    Prop :=
  ∀ (V : S.Opens) (e : VectorBundleZeroSection.Trivialization S d F V),
    (upperStar (ModuleCat.{u + 1} (Scheme.finiteTateCoefficient l E n)) V.ι).leftDerivedFunctor.map
         t ≫
      (pullbackUnit (Scheme.finiteTateCoefficient l E n) V.ι).hom =
    (upperStar (ModuleCat.{u + 1} (Scheme.finiteTateCoefficient l E n)) V.ι).leftDerivedFunctor.map
         (vectorSite l E n S r hA d F hS).hom ≫
      (pullback (Scheme.finiteTateCoefficient l E n) V.ι).inv.app _ ≫
        localIntegration l E n S hS r hA d F V e

private theorem compared_pullback_unit (A : Type (u + 1)) [CommRing A]
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    {K : Etale.DerivedCategoryModule A Y} (g : K ⟶ Etale.ordinaryFiniteUnit A Y) :
    (upperStar (ModuleCat.{u + 1} A) f).leftDerivedFunctor.map
        ((comparison A Y).map g) ≫ (pullbackUnit A f).hom =
      (pullback A f).inv.app K ≫ (comparison A X).map
        ((Etale.ordinaryFinitePullback A f).map g ≫
          (Etale.ordinaryFiniteUnitPullback A f).hom) := by
  have hn := (pullback A f).inv.naturality g
  dsimp only [Functor.comp_map] at hn
  unfold pullbackUnit geoP1UnitPullback
  simp only [Iso.trans_hom, Functor.mapIso_hom]
  unfold pullback at hn ⊢
  with_unfolding_all
    erw [← Category.assoc, hn, Category.assoc, ← CategoryTheory.Functor.map_comp]

private theorem localIntegration_comparison (hS : IsUnit (l : Γ(S, ⊤)))
    (V : S.Opens) (e : VectorBundleZeroSection.Trivialization S d F V) :
    localIntegration l E n S hS r hA d F V e =
      (comparison (Scheme.finiteTateCoefficient l E n) V.toScheme).map
        (Etale.vectorIntegrationLocalTrace (l ^ (r + 1))
          (pow_pos (Fact.out : l.Prime).pos _) _ hA
          (Etale.projectiveLineTraceTransport _ (pow_pos (Fact.out : l.Prime).pos _) _ hA)
          (Etale.projectiveLineTraceDatum _ (pow_pos (Fact.out : l.Prime).pos _) _ hA)
          S (by simpa only [Nat.cast_pow] using hS.pow (r + 1)) d F V e) := by
  let : TopologicalSpace.NoetherianSpace V.toScheme :=
    V.ι.isOpenEmbedding.isInducing.noetherianSpace
  let : IsNoetherian V.toScheme :=
    { toIsLocallyNoetherian := inferInstance
      isCompact_univ := TopologicalSpace.NoetherianSpace.isCompact _ }
  unfold localIntegration
  rw [orderedIntegration_comparison]
  rw [← Functor.map_comp]
  unfold chartPrefix Etale.vectorIntegrationLocalTrace
  simp only [Category.assoc]

private theorem normalization_comparison (hS : IsUnit (l : Γ(S, ⊤)))
    (g : Etale.vectorIntegrationSource (Scheme.finiteTateCoefficient l E n)
      (l ^ (r + 1)) hA S d F ⟶
        Etale.ordinaryFiniteUnit (Scheme.finiteTateCoefficient l E n) S) :
    VectorNormalization l E n S r hA d F hS
        ((vectorSite l E n S r hA d F hS).hom ≫
          (comparison (Scheme.finiteTateCoefficient l E n) S).map g) ↔
      Etale.VectorIntegrationNormalization (l ^ (r + 1))
        (pow_pos (Fact.out : l.Prime).pos _) _ hA S
        (by simpa only [Nat.cast_pow] using hS.pow (r + 1)) d F g := by
  let A := Scheme.finiteTateCoefficient l E n
  let N := l ^ (r + 1)
  have hN : 0 < N := pow_pos (Fact.out : l.Prime).pos _
  let t := Etale.projectiveLineTraceTransport N hN A hA
  let D := Etale.projectiveLineTraceDatum N hN A hA
  unfold VectorNormalization Etale.VectorIntegrationNormalization
  constructor
  · intro h t' D' V e
    have ht : t' = t := Etale.ordinaryFiniteTwistTransport_unique A N hA t' t
    subst t'
    have hd : D' = D := by
      funext T inst hT
      exact Etale.ordinaryFiniteP1Datum_unique A N hA t T hT (D' T hT) (D T hT)
    subst D'
    have he := h V e
    simp only [Functor.map_comp, Category.assoc] at he
    rw [compared_pullback_unit, localIntegration_comparison] at he
    have he' := (cancel_epi
      ((upperStar (ModuleCat.{u + 1} A) V.ι).leftDerivedFunctor.map
        (vectorSite l E n S r hA d F hS).hom)).mp he
    have he'' := (cancel_epi ((pullback A V.ι).inv.app _)).mp he'
    exact (bijective_comparisonUpperStar_mapDerivedCategory_map _ _
      (show DerivedCategory.TStructure.t.plus (Etale.ordinaryFiniteUnit A V.toScheme)
        from ⟨0, inferInstance⟩)).1 he''
  · intro h V e
    simp only [Functor.map_comp, Category.assoc]
    rw [compared_pullback_unit, localIntegration_comparison, h t D V e]

private theorem ordinary_integration_unique
    (N : ℕ) (hN : 0 < N) (A : Type (u + 1)) [CommRing A] [Finite A]
    (hA : (N : A) = 0) (hS : IsUnit (N : Γ(S, ⊤)))
    (g : Etale.vectorIntegrationSource A N hA S d F ⟶ Etale.ordinaryFiniteUnit A S)
    (hg : Etale.VectorIntegrationNormalization N hN A hA S hS d F g) :
    g = Etale.vectorBundleIntegration N hN A hA S hS d F := by
  let p := Etale.vectorIntegrationGluing N hN A hA S hS d F
  have hp := (Etale.existsUnique_vectorIntegrationGluing N hN A hA S hS d F).2
  have hpn := hp.exists.choose_spec
  obtain ⟨a, ha⟩ := (DerivedCategory.singleFunctor _ 0).map_surjective (p.1.inv ≫ g)
  have hga : p.1.hom ≫ (DerivedCategory.singleFunctor _ 0).map a = g := by
    rw [ha, ← Category.assoc, p.1.hom_inv_id, Category.id_comp]
  have heq : (p.1, a) = p := hp.unique ⟨hpn.1, by rwa [hga]⟩ hpn
  have hea : a = p.2 := congrArg Prod.snd heq
  rw [← hga, hea]
  rfl

/-- The local maps agree on overlaps and glue uniquely as degree-zero sheaf maps.
Source: blueprint vector-bundle integration; Stacks 06XS and 03EM
(blueprint: def-pur-proetale-vector-integration).
Proof: compare each coordinate's open counit and proper trace under the canonical
mate. Induct on the ordered coordinates using the composite-counit formula. Under
site comparison these are the ordinary normalized affine traces; linear invariance
makes their restrictions agree on overlaps. The compact-support source has no
cohomology outside degree zero on a frame cover, so the same is true globally.
The target is also degree zero. The degree-zero embedding is fully faithful, so
sheaf-Hom gluing gives existence and uniqueness. Rank zero uses the identity trace;
for the empty base the unique sheaf morphism supplies the same conclusion.
-/
theorem existsUniqueVectorIntegration (hS : IsUnit (l : Γ(S, ⊤))) :
    ∃! t : vectorSource l E n S r hA d F ⟶ unit (Scheme.finiteTateCoefficient l E n) S,
      VectorNormalization l E n S r hA d F hS t := by
  let A := Scheme.finiteTateCoefficient l E n
  let N := l ^ (r + 1)
  have hN : 0 < N := pow_pos (Fact.out : l.Prime).pos _
  have hSN : IsUnit (N : Γ(S, ⊤)) := by
    simpa only [N, Nat.cast_pow] using hS.pow (r + 1)
  let g := Etale.vectorBundleIntegration N hN A hA S hSN d F
  have hg : Etale.VectorIntegrationNormalization N hN A hA S hSN d F g :=
    (Etale.existsUnique_vectorIntegrationGluing N hN A hA S hSN d F).2.exists.choose_spec.2
  let c := vectorSite l E n S r hA d F hS
  refine ⟨c.hom ≫ (comparison A S).map g,
    (normalization_comparison l E n S r hA d F hS g).2 hg, ?_⟩
  intro f hf
  obtain ⟨a, ha⟩ := (bijective_comparisonUpperStar_mapDerivedCategory_map
    (Etale.vectorIntegrationSource A N hA S d F) (Etale.ordinaryFiniteUnit A S)
    (show DerivedCategory.TStructure.t.plus (Etale.ordinaryFiniteUnit A S)
      from ⟨0, inferInstance⟩)).2 (c.inv ≫ f)
  have hfa : c.hom ≫ (comparison A S).map a = f := by
    change (comparison A S).map a = c.inv ≫ f at ha
    rw [ha, ← Category.assoc, c.hom_inv_id, Category.id_comp]
  have hnorm := (normalization_comparison l E n S r hA d F hS a).1
    (by rwa [hfa])
  have hag : a = g := ordinary_integration_unique S d F N hN A hA hSN a hnorm
  rw [← hfa, hag]

/-- The unique glued morphism with the specified local integration formulas.
Source: blueprint vector-bundle integration
(blueprint: def-pur-proetale-vector-integration). -/
@[irreducible]
def vectorIntegration (hS : IsUnit (l : Γ(S, ⊤))) :
    vectorSource l E n S r hA d F ⟶ unit (Scheme.finiteTateCoefficient l E n) S :=
  (existsUniqueVectorIntegration l E n S r hA d F hS).exists.choose

end AlgebraicGeometry.ProEtale.VectorIntegrationSite
