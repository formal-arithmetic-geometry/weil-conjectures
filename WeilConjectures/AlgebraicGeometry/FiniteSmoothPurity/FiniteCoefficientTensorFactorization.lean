/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.FiniteSmoothPurity.FiniteSmoothCoefficientArrows
public import WeilConjectures.AlgebraicGeometry.VectorTraceScalar.VectorTraceScalarDescent
public import WeilConjectures.AlgebraicGeometry.Finite.General.FiniteGeneralRingData
import all WeilConjectures.AlgebraicGeometry.Etale.ProEtale.EtaleProEtaleScalarMate
import all WeilConjectures.AlgebraicGeometry.OrdinaryFiniteTwistTransportUniqueness
import all WeilConjectures.AlgebraicGeometry.OrdinaryFiniteP1Arrows
import all WeilConjectures.AlgebraicGeometry.Ordinary.OrdinaryFiniteP1KummerSupplement
import all WeilConjectures.AlgebraicGeometry.Relative.RelativeKummerExchangeGeneratorsSupplement
import all WeilConjectures.AlgebraicGeometry.Etale.EtaleSinglePullbackComparisonsSupplement
import all WeilConjectures.AlgebraicGeometry.EtaleFiniteTwistPullback
import all Mathlib.AlgebraicGeometry.Sites.Etale
import all Mathlib.AlgebraicGeometry.Scheme
import all WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
import all WeilConjectures.AlgebraicGeometry.FiniteEtaleTateSheaf
import all WeilConjectures.AlgebraicGeometry.FiniteEtaleTateTwist
import all WeilConjectures.AlgebraicGeometry.Sites.Kummer
import all Mathlib.Algebra.Module.ZMod
import all Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
import all Mathlib.CategoryTheory.Sites.Monoidal
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import all WeilConjectures.AlgebraicGeometry.EtaleConstantRingModuleEquivalence
import all WeilConjectures.CategoryTheory.RingedSiteModules
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHom
import all WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.TensorColimits
import all WeilConjectures.AlgebraicGeometry.EtaleSheaves
import all WeilConjectures.AlgebraicGeometry.DerivedCategories
import all WeilConjectures.AlgebraicGeometry.RingedTopoiDerivedPullback
import all WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Flat
import all WeilConjectures.CategoryTheory.AlgebraicInverseImage
import all Mathlib.Algebra.Category.ModuleCat.Sheaf
import all Mathlib.Algebra.Category.Ring.Limits
import all Mathlib.Algebra.Category.Grp.Limits
import all Mathlib.CategoryTheory.Sites.Whiskering
import all Mathlib.CategoryTheory.Sites.Equivalence
import all Mathlib.Algebra.Homology.DerivedCategory.Basic
import all Mathlib.CategoryTheory.Functor.Derived.LeftDerived
import all WeilConjectures.Algebra.Homology.KFlatResolution
import all WeilConjectures.Algebra.Homology.ChangeOfRingsKFlatQuasiIso
import all WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
import all WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import all Mathlib.Algebra.Category.Grp.FilteredColimits
import all Mathlib.Algebra.Homology.BifunctorShift
import all Mathlib.Algebra.Homology.QuasiIso
import all Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import all Mathlib.CategoryTheory.Limits.EssentiallySmall
import all WeilConjectures.AlgebraicGeometry.KFlatRingedToposPullback
import all WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import all WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import all Mathlib.CategoryTheory.Limits.ExactFunctor
import all WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import all Mathlib.Algebra.Homology.HomologicalComplex
import all Mathlib.Algebra.Homology.Additive
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.RingedToposFlatPullback
import all WeilConjectures.CategoryTheory.AlgebraicInverseImageOfUniverses
import all Mathlib.CategoryTheory.Types.Basic
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatAlgebraicInverseImageOfUniverses
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatEquationalCriterionOfUniverses
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatLocalRelationsOfUniverses
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
import all WeilConjectures.CategoryTheory.Sites.WeakSheafifyAddCommGrpLeftExact
import all Mathlib.Algebra.Category.ModuleCat.Presheaf.Submodule
import all Mathlib.LinearAlgebra.TensorProduct.Vanishing
import all Mathlib.RingTheory.TensorProduct.DirectLimitFG
import all Mathlib.LinearAlgebra.TensorProduct.Finiteness
import all Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import all Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
import all WeilConjectures.CategoryTheory.Sites.InverseImageLocalFamilies
import all Mathlib.CategoryTheory.Sites.Sheaf
import all Mathlib.CategoryTheory.Sites.LocallyBijective
import all Mathlib.CategoryTheory.Sites.Limits
import all Mathlib.CategoryTheory.Adjunction.Limits
import all Mathlib.CategoryTheory.Limits.Types.Pullbacks
import all Mathlib.CategoryTheory.Functor.EpiMono
import all Mathlib.CategoryTheory.Limits.Types.Equalizers
import all Mathlib.CategoryTheory.Limits.Preserves.Shapes.Equalizers
import all Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.ScalarTensorComparisonOfUniverses
import all Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
import all Mathlib.Algebra.Homology.HomotopyCategory.MappingCone
import all Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import all WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
import all WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import all WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
import all Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import all Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import all WeilConjectures.Algebra.Homology.RingedToposAdaptedFlatResolution
import all WeilConjectures.Algebra.Homology.RingedToposPullbackFilteredColimits
import all WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import all Mathlib.CategoryTheory.Sites.PreservesSheafification
import all Mathlib.CategoryTheory.Limits.Preserves.Limits
import all WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import all Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import all Mathlib.RingTheory.Flat.CategoryTheory
import all Mathlib.CategoryTheory.ObjectProperty.ColimitsOfShape
import all Mathlib.Algebra.Homology.Embedding.CochainComplex
import all Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import all Mathlib.Algebra.Category.Grp.AB
import all WeilConjectures.Algebra.Homology.RingedToposAcyclicKFlatPullback
import all WeilConjectures.Algebra.Homology.BoundedFlatIndependentCoefficients
import all Mathlib.CategoryTheory.Monoidal.Preadditive
import all WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import all Mathlib.CategoryTheory.Monoidal.Closed.Basic
import all WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import all Mathlib.CategoryTheory.Sites.EpiMono
import all Mathlib.CategoryTheory.Adjunction.Additive
import all Mathlib.Algebra.Category.Grp.EpiMono
import all Mathlib.Algebra.Category.Grp.Abelian
import all Mathlib.CategoryTheory.Sites.Abelian
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.MonoidalClosed
import all WeilConjectures.Algebra.Homology.Site.SiteDerivedTensorDescent
import all WeilConjectures.SixFunctors.Etale.UpperLowerStar.Coherence
import all WeilConjectures.SixFunctors.Etale.UpperLowerStar.Monoidal
import all WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal
import all WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal.TensorShiftIso
import all WeilConjectures.SixFunctors.Etale.UpperLowerStar.FlatModuleCat
import all WeilConjectures.AlgebraicGeometry.EtaleFiniteTwistPullbackBase
import all WeilConjectures.ConstructibleSheaf.Defs
import all WeilConjectures.EtaleCohomology.TateTwist.Sheaf
import all WeilConjectures.AlgebraicGeometry.FiniteEtaleTateLinePullback
import all WeilConjectures.EtaleCohomology.TateTwist.RootsOfUnityPullback
import all WeilConjectures.AlgebraicGeometry.FiniteEtaleTateTensorFamily
import all WeilConjectures.CategoryTheory.NormalizedSignedTensorPowers
import all WeilConjectures.CategoryTheory.Monoidal.IntTensorFamily
import all WeilConjectures.CategoryTheory.IntTensorFamilyIso
import all Mathlib.CategoryTheory.Monoidal.Braided.Basic
import all WeilConjectures.AlgebraicGeometry.FiniteEtaleTateLocalLine
import all WeilConjectures.AlgebraicGeometry.Sites.SmallEtaleRepresentablePresheafSheaf
import all WeilConjectures.ConstructibleSheaf.Pullback
import all WeilConjectures.SixFunctors.Etale.UpperLowerStar.LocallyTrivialInverse
import all WeilConjectures.SixFunctors.Etale.UpperLowerStar.Surjective
import all WeilConjectures.SixFunctors.Etale.UpperLowerStar.MonoidalComp
import all WeilConjectures.SixFunctors.Etale.Derived.ProjectionFormula.Unit
import all WeilConjectures.AlgebraicGeometry.EtaleFiniteTwistPullbackRest
import all Mathlib.CategoryTheory.Abelian.Refinements
import all Mathlib.Algebra.Homology.ShortComplex.Exact
import all WeilConjectures.AlgebraicGeometry.ProperProjectionFormula
import all WeilConjectures.SixFunctors.Etale.Derived.LowerStarProjection
import all WeilConjectures.CategoryTheory.Monoidal.EtaleDerivedTensorSymmetrySupplement
import all WeilConjectures.SixFunctors.Etale.Derived.ProjectionFormula
import all Mathlib.AlgebraicGeometry.Morphisms.Proper
import all Mathlib.AlgebraicGeometry.Noetherian
import all Mathlib.Topology.Defs.Filter
import all WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact
import all WeilConjectures.SixFunctors.Etale.Derived.Tensor
import all WeilConjectures.AlgebraicGeometry.ExactUnboundedExchange
import all WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStar
import all WeilConjectures.SixFunctors.BaseChange.Square
import all WeilConjectures.SixFunctors.Etale.Derived.Shift
import all WeilConjectures.SixFunctors.Etale.Derived.ReductionConservative
import all Mathlib.CategoryTheory.Adjunction.Whiskering
public import WeilConjectures.SmoothPurity.OrdinaryFiniteTwistTransportUniqueness

/-! # Factorization of normalized scalar and exponent comparisons

Source: blueprint/latest, sec-smooth-purity/sk-prop-an,
cor-pur-vector-bundle-purity.proof.md, paragraph 2.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme
namespace AlgebraicGeometry.Etale.FiniteSmoothPurity
set_option linter.auxLemma false in
attribute [local instance 100000] DerivedCategoryModule._proof_1 DerivedCategoryModule._proof_2
set_option linter.auxLemma false in
attribute [local instance 100000]
  ordinaryFinitePullback._proof_1 ordinaryFinitePullback._proof_2
  ordinaryFinitePullback._proof_3 ordinaryFinitePullback._proof_4
  ordinaryFinitePullback._proof_5 ordinaryFinitePullback._proof_6
  ordinaryFinitePullback._proof_7 ordinaryFinitePullback._proof_8
  ordinaryFinitePullback._proof_9 ordinaryFinitePullback._proof_10
  ordinaryFinitePullback._proof_11 ordinaryFinitePullback._proof_12
  ordinaryFinitePullback._proof_13
attribute [local implicit_reducible] ordinaryFiniteSingleFunctor
attribute [local irreducible] HasDerivedCategory.ofIsGrothendieckAbelian
  HasDerivedCategory.ofHasKInjectiveResolutions
attribute [local instance] cachedEtaleGroth cachedEtaleSheafify
  cachedEtaleMonoidalPreadditive cachedEtaleCoproducts cachedEtaleColimits
  cachedEtaleFlatResolution cachedEtaleInjectiveResolution
  cachedEtaleExactColimits cachedEtaleTensor4 cachedEtaleTensor12
  cachedEtaleTensor23 cachedEtaleTensorColimits cachedEtaleTensorFlipColimits

open WeilConjectures.PurityFiniteSetting
open CategoryTheory.MonoidalCategory
attribute [local irreducible] Functor.leftAdjoint Functor.rightAdjoint
  Functor.leftDerivedFunctor Functor.rightDerivedFunctor Functor.mapDerivedCategory
  ProEtale.pbcFixedScalarExtension derivedTensor upperStar lowerStar

attribute [-instance] CategoryTheory.catToReflQuiver in

private theorem sheaf_factor
    {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) (N M : ℕ) (hN : 0 < N)
    (hA : (N : A) = 0) (hBN : (N : B) = 0) (hB : (M : B) = 0)
    (T : Scheme.{u}) (hT : IsUnit (N : Γ(T, ⊤)))
    (t : CoefficientLineComparison φ N M hA hB T)
    (q : T.rootsOfUnitySheaf N ⟶ T.rootsOfUnitySheaf M)
    (b : Scheme.finiteEtaleTateLine T N B hBN ≅ Scheme.finiteEtaleTateLine T M B hB)
    (hb : ProEtale.FiniteGeneralRingKummerComparison B N M hBN hB T q b) :
    t.sheafIso.hom = (VectorTraceScalar.balancing φ N hN hA hBN T hT 1).hom ≫ b.hom := by
  have hroot : t.roots = q := by
    apply (cancel_mono (kernel.ι (M • 𝟙 T.gmSheaf))).1
    exact t.roots_power.trans hb.1.symm
  have norm := finite_tate_scalar_source_normalization φ N hN hA hBN T
    (fun x ↦ by simpa only [map_natCast] using hT.map (T.presheaf.germ ⊤ x trivial).hom)
  have hn := (Classical.choose_spec norm.2.exists).1.1 1
  have hs (W : T.Etaleᵒᵖ) (a : A) (z : (T.rootsOfUnitySheaf N).obj.obj W) :
      ((ProEtale.etaleSheafExtendScalarsAdjunction φ T).homEquiv _ _
        (VectorTraceScalar.balancing φ N hN hA hBN T hT 1).hom).hom.app W
          (Scheme.finiteEtaleTateOneGenerator A N T hA W a z) =
        Scheme.finiteEtaleTateOneGenerator B N T hBN W (φ a) z := by
    have hg := hn W a 1 (fun _ ↦ z)
    simp only [one_smul, mul_one, Scheme.finiteTateEtalePowerGenerator] at hg
    rw [Adjunction.homEquiv_unit]
    unfold VectorTraceScalar.balancing
    exact hg
  apply ((ProEtale.etaleSheafExtendScalarsAdjunction φ T).homEquiv _ _).injective
  rw [Adjunction.homEquiv_naturality_right]
  apply (Scheme.lineHomEquiv T N A hA _).injective
  ext W z
  simp only [Scheme.lineHomEquiv_generator]
  rw [t.generators, hroot]
  change _ = b.hom.hom.app W
    (((ProEtale.etaleSheafExtendScalarsAdjunction φ T).homEquiv _ _
      (VectorTraceScalar.balancing φ N hN hA hBN T hT 1).hom).hom.app W
        (Scheme.finiteEtaleTateOneGenerator A N T hA W 1 z))
  rw [hs, hb.2]

private theorem tensor_comp
    {C : Type*} [Category C] (T : C ⥤ C ⥤ C)
    {X Y Z U V W : C} (a : X ⟶ Y) (b : Y ⟶ Z) (c : U ⟶ V) (d : V ⟶ W) :
    (T.map (a ≫ b)).app U ≫ (T.obj Z).map (c ≫ d) =
      (T.map a).app U ≫ (T.obj Y).map c ≫ (T.map b).app V ≫ (T.obj Z).map d := by
  simp only [T.map_comp, NatTrans.comp_app, Functor.map_comp, Category.assoc]
  rw [← reassoc_of% (T.map b).naturality c]

private theorem tensor_step
    {C : Type*} [Category C] (T : C ⥤ C ⥤ C)
    {P X Y Z U V W : C} (θ : P ⟶ (T.obj X).obj U)
    (a : X ⟶ Y) (b : Y ⟶ Z) (c : U ⟶ V) (d : V ⟶ W)
    (h : X ⟶ Z) (k : U ⟶ W) (hh : h = a ≫ b) (hk : k = c ≫ d) :
    θ ≫ (T.map h).app U ≫ (T.obj Z).map k =
      (θ ≫ (T.map a).app U ≫ (T.obj Y).map c) ≫
        (T.map b).app V ≫ (T.obj Z).map d := by
  rw [hh, hk, tensor_comp]
  simp only [Category.assoc]

private theorem shifted_line_factor
    {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) (N M : ℕ) (hN : 0 < N)
    (hA : (N : A) = 0) (hBN : (N : B) = 0) (hB : (M : B) = 0)
    (T : Scheme.{u}) (hT : IsUnit (N : Γ(T, ⊤)))
    (t : CoefficientLineComparison φ N M hA hB T)
    (q : T.rootsOfUnitySheaf N ⟶ T.rootsOfUnitySheaf M)
    (b : Scheme.finiteEtaleTateLine T N B hBN ≅ Scheme.finiteEtaleTateLine T M B hB)
    (hb : ProEtale.FiniteGeneralRingKummerComparison B N M hBN hB T q b) :
    (scalarShiftIso φ T (2 : ℤ)).hom.app _ ≫
      (shiftFunctor _ (2 : ℤ)).map t.derivedIso.hom =
    VectorTraceScalar.line φ N hN hA hBN T hT ≫
      (shiftFunctor _ (2 : ℤ)).map ((DerivedCategory.singleFunctor _ 0).map b.hom) := by
  rw [t.derived_normalization, sheaf_factor φ N M hN hA hBN hB T hT t q b hb]
  change _ =
    ((scalarShiftIso φ T (2 : ℤ)).hom.app (ordinaryFiniteLine A N hA T) ≫
      (shiftFunctor _ (2 : ℤ)).map
        (scalarSingleMap φ T (Scheme.finiteEtaleTateLine T N A hA) ≫
          (DerivedCategory.singleFunctor _ 0).map
            (VectorTraceScalar.balancing φ N hN hA hBN T hT 1).hom)) ≫ _
  simp only [Functor.map_comp, Category.assoc]

private theorem zero_factor
    {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) (N M : ℕ) (hA : (N : A) = 0) (hB : (M : B) = 0)
    (T : Scheme.{u}) :
    (scalarZeroLineIso φ N M hA hB T).hom = VectorTraceScalar.unit φ T := by
  rfl

/-- The normalized coefficient comparison factors through scalar extension at N
and the given exponent change inside B, in the ordered shifted tensor presentation.
Source: blueprint/latest, sec-smooth-purity/sk-lem-sp-reduction/
sk-lem-sp-reduction-compatibilities.proof.md (3), Orientation; vector-bundle purity,
cor-pur-vector-bundle-purity.proof.md paragraph 2.
(blueprint: lem-sp-finite-coefficient-tensor-factorization).

Proof: the root-kernel inclusion is monic, so t.roots equals q. The generator
normalizations of t, the unique scalar balancing, and b agree. Injectivity of
the scalar-adjunction Hom equivalence and of the root-line universal property
therefore identifies the sheaf map with balancing followed by b. Apply the
specified derived normalization and then the shift functor. Induct on the number
of ordered shifted factors. The zero case is the same transported scalar unit;
the successor uses functoriality in both tensor arguments and the naturality of
the tensor bifunctor to separate the scalar and exponent maps. No factor is
permuted. The calculation includes zero rings, empty bases and rank zero and
requires no flatness. -/
theorem finiteCoefficientTensor_factor
    {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) (N M : ℕ) (hN : 0 < N)
    (hA : (N : A) = 0) (hBN : (N : B) = 0) (hB : (M : B) = 0)
    (T : Scheme.{u}) (hT : IsUnit (N : Γ(T, ⊤)))
    (t : CoefficientLineComparison φ N M hA hB T)
    (q : T.rootsOfUnitySheaf N ⟶ T.rootsOfUnitySheaf M)
    (b : Scheme.finiteEtaleTateLine T N B hBN ≅ Scheme.finiteEtaleTateLine T M B hB)
    (hb : ProEtale.FiniteGeneralRingKummerComparison B N M hBN hB T q b) (d : ℕ) :
    (t.tensorPower d).hom = VectorTraceScalar.base φ N hN hA hBN T hT d ≫
      (ProEtale.finiteGeneralRingLevelPower B N M hBN hB T b d).hom := by
  have hline := shifted_line_factor φ N M hN hA hBN hB T hT t q b hb
  induction d with
  | zero =>
    change (scalarZeroLineIso φ N M hA hB T).hom = VectorTraceScalar.unit φ T ≫ 𝟙 _
    exact (zero_factor φ N M hA hB T).trans (Category.comp_id _).symm
  | succ d ih =>
    exact tensor_step (ordinaryFiniteTensor B T)
      ((ExceptionalCoefficients.tensorIso φ T).hom.app
        (line A N hA T d, (ordinaryFiniteLine A N hA T)⟦(2 : ℤ)⟧))
      (VectorTraceScalar.base φ N hN hA hBN T hT d)
      (ProEtale.finiteGeneralRingLevelPower B N M hBN hB T b d).hom
      (VectorTraceScalar.line φ N hN hA hBN T hT)
      ((shiftFunctor _ (2 : ℤ)).map ((DerivedCategory.singleFunctor _ 0).map b.hom))
      (t.tensorPower d).hom
      ((scalarShiftIso φ T (2 : ℤ)).hom.app _ ≫
        (shiftFunctor _ (2 : ℤ)).map t.derivedIso.hom) ih hline

end AlgebraicGeometry.Etale.FiniteSmoothPurity
