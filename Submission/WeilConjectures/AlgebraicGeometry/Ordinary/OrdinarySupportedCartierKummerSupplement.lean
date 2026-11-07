/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Submission.WeilConjectures.AlgebraicGeometry.Ordinary.OrdinarySupportedKummerSystemSupplement
import Submission.WeilConjectures.AlgebraicGeometry.SupportedCartierBoundaryExistence
import Submission.WeilConjectures.AlgebraicGeometry.Ordinary.OrdinarySupportedKummerSystemSupplement
import Submission.WeilConjectures.AlgebraicGeometry.Cartier.CartierReductionDataSupplement
import Submission.WeilConjectures.AlgebraicGeometry.SupportedDerivedUnitForget
import Submission.WeilConjectures.ConstructibleSheaf.FinitePushforward.ConstantUnit
import Submission.WeilConjectures.CategoryTheory.DerivedSingleUnitExact
import Submission.WeilConjectures.CategoryTheory.DerivedSingleUnit
import Submission.WeilConjectures.CategoryTheory.DerivedCategory.Adjunction
import Submission.WeilConjectures.AlgebraicGeometry.SupportedKummerChernRealization
import Submission.WeilConjectures.AlgebraicGeometry.Ordinary.OrdinarySupportedKummerBoundarySupplement
import Submission.WeilConjectures.CategoryTheory.Sites.Torsor
import Submission.WeilConjectures.AlgebraicGeometry.Sites.GmPicard
import Submission.WeilConjectures.AlgebraicGeometry.Supported.SupportedKummerBoundaryPullback
import Submission.WeilConjectures.AlgebraicGeometry.Supported.SupportedKummerBoundaryScalar
import Submission.WeilConjectures.AlgebraicGeometry.EtaleFiniteTwistPullback
import Mathlib.AlgebraicGeometry.Sites.Etale
import Mathlib.AlgebraicGeometry.Scheme
import Submission.WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
import Submission.WeilConjectures.AlgebraicGeometry.FiniteEtaleTateSheaf
import Submission.WeilConjectures.AlgebraicGeometry.FiniteEtaleTateTwist
import Submission.WeilConjectures.AlgebraicGeometry.Sites.Kummer
import Mathlib.Algebra.Module.ZMod
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
import Mathlib.CategoryTheory.Sites.Monoidal
import Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import Submission.WeilConjectures.AlgebraicGeometry.EtaleConstantRingModuleEquivalence
import Submission.WeilConjectures.CategoryTheory.RingedSiteModules
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHom
import Submission.WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.TensorColimits
import Submission.WeilConjectures.AlgebraicGeometry.EtaleSheaves
import Submission.WeilConjectures.AlgebraicGeometry.DerivedCategories
import Submission.WeilConjectures.AlgebraicGeometry.RingedTopoiDerivedPullback
import Submission.WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Flat
import Submission.WeilConjectures.CategoryTheory.AlgebraicInverseImage
import Mathlib.Algebra.Category.ModuleCat.Sheaf
import Mathlib.Algebra.Category.Ring.Limits
import Mathlib.Algebra.Category.Grp.Limits
import Mathlib.CategoryTheory.Sites.Whiskering
import Mathlib.CategoryTheory.Sites.Equivalence
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Mathlib.CategoryTheory.Functor.Derived.LeftDerived
import Submission.WeilConjectures.Algebra.Homology.KFlatResolution
import Submission.WeilConjectures.Algebra.Homology.ChangeOfRingsKFlatQuasiIso
import Submission.WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
import Submission.WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Homology.BifunctorShift
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import Mathlib.CategoryTheory.Limits.EssentiallySmall
import Submission.WeilConjectures.AlgebraicGeometry.KFlatRingedToposPullback
import Submission.WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import Submission.WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
import Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import Mathlib.CategoryTheory.Limits.ExactFunctor
import Submission.WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import Mathlib.Algebra.Homology.HomologicalComplex
import Mathlib.Algebra.Homology.Additive
import Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.RingedToposFlatPullback
import Submission.WeilConjectures.CategoryTheory.AlgebraicInverseImageOfUniverses
import Mathlib.CategoryTheory.Types.Basic
import Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatAlgebraicInverseImageOfUniverses
import Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatEquationalCriterionOfUniverses
import Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatLocalRelationsOfUniverses
import Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
import Submission.WeilConjectures.CategoryTheory.Sites.WeakSheafifyAddCommGrpLeftExact
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Submodule
import Mathlib.LinearAlgebra.TensorProduct.Vanishing
import Mathlib.RingTheory.TensorProduct.DirectLimitFG
import Mathlib.LinearAlgebra.TensorProduct.Finiteness
import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
import Submission.WeilConjectures.CategoryTheory.Sites.InverseImageLocalFamilies
import Mathlib.CategoryTheory.Sites.Sheaf
import Mathlib.CategoryTheory.Sites.LocallyBijective
import Mathlib.CategoryTheory.Sites.Limits
import Mathlib.CategoryTheory.Adjunction.Limits
import Mathlib.CategoryTheory.Limits.Types.Pullbacks
import Mathlib.CategoryTheory.Functor.EpiMono
import Mathlib.CategoryTheory.Limits.Types.Equalizers
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Equalizers
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
import Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.ScalarTensorComparisonOfUniverses
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
import Mathlib.Algebra.Homology.HomotopyCategory.MappingCone
import Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import Submission.WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
import Submission.WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import Submission.WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import Submission.WeilConjectures.Algebra.Homology.RingedToposAdaptedFlatResolution
import Submission.WeilConjectures.Algebra.Homology.RingedToposPullbackFilteredColimits
import Submission.WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.CategoryTheory.Sites.PreservesSheafification
import Mathlib.CategoryTheory.Limits.Preserves.Limits
import Submission.WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import Mathlib.RingTheory.Flat.CategoryTheory
import Mathlib.CategoryTheory.ObjectProperty.ColimitsOfShape
import Mathlib.Algebra.Homology.Embedding.CochainComplex
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.Algebra.Category.Grp.AB
import Submission.WeilConjectures.Algebra.Homology.RingedToposAcyclicKFlatPullback
import Submission.WeilConjectures.Algebra.Homology.BoundedFlatIndependentCoefficients
import Mathlib.CategoryTheory.Monoidal.Preadditive
import Submission.WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import Mathlib.CategoryTheory.Monoidal.Closed.Basic
import Submission.WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import Mathlib.CategoryTheory.Sites.EpiMono
import Mathlib.CategoryTheory.Adjunction.Additive
import Mathlib.Algebra.Category.Grp.EpiMono
import Mathlib.Algebra.Category.Grp.Abelian
import Mathlib.CategoryTheory.Sites.Abelian
import Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.MonoidalClosed
import Submission.WeilConjectures.Algebra.Homology.Site.SiteDerivedTensorDescent
import Submission.WeilConjectures.SixFunctors.Etale.UpperLowerStar.Coherence
import Submission.WeilConjectures.SixFunctors.Etale.UpperLowerStar.Monoidal
import Submission.WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal
import Submission.WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal.TensorShiftIso
import Submission.WeilConjectures.SixFunctors.Etale.UpperLowerStar.FlatModuleCat
import Submission.WeilConjectures.AlgebraicGeometry.EtaleFiniteTwistPullbackBase
import Submission.WeilConjectures.ConstructibleSheaf.Defs
import Submission.WeilConjectures.EtaleCohomology.TateTwist.Sheaf
import Submission.WeilConjectures.AlgebraicGeometry.FiniteEtaleTateLinePullback
import Submission.WeilConjectures.EtaleCohomology.TateTwist.RootsOfUnityPullback
import Submission.WeilConjectures.AlgebraicGeometry.FiniteEtaleTateTensorFamily
import Submission.WeilConjectures.CategoryTheory.NormalizedSignedTensorPowers
import Submission.WeilConjectures.CategoryTheory.Monoidal.IntTensorFamily
import Submission.WeilConjectures.CategoryTheory.IntTensorFamilyIso
import Mathlib.CategoryTheory.Monoidal.Braided.Basic
import Submission.WeilConjectures.AlgebraicGeometry.FiniteEtaleTateLocalLine
import Submission.WeilConjectures.AlgebraicGeometry.Sites.SmallEtaleRepresentablePresheafSheaf
import Submission.WeilConjectures.ConstructibleSheaf.Pullback
import Submission.WeilConjectures.SixFunctors.Etale.UpperLowerStar.LocallyTrivialInverse
import Submission.WeilConjectures.SixFunctors.Etale.UpperLowerStar.Surjective
import Submission.WeilConjectures.SixFunctors.Etale.UpperLowerStar.MonoidalComp
import Submission.WeilConjectures.SixFunctors.Etale.Derived.ProjectionFormula.Unit
import Submission.WeilConjectures.AlgebraicGeometry.EtaleFiniteTwistPullbackRest
import Mathlib.CategoryTheory.Abelian.Refinements
import Mathlib.Algebra.Homology.ShortComplex.Exact
import Submission.WeilConjectures.SixFunctors.Finite.BaseChange
public import Submission.WeilConjectures.AlgebraicGeometry.OrdinarySupportedCartierKummer

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

/-!
# Existence of an ordinary supported Cartier Kummer map

Source: Stacks Project, Tags 03PL and 0A45; blueprint
sec-smooth-purity/sk-prop-sf-cbc/lem-amb-cartier-kummer-map.md
(blueprint: lem-asd-ordinary-supported-kummer).
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u

open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

private theorem supportedConstantExchange_isIso
    (A : Type (u + 1)) [CommRing A] {D D' T T' : Scheme.{u}}
    (i : D ⟶ T) [IsClosedImmersion i] (i' : D' ⟶ T')
    (v : T' ⟶ T) (w : D' ⟶ D) (sq : IsPullback w i' i v) :
    IsIso (supportedConstantExchange A i i' v w sq.toCommSq) := by
  let := isIso_baseChangeMap_of_isFinite (ModuleCat.{u + 1} A) sq
  unfold supportedConstantExchange
  infer_instance

private theorem ordinaryTwistTransport_exists
    (A : Type (u + 1)) [CommRing A] (N : ℕ) (hN : 0 < N) (hA : (N : A) = 0) :
    Nonempty (OrdinaryFiniteTwistTransport A N hA) := by
  obtain ⟨r, c, p, hcover, hr, hc, _⟩ := Scheme.etaleFiniteTwistPullback A N hN hA
  let t : OrdinaryFiniteTwistTransport A N hA :=
    { roots := r
      line := fun v hT ↦ c v hT (by simpa using hT.map v.appTop.hom) 1
      roots_normalization := hr
      line_normalization := fun v hT ↦
        hc v hT (by simpa using hT.map v.appTop.hom) }
  exact ⟨t⟩

section

-- Use the same category-instance proofs as the recorded derived module category.
set_option linter.auxLemma false in
attribute [local instance 100000] DerivedCategoryModule._proof_1 DerivedCategoryModule._proof_2

/-- The supported Cartier Kummer morphism, with its defining relative boundary,
unit/Chern equation, Cartier-preserving pullback square, and derived scalar square.
The derived arrow is displayed explicitly; Ext is only its canonical degree-two
representative. The boundary determines that representative uniquely. Pullback and
scalar-extension representatives are themselves normalized by the same boundary.

Source: Stacks 03PL and 0A45; blueprint lem-amb-cartier-kummer-map
(blueprint: lem-asd-ordinary-supported-kummer).

Proof:
1. Take the unique relative-boundary representative from
   supported_cartier_boundary_existsUnique. It already contains the integral
   torsor extension and the positive Kummer normalization.
2. The normalized roots and tensor-line comparisons of etaleFiniteTwistPullback
   give an OrdinaryFiniteTwistTransport; take its degree-one line comparison.
3. Let c be supportedExactDerivedMap applied to that representative, and let c₁
   be the inverse Ext realization of supportedDerivedUnit followed by c. The
   generic exact-single adjunction comparison identifies this with Yoneda
   precomposition by the ordinary constant unit. The integral generator commutes
   with that unit. The boundary's equivariant map identifies the divisor frame
   torsor with the lifting torsor of its extension over section one. Its H¹ class
   is therefore the Picard class of the dual Cartier ideal. Composing with the
   positive Kummer extension and the root tensor map gives the Chern equation,
   as proved in supported_kummer_chern_realization. Ext.homEquiv supplies the
   derived realization equation by its inverse identity.
4. On a Cartier pullback take the uniquely normalized primed boundary. Closed
   immersions are finite, so finite sheaf base change and the constant comparison
   make supportedConstantExchange invertible. Apply the separate normalized
   boundary pullback result to obtain the required Ext square.
5. Take the uniquely normalized boundary over the lifted residue coefficient ring.
   The separate scalar compatibility result supplies its unbounded scalar-unit
   universal properties and the coefficient Ext square with the chosen class.
No flatness of the coefficient map or the Cartier-preserving base map is assumed.
-/
theorem ordinary_supported_kummer (T : Scheme.{u}) (N : ℕ) (hN : 0 < N)
    (A : Type (u + 1)) [CommRing A] [Finite A] (hA : (N : A) = 0)
    (hT : IsUnit (N : Γ(T, ⊤))) {D : Scheme.{u}} (i : D ⟶ T)
    [IsClosedImmersion i] (hI : i.ker.IsInvertible) :
    ∃ (κ : Ext
        ((lowerStar (ModuleCat.{u + 1} A) i).obj (ordinaryFiniteConstant A D))
        (Scheme.finiteEtaleTateLine T N A hA) 2)
      (c : (ordinaryFinitePushforward A i).obj (ordinaryFiniteUnit A D) ⟶
        (ordinaryFiniteLine A N hA T)⟦(2 : ℤ)⟧)
      (c₁ : Ext (ordinaryFiniteConstant A T) (Scheme.finiteEtaleTateLine T N A hA) 2)
      (t : OrdinaryFiniteTwistTransport A N hA),
      c = supportedExactDerivedMap (lowerStar (ModuleCat.{u + 1} A) i)
        (ordinaryFiniteConstant A D) (Scheme.finiteEtaleTateLine T N A hA) κ ∧
      SupportedKummerBoundary A N hA i hI hT κ ∧
      (∀ κ' : Ext
        ((lowerStar (ModuleCat.{u + 1} A) i).obj (ordinaryFiniteConstant A D))
        (Scheme.finiteEtaleTateLine T N A hA) 2,
        SupportedKummerBoundary A N hA i hI hT κ' → κ' = κ) ∧
      (Ext.mk₀ (ordinaryFiniteIntegralGenerator A T)).comp
        (c₁.mapExactFunctor (RawModuleScalarComparison.forget A T)) (zero_add 2) =
          supportedKummerChern A N hA i hI hT ∧
      supportedDerivedUnit A i ≫ c = c₁.hom ∧
      (∀ {D' T' : Scheme.{u}} (i' : D' ⟶ T') [IsClosedImmersion i']
        (v : T' ⟶ T) (w : D' ⟶ D) (sq : IsPullback w i' i v)
        (hI' : i'.ker.IsInvertible),
        ∃ κ' : Ext
          ((lowerStar (ModuleCat.{u + 1} A) i').obj (ordinaryFiniteConstant A D'))
          (Scheme.finiteEtaleTateLine T' N A hA) 2,
          SupportedKummerBoundary A N hA i' hI'
            (by simpa using hT.map v.appTop.hom) κ' ∧
          IsIso (supportedConstantExchange A i i' v w sq.toCommSq) ∧
          (Ext.mk₀ (supportedConstantExchange A i i' v w sq.toCommSq)).comp
              κ' (zero_add 2) =
            (κ.mapExactFunctor (upperStar (ModuleCat.{u + 1} A) v)).comp
              (Ext.mk₀ (t.line v hT).hom) (add_zero 2)) ∧
      (∀ [NeZero N],
        ∃ κ₀ : Ext
          ((lowerStar (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod N))) i).obj
            (ordinaryFiniteConstant (ULift.{u + 1} (ZMod N)) D))
          (Scheme.finiteEtaleTateLine T N (ULift.{u + 1} (ZMod N))
            (congrArg (ULift.up : ZMod N → ULift.{u + 1} (ZMod N))
              (ZMod.natCast_self N))) 2,
          SupportedKummerBoundary (ULift.{u + 1} (ZMod N)) N
            (congrArg (ULift.up : ZMod N → ULift.{u + 1} (ZMod N))
              (ZMod.natCast_self N)) i hI hT κ₀ ∧
          SupportedKummerScalar
            ((Scheme.finiteEtaleTwistScalar N A hA).comp ULift.ringEquiv.toRingHom) N
            (congrArg (ULift.up : ZMod N → ULift.{u + 1} (ZMod N))
              (ZMod.natCast_self N)) hA i κ₀ κ) := by
  classical
  obtain ⟨κ, hκ, huniq⟩ := supported_cartier_boundary_existsUnique T N hN A hA hT i hI
  obtain ⟨t⟩ := ordinaryTwistTransport_exists A N hN hA
  let d := supportedExactDerivedMap (lowerStar (ModuleCat.{u + 1} A) i)
    (ordinaryFiniteConstant A D) (Scheme.finiteEtaleTateLine T N A hA) κ
  let c₁ : Ext (ordinaryFiniteConstant A T) (Scheme.finiteEtaleTateLine T N A hA) 2 :=
    Ext.homEquiv.symm (supportedDerivedUnit A i ≫ d)
  refine ⟨κ, d, c₁, t, rfl, hκ, huniq, ?_, ?_, ?_, ?_⟩
  · exact (supported_derived_unit_forget A i _ κ).trans
      (supported_kummer_chern_realization T N A hA hT i hI κ hκ)
  · exact Ext.homEquiv.apply_symm_apply _ |>.symm
  · intro D' T' i' _ v w sq hI'
    obtain ⟨κ', hκ', _⟩ := supported_cartier_boundary_existsUnique T' N hN A hA
      (by simpa using hT.map v.appTop.hom) i' hI'
    exact ⟨κ', hκ', supportedConstantExchange_isIso A i i' v w sq,
      supported_kummer_boundary_pullback T N hN A hA hT i hI κ hκ
      t i' v w sq hI' κ' hκ'⟩
  · intro _
    obtain ⟨κ₀, hκ₀, _⟩ := supported_cartier_boundary_existsUnique T N hN
      (ULift.{u + 1} (ZMod N))
      (congrArg (ULift.up : ZMod N → ULift.{u + 1} (ZMod N))
        (ZMod.natCast_self N)) hT i hI
    exact ⟨κ₀, hκ₀, supported_kummer_boundary_scalar T N hN A hA hT i hI κ hκ κ₀ hκ₀⟩

end

end AlgebraicGeometry.Etale
