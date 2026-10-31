/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Finite.General.FiniteGeneralRingData
public import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteP1Data
public import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteP1Arrows
public import WeilConjectures.AlgebraicGeometry.Ordinary.OrdinaryFiniteP1KummerSupplement
public import WeilConjectures.AlgebraicGeometry.Relative.RelativeKummerExchangeGeneratorsSupplement
public import WeilConjectures.AlgebraicGeometry.Etale.EtaleSinglePullbackComparisonsSupplement
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
public import WeilConjectures.AlgebraicGeometry.ProperProjectionFormula
public import WeilConjectures.SixFunctors.Etale.Derived.LowerStarProjection
public import WeilConjectures.CategoryTheory.Monoidal.EtaleDerivedTensorSymmetrySupplement
public import WeilConjectures.SixFunctors.Etale.Derived.ProjectionFormula
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.Topology.Defs.Filter
public import WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact
public import WeilConjectures.SixFunctors.Etale.Derived.Tensor
public import WeilConjectures.AlgebraicGeometry.ExactUnboundedExchange
public import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStar
public import WeilConjectures.SixFunctors.BaseChange.Square
public import WeilConjectures.SixFunctors.Etale.Derived.Shift
public import WeilConjectures.SixFunctors.Etale.Derived.ReductionConservative
import WeilConjectures.AlgebraicGeometry.Finite.General.FiniteGeneralRingLocalTraceAffineLine
import WeilConjectures.AlgebraicGeometry.Finite.General.FiniteGeneralRingLocalTraceAffineSuccessor

/-! # Ordered affine counit Kummer transition

Source: general-ring smooth purity, proof (3), exponent independence.
(blueprint: lem-sp-general-ring-integration-exponent-local-trace-affine-helper).

The coefficient transition conjugates the pullback of the recursively defined finite-ring
level power by the canonical affine coefficient descents at the two exponents; the theorem
below is the ordered affine-tower calculation after the frame prefix. -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry
open AlgebraicGeometry.Scheme
namespace AlgebraicGeometry.ProEtale

/-- The affine coefficient transition from exponent M to exponent N.

Source: general-ring smooth purity, proof (3), exponent independence; the canonical
affine coefficient descent of the linear trace lemma
(blueprint: def-amb-affine-linear-trace-action).

Construction: the canonical affine coefficient descent at M, the pullback along the
projection of the finite-ring level power `finiteGeneralRingLevelPower` of `b`, and
the inverse canonical affine coefficient descent at N. -/
def finiteGeneralRingAffineTransition
    (A : Type (u + 1)) [CommRing A] [Finite A]
    (M N : ℕ) (hM : (M : A) = 0) (hN : (N : A) = 0)
    (S : Scheme.{u}) [IsNoetherian S]
    (hS : IsUnit (M : Γ(S, ⊤))) (hS' : IsUnit (N : Γ(S, ⊤)))
    (b : Scheme.finiteEtaleTateLine S M A hM ≅
      Scheme.finiteEtaleTateLine S N A hN)
    (tM : Etale.OrdinaryFiniteTwistTransport A M hM)
    (tN : Etale.OrdinaryFiniteTwistTransport A N hN)
    (d : ℕ) :
    (Etale.affineTraceRight A M hM S d).obj
        (Etale.ordinaryFiniteUnit A S) ⟶
      (Etale.affineTraceRight A N hN S d).obj
        (Etale.ordinaryFiniteUnit A S) := by
  /- Source: the canonical affine coefficient descent on both exponents, with the
     finite-ring level power inserted between the two descent isomorphisms. -/
  simpa only [Etale.FiniteSmoothPurity.line] using
    ((Etale.affineLinearCoefficientDescent A M hM tM S hS d).hom ≫
      (Etale.ordinaryFinitePullback A (affineTraceProjection S d)).map
        (finiteGeneralRingLevelPower A M N hM hN S b d).hom ≫
      (Etale.affineLinearCoefficientDescent A N hN tN S hS' d).inv)

/-- The dimension-zero affine counit calculation. -/
private theorem finiteGeneralRingLocalTraceExponent_affine_zero
    (A : Type (u + 1)) [CommRing A] [Finite A]
    (M N : ℕ) (hM : (M : A) = 0) (hN : (N : A) = 0)
    (T : Scheme.{u}) [IsNoetherian T]
    (hMunit : IsUnit (M : Γ(T, ⊤))) (hNunit : IsUnit (N : Γ(T, ⊤)))
    (b : Scheme.finiteEtaleTateLine T M A hM ≅
      Scheme.finiteEtaleTateLine T N A hN)
    (tN : Etale.OrdinaryFiniteTwistTransport A N hN)
    (DN : ∀ (T : Scheme.{u}) [IsNoetherian T] (hT : IsUnit (N : Γ(T, ⊤))),
      Etale.OrdinaryFiniteP1Datum A N hN tN T hT)
    (tM : Etale.OrdinaryFiniteTwistTransport A M hM)
    (DM : ∀ (T : Scheme.{u}) [IsNoetherian T] (hT : IsUnit (M : Γ(T, ⊤))),
      Etale.OrdinaryFiniteP1Datum A M hM tM T hT) :
    (Etale.affineTraceLeft A T 0).map
        (finiteGeneralRingAffineTransition A M N hM hN T hMunit hNunit b tM tN 0) ≫
      Etale.affineTraceCounit A N hN tN DN T hNunit 0 =
      Etale.affineTraceCounit A M hM tM DM T hMunit 0 := by
  have hc (J : ℕ) (hJ : (J : A) = 0)
      (t : Etale.OrdinaryFiniteTwistTransport A J hJ)
      (D : ∀ (S : Scheme.{u}) [IsNoetherian S] (hS : IsUnit (J : Γ(S, ⊤))),
        Etale.OrdinaryFiniteP1Datum A J hJ t S hS)
      (hT : IsUnit (J : Γ(T, ⊤))) :
      Etale.affineTraceCounit A J hJ t D T hT 0 = 𝟙 _ := by
    unfold Etale.affineTraceCounit Etale.affineTraceAdjunction
    rfl
  rw [hc N hN tN DN hNunit, hc M hM tM DM hMunit]
  dsimp only [finiteGeneralRingAffineTransition, Etale.affineLinearCoefficientDescent,
    finiteGeneralRingLevelPower, Nat.rec_zero, Etale.affineTraceLeft,
    Etale.affineTraceLeftTower, Functor.id_map, Iso.refl_hom, Iso.symm_hom, Iso.symm_inv]
  change
    (((Etale.affineLinearPullbackId A T).app (Etale.ordinaryFiniteUnit A T)).inv ≫
      (Etale.ordinaryFinitePullback A (𝟙 T)).map (𝟙 (Etale.ordinaryFiniteUnit A T)) ≫
      ((Etale.affineLinearPullbackId A T).app (Etale.ordinaryFiniteUnit A T)).hom) ≫
        𝟙 _ = 𝟙 _
  simp

/-- The Kummer comparison transports the ordered affine counit.

Source: general-ring smooth purity, proof (3), exponent independence.
(blueprint: lem-sp-general-ring-integration-exponent-local-trace-affine-helper).

Proof: induction on `d`. For `d = 0` both counits are identities and both descents are
the same identity comparison, so the transition is the identity. For the successor,
the counit of the composite adjunction is the one-coordinate counit followed by the
counit in dimension `d` (`affineTraceAdjunctionTower_counit_succ`); the coefficient
descent step and `finiteGeneralRingLevelPower` at `d + 1` both tensor with one more
shifted Tate line, so the transition at `d + 1` is the transition at `d` tensored with
`b`. The one-coordinate counit is the projective-line trace normalized by `DM`, resp.
`DN`, through the Kummer class; the two clauses of `FiniteGeneralRingKummerComparison`
say that `b` carries the Kummer generator at M to that at N, so `b` intertwines the
two one-coordinate counits. Naturality of the counit then closes the induction. -/
theorem finiteGeneralRingLocalTraceExponent_affine
    (A : Type (u + 1)) [CommRing A] [Finite A]
    (M N : ℕ) (hMpos : 0 < M) (hNpos : 0 < N)
    (hM : (M : A) = 0) (hN : (N : A) = 0)
    (T : Scheme.{u}) [IsNoetherian T]
    (hMunit : IsUnit (M : Γ(T, ⊤))) (hNunit : IsUnit (N : Γ(T, ⊤)))
    (q : T.rootsOfUnitySheaf M ⟶ T.rootsOfUnitySheaf N)
    (b : Scheme.finiteEtaleTateLine T M A hM ≅
      Scheme.finiteEtaleTateLine T N A hN)
    (hb : FiniteGeneralRingKummerComparison A M N hM hN T q b)
    (tN : Etale.OrdinaryFiniteTwistTransport A N hN)
    (DN : ∀ (T : Scheme.{u}) [IsNoetherian T] (hT : IsUnit (N : Γ(T, ⊤))),
      Etale.OrdinaryFiniteP1Datum A N hN tN T hT)
    (tM : Etale.OrdinaryFiniteTwistTransport A M hM)
    (DM : ∀ (T : Scheme.{u}) [IsNoetherian T] (hT : IsUnit (M : Γ(T, ⊤))),
      Etale.OrdinaryFiniteP1Datum A M hM tM T hT)
    (d : ℕ) :
    (Etale.affineTraceLeft A T d).map
        (finiteGeneralRingAffineTransition A M N hM hN T hMunit hNunit b tM tN d) ≫
      Etale.affineTraceCounit A N hN tN DN T hNunit d =
      Etale.affineTraceCounit A M hM tM DM T hMunit d := by
  induction d with
  | zero =>
    exact finiteGeneralRingLocalTraceExponent_affine_zero A M N hM hN T hMunit hNunit
      b tN DN tM DM
  | succ d ih =>
    have hline := finiteGeneralRingLocalTraceExponent_affine_line A M N hMpos hNpos
      hM hN T hMunit hNunit q b hb tN DN tM DM
      (finiteGeneralRingAffineTransition A M N hM hN T hMunit hNunit b tM tN 1)
      (by
        simp only [finiteGeneralRingAffineTransition, Etale.FiniteSmoothPurity.line])
    exact finiteGeneralRingLocalTraceExponent_affine_successor A M N hMpos hNpos hM hN
      T hMunit hNunit q b hb tN DN tM DM d
      (finiteGeneralRingAffineTransition A M N hM hN T hMunit hNunit b tM tN d)
      (by
        simp only [finiteGeneralRingAffineTransition, Etale.FiniteSmoothPurity.line])
      (finiteGeneralRingAffineTransition A M N hM hN T hMunit hNunit b tM tN (d + 1))
      (by
        simp only [finiteGeneralRingAffineTransition, Etale.FiniteSmoothPurity.line])
      (finiteGeneralRingAffineTransition A M N hM hN T hMunit hNunit b tM tN 1)
      (by
        simp only [finiteGeneralRingAffineTransition, Etale.FiniteSmoothPurity.line])
      ih hline

end AlgebraicGeometry.ProEtale
