/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SecSmoothPurity.IntrinsicCompactSupportRestriction
public import WeilConjectures.SecSmoothPurity.ReductionDirectImage
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
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible
import WeilConjectures.SixFunctors.RingedDerivedMonoidalComparisons
import WeilConjectures.AlgebraicGeometry.ProEtaleConstantRingMap
import WeilConjectures.AlgebraicGeometry.ProEtaleRingSheafChangeAdjunctionSupplement
import WeilConjectures.AlgebraicGeometry.ProEtaleExtensionZero
import WeilConjectures.AlgebraicGeometry.ProEtaleFixedScalarRestrictionDirectImage
import WeilConjectures.CategoryTheory.RingedToposDerivedPushforwardComposition
import WeilConjectures.CategoryTheory.RingedToposMorphismSupplement
import WeilConjectures.CategoryTheory.RingedSiteModules
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
import Mathlib.CategoryTheory.Functor.Derived.RightDerived
import WeilConjectures.CategoryTheory.RingedSiteKInjectiveResolutionsSupplement
import WeilConjectures.Mathlib.Algebra.Homology.GrothendieckAbelian
import Mathlib.CategoryTheory.Localization.DerivabilityStructure.Derives
import WeilConjectures.Algebra.Homology.KFlatSupplement
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
import Mathlib.CategoryTheory.Sites.Equivalence
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
import Mathlib.CategoryTheory.Adjunction.Limits
import WeilConjectures.CategoryTheory.GeometricRingTransport
import Mathlib.CategoryTheory.Sites.Limits
import WeilConjectures.CategoryTheory.SheavesAlgebraicStructuresRingCore
import WeilConjectures.CategoryTheory.SheafRingObjectReconstruction
import WeilConjectures.CategoryTheory.Adjunction.FiniteProductRingFunctor
import WeilConjectures.CategoryTheory.ModulePullbackPushforwardAdjunctionSupplement
import WeilConjectures.AlgebraicGeometry.KFlatRingedToposPullback
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
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
import WeilConjectures.Algebra.Homology.ChangeOfRingsKFlatQuasiIsoSupplement
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
import Mathlib.CategoryTheory.Sites.EpiMono
import Mathlib.CategoryTheory.Adjunction.Additive
import Mathlib.Algebra.Category.Grp.EpiMono
import Mathlib.Algebra.Category.Grp.Abelian
import Mathlib.CategoryTheory.Sites.Abelian
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.MonoidalClosed
import WeilConjectures.AlgebraicGeometry.ProEtaleConstantRingOperations
import WeilConjectures.AlgebraicGeometry.ProEtaleIntrinsicExtensionByZero
import WeilConjectures.SecSmoothPurity.ScalarExtensionFunctor

/-!
# Scalar-adjunction transposes of mixed-coefficient compact-support maps

Source: Stacks Project, Cohomology on Sites, Tags 07A6, 0D6D and 0D6E;
blueprint det-sp-reduction-direct-image, proper-counit and open-tensor normalization
(blueprint: lem-sp-restriction-transition-transpose).

All scalar functors, geometric functors and adjunctions are the published ordinary
uncompleted constructions. The restriction comparison is repaired to use their intrinsic
constant-ring coordinates. The ambient counit equation does not assert that restriction
preserves finite Tor amplitude.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe u
open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.ProEtale

/-- Scalar transpose under the published universal-counit-normalized adjunction.
Source: Stacks Tag 07A6 (blueprint: lem-sp-restriction-transition-transpose). -/
def restrictionTransitionScalarTranspose
    {A B : Type u} [CommRing A] [CommRing B] (φ : A →+* B) (W : Scheme.{u})
    {K : proEtaleDerivedCategory W A} {L : proEtaleDerivedCategory W B}
    (t : K ⟶ (scalarRestriction φ W).obj L) :
    (scalarExtensionFunctor φ W).obj K ⟶ L :=
  ((proEtaleRingDerivedExtensionAdjunction
    (proEtaleConstantRingMap (T := W) φ)).homEquiv K L).symm t

/-- The left-hand side of the node's mixed-coefficient transpose formula, using its
specified restriction comparison, on the entire ambient category.
Source: Stacks Tags 07A6 and 0D6E
(blueprint: lem-sp-restriction-transition-transpose). -/
def restrictionTransitionMixedTranspose
    {A B : Type u} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) {X Z Y : Scheme.{u}} (j : X ⟶ Z) [IsOpenImmersion j] (h : Z ⟶ Y)
    {K : proEtaleDerivedCategory X A} {L : proEtaleDerivedCategory X B}
    (t : K ⟶ (scalarRestriction φ X).obj L) :
    (scalarExtensionFunctor φ Y).obj ((reductionCompactSupport A j h).obj K) ⟶
      (reductionCompactSupport B j h).obj L :=
  restrictionTransitionScalarTranspose φ Y
    ((reductionCompactSupport A j h).map t ≫
      (intrinsicCompactSupportRestriction φ j h).hom.app L)

/-- The input map for identity coefficients, in the canonical identity-adjunction
coordinates. This is t itself under the identity restriction identification.
Source: Stacks Tag 07A6, identity adjunction normalization
(blueprint: lem-sp-restriction-transition-transpose). -/
def restrictionTransitionIdentityInput
    {A : Type u} [CommRing A] (X : Scheme.{u})
    {K L : proEtaleDerivedCategory X A} (t : K ⟶ L) :
    K ⟶ (scalarRestriction (RingHom.id A) X).obj L :=
  (proEtaleRingDerivedExtensionAdjunction
      (proEtaleConstantRingMap (T := X) (RingHom.id A))).unit.app K ≫
    (scalarRestriction (RingHom.id A) X).map
      ((scalarExtensionFunctor_identity (A := A) X).hom.app K ≫ t)

/-- The transpose, ambient counit, naturality, coefficient composition and identity
assertions for the specified compact-support comparisons.
Source: Stacks Tags 07A6, 0D6D and 0D6E; the proper-counit/open-tensor normalization
of blueprint det-sp-reduction-direct-image
(blueprint: lem-sp-restriction-transition-transpose).

Proof (the seven steps of the DAG node):
1. By lem-pur-sheaf-ring-derived-coefficient-adjunction, the scalar transpose of v
is T(v) followed by the scalar counit. Write P_R for h_R^*, R_R for Rh_{*,R},
J_R for j_{!,R}, and D for the inverse of the normalized direct-image restriction
comparison. The proper factor gamma of b is characterized by its geometric
transpose T(e_A) after the canonical scalar/pullback comparison chi.
2. The two factorizations of (Z,B_Z) to (Y,A_Y) have left adjoints P_B T_Y and
T_Z P_A. By lem-sfb-ringed-derived-monoidal-comparisons, their composite counits
agree under chi and D. Precompose with chi and T(D), cancel D inverse with D,
and use counit naturality. The geometric transposes of epsilon_Y T(D) and
R_B(epsilon_Z) gamma agree, so the Hom bijection identifies these maps on every
ambient B-object. No Tor assertion about its scalar restriction is used.
3. For the open restriction comparison a and tensor comparison E, both maps
T_Z J_A Res(L) to J_B L restrict to epsilon_X(L). The extension/restriction
unit is identity on the defining presheaf and its sheafification over X by
def-weil-extension-by-zero. Exactness descends this assertion to complexes.
The open adjunction therefore gives epsilon_Z T(a) = J_B(epsilon_X) E.
4. By lem-sf-compact-support-restriction-of-scalars, d_f is R_A(a) followed by D.
The K-injective normalization agrees with the ring-sheaf comparison by
lem-weil-pbc-ringed-topoi-derived-pushforward-composition. Substitute Step 2,
use naturality of gamma at a, and then Step 3. Since b = R_B(E) gamma J_A,
this is precisely the ambient counit equation in the second conjunct below.
5. Expand the transpose in the first conjunct using Step 1, apply Step 4 and
naturality of b at t. It becomes b(K) followed by F_B(T_X(t) epsilon_X(L)),
the required right-hand side. Naturality of the scalar Hom bijections and of
all displayed functors gives the third conjunct, including arbitrary u and v.
6. For A to B to C the scalar composite counit is epsilon_BC after T_BC(epsilon_AB).
The composition normalization in lem-sfb-ringed-derived-monoidal-comparisons
identifies it with the A-to-C counit under the specified tensor associator.
Thus successive transposes equal the direct transpose after alpha. The d_f
comparisons compose by lem-sf-compact-support-restriction-of-scalars, and the
b cocycle is det-sp-reduction-direct-image. These give the three equalities
in the fourth conjunct: scalar transposes, mixed maps, and comparison factors.
7. Under the multiplication-normalized scalar identity unitor the adjunction
is the identity adjunction, d_f is identity on open sections and on direct-image
representatives, and Step 4 makes b identity. The mixed transpose is F_A(t).
At t = identity this is identity by functoriality, giving the final two conjuncts.
Invertibility of b on the stated Dctf input is det-sp-reduction-direct-image.
Every counit calculation is ambient and uses no flatness assumption on B/A. -/
theorem restrictionTransitionTranspose
    (ℓ pchar : ℕ) [Fact ℓ.Prime] (hp : 0 < pchar) (hℓ : pchar ≠ ℓ)
    (k : Type u) [Field k] [CharP k pchar]
    {X Z Y : Scheme.{u}}
    [X.Over (Spec (.of k))] [Z.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))]
    [LocallyOfFiniteType (Z ↘ Spec (.of k))] [QuasiCompact (Z ↘ Spec (.of k))]
    [IsSeparated (Z ↘ Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
    [IsSeparated (Y ↘ Spec (.of k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of k))]
    (j : X ⟶ Z) [IsOpenImmersion j] [j.IsOver (Spec (.of k))]
    (h : Z ⟶ Y) [IsProper h] [h.IsOver (Spec (.of k))] (hf : j ≫ h = f)
    {A B : Type u} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (hA : ∃ n : ℕ, ∀ x : A, (ℓ ^ n) • x = 0)
    (hB : ∃ n : ℕ, ∀ x : B, (ℓ ^ n) • x = 0) (φ : A →+* B)
    (K : proEtaleDerivedCategory X A) (L : proEtaleDerivedCategory X B)
    (hKb : Set.Finite {i : ℤ | ¬ IsZero ((DerivedCategory.homologyFunctor
      (proEtaleRingModules X (proEtaleConstantRing X A)) i).obj K)})
    (hKc : ∀ i : ℤ, IsConstructibleProEtaleModuleSheaf X A
      ((DerivedCategory.homologyFunctor
        (proEtaleRingModules X (proEtaleConstantRing X A)) i).obj K))
    (hKt : HasFiniteProEtaleTorAmplitude X A K)
    (hLb : Set.Finite {i : ℤ | ¬ IsZero ((DerivedCategory.homologyFunctor
      (proEtaleRingModules X (proEtaleConstantRing X B)) i).obj L)})
    (hLc : ∀ i : ℤ, IsConstructibleProEtaleModuleSheaf X B
      ((DerivedCategory.homologyFunctor
        (proEtaleRingModules X (proEtaleConstantRing X B)) i).obj L))
    (hLt : HasFiniteProEtaleTorAmplitude X B L)
    (t : K ⟶ (scalarRestriction φ X).obj L) :
    restrictionTransitionMixedTranspose φ j h t =
        (reductionDirectImageComparison φ j h).app K ≫
          (reductionCompactSupport B j h).map
            (restrictionTransitionScalarTranspose φ X t) ∧
    (∀ H : proEtaleDerivedCategory X B,
      (scalarExtensionFunctor φ Y).map
          ((intrinsicCompactSupportRestriction φ j h).hom.app H) ≫
        (proEtaleRingDerivedExtensionAdjunction
          (proEtaleConstantRingMap (T := Y) φ)).counit.app
            ((reductionCompactSupport B j h).obj H) =
      (reductionDirectImageComparison φ j h).app ((scalarRestriction φ X).obj H) ≫
        (reductionCompactSupport B j h).map
          ((proEtaleRingDerivedExtensionAdjunction
            (proEtaleConstantRingMap (T := X) φ)).counit.app H)) ∧
    (∀ (K' : proEtaleDerivedCategory X A) (L' : proEtaleDerivedCategory X B)
        (u : K' ⟶ K) (v : L ⟶ L'),
      restrictionTransitionMixedTranspose φ j h
          (u ≫ t ≫ (scalarRestriction φ X).map v) =
        (scalarExtensionFunctor φ Y).map ((reductionCompactSupport A j h).map u) ≫
          restrictionTransitionMixedTranspose φ j h t ≫
            (reductionCompactSupport B j h).map v) ∧
    (∀ (C : Type u) [CommRing C] [Finite C]
        (_hC : ∃ n : ℕ, ∀ x : C, (ℓ ^ n) • x = 0) (ψ : B →+* C)
        (H : proEtaleDerivedCategory X C)
        (s : K ⟶ (scalarRestriction φ X).obj ((scalarRestriction ψ X).obj H)),
      (restrictionTransitionScalarTranspose ψ X
          (restrictionTransitionScalarTranspose φ X s) =
        (scalarExtensionFunctor_composition φ ψ X).hom.app K ≫
          restrictionTransitionScalarTranspose (ψ.comp φ) X
            (s ≫ (sfDerivedCoefficientRestrictionComp X φ ψ).hom.app H)) ∧
      (restrictionTransitionScalarTranspose ψ Y
          (restrictionTransitionMixedTranspose φ j h s ≫
            (intrinsicCompactSupportRestriction ψ j h).hom.app H) =
        (scalarExtensionFunctor_composition φ ψ Y).hom.app
            ((reductionCompactSupport A j h).obj K) ≫
          restrictionTransitionMixedTranspose (ψ.comp φ) j h
            (s ≫ (sfDerivedCoefficientRestrictionComp X φ ψ).hom.app H)) ∧
      ((scalarExtensionFunctor ψ Y).map ((reductionDirectImageComparison φ j h).app K) ≫
          (reductionDirectImageComparison ψ j h).app ((scalarExtensionFunctor φ X).obj K) ≫
          (reductionCompactSupport C j h).map
            ((scalarExtensionFunctor_composition φ ψ X).hom.app K) =
        (scalarExtensionFunctor_composition φ ψ Y).hom.app
            ((reductionCompactSupport A j h).obj K) ≫
          (reductionDirectImageComparison (ψ.comp φ) j h).app K)) ∧
    (∀ (M N : proEtaleDerivedCategory X A) (s : M ⟶ N),
      (scalarExtensionFunctor_identity (A := A) Y).inv.app
          ((reductionCompactSupport A j h).obj M) ≫
        restrictionTransitionMixedTranspose (RingHom.id A) j h
          (restrictionTransitionIdentityInput X s) =
      (reductionCompactSupport A j h).map s) ∧
    (∀ M : proEtaleDerivedCategory X A,
      (scalarExtensionFunctor_identity (A := A) Y).inv.app
          ((reductionCompactSupport A j h).obj M) ≫
        restrictionTransitionMixedTranspose (RingHom.id A) j h
          (restrictionTransitionIdentityInput X (𝟙 M)) =
      𝟙 ((reductionCompactSupport A j h).obj M)) ∧
    IsIso ((reductionDirectImageComparison φ j h).app K) := by
  sorry

end AlgebraicGeometry.ProEtale
