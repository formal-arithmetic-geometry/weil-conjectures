/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Submission.WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleRootsOfUnitySheafSupplement
public import Submission.WeilConjectures.SmoothPurity.Coefficient.CoefficientTwistsDetailed
public import Submission.WeilConjectures.AlgebraicGeometry.ProEtaleInverseImage
public import Submission.WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
public import Submission.WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Submission.WeilConjectures.CategoryTheory.RingedSiteModules
public import Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Submission.WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.Defs
public import Submission.WeilConjectures.Mathlib.CategoryTheory.Sites.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Category.ModuleCat.AB
public import Mathlib.Algebra.Category.ModuleCat.Sheaf
public import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.CategoryTheory.Sites.Sheafification
public import Submission.WeilConjectures.CategoryTheory.Adjunction.LiftsGroupRingObjects
public import Mathlib.CategoryTheory.Monoidal.CommGrp_
public import Mathlib.CategoryTheory.Monoidal.Ring
public import Mathlib.CategoryTheory.Adjunction.Limits
public import Submission.WeilConjectures.CategoryTheory.Adjunction.LiftedCommRingBranch
public import Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import Submission.WeilConjectures.AlgebraicGeometry.ProEtaleTensorComparison.ProEtaleInverseImageTensorComparisonSupplement
import Submission.WeilConjectures.AlgebraicGeometry.Pur.PurInverseImageHomComparison
import Submission.WeilConjectures.AlgebraicGeometry.ProEtaleImmersionLimitPreservation
import Mathlib.AlgebraicGeometry.Scheme
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.AlgebraicGeometry.Morphisms.Immersion
import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Submission.WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.CategoryTheory.Sites.Limits
import Submission.WeilConjectures.AlgebraicGeometry.ProEtale.AffineClosedInverseImageLeftAdjoint
import Submission.WeilConjectures.AlgebraicGeometry.IndEtaleBasisWeaklyContractibleCover
import Submission.WeilConjectures.AlgebraicGeometry.ProEtale.Comparison.Affine
import Submission.WeilConjectures.AlgebraicGeometry.ProEtale.WeaklyContractible
import Submission.WeilConjectures.CategoryTheory.Sites.LowerShriekCoveringGenerators
import Mathlib.CategoryTheory.Limits.Preserves.Finite
import Submission.WeilConjectures.CategoryTheory.Sites.LowerShriekCorepresentability
import Mathlib.CategoryTheory.Adjunction.PartialAdjoint
import Mathlib.CategoryTheory.Sites.Sheaf
import Submission.WeilConjectures.CategoryTheory.Sites.CoveringRepresentableCoequalizer
import Mathlib.CategoryTheory.Sites.LeftExact
import Mathlib.CategoryTheory.Limits.Shapes.Equalizers
import Mathlib.CategoryTheory.Yoneda
import Mathlib.CategoryTheory.Sites.RegularEpi
import Mathlib.CategoryTheory.Limits.Shapes.KernelPair
import Submission.WeilConjectures.AlgebraicGeometry.ProEtale.AffineClosedInverseImageEvaluation
import Submission.WeilConjectures.AlgebraicGeometry.ProEtale.AffineClosedSiteFunctorProperties
import Submission.WeilConjectures.CategoryTheory.InverseMateEquivalence
import Submission.WeilConjectures.AlgebraicGeometry.ProEtale.Replete
import Submission.WeilConjectures.Mathlib.CategoryTheory.Limits.Shapes.Products
import Submission.WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Iso
import Submission.WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleOperationsSupplement
import Submission.WeilConjectures.AlgebraicGeometry.ProEtaleInverseImageLimitsZariskiLocal
import Mathlib.CategoryTheory.Functor.ReflectsIso.Limits
import Submission.WeilConjectures.Mathlib.CategoryTheory.Sites.Sheaf
import Submission.WeilConjectures.Mathlib.CategoryTheory.NatIso
import Submission.WeilConjectures.AlgebraicGeometry.ProEtaleModuleInverseImageComparison
import Mathlib.Algebra.Category.Ring.Limits
import Mathlib.Algebra.Category.Ring.FilteredColimits
import Submission.WeilConjectures.AlgebraicGeometry.ProEtaleModuleInverseImageUnderlying
import Submission.WeilConjectures.AlgebraicGeometry.ProEtaleModelRingPresentation
import Submission.WeilConjectures.CategoryTheory.SheafPullbackUnitPresentation
import Mathlib.CategoryTheory.Sites.Pullback
import Mathlib.CategoryTheory.Sites.CartesianMonoidal
import Submission.WeilConjectures.CategoryTheory.SheafPullbackForgetComparison
import Submission.WeilConjectures.CategoryTheory.ModuleInverseImageAdjunction
import Submission.WeilConjectures.CategoryTheory.ModuleInverseImageAction
import Submission.WeilConjectures.CategoryTheory.ModuleInverseImageActionOfPresentations
import Submission.WeilConjectures.AlgebraicGeometry.EtaleInverseImageModuleAdjunction
import Submission.WeilConjectures.AlgebraicGeometry.ProEtaleModuleInverseImageScalarGraph
import Submission.WeilConjectures.CategoryTheory.SheavesAlgebraicStructuresAbelian
import Mathlib.CategoryTheory.Limits.HasLimits

import all Submission.WeilConjectures.Algebra.Homology.Scalar.ScalarExtensionDualLocalIso
import all Submission.WeilConjectures.AlgebraicGeometry.Pur.PurTwistSheafLocallyFree
import all Submission.WeilConjectures.AlgebraicGeometry.Pur.PurInverseImageScalarComparison
import all Submission.WeilConjectures.AlgebraicGeometry.Pur.PurTwistRootLocalModels
import Submission.WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
import Submission.WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import Submission.WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import Submission.WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import Mathlib.Algebra.Homology.BifunctorShift
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import Mathlib.CategoryTheory.Limits.EssentiallySmall
import Submission.WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import Submission.WeilConjectures.Algebra.Homology.SixFunctors.LocalizedSiteTensorRestrictionSupplement
import Submission.WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

/-! # Tate twists with finite coefficients are locally free of rank one

Source: `literature/blueprint/main-20261015/blueprint/sec-smooth-purity/sk-prop-an/
sk-def-sp-tate-twist-locally-free.md`, clauses (1)--(3) for finite coefficients
(blueprint: det-def-sp-tate-twist-locally-free).

The finite part of `WeilConjectures.AlgebraicGeometry.Tate.TateTwistLocallyFree`, in its own module
so that the finite twists do not depend on the integral, rational and algebraically closed
coefficient clauses.
All positive root levels are indexed by `n + 1`.

## Main definitions

* `tateFiniteLine` is the recorded roots module tensored with a finite coefficient ring.
* `TateSignedLine` states rank one, same-cover triviality and the tensor inverse.
* `TateInverseTwists` fixes the actual functor and negative inverse of an equivalence.

## Main statements

* `tateTwist_finite_locallyFree` states the common cover, the compatible root generators and
  the finite coefficient clauses.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 2048

universe u v d c h

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme WeilConjectures

namespace AlgebraicGeometry.Scheme

/-- The constant commutative coefficient sheaf in clause (2).
Source: blueprint clause (2) (blueprint: det-def-sp-tate-twist-locally-free). -/
abbrev tateFiniteCoefficient (X : Scheme.{u}) (A : Type (u + 1)) [CommRing A] :=
  (constantSheaf (ProEt.topology X) CommRingCat.{u + 1}).obj (CommRingCat.of A)

/-- Apply the canonical quotient coefficient homomorphism to constant sheaves.
Source: blueprint clause (2) (blueprint: det-def-sp-tate-twist-locally-free). -/
def tateFiniteScalar (X : Scheme.{u}) (ℓ : ℕ) (A : Type (u + 1)) [CommRing A]
    (n : ℕ) (a : ZMod (ℓ ^ (n + 1)) →+* A) :
    purTwistFiniteRing X ℓ n ⟶ tateFiniteCoefficient X A :=
  (constantSheaf (ProEt.topology X) CommRingCat.{u + 1}).map
    (CommRingCat.ofHom (a.comp ULift.ringEquiv.toRingHom))

/-- The finite A-line is exactly the recorded roots module tensored with A_X.
Source: blueprint clauses (2)--(3) (blueprint: det-def-sp-tate-twist-locally-free). -/
def tateFiniteLine (X : Scheme.{u}) (ℓ : ℕ) [Fact ℓ.Prime]
    (A : Type (u + 1)) [CommRing A] (n : ℕ) (a : ZMod (ℓ ^ (n + 1)) →+* A) :=
  SheafOfModules.changeOfRingsOfUniverses.{u, u + 1, u + 1, u + 1}
    (tateFiniteScalar X ℓ A n a) (purTwistRootsModule X ℓ n)

/-- Signed line clauses on a specified cover: rank one, the same-cover trivializations,
and the positive/negative tensor pairing. All powers and duals are the recorded ones.
Source: blueprint clause (3) (blueprint: det-def-sp-tate-twist-locally-free). -/
def TateSignedLine (X : Scheme.{u})
    (R : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
    (L : SheafOfModules.{u + 1} (purTwistRing X R))
    {I : Type (u + 1)} (U : I → X.ProEt) : Prop :=
  (∀ m : ℤ, (coefficientTwistLine X (R := R) L m).IsFiniteLocallyFreeOfRank 1 ∧
    ∀ i : I, Nonempty ((coefficientTwistLine X (R := R) L m).over (U i) ≅
      (SheafOfModules.unit (purTwistRing X R)).over (U i))) ∧
  ∀ n : ℕ, Nonempty
    ((SheafOfModules.siteSheafTensorRight (A := R)
      (coefficientTwistLine X L (-(n : ℤ)))).obj (coefficientTwistLine X L n) ≅
        SheafOfModules.unit (purTwistRing X R))

/-- Fixing the right input of a published tensor bifunctor retains its full arrow action.
Source: blueprint K(m) formula (blueprint: det-def-sp-tate-twist-locally-free). -/
def tateTensorRight {C : Type c} [Category.{h} C] (T : C × C ⥤ C) (L : C) : C ⥤ C :=
  (𝟭 C).prod' ((Functor.const C).obj L) ⋙ T

/-- An equivalence whose actual functor and inverse are the two prescribed twists.
Source: blueprint clause (3), final sentence
(blueprint: det-def-sp-tate-twist-locally-free). -/
def TateInverseTwists {C : Type c} [Category.{h} C] (F G : C ⥤ C) : Prop :=
  ∃ e : C ≌ C, e.functor = F ∧ e.inverse = G

set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] HasDerivedCategory.standard

private theorem tateAbSheafify (X : Scheme.{u}) :
    HasSheafify (ProEt.topology X) AddCommGrpCat.{u + 1} :=
  integralCoefficientAbSheafify.{u, u} X
attribute [local instance 20000] tateAbSheafify
private theorem tateAbBijective (X : Scheme.{u}) :
    (ProEt.topology X).WEqualsLocallyBijective AddCommGrpCat.{u + 1} :=
  integralCoefficientAbLocallyBijective.{u, u} X
attribute [local instance 20000] tateAbBijective

private theorem tateWeakSheafify (X : Scheme.{u}) :
    HasWeakSheafify (ProEt.topology X) AddCommGrpCat.{u + 1} :=
  (tateAbSheafify X).isRightAdjoint
attribute [local instance 20000] tateWeakSheafify

private theorem tateSiteSmall (X : Scheme.{u}) :
    EssentiallySmall.{u + 1} X.ProEt := essentiallySmallSelf.{0, u, u + 1} _
attribute [local instance 20000] tateSiteSmall

@[instance_reducible] private def tateDerived (X : Scheme.{u})
    (R : Sheaf (ProEt.topology X) CommRingCat.{u + 1}) :
    HasDerivedCategory.{u + 2} (SheafOfModules.{u + 1} (purTwistRing X R)) :=
  HasDerivedCategory.standard _
attribute [local instance 20000] tateDerived

end AlgebraicGeometry.Scheme
