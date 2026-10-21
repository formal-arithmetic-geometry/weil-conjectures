/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q145
-/
module

public import Sheaf.SixFunctors.IntegralDualizing
public import Sheaf.Paper.IntegralHomReduction
public import Sheaf.Paper.SfIntegralConstructibleTriangulated
public import Mathlib.CategoryTheory.Triangulated.Opposite.Pretriangulated
public import Sheaf.Paper.DualityPairing
public import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Closed
public import WeilConjectures.Compactification.NagataCompactification
public import WeilConjectures.SixFunctors.Etale.Derived.Dualizing
public import Sheaf.Paper.DeltaRestriction
public import Sheaf.Algebra.Homology.DerivedInternalHomOfUniverses
public import Sheaf.AlgebraicGeometry.CompactifiableOverField
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import Sheaf.AlgebraicGeometry.EtaleAmbientAdjointLocality
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekLeftAdjoint
public import Sheaf.AlgebraicGeometry.ProEtaleDerivedCategory
public import Sheaf.CategoryTheory.RingedDerivedRestriction
public import WeilConjectures.Algebra.Homology.HomotopyCategory.DerivabilityStructure
public import WeilConjectures.Algebra.Homology.HomotopyCategory.OplaxMonoidal
public import WeilConjectures.CategoryTheory.Abelian.Flat.PreservesFlat
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasColimitsOfShape
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.TensorColimits
public import WeilConjectures.CategoryTheory.Sites.PullbackFlat
public import WeilConjectures.FromJoel.CategoryTheory.Localization.DerivabilityStructure.DerivesTwo
public import WeilConjectures.Mathlib.CategoryTheory.EssentialImage
public import WeilConjectures.Mathlib.CategoryTheory.Limits.MorphismProperty
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Monoidal
public import WeilConjectures.Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import WeilConjectures.Mathlib.CategoryTheory.Whiskering
public import WeilConjectures.SixFunctors.Etale.Derived.Coefficients
public import WeilConjectures.SixFunctors.Etale.Derived.Tensor
public import WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal
public import WeilConjectures.SixFunctors.Etale.SmoothBaseChange.HigherDirectImage.FreeSheaf
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.FlatModuleCat
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Monoidal
public import Sheaf.Paper.DerivedCompleteOnSlices
public import Sheaf.AlgebraicGeometry.FixedFiniteExceptionalAt
import Sheaf.Paper.ProEtaleConstructibleOrigin
import Sheaf.Paper.ComparisonTorAmplitude
import Sheaf.AlgebraicGeometry.CoefficientProEtaleTorAmplitude
import Sheaf.Paper.IntegralReductionTowerCanonical
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorClosed
import Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel

import Sheaf.Paper.IntegralResidueTor

import Sheaf.AlgebraicGeometry.ProEtaleCohomologicalSupport
import Sheaf.AlgebraicGeometry.ProEtaleTorAmplitude
import Sheaf.Paper.DerivedScalarExtensionRestrictionAdjunction
import Sheaf.Paper.FiniteFieldFiber
import Sheaf.Paper.FiniteTorAmplitude
import Sheaf.Paper.SfIntegralConstructible
import Sheaf.Paper.IntrinsicFiniteTorsionConstructibility
import Sheaf.Paper.SfDerivedComplete
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FiniteType

import Sheaf.Paper.WeilVerdierPreservationStrata

import Sheaf.Paper.FiniteStageVerdierBiduality

import Sheaf.Algebra.Homology.RingedInternalHomSignedCalculus

import Sheaf.Algebra.Homology.RingedInternalHomExactRestriction
import Sheaf.Paper.CoefficientRingedTensorHomModel
import Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients
import Sheaf.Paper.CoefficientHomRepresentativeEvaluation
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.MonoidalClosed
import WeilConjectures.CategoryTheory.DerivedCategory.HasMonoidalDerivedCategory
import WeilConjectures.CategoryTheory.Monoidal.Instances.DerivedCategory
import Sheaf.Algebra.Homology.RhomGlobalSectionsOfUniverses
import Sheaf.Algebra.Homology.RingedInternalHomShiftOfUniverses
import Sheaf.Paper.FiniteTorAmplitudeSites
import Sheaf.SixFunctors.FiniteDualitySiteComparison
import WeilConjectures.CategoryTheory.Triangulated.DerivedLimit

/-! # Integral Verdier biduality

Source: Weil blueprint, sec-six-functors/sk-prop-sf-biduality-general, order 2146
(blueprint: thm-coef-integral-verdier).

The dual is the ambient K-injective internal Hom over the completed ring sheaf.
Positive level n+1 is indexed by n : ℕ. The dualizing input is the object with
its specified reductions from prop-coef-integral-dualizing.

## Main definitions and statement

* `IntegralVerdier.dual`: ambient internal Hom into the integral dualizing object.
* `IntegralVerdier.comparison`: the evaluation-defined reduction map.
* `IntegralVerdier.delta`: specialization of the recorded evaluation transpose.
* `integral_verdier_biduality`: all integral duality and compatibility clauses.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency true
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme

open CategoryTheory.Pretriangulated CategoryTheory.Pretriangulated.Opposite

namespace WeilConjectures.IntegralVerdier

/-- The signed symmetry on a normalized tensor presentation, fixed on all homogeneous
local tensor generators. Its data are determined by this representative formula.
Source: blueprint order 2146, proof step 5; Stacks 06YL and 08J9
(blueprint: thm-coef-integral-verdier). -/
structure SignedSymmetry (X : Scheme.{u})
    (R : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
    (a : IntegralHom.TensorPresentation.{u, u} X R) where
  swap : ∀ K L : IntegralHom.Derived.{u, u} X R,
    a.tensor.obj (K, L) ≅ a.tensor.obj (L, K)
  representative : ∀ (P Q : CochainComplex (IntegralHom.Modules.{u, u} X R) ℤ)
    (hP : IntegralHom.flat.{u, u} X R P) (hQ : IntegralHom.flat.{u, u} X R Q),
    ∃ s : ((IntegralHom.totalTensor.{u, u} X R).obj P).obj Q ⟶
        ((IntegralHom.totalTensor.{u, u} X R).obj Q).obj P,
      (∀ (i j : ℤ) (U : X.ProEtᵒᵖ)
        (x : (P.X i).val.obj U) (y : (Q.X j).val.obj U),
        (s.f (i + j)).val.app U (IntegralHom.totalPair.{u, u} X R P Q i j U x y) =
          (i * j).negOnePow •
            (eqToHom (congrArg
              (fun k : ℤ ↦ (((IntegralHom.totalTensor.{u, u} X R).obj Q).obj P).X k)
                (add_comm j i))).val.app U
                  (IntegralHom.totalPair.{u, u} X R Q P j i U y x)) ∧
      a.representative.inv.app (⟨P, hP⟩, ⟨Q, hQ⟩) ≫ DerivedCategory.Q.map s ≫
        a.representative.hom.app (⟨Q, hQ⟩, ⟨P, hP⟩) =
          (swap (DerivedCategory.Q.obj P) (DerivedCategory.Q.obj Q)).hom

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (X : Scheme.{u})

/-- The unchanged completed-coefficient derived category.
Source: blueprint order 2146 (blueprint: thm-coef-integral-verdier). -/
abbrev Ambient := DerivedCategory (scalarReductionSource.{u, u} l E X)

/-- Ambient Verdier duality is RHom into the supplied integral dualizing object.
Source: blueprint order 2146, first display (blueprint: thm-coef-integral-verdier). -/
def dual (ω : Ambient l E X) : (Ambient l E X)ᵒᵖ ⥤ Ambient l E X :=
  (Functor.curry.obj (IntegralHom.hom.{u, u} X
    (completedIntegralCommRingSheafUnrestricted l E X))).flip.obj ω

/-- The actual finite dual with the specified finite dualizing object.
Source: blueprint order 2146, finite dual (blueprint: thm-coef-integral-verdier). -/
def finiteDual (n : ℕ) (ω : DerivedCategory (scalarReductionTarget l E X n)) :
    (DerivedCategory (scalarReductionTarget l E X n))ᵒᵖ ⥤
      DerivedCategory (scalarReductionTarget l E X n) :=
  (Functor.curry.obj (IntegralHom.hom.{u, u} X
    (integralCoefficientCommRingSheaf l E X n))).flip.obj ω

/-- The double-dual map is the transpose of evaluation with its factors interchanged.
The symmetry is the signed representative symmetry above.
Source: blueprint order 2146, proof step 5; Stacks 08J9
(blueprint: thm-coef-integral-verdier). -/
def delta {R : Sheaf (ProEt.topology X) CommRingCat.{u + 1}}
    (a : IntegralHom.TensorPresentation.{u, u} X R) (s : SignedSymmetry X R a)
    (ω K : IntegralHom.Derived.{u, u} X R) :
    K ⟶ (IntegralHom.hom.{u, u} X R).obj
      (op ((IntegralHom.hom.{u, u} X R).obj (op K, ω)), ω) :=
  restrictionDualDelta (Functor.curry.obj a.tensor)
    (Functor.curry.obj (IntegralHom.hom.{u, u} X R)) a.adjunction s.swap ω K

/-- Restriction of the actual dual functor, using the preservation clause as a proof.
Source: blueprint order 2146, anti-equivalence (blueprint: thm-coef-integral-verdier). -/
def restrictedDual (ω : Ambient l E X)
    (h : ∀ K : sfIntegralConstructibleCategory l E X,
      sfIntegralConstructible l E X ((dual l E X ω).obj (op K.obj))) :
    (sfIntegralConstructibleCategory l E X)ᵒᵖ ⥤ sfIntegralConstructibleCategory l E X :=
  ObjectProperty.lift (sfIntegralConstructible l E X)
    ((sfIntegralConstructible l E X).ι.op ⋙ dual l E X ω) (fun K ↦ h K.unop)

variable (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p)
  [X.Over (Spec (.of D.k))] [LocallyOfFiniteType (X ↘ Spec (.of D.k))]
  [QuasiCompact (X ↘ Spec (.of D.k))] [IsSeparated (X ↘ Spec (.of D.k))]

/-- The evaluation-defined comparison, followed by the specified dualizing reduction.
Source: blueprint order 2146, first comparison; lem-coef-integral-hom-reduction
(blueprint: thm-coef-integral-verdier). -/
def comparison
    {a : IntegralHom.TensorPresentation.{u, u} X
      (completedIntegralCommRingSheaf l E X D hl)}
    {n : ℕ} (m : IntegralHom.ReductionPresentation l E X D hl a n)
    (ω : sfIntegralConstructibleCategory l E X)
    (r : ∀ n : ℕ, (scalarReductionDerivedExtension l E X n).obj ω.obj ≅
      integralDualizingFiniteTerm l E D X n) (K : Ambient l E X) :
    (scalarReductionDerivedExtension l E X n).obj ((dual l E X ω.obj).obj (op K)) ⟶
      (finiteDual l E X n (integralDualizingFiniteTerm l E D X n)).obj
        (op ((scalarReductionDerivedExtension l E X n).obj K)) :=
  IntegralHom.comparison.{u, u, u} l E X D hl m K ω.obj ≫
    (IntegralHom.hom.{u, u} X (integralCoefficientCommRingSheaf l E X n)).map
      (Prod.mkHom (𝟙 (op ((scalarReductionDerivedExtension l E X n).obj K)))
        (r n).hom)

/-- The finite dual terms in one ambient category, using actual restriction of scalars.
Source: blueprint order 2146, second display (blueprint: thm-coef-integral-verdier). -/
def finiteTerms (K : Ambient l E X) (n : ℕ) : Ambient l E X :=
  (scalarReductionDerivedRestriction l E X n).obj
    ((finiteDual l E X n (integralDualizingFiniteTerm l E D X n)).obj
      (op ((scalarReductionDerivedExtension l E X n).obj K)))

/-- Restrict the evaluation-defined comparison, using its asserted invertibility.
Source: blueprint order 2146, reconstruction (blueprint: thm-coef-integral-verdier). -/
def restrictedComparison
    {a : IntegralHom.TensorPresentation.{u, u} X
      (completedIntegralCommRingSheaf l E X D hl)}
    (m : ∀ n : ℕ, IntegralHom.ReductionPresentation l E X D hl a n)
    (ω : sfIntegralConstructibleCategory l E X)
    (r : ∀ n : ℕ, (scalarReductionDerivedExtension l E X n).obj ω.obj ≅
      integralDualizingFiniteTerm l E D X n)
    (K : Ambient l E X)
    (h : ∀ n : ℕ, IsIso (comparison l E X D hl (m n) ω r K)) (n : ℕ) :
    (sfDerivedReductionRestricted l E X n).obj ((dual l E X ω.obj).obj (op K)) ≅
      finiteTerms l E X D K n :=
  (scalarReductionDerivedRestriction l E X n).mapIso
    (@asIso _ _ _ _ (comparison l E X D hl (m n) ω r K) (h n))

/-- The finite-dual transition in the completed-coefficient category. This is the
comparison transport of the actual quotient transition, not a chosen tower on the
same objects. The evaluation and transpose equations of the theorem identify it
with the transition induced by finite evaluation and dualizing reduction.
Source: blueprint order 2146, proof step 4 (blueprint: thm-coef-integral-verdier). -/
def finiteTransition
    {a : IntegralHom.TensorPresentation.{u, u} X
      (completedIntegralCommRingSheaf l E X D hl)}
    (m : ∀ n : ℕ, IntegralHom.ReductionPresentation l E X D hl a n)
    (ω : sfIntegralConstructibleCategory l E X)
    (r : ∀ n : ℕ, (scalarReductionDerivedExtension l E X n).obj ω.obj ≅
      integralDualizingFiniteTerm l E D X n)
    (K : Ambient l E X)
    (h : ∀ n : ℕ, IsIso (comparison l E X D hl (m n) ω r K)) (n : ℕ) :
    finiteTerms l E X D K (n + 1) ⟶ finiteTerms l E X D K n :=
  (restrictedComparison l E X D hl m ω r K h (n + 1)).inv ≫
    (sfDerivedReductionTransition l E X n).app ((dual l E X ω.obj).obj (op K)) ≫
      (restrictedComparison l E X D hl m ω r K h n).hom

/-- The specified reduction leg to the finite dual.
Source: blueprint order 2146, proof step 4 (blueprint: thm-coef-integral-verdier). -/
def finiteLeg
    {a : IntegralHom.TensorPresentation.{u, u} X
      (completedIntegralCommRingSheaf l E X D hl)}
    (m : ∀ n : ℕ, IntegralHom.ReductionPresentation l E X D hl a n)
    (ω : sfIntegralConstructibleCategory l E X)
    (r : ∀ n : ℕ, (scalarReductionDerivedExtension l E X n).obj ω.obj ≅
      integralDualizingFiniteTerm l E D X n)
    (K : Ambient l E X)
    (h : ∀ n : ℕ, IsIso (comparison l E X D hl (m n) ω r K)) (n : ℕ) :
    (dual l E X ω.obj).obj (op K) ⟶ finiteTerms l E X D K n :=
  (sfDerivedReductionUnit l E X n).app ((dual l E X ω.obj).obj (op K)) ≫
    (restrictedComparison l E X D hl m ω r K h n).hom

/-- Finite evaluation, adjointed back to completed coefficients. This explicitly
uses reduction of K and the reduction/restriction counit, so it is finite evaluation
with its input reduced, rather than an evaluation on an unrelated ambient object.
Source: blueprint order 2146, proof step 4 (blueprint: thm-coef-integral-verdier). -/
def finiteEvaluation
    {a : IntegralHom.TensorPresentation.{u, u} X
      (completedIntegralCommRingSheaf l E X D hl)}
    (m : ∀ n : ℕ, IntegralHom.ReductionPresentation l E X D hl a n)
    (K : Ambient l E X) (n : ℕ) :
    a.tensor.obj (K, finiteTerms l E X D K n) ⟶
      (scalarReductionDerivedRestriction l E X n).obj
        (integralDualizingFiniteTerm l E D X n) :=
  (derivedScalarExtensionRestrictionAdjunction.{u, u} l E X n).choose.homEquiv _ _
    ((m n).mu.hom.app (K, finiteTerms l E X D K n) ≫
      (m n).target.tensor.map
        (Prod.mkHom (𝟙 ((scalarReductionDerivedExtension l E X n).obj K))
          ((derivedScalarExtensionRestrictionAdjunction.{u, u} l E X n).choose.counit.app
            ((finiteDual l E X n (integralDualizingFiniteTerm l E D X n)).obj
              (op ((scalarReductionDerivedExtension l E X n).obj K))))) ≫
      ((m n).target.adjunction ((scalarReductionDerivedExtension l E X n).obj K)).counit.app
        (integralDualizingFiniteTerm l E D X n))

/-- The specified finite dualizing transition transported through its reductions.
Source: blueprint order 2146, proof step 4 (blueprint: thm-coef-integral-verdier). -/
def dualizingTransition (ω : sfIntegralConstructibleCategory l E X)
    (r : ∀ n : ℕ, (scalarReductionDerivedExtension l E X n).obj ω.obj ≅
      integralDualizingFiniteTerm l E D X n) (n : ℕ) :
    (scalarReductionDerivedRestriction l E X (n + 1)).obj
        (integralDualizingFiniteTerm l E D X (n + 1)) ⟶
      (scalarReductionDerivedRestriction l E X n).obj (integralDualizingFiniteTerm l E D X n) :=
  ((scalarReductionDerivedRestriction l E X (n + 1)).mapIso (r (n + 1))).inv ≫
    (sfDerivedReductionTransition l E X n).app ω.obj ≫
      ((scalarReductionDerivedRestriction l E X n).mapIso (r n)).hom

/-- Every clause of integral Verdier duality for the ambient internal Hom.
Tensor presentations and signed symmetries are supplied as part of the conclusion;
their representative normalizations fix evaluation and its transposes.
Source: blueprint order 2146 (blueprint: thm-coef-integral-verdier). -/
def Conclusion (ω : sfIntegralConstructibleCategory l E X)
    (r : ∀ n : ℕ, (scalarReductionDerivedExtension l E X n).obj ω.obj ≅
      integralDualizingFiniteTerm l E D X n) : Prop :=
  ∃ (tensor : IntegralHom.TensorPresentation.{u, u} X
    (completedIntegralCommRingSheaf l E X D hl)),
  ∃ (symmetry : SignedSymmetry X (completedIntegralCommRingSheaf l E X D hl) tensor),
  ∃ (reduction : ∀ n : ℕ, IntegralHom.ReductionPresentation l E X D hl tensor n),
  ∃ (finiteSymmetry : ∀ n : ℕ,
    SignedSymmetry X (integralCoefficientCommRingSheaf l E X n) (reduction n).target),
  ∃ (_categories_equal : sfIntegralConstructible l E X = finiteTorConstructibleIntegral l E X),
  ∃ (preservation : ∀ K : sfIntegralConstructibleCategory l E X,
    sfIntegralConstructible l E X ((dual l E X ω.obj).obj (op K.obj))),
  ∃ (_anti_equivalence : (restrictedDual l E X ω.obj preservation).IsEquivalence),
  ∃ (_exact : ∃ s : (dual l E X ω.obj).CommShift ℤ,
    ∀ T : CategoryTheory.Pretriangulated.Triangle (Ambient l E X)ᵒᵖ,
      sfIntegralConstructible l E X T.obj₁.unop →
      sfIntegralConstructible l E X T.obj₂.unop →
      sfIntegralConstructible l E X T.obj₃.unop →
      T ∈ distTriang (Ambient l E X)ᵒᵖ →
      CategoryTheory.Pretriangulated.Triangle.mk
        ((dual l E X ω.obj).map T.mor₁) ((dual l E X ω.obj).map T.mor₂)
        ((dual l E X ω.obj).map T.mor₃ ≫
          (s.commShiftIso (1 : ℤ)).hom.app T.obj₁) ∈
        distTriang (Ambient l E X)),
  ∃ (comparisons : ∀ (K : sfIntegralConstructibleCategory l E X) (n : ℕ),
    IsIso (comparison l E X D hl (reduction n) ω r K.obj)),
  ∃ (_evaluation : ∀ (K : sfIntegralConstructibleCategory l E X) (n : ℕ),
    (reduction n).target.tensor.map
        (Prod.mkHom (𝟙 ((scalarReductionDerivedExtension l E X n).obj K.obj))
          (comparison l E X D hl (reduction n) ω r K.obj)) ≫
      ((reduction n).target.adjunction
        ((scalarReductionDerivedExtension l E X n).obj K.obj)).counit.app
          (integralDualizingFiniteTerm l E D X n) =
    (reduction n).mu.inv.app (K.obj, (dual l E X ω.obj).obj (op K.obj)) ≫
      (scalarReductionDerivedExtension l E X n).map
        ((tensor.adjunction K.obj).counit.app ω.obj) ≫
          (r n).hom),
  ∃ (_transposes : ∀ (K : sfIntegralConstructibleCategory l E X) (n : ℕ)
    (V : Ambient l E X) (f : V ⟶ (dual l E X ω.obj).obj (op K.obj)),
    ((reduction n).target.adjunction
      ((scalarReductionDerivedExtension l E X n).obj K.obj)).homEquiv
        ((scalarReductionDerivedExtension l E X n).obj V)
        (integralDualizingFiniteTerm l E D X n)
        ((reduction n).mu.inv.app (K.obj, V) ≫
          (scalarReductionDerivedExtension l E X n).map
            (((tensor.adjunction K.obj).homEquiv V ω.obj).symm f) ≫
              (r n).hom) =
      (scalarReductionDerivedExtension l E X n).map f ≫
        comparison l E X D hl (reduction n) ω r K.obj),
  ∃ (_transition_evaluation : ∀ (K : sfIntegralConstructibleCategory l E X) (n : ℕ),
    tensor.tensor.map (Prod.mkHom (𝟙 K.obj)
        (finiteTransition l E X D hl reduction ω r K.obj (comparisons K) n)) ≫
      finiteEvaluation l E X D hl reduction K.obj n =
    finiteEvaluation l E X D hl reduction K.obj (n + 1) ≫
      dualizingTransition l E X D ω r n),
  ∃ (_reconstruction : ∀ K : sfIntegralConstructibleCategory l E X,
    ∃ hprod : HasProduct (fun n : ℕ ↦ finiteTerms l E X D K.obj n),
      (fun [_productInst : HasProduct (fun n : ℕ ↦ finiteTerms l E X D K.obj n)] ↦
        ∃ δ : (∏ᶜ fun n : ℕ ↦ finiteTerms l E X D K.obj n) ⟶
            ((dual l E X ω.obj).obj (op K.obj))⟦(1 : ℤ)⟧,
          IsDerivedLimitTriangle
            (finiteTransition l E X D hl reduction ω r K.obj (comparisons K))
            ((dual l E X ω.obj).obj (op K.obj))
            (Pi.lift (finiteLeg l E X D hl reduction ω r K.obj (comparisons K))) δ)
        (_productInst := hprod)),
  ∃ (_tor_bound : ∀ (K : sfIntegralConstructibleCategory l E X) (d : ℕ),
    topologicalKrullDim X ≤ (d : WithBot ℕ∞) → ∀ a b : ℤ, a ≤ b →
    (∀ n : ℕ, HasProEtaleTorAmplitude X (Padic.coefficientExtensionRing l E (n + 1))
      ((scalarReductionDerivedExtension l E X n).obj K.obj) a b) →
    ∀ n : ℕ, HasProEtaleTorAmplitude X (Padic.coefficientExtensionRing l E (n + 1))
      ((scalarReductionDerivedExtension l E X n).obj ((dual l E X ω.obj).obj (op K.obj)))
        (-b - 2 * (d : ℤ)) (-a)),
  ∃ (_reduction_delta : ∀ (K : sfIntegralConstructibleCategory l E X) (n : ℕ),
    (scalarReductionDerivedExtension l E X n).map
        (delta X tensor symmetry ω.obj K.obj) ≫
      comparison l E X D hl (reduction n) ω r
        ((dual l E X ω.obj).obj (op K.obj)) ≫
      (IntegralHom.hom.{u, u} X (integralCoefficientCommRingSheaf l E X n)).map
        (Prod.mkHom
          ((@asIso _ _ _ _
            (comparison l E X D hl (reduction n) ω r K.obj) (comparisons K n)).inv.op)
          (𝟙 (integralDualizingFiniteTerm l E D X n))) =
      delta X (reduction n).target (finiteSymmetry n) (integralDualizingFiniteTerm l E D X n)
        ((scalarReductionDerivedExtension l E X n).obj K.obj)),
  ∃ (_biduality : ∀ K : sfIntegralConstructibleCategory l E X,
    IsIso (delta X tensor symmetry ω.obj K.obj)),
  ∀ (K L : sfIntegralConstructibleCategory l E X) (f : K ⟶ L),
    f.hom ≫ delta X tensor symmetry ω.obj L.obj =
      delta X tensor symmetry ω.obj K.obj ≫
        (dual l E X ω.obj).map ((dual l E X ω.obj).map f.hom.op).op

end WeilConjectures.IntegralVerdier

namespace WeilConjectures

/-- Integral Verdier biduality for the dualizing object with its reductions
supplied by prop-coef-integral-dualizing. The finite terms and their
transition adjuncts are the exceptional inverse images of the coefficient units.
The conclusion states equality of the constructible and finite-Tor categories,
exact anti-equivalence, canonical reduction and Roos reconstruction, the uniform
Tor bound, and invertibility and naturality of the evaluation-defined double dual.

Source: Weil blueprint, sec-six-functors/sk-prop-sf-biduality-general, order 2146
(blueprint: thm-coef-integral-verdier).

Proof plan, following all eight steps of the node:
1. Choose a cohomological interval containing the residue reduction of K.
   lem-coef-integral-residue-tor gives this same Tor interval at every positive
   level. This proves equality with the uniform finite-Tor subcategory. Choose
   a nonnegative dimension bound by lem-kun-dimension-finite-type; for the empty
   scheme take zero.
2. prop-coef-integral-dualizing makes omega complete with its specified coherent
   finite reductions. Apply lem-coef-integral-hom-reduction to K and omega.
   Ambient RHom is complete, and the evaluation-defined comparisons are invertible.
   Their defining transpose equations give evaluation and transpose compatibility.
3. lem-sf-proetale-constructible-origin and lem-sf-comparison-tor-amplitude give
   finite etale origins with the input Tor interval. Apply
   lem-weil-verdier-preservation-strata and then
   lem-weil-finite-duality-site-comparison. The output reductions are constructible
   with Tor interval [-b-2d,-a], hence have cohomology in that same interval.
   Completeness and these bounds are precisely sfIntegralConstructible.
4. Take the actual Roos triangle of the complete ambient Hom. The comparisons
   identify each restricted reduction with the finite dual. Their evaluation and
   transpose equations identify finite evaluation's transition with conjugation
   by these comparisons. The product of the comparisons intertwines 1-s, checked
   on each projection. Transport the Roos triangle, including its specified first
   legs; this is def-weil-derived-limit, without choosing a second limit model.
5. Ringed-site internal-Hom exactness, lem-pur-rhom-global-sections and the
   inherited triangulation of lem-weil-integral-constructible-triangulated give
   exactness. The sheaf tensor symmetry with sign (-1)^(ij) descends on K-flats.
   Transpose evaluation after this symmetry to obtain delta. Evaluation naturality
   makes both sides of delta's naturality square have the same transpose.
6. Apply the Hom reduction comparison twice, using preservation for DK. Its
   evaluation and transpose equations carry the actual reduced delta to the
   finite delta of lem-weil-duality-pairing. This map is invertible by
   thm-fix-general-biduality, since the reductions are finite-Tor constructible.
7. The cone of delta is constructible and complete by triangulated closure.
   Exact derived reduction (lem-pur-derived-change-of-rings) makes every reduction
   of the cone zero. Its Roos triangle then has two zero product vertices, so
   lem-kun-distinguished-cone-zero kills the cone and makes delta invertible.
8. Uncurrying D(delta_K) composed with delta_DK gives evaluation itself, by
   evaluation naturality and the two inverse signed symmetries. Thus that
   composite is the identity. Naturality and invertibility of delta give full
   faithfulness: a map v:DL to DK has preimage delta_K followed by Dv and the
   inverse of delta_L. Every L is isomorphic to D(DL), proving essential
   surjectivity. Together with step 5 this is the exact anti-equivalence.
-/
theorem integral_verdier_biduality
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (X : Scheme.{u}) [X.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))]
    [QuasiCompact (X ↘ Spec (.of D.k))] [IsSeparated (X ↘ Spec (.of D.k))]
    (ω : sfIntegralConstructibleCategory l E X)
    (r : ∀ n : ℕ, (scalarReductionDerivedExtension l E X n).obj ω.obj ≅
      integralDualizingFiniteTerm l E D X n) :
    IntegralVerdier.Conclusion l E X D hl ω r := by
  sorry

end WeilConjectures
