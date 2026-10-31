/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.PointFibreDerivedTensor
public import WeilConjectures.AlgebraicGeometry.FixedFiniteExceptionalAt
public import WeilConjectures.AlgebraicGeometry.CompactSupportComparisonUnit

import WeilConjectures.NumberTheory.Padics.ExtensionIntegersDvr
import Mathlib.Algebra.Order.AbsoluteValue.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.NumberTheory.Padics.PadicNumbers
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.Localization.FractionRing
import WeilConjectures.NumberTheory.Padics.ExtensionIntegersDvrCore
import Mathlib.Analysis.Normed.Algebra.Ultra
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.NumberTheory.Padics.ProperSpace
import Mathlib.Topology.Algebra.Valued.LocallyCompact
import WeilConjectures.NumberTheory.Padics.ExtensionIntegersDvrFactorization
import WeilConjectures.NumberTheory.Padics.ExtensionIntegersDvrFactorizationUnique
import WeilConjectures.Mathlib.RingTheory.OrderOfVanishing.Noetherian
import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek
import WeilConjectures.AlgebraicGeometry.ComparisonPullbackExact
import WeilConjectures.AlgebraicGeometry.PointProEtaleSectionsExact
import WeilConjectures.AlgebraicGeometry.PointSectionsReconstruction
import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import WeilConjectures.Algebra.Homology.KFlatSupplement
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
import Mathlib.CategoryTheory.Monoidal.Closed.Basic
import Mathlib.CategoryTheory.Limits.ExactFunctor
import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.Algebra.Category.Grp.AB
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import Mathlib.RingTheory.Flat.CategoryTheory
import WeilConjectures.AlgebraicGeometry.PointDerivedHomEvaluation
import WeilConjectures.AlgebraicGeometry.FiniteConstructibleHom

import WeilConjectures.Algebra.Homology.DerivedInternalHomOfUniverses
import WeilConjectures.Algebra.Homology.DerivedInternalHom
import WeilConjectures.SixFunctors.Etale.Derived.Hom
import WeilConjectures.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses
import Mathlib.Algebra.Category.Ring.Limits
import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
import Mathlib.CategoryTheory.Yoneda
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
import Mathlib.CategoryTheory.Generator.Basic
import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolutionInjective
import WeilConjectures.Algebra.Homology.QuasiIsoHomComplexMapOfUniverses
import WeilConjectures.Algebra.Homology.HomComplex
import WeilConjectures.Algebra.Homology.HomComplexSectionsQuasiIsoOfUniverses
import WeilConjectures.CategoryTheory.Sites.RGammaDerivedLimitSupplement
import Mathlib.Algebra.Category.Grp.Abelian
import WeilConjectures.Algebra.Homology.HomComplexSectionsDerivedNaturalityOfUniverses
import WeilConjectures.Algebra.Homology.RhomIntoKInjectiveLocal
import WeilConjectures.Algebra.Homology.KInjectiveRestrictLocalizedOfUniverses
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
import WeilConjectures.Algebra.Homology.LocalizedRestrictionAdjunctionOfUniverses
import WeilConjectures.Algebra.Homology.LocalizedRestrictionExtensionExistsOfUniverses
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import WeilConjectures.CategoryTheory.ExtensionByZeroPresheaf
import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
import Mathlib.CategoryTheory.Adjunction.Additive
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp
import Mathlib.Algebra.Homology.DerivedCategory.KInjective
import WeilConjectures.Algebra.Homology.HomComplexSectionsHomotopyNaturalityOfUniverses
import WeilConjectures.Algebra.Homology.HomComplexProjections
import WeilConjectures.Algebra.Homology.HomComplexSectionsCanonicalComparisonOfUniverses
import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexShift
import WeilConjectures.Algebra.Homology.HomComplexSectionsCochainsOfUniverses
import WeilConjectures.Algebra.Homology.HomComplexSectionsCochainsCommOfUniverses
import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexCohomology
import Mathlib.Algebra.Category.Grp.EpiMono
import WeilConjectures.Algebra.Homology.LocalizedModuleRestrictionQuasiIsoOfUniverses
import WeilConjectures.Mathlib.CategoryTheory.Sites.Continuous
import WeilConjectures.Algebra.Homology.QuasiIsoOfSectionsOfUniverses
import Mathlib.CategoryTheory.Sites.Abelian
import Mathlib.Algebra.Homology.Functor
import WeilConjectures.AlgebraicGeometry.BoundedConstructibleComplexes
import WeilConjectures.AlgebraicGeometry.DerivedCategories
import WeilConjectures.AlgebraicGeometry.IsConstructibleEtaleModuleSheaf
import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
import Mathlib.AlgebraicGeometry.Sites.Proetale
import Mathlib.CategoryTheory.Sites.ConstantSheaf
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
import Mathlib.RingTheory.Ideal.Quotient.Index
import WeilConjectures.AlgebraicGeometry.FiniteFieldFiberSupplement
import WeilConjectures.AlgebraicGeometry.FiniteTorAmplitude
import WeilConjectures.AlgebraicGeometry.ProEtaleTorAmplitude
import WeilConjectures.AlgebraicGeometry.SfIntegralConstructible
import WeilConjectures.AlgebraicGeometry.ProEtaleCohomologicalSupport
import WeilConjectures.AlgebraicGeometry.SfDerivedComplete
import WeilConjectures.AlgebraicGeometry.IntrinsicFiniteTorsionConstructibility
import WeilConjectures.Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
import WeilConjectures.SixFunctors.Etale.Derived.Coefficients
import WeilConjectures.SixFunctors.Etale.Derived.TorAmplitude
import WeilConjectures.AlgebraicGeometry.ConnectedConstantH0
import WeilConjectures.AlgebraicGeometry.ConstructibleExceptionalAdjunctionCoefficients
import WeilConjectures.AlgebraicGeometry.FiniteCoefficientPoint
/-! # Evaluation comparison for finite coefficients at the geometric point

Source: Weil blueprint, main-20261015, lem-pod-point-dualizing-complex.proof.md,
opening paragraph (blueprint: lem-coef-finite-point-internal-hom-evaluation).

The identity compactification is evaluated with the identity as right adjoint of
identity compact support. Thus its transported dualizing object is nu^* R nu_* B.
The normalization below is the actual comparison counit, transported through the
recorded intrinsic coefficient realization. Transposition uses the recorded
point tensor and unit comparisons and the ordinary coefficient tensor-Hom adjunction.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
open CategoryTheory CategoryTheory.MonoidalCategory AlgebraicGeometry
open AlgebraicGeometry.Scheme AlgebraicGeometry.ProEtale Opposite

namespace WeilConjectures

variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime]
  (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (n : ℕ)

/-- The coefficient sheaf in degree zero, in the recorded intrinsic tensor structure.
Source: blueprint point-dualizing proof, opening paragraph
(blueprint: lem-coef-finite-point-internal-hom-evaluation). -/
def finitePointCoefficientUnit :=
  (finiteIntrinsicClosed l E (Spec (.of D.k)) n).monoidal.tensorUnit

/-- The identity exceptional object with the identity etale adjoint: nu^* R nu_* B.
The canonical coefficient realization changes presentations, not the site or coefficients.
Source: blueprint point-dualizing proof, opening paragraph
(blueprint: lem-coef-finite-point-internal-hom-evaluation). -/
def finitePointComparisonOmega :=
  (sfIntrinsicDerivedEquivalence (Spec (.of D.k))
    (Padic.coefficientExtensionRing l E (n + 1))).functor.obj
      (((comparisonLowerStar
        (ModuleCat.{u + 1} (ULift.{u + 1, u}
          (Padic.coefficientExtensionRing l E (n + 1))))
        (Spec (.of D.k))).rightDerivedFunctor ⋙
        (comparisonUpperStar
          (ModuleCat.{u + 1} (ULift.{u + 1, u}
            (Padic.coefficientExtensionRing l E (n + 1))))
          (Spec (.of D.k))).mapDerivedCategory).obj
        ((sfIntrinsicDerivedEquivalence (Spec (.of D.k))
          (Padic.coefficientExtensionRing l E (n + 1))).inverse.obj
          (finitePointCoefficientUnit D l E n)))

/-- The specified normalization is the comparison counit, followed by realization's counit.
Source: blueprint point-dualizing proof, opening paragraph
(blueprint: lem-coef-finite-point-internal-hom-evaluation). -/
def finitePointComparisonNormalization :
    finitePointComparisonOmega D l E n ⟶ finitePointCoefficientUnit D l E n :=
  (sfIntrinsicDerivedEquivalence (Spec (.of D.k))
    (Padic.coefficientExtensionRing l E (n + 1))).functor.map
      ((derivedComparisonAdjunction
        (ModuleCat.{u + 1} (ULift.{u + 1, u}
          (Padic.coefficientExtensionRing l E (n + 1))))
        (Spec (.of D.k))).counit.app
        ((sfIntrinsicDerivedEquivalence (Spec (.of D.k))
          (Padic.coefficientExtensionRing l E (n + 1))).inverse.obj
          (finitePointCoefficientUnit D l E n))) ≫
    (sfIntrinsicDerivedEquivalence (Spec (.of D.k))
      (Padic.coefficientExtensionRing l E (n + 1))).counitIso.hom.app
      (finitePointCoefficientUnit D l E n)

/-- Sheaf internal Hom into the identity dualizing object; this is the recorded
K-injective internal Hom, not a new duality functor.
Source: blueprint point-dualizing proof, second sentence
(blueprint: lem-coef-finite-point-internal-hom-evaluation). -/
def finitePointSheafDual
    (C : proEtaleDerivedCategory (Spec (.of D.k))
      (Padic.coefficientExtensionRing l E (n + 1))) :=
  (finiteIntrinsicDerivedInternalHom l E (Spec (.of D.k)) n).obj
    (op C, finitePointComparisonOmega D l E n)

/-- The actual evaluation pairing after point fibre, tensor comparison and normalization.
The finite-Tor witness merely permits using the recorded restricted tensor comparison.
Source: blueprint point-dualizing proof, second sentence
(blueprint: lem-coef-finite-point-internal-hom-evaluation). -/
def finitePointDualPairing (S : PointFiniteTensorData D l E n)
    (C : finiteTorConstructibleCategory l E (n + 1)
      (Nat.succ_le_succ (Nat.zero_le n)) (Spec (.of D.k)))
    (h : finiteTorConstructible l E (n + 1)
      (Nat.succ_le_succ (Nat.zero_le n)) (Spec (.of D.k))
      (finitePointSheafDual D l E n C.obj)) :=
  (pointFiniteTensorComparison D l E n S
    ⟨finitePointSheafDual D l E n C.obj, h⟩ C).inv ≫
    (pointFiniteSections D.k
      (Padic.coefficientExtensionRing l E (n + 1))).mapDerivedCategory.map
      ((finiteIntrinsicEvaluation l E (Spec (.of D.k)) n C.obj
        (finitePointComparisonOmega D l E n)) ≫ finitePointComparisonNormalization D l E n) ≫
    S.unitIso.hom

/-- The canonical evaluation transpose. The Koszul braiding puts the input first,
matching Mathlib's left-tensor internal-Hom convention.
Source: blueprint point-dualizing proof, second sentence
(blueprint: lem-coef-finite-point-internal-hom-evaluation). -/
def finitePointInternalHomKappa (S : PointFiniteTensorData D l E n)
    (C : finiteTorConstructibleCategory l E (n + 1)
      (Nat.succ_le_succ (Nat.zero_le n)) (Spec (.of D.k)))
    (h : finiteTorConstructible l E (n + 1)
      (Nat.succ_le_succ (Nat.zero_le n)) (Spec (.of D.k))
      (finitePointSheafDual D l E n C.obj)) :=
  MonoidalClosed.curry
    (((pointModuleDerivedBraiding
      (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E (n + 1)))).braiding
        ((finitePointFibreTensorSource D l E n).obj C)
        ((pointFiniteSections D.k
          (Padic.coefficientExtensionRing l E (n + 1))).mapDerivedCategory.obj
          (finitePointSheafDual D l E n C.obj))).hom ≫
      finitePointDualPairing D l E n S C h)

/-- The counit-normalized evaluation transpose is an isomorphism, naturally in C.
The tensor witness is constrained by the existing canonical model predicate; no
arbitrary comparison map or identification of the coefficient object is used.
Source: blueprint main-20261015, lem-pod-point-dualizing-complex.proof.md,
opening paragraph (blueprint: lem-coef-finite-point-internal-hom-evaluation).

Proof:
1. The extension absolute-value theorem, the valuation-ring DVR theorem and the
finite-quotient theorem make A finite. For the identity compactification etale
compact support and its normalized right adjoint are identity. Thus omega is
nu^* R nu_* B. Constant-ring comparison gives B = nu^* G. Bounded-below site
comparison makes the unit at G invertible; the triangle identity identifies the
counit at B as its inverse. Transport through intrinsic realization gives exactly
finitePointComparisonNormalization.
2. Constant-module realization is exact by module-presheaf sheafification, and
point sections is exact. Connected constant H0 identifies A with sections of B
by a -> a times 1. Point-sections reconstruction gives the natural isomorphism
L(Gamma C) -> C and the derived adjunction triangle identity.
3. Choose a K-flat flat-term model P for Gamma C and a K-injective model I for B.
Point-derived-Hom evaluation identifies Gamma Hom(LP,I) with Hom(P,Gamma I),
with differential dh = d_I h - (-1)^deg(h) h d_P. Normalize the target by the
specified counit and precompose with reconstruction. This gives an isomorphism
from Gamma RHom(C,omega) to RHom(Gamma C,A).
4. Finite constructible Hom on the zero-dimensional point puts RHom(C,B), hence
RHom(C,omega), in D^b_ctf. The recorded tensor comparison therefore applies.
On homogeneous x of degree i and h of degree j the signed evaluations agree:
both give (-1)^(ij) h(1 tensor x) in input-first convention. The reconstruction
triangle removes its extra unit. Uniqueness of the closed transpose identifies
the preceding isomorphism with finitePointInternalHomKappa. In the Hom-first
convention this gives the displayed equation with perfectTraceEvaluation.
5. Naturality of reconstruction and of the derived Hom comparison gives the
contravariant square for every derived morphism, including inverse quasi-isomorphisms.
The normalization is fixed independently of C. -/
theorem finitePointInternalHomEvaluation (hl : l ≠ D.p) :
    IsIso (finitePointComparisonNormalization D l E n) ∧
      ∃ S : PointFiniteTensorData D l E n,
        PointFiniteSourceConstraints D l E n S ∧
        PointFiniteTensorCanonical D l E n S ∧
        ∃ h : ∀ C : finiteTorConstructibleCategory l E (n + 1)
            (Nat.succ_le_succ (Nat.zero_le n)) (Spec (.of D.k)),
            finiteTorConstructible l E (n + 1)
              (Nat.succ_le_succ (Nat.zero_le n)) (Spec (.of D.k))
              (finitePointSheafDual D l E n C.obj),
          (∀ C, IsIso (finitePointInternalHomKappa D l E n S C (h C))) ∧
          (∀ (C C' : finiteTorConstructibleCategory l E (n + 1)
              (Nat.succ_le_succ (Nat.zero_le n)) (Spec (.of D.k))) (f : C ⟶ C'),
            (pointFiniteSections D.k
              (Padic.coefficientExtensionRing l E (n + 1))).mapDerivedCategory.map
                ((finiteIntrinsicDerivedInternalHom l E (Spec (.of D.k)) n).map
                  (Prod.mkHom f.hom.op (𝟙 (finitePointComparisonOmega D l E n)))) ≫
                finitePointInternalHomKappa D l E n S C (h C) =
              finitePointInternalHomKappa D l E n S C' (h C') ≫
                (MonoidalClosed.pre ((finitePointFibreTensorSource D l E n).map f)).app
                  (𝟙_ _)) ∧
          (∀ C,
            (finitePointInternalHomKappa D l E n S C (h C) ▷
              (finitePointFibreTensorSource D l E n).obj C) ≫
                DerivedCategory.perfectTraceEvaluation
                  ((finitePointFibreTensorSource D l E n).obj C) =
              finitePointDualPairing D l E n S C (h C)) := by
  sorry

end WeilConjectures
