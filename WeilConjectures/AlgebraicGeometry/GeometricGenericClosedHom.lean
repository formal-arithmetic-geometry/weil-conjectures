/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.FunctionField
public import WeilConjectures.AlgebraicGeometry.Curve
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import WeilConjectures.AlgebraicGeometry.EtaleGenericStratumMate
public import WeilConjectures.SixFunctors.Etale.Derived.GenericFibre.InternalHom
public import WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.Proper
public import WeilConjectures.AlgebraicGeometry.GeometricGenericDirectImage
public import WeilConjectures.SixFunctors.Etale.Derived.Coefficients
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import WeilConjectures.AlgebraicGeometry.BoundedConstructibleComplexes
public import WeilConjectures.AlgebraicGeometry.EtaleTorAmplitude
public import WeilConjectures.AlgebraicGeometry.EtaleClosedAmbientAdjoint
public import WeilConjectures.Algebra.Homology.DerivedInternalHomMixedUniverses
public import WeilConjectures.Algebra.Homology.RingedDerivedClosedSymmetricMonoidal

import WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact
import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import WeilConjectures.AlgebraicGeometry.ConstructibleEtaleSetPullback
import WeilConjectures.AlgebraicGeometry.RingedTopoiCanonicalTensorPullbackOfUniverses
import WeilConjectures.AlgebraicGeometry.EtaleClosedSupportTriangle
import WeilConjectures.AlgebraicGeometry.FiniteTypeDirectImageConstructibility
import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
import WeilConjectures.ConstructibleSheaf.KernelCokernel
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import WeilConjectures.SixFunctors.Finite.BaseChange
import WeilConjectures.AlgebraicGeometry.OpenClosedRecollement
import WeilConjectures.SixFunctors.OpenClosed.ClosedImmersion
import WeilConjectures.SixFunctors.OpenClosed.Derived
import Mathlib.CategoryTheory.Functor.Derived.Adjunction
import Mathlib.CategoryTheory.Triangulated.Pretriangulated
import Mathlib.CategoryTheory.Yoneda
import WeilConjectures.AlgebraicGeometry.EtaleModuleSheavesGrothendieckAbelian
import WeilConjectures.CategoryTheory.GrothendieckAbelian.Sheaf
import WeilConjectures.Algebra.Homology.FlatCoverFunctor
import WeilConjectures.CategoryTheory.NativeDerivedHomSignedExact
import WeilConjectures.CategoryTheory.ExactDerivedHomComparisonShift
import WeilConjectures.Mathlib.CategoryTheory.Triangulated.Functor
import WeilConjectures.SixFunctors.FlatModel
import Mathlib.RingTheory.Flat.EquationalCriterion
import WeilConjectures.SixFunctors.EtaleLocallyClosedExtensionComparison
import WeilConjectures.AlgebraicGeometry.EtaleGenericImmersionProjection
import WeilConjectures.SixFunctors.Etale.Derived.Perfect.SitePerfect
import WeilConjectures.AlgebraicGeometry.FlatConstructibleTensor
import WeilConjectures.SixFunctors.BaseChange.Derived

/-! # Geometric generic closed-exceptional and internal-Hom comparisons

Source: literature/blueprint/latest/blueprint/sec-six-functors/
sk-lem-pd-generic-restriction/det-pd-generic-closed-hom.md
(blueprint: det-pd-generic-closed-hom).

The ambient exceptional restriction is the right adjoint of ordinary closed direct image.
The comparison is its mate of inverse closed exchange. The internal-Hom comparison is the
existing tensor-adjoint of pulled-back evaluation; right-ordered evaluation uses the
existing signed derived symmetry.

## Main definitions

- `closedDerivedDirectImageExchangeIso`: the canonical closed direct-image exchange.
- `closedAmbientUpperShriekComparison`: its exceptional-adjoint mate.

## Main statements

- `geometricGenericClosedHom`: invertibility, naturality and evaluation normalization.
-/

set_option autoImplicit false

@[expose] public section

universe u

open CategoryTheory Limits Opposite
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

/-- Canonical closed direct-image exchange on the entire ordinary derived category.
The isomorphism is the existing base-change map, whose invertibility follows from proper
base change for torsion coefficients; a finite ring is additively torsion.
Source: blueprint det-pd-generic-closed-hom, part (1), canonical closed exchange
(blueprint: det-pd-generic-closed-hom). -/
noncomputable def closedDerivedDirectImageExchangeIso
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {Z X Z' X' : Scheme.{u}} {i : Z ⟶ X} {i' : Z' ⟶ X'}
    {gZ : Z' ⟶ Z} {gX : X' ⟶ X} [IsClosedImmersion i]
    (sq : IsPullback gZ i' i gX) :
    R(lowerStar (ModuleCat.{u + 1} A) i) ⋙ L(upperStar (ModuleCat.{u + 1} A) gX) ≅
      L(upperStar (ModuleCat.{u + 1} A) gZ) ⋙ R(lowerStar (ModuleCat.{u + 1} A) i') :=
  haveI := isIso_derivedBaseChangeMap_of_isProper_of_isAddTorsion_ring A
    isAddTorsion_of_finite sq
  asIso (derivedBaseChangeMap (ModuleCat.{u + 1} A) sq.toCommSq)

/-- The actual comparison `gZ* Ri! → Ri'! gX*`, obtained by transposing inverse closed
exchange followed by the pulled-back exceptional counit. The adjoints are exactly those
of lem-exc-closed-ambient; no arbitrary comparison or isomorphism is chosen.
Source: blueprint det-pd-generic-closed-hom, part (1) and Evaluation
(blueprint: det-pd-generic-closed-hom). -/
noncomputable def closedAmbientUpperShriekComparison
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {Z X Z' X' : Scheme.{u}} {i : Z ⟶ X} {i' : Z' ⟶ X'}
    {gZ : Z' ⟶ Z} {gX : X' ⟶ X} [IsClosedImmersion i] [IsClosedImmersion i']
    (sq : IsPullback gZ i' i gX) :
    (R(lowerStar (ModuleCat.{u + 1} A) i)).rightAdjoint ⋙
        L(upperStar (ModuleCat.{u + 1} A) gZ) ⟶
      L(upperStar (ModuleCat.{u + 1} A) gX) ⋙
        (R(lowerStar (ModuleCat.{u + 1} A) i')).rightAdjoint :=
  mateEquiv
    (Adjunction.ofIsLeftAdjoint (R(lowerStar (ModuleCat.{u + 1} A) i)))
    (Adjunction.ofIsLeftAdjoint (R(lowerStar (ModuleCat.{u + 1} A) i')))
    (closedDerivedDirectImageExchangeIso A sq).inv

/-- Geometric generic restriction commutes with closed exceptional restriction and with
internal Hom having bounded constructible finite-Tor first argument. Both canonical maps
are natural and satisfy the displayed exceptional-counit and tensor-evaluation identities.
Source: blueprint sec-six-functors/sk-lem-pd-generic-restriction,
det-pd-generic-closed-hom, parts (1), (2), Evaluation
(blueprint: det-pd-generic-closed-hom).

Proof in words:
1. Exact inverse image commutes with cohomology and pulls finite locally constant
   stratifications back. Its canonical derived tensor comparison is invertible.
2. The supported localization triangle, finite-type direct-image constructibility, the
   cohomology long exact sequence and constructible Serre closure show that Ri!M is
   bounded constructible; finite direct image reflects this property.
3. Pull back that triangle. Finite closed exchange identifies its first vertex, while
   det-pd-generic-direct-image for the complementary open immersion identifies the third.
   The first arrow is inverse closed exchange followed by pulled-back exceptional counit.
4. Closed direct image is fully faithful. Open restriction kills its image; the derived
   open adjunction gives vanishing of Hom from closed-supported objects into the third
   vertex and its shift. Hom exactness makes Hom(V,beta) bijective for every V. Yoneda
   proves beta invertible, with the stated counit normalization.
5. Fix M. Signed exactness of internal Hom and comparison-shift compatibility make the
   first arguments for which rho is invertible a thick class. The flat-model generation
   theorem reduces to t!P, with P lisse finite projective on a locally closed stratum.
6. Factor t as closed then open. Part (1) and open restriction give the exceptional
   comparison gamma. The composite adjunction counit gives its evaluation normalization.
7. P is site-perfect and dualizable. The dualizable Hom comparison identifies Hom(P,N)
   with P-dual tensor N; flat constructible tensor makes this bounded constructible for
   N = Rt!M. Thus the direct-image theorem applies to this stratum Hom.
8. Use the evaluation-normalized stratum-Hom adjunction, generic direct-image exchange,
   the dualizable Hom comparison, and gamma to form the generator isomorphism.
9. Transpose that composite. Substitute the stratum evaluation identity, the counit-mate
   description of ordinary exchange, the defining rho evaluation identity, the gamma
   counit equation and projection base-change compatibility. The result is pulled-back
   evaluation after tensor comparison, so uniqueness of transposition identifies it with
   the actual rho. Thick generation now proves invertibility for every finite-Tor K.
10. The mate and tensor transpose definitions give both evaluation equations and
    naturality, including contravariant naturality in K.
-/
theorem geometricGenericClosedHom
    {k : Type u} [Field k] {B : Scheme.{u}} [IsIntegral B]
    (aB : B ⟶ Spec (CommRingCat.of k)) [IsCurve aB] [Smooth aB]
    (Ω : Type u) [Field Ω] [Algebra B.functionField Ω] [IsAlgClosure B.functionField Ω]
    (A : Type (u + 1)) [CommRing A] [Finite A]
    (_hA : ∃ n : ℕ, 0 < n ∧ (n : A) = 0 ∧ IsUnit (n : k))
    {X Xη Z Zη : Scheme.{u}} (x : X ⟶ B)
    [LocallyOfFiniteType x] [QuasiCompact x]
    (gX : Xη ⟶ X) (pX : Xη ⟶ Spec (CommRingCat.of Ω))
    (_sqX : IsPullback gX pX x
      (Spec.map (CommRingCat.ofHom (algebraMap B.functionField Ω)) ≫
        B.fromSpecStalk (genericPoint B)))
    (i : Z ⟶ X) (iη : Zη ⟶ Xη) (gZ : Zη ⟶ Z)
    [IsClosedImmersion i] [IsClosedImmersion iη] (sq : IsPullback gZ iη i gX)
    (M : DerivedCategoryModule A X) (_hM : DerivedCategory.isBoundedConstructible A X M) :
    IsIso ((closedAmbientUpperShriekComparison A sq).app M) ∧
    (∀ (K : DerivedCategoryModule A X), DerivedCategory.isBoundedConstructible A X K →
      ∀ a b : ℤ, a ≤ b → DerivedCategory.hasTorAmplitudeIn A X a b K →
        IsIso (derivedHomUpperStarComparison (ModuleCat.{u + 1} A) gX K M)) ∧
    (∀ (N N' : DerivedCategoryModule A X) (f : N ⟶ N'),
      (L(upperStar (ModuleCat.{u + 1} A) gZ)).map
          ((R(lowerStar (ModuleCat.{u + 1} A) i)).rightAdjoint.map f) ≫
          (closedAmbientUpperShriekComparison A sq).app N' =
        (closedAmbientUpperShriekComparison A sq).app N ≫
          (R(lowerStar (ModuleCat.{u + 1} A) iη)).rightAdjoint.map
            ((L(upperStar (ModuleCat.{u + 1} A) gX)).map f)) ∧
    (∀ (K K' N N' : DerivedCategoryModule A X) (f : K' ⟶ K) (h : N ⟶ N'),
      (L(upperStar (ModuleCat.{u + 1} A) gX)).map
          (((derivedHom (ModuleCat.{u + 1} A) X).map f.op).app N ≫
            ((derivedHom (ModuleCat.{u + 1} A) X).obj (op K')).map h) ≫
          derivedHomUpperStarComparison (ModuleCat.{u + 1} A) gX K' N' =
        derivedHomUpperStarComparison (ModuleCat.{u + 1} A) gX K N ≫
          ((derivedHom (ModuleCat.{u + 1} A) Xη).map
            ((L(upperStar (ModuleCat.{u + 1} A) gX)).map f).op).app
              ((L(upperStar (ModuleCat.{u + 1} A) gX)).obj N) ≫
          ((derivedHom (ModuleCat.{u + 1} A) Xη).obj
            (op ((L(upperStar (ModuleCat.{u + 1} A) gX)).obj K'))).map
              ((L(upperStar (ModuleCat.{u + 1} A) gX)).map h)) ∧
    ((closedDerivedDirectImageExchangeIso A sq).hom.app
        ((R(lowerStar (ModuleCat.{u + 1} A) i)).rightAdjoint.obj M) ≫
      (R(lowerStar (ModuleCat.{u + 1} A) iη)).map
        ((closedAmbientUpperShriekComparison A sq).app M) ≫
      (Adjunction.ofIsLeftAdjoint (R(lowerStar (ModuleCat.{u + 1} A) iη))).counit.app
        ((L(upperStar (ModuleCat.{u + 1} A) gX)).obj M) =
      (L(upperStar (ModuleCat.{u + 1} A) gX)).map
        ((Adjunction.ofIsLeftAdjoint (R(lowerStar (ModuleCat.{u + 1} A) i))).counit.app M)) ∧
    (∀ (K : DerivedCategoryModule A X),
      derivedTensorHom (ModuleCat.{u + 1} A)
          (derivedHomUpperStarComparison (ModuleCat.{u + 1} A) gX K M)
          (𝟙 ((L(upperStar (ModuleCat.{u + 1} A) gX)).obj K)) ≫
        immersionHomEvaluation A Xη ((L(upperStar (ModuleCat.{u + 1} A) gX)).obj K)
          ((L(upperStar (ModuleCat.{u + 1} A) gX)).obj M) =
      inv (((leftDerivedUpperStarTensorComparison (ModuleCat.{u + 1} A) gX).app
          (((derivedHom (ModuleCat.{u + 1} A) X).obj (op K)).obj M)).app K) ≫
        (L(upperStar (ModuleCat.{u + 1} A) gX)).map (immersionHomEvaluation A X K M)) := by
  sorry

end AlgebraicGeometry.Etale
