/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CohomologyTransport.CondensedFiniteCohomologyTransport
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CohomologyTransport.CondensedGeometricFrobeniusTransport
public import WeilConjectures.PoincareDuality.CondensedFrobeniusOperators.FiniteStrictWeilComplex.TraceFormulaFiniteStrictWeilComplex
public import WeilConjectures.SmoothPurity.FiniteFieldDatum.SchemeFrobenius
public import WeilConjectures.SmoothPurity.FiniteFieldDatum.FrobeniusFactorization
public import WeilConjectures.AlgebraicGeometry.Morphisms.Frobenius
public import WeilConjectures.AlgebraicGeometry.SixFunctors.AbsoluteFrobeniusSite
public import WeilConjectures.AlgebraicGeometry.SixFunctors.FrobeniusTrivializationPullback
public import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantRingOperations
public import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantRingPullbackComparison
public import Mathlib.CategoryTheory.MorphismProperty.Limits
public import Mathlib.AlgebraicGeometry.Morphisms.Constructors
public import Mathlib.Topology.Homeomorph.Defs
public import WeilConjectures.Compactification.FiniteFieldDatum.FiniteFieldFiberSupplement
public import WeilConjectures.AlgebraicGeometry.AbsoluteFrobenius
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ModuleDerivedCategory
public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.Algebra.Algebra.Subalgebra.Lattice
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Tower
public import Mathlib.RingTheory.Spectrum.Prime.Homeomorph
public import Mathlib.RingTheory.TensorProduct.Maps
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.Data.Nat.Choose.Sum
public import Mathlib.RingTheory.WittVector.Frobenius
public import Mathlib.Tactic.Ring
public import WeilConjectures.AlgebraicGeometry.Morphisms.UniversalHomeomorphism.Algebra
public import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantRingMap
public import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantExact
public import WeilConjectures.AlgebraicGeometry.ProEtale.Canonical.ProEtaleCanonicalPullbackComposition
public import WeilConjectures.AlgebraicGeometry.Picard.KFlatResolutionIndependentCoefficients
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.AbsoluteFrobenius
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperLowerStar

/-!
# Normalized scheme/Galois comparison

Source: `literature/blueprint/latest/blueprint/part-duality-trace-formula/
sec-lefschetz-verdier/sec-frobenius/sk-def-sf-weil-complexes/prop-trf-scheme-galois-comparison.md`
(blueprint: prop-trf-scheme-galois-comparison).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false

-- Fix the native site size before synthesizing derived module instances.
attribute [-instance] WeilConjectures.integralOperationsSiteSmall
  WeilConjectures.integralReductionSiteEssentiallySmall
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.ProEtale
open scoped CategoryTheory.Obj
open scoped AlgebraicGeometry.ProEtale.CondensedRing.CachedModInstances
namespace WeilConjectures.CondensedFrobeniusOperators
open AlgebraicGeometry.ProEtale.CondensedRing
open AlgebraicGeometry.ProEtale.CondensedRing.CohomologyTransport
/-- Characteristic-p witness on the geometric fibre.
Source: `literature/blueprint/latest/blueprint/part-duality-trace-formula/
sec-lefschetz-verdier/sec-frobenius/
sk-def-sf-weil-complexes/prop-trf-scheme-galois-comparison.proof.md`
(blueprint: prop-trf-scheme-galois-comparison). -/
abbrev finiteFiberCharacteristic (F : WeilConjectures.FiniteFieldDatum.{u})
    (Y₀ : Over (Spec (CommRingCat.of F.k₀))) :=
  F.model_characteristic (pullback.fst Y₀.hom
    (Spec.map (CommRingCat.ofHom (algebraMap F.k₀ F.k))) ≫ Y₀.hom)

/-- The factorization used by the specified comparison, for every positive iterate.
Source: `literature/blueprint/latest/blueprint/part-duality-trace-formula/
sec-lefschetz-verdier/sec-frobenius/
sk-def-sf-weil-complexes/prop-trf-scheme-galois-comparison.proof.md`
(blueprint: prop-trf-scheme-galois-comparison).
Proof: cancel the arithmetic Galois power from absoluteFrobenius_factorization using
its inverse geometric Galois power; Iso.pow_hom_eq_pow identifies the resulting power. -/
theorem finiteComparisonFactorization (F : WeilConjectures.FiniteFieldDatum.{u})
    (Y₀ : Over (Spec (CommRingCat.of F.k₀))) [IsSeparated Y₀.hom]
    [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom] (m : ℕ) (hm : 1 ≤ m) :
    F.schemeFrobeniusIterate Y₀ m =
      (F.geometricFiber Y₀).left.iterateFrobenius F.prime
        (finiteFiberCharacteristic F Y₀) (F.a * m) ≫
      ((geometricFrobeniusGeometry F Y₀).h.pow m).hom := by
  sorry

/-- The normalized condensed comparison: the actual factorization compositor followed
by the relative-Frobenius trivialization at exponent a*m. No comparison is free data.
Source: `literature/blueprint/latest/blueprint/part-duality-trace-formula/
sec-lefschetz-verdier/sec-frobenius/
sk-def-sf-weil-complexes/prop-trf-scheme-galois-comparison.proof.md`
(blueprint: prop-trf-scheme-galois-comparison). -/
noncomputable def finiteSchemeGaloisComparisonFunctor
    (F : WeilConjectures.FiniteFieldDatum.{u})
    (Y₀ : Over (Spec (CommRingCat.of F.k₀))) [IsSeparated Y₀.hom]
    [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom]
    (ell : ℕ) [Fact ell.Prime] (E : Type u) [Field E]
    [Algebra (Padic ell) E] [FiniteDimensional (Padic ell) E]
    (n : ℕ) (_hn : 1 ≤ n)
    (m : ℕ) (hm : 1 ≤ m) :
    (L (finiteCoefficient ell E n) (F.schemeFrobeniusIterate Y₀ m)) ≅
      (L (finiteCoefficient ell E n)
        ((geometricFrobeniusGeometry F Y₀).h.pow m).hom) := by
  let Λ := finiteCoefficient ell E n
  let g := ((geometricFrobeniusGeometry F Y₀).h.pow m).hom
  let H := (F.geometricFiber Y₀).left.iterateFrobenius F.prime
    (finiteFiberCharacteristic F Y₀) (F.a * m)
  let t := Functor.leftDerivedFunctorIdIso
    (upperStarIterateFrobeniusIso Λ F.prime (finiteFiberCharacteristic F Y₀) (F.a * m))
  exact eqToIso (congrArg (L Λ) (finiteComparisonFactorization F Y₀ m hm)) ≪≫
    leftDerivedUpperStarComp Λ H g ≪≫
    Functor.isoWhiskerLeft (L Λ g) t ≪≫ Functor.rightUnitor _

/-- The normalized comparisons form the multiplicative positive-iterate family.
Source: `literature/blueprint/latest/blueprint/part-duality-trace-formula/
sec-lefschetz-verdier/sec-frobenius/
sk-def-sf-weil-complexes/prop-trf-scheme-galois-comparison.proof.md`.
(blueprint: prop-trf-scheme-galois-comparison).
Proof: relative Frobenius maps compose to the corresponding power map. Apply the
canonical inverse-image compositors and their associativity to the sectionwise
relative-Frobenius trivializations; their unit normalizations identify the result
with the trivialization at exponent a*(m+n). The two scheme powers add exponents. -/
theorem finiteSchemeGaloisComparison_add
    (F : WeilConjectures.FiniteFieldDatum.{u})
    (Y₀ : Over (Spec (CommRingCat.of F.k₀))) [IsSeparated Y₀.hom]
    [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom]
    (ell : ℕ) [Fact ell.Prime] (_hEll : ell ≠ F.p) (E : Type u) [Field E]
    [Algebra (Padic ell) E] [FiniteDimensional (Padic ell) E]
    (n : ℕ) (hn : 1 ≤ n) (m r : ℕ) (hm : 1 ≤ m) (hr : 1 ≤ r) :
    let Λ := finiteCoefficient ell E n
    let P := fun j => F.schemeFrobeniusIterate Y₀ j
    let G := fun j => ((geometricFrobeniusGeometry F Y₀).h.pow j).hom
    let κ := fun j hj => (finiteSchemeGaloisComparisonFunctor F Y₀ ell E n hn j hj).hom
    ∃ hP : P m ≫ P r = P (m + r), ∃ hG : G m ≫ G r = G (m + r),
      κ (m + r) (by omega) =
        eqToHom (congrArg (L Λ) hP.symm) ≫
        (leftDerivedUpperStarComp Λ (P m) (P r)).hom ≫
        Functor.whiskerLeft (L Λ (P r)) (κ m hm) ≫
        Functor.whiskerRight (κ r hr) (L Λ (G m)) ≫
        (leftDerivedUpperStarComp Λ (G m) (G r)).inv ≫
        eqToHom (congrArg (L Λ) hG) := by
  sorry

/-- Evaluation of the normalized natural comparison on a finite strict Weil carrier.
Source: `literature/blueprint/latest/blueprint/part-duality-trace-formula/
sec-lefschetz-verdier/sec-frobenius/
sk-def-sf-weil-complexes/prop-trf-scheme-galois-comparison.proof.md`.
(blueprint: prop-trf-scheme-galois-comparison). -/
noncomputable def finiteSchemeGaloisComparison
    (F : WeilConjectures.FiniteFieldDatum.{u})
    (Y₀ : Over (Spec (CommRingCat.of F.k₀))) [IsSeparated Y₀.hom]
    [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom]
    (ell : ℕ) [Fact ell.Prime] (_hEll : ell ≠ F.p) (E : Type u) [Field E]
    [Algebra (Padic ell) E] [FiniteDimensional (Padic ell) E]
    (n : ℕ) (hn : 1 ≤ n) (K : FiniteStrictWeilComplex F Y₀ ell E n hn)
    (m : ℕ) (hm : 1 ≤ m) :
    (L (finiteCoefficient ell E n) (F.schemeFrobeniusIterate Y₀ m)).obj K.carrier.obj ≅
      (L (finiteCoefficient ell E n)
        ((geometricFrobeniusGeometry F Y₀).h.pow m).hom).obj K.carrier.obj :=
  (finiteSchemeGaloisComparisonFunctor F Y₀ ell E n hn m hm).app K.carrier.obj

end WeilConjectures.CondensedFrobeniusOperators
