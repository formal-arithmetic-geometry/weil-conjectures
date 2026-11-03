/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Compactification.FiniteFieldDatum.FiniteFieldFiberSupplement
public import WeilConjectures.SixFunctors.Finite.FiniteTorAmplitude
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleTorAmplitude
public import WeilConjectures.AlgebraicGeometry.Intrinsic.IntrinsicFiniteTorsionConstructibility
public import WeilConjectures.SmoothPurity.Supporting.ConstructibleIntervalsUnordered
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SmoothPurity.SitePerfectComplex
public import WeilConjectures.SmoothPurity.Sf.SfIntegralConstructible
public import WeilConjectures.SmoothPurity.Sf.SfDerivedComplete
public import Mathlib.Topology.KrullDimension
public import Mathlib.AlgebraicGeometry.AffineSpace
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Constructible
public import WeilConjectures.SmoothPurity.Supporting.Coefficient.IntrinsicCoefficientTwists

public import WeilConjectures.SmoothPurity.Derived.DerivedPullbackTensorHom
public import WeilConjectures.AlgebraicGeometry.Sf.SfFiniteExceptionalInverseImage
public import WeilConjectures.SmoothPurity.Sf.SfDerivedDirectImage

public import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantDerivedDirectImage
public import WeilConjectures.SixFunctors.Sf.SfIntegralReductionTowerSupplement
public import WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
public import WeilConjectures.AlgebraicGeometry.Sf.SfCompactSupportRestrictionOfScalars
public import WeilConjectures.AlgebraicGeometry.Finite.Coefficient.FiniteCoefficientDirectImage
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
public import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology
public import Mathlib.CategoryTheory.Adjunction.Additive
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasLeftKanExtension
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasSheafify
public import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Proetale
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Continuous
public import WeilConjectures.AlgebraicGeometry.Sf.SfIntrinsicCompactSupport
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.Algebra.Category.ModuleCat.AB
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Defs
public import WeilConjectures.AlgebraicGeometry.ProEtaleInverseImage
public import WeilConjectures.SmoothPurity.ProEtaleWeaklyEtaleLocalization
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.OpenImmersion
public import WeilConjectures.CategoryTheory.LocalizedModuleExactForSystems
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import WeilConjectures.AlgebraicGeometry.FiniteEtaleEtaleLocalSplit
public import WeilConjectures.CategoryTheory.ExtensionByZeroPresheaf
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.HomCoverGluing
public import WeilConjectures.AlgebraicGeometry.Sf.SfIntrinsicRealizationTransport
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Adjunction
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.MapDerivedCategory
public import Mathlib.Algebra.CharP.CharAndCard
public import Mathlib.Algebra.CharP.Invertible
public import WeilConjectures.AlgebraicGeometry.Finite.Coefficient.FiniteCoefficientReductionFlatModel
public import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantExact
public import WeilConjectures.AlgebraicGeometry.ProEtale.Ring.ProEtaleRingSheafChangeAdjunctionSupplement
public import WeilConjectures.AlgebraicGeometry.WeilSheaf.ProfiniteCoefficientInverseImageSupplement
public import Mathlib.CategoryTheory.Adjunction.Mates
public import WeilConjectures.SmoothPurity.Derived.DerivedScalarExtensionRestrictionAdjunctionSupplement
public import WeilConjectures.AlgebraicGeometry.ProEtale.Bounded.ProEtaleBoundedConstructibleTriangulated
public import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantModuleConstructibility
public import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantModulePullbackEncoding
public import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantRingOperations
public import WeilConjectures.ConstructibleSheaf.Pullback
public import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantOpenSquareExchange
public import WeilConjectures.AlgebraicGeometry.Intrinsic.IntrinsicTorAmplitudeTransport
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Stability
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.FlatModuleCat
public import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantRingMap
public import WeilConjectures.AlgebraicGeometry.Scalar.ScalarExtensionFunctor
public import WeilConjectures.AlgebraicGeometry.ExceptionalCoefficients.ExceptionalCoefficientComparison
public import WeilConjectures.SixFunctors.Integral.IntegralConstructibleInternalHom
public import WeilConjectures.SixFunctors.Integral.IntegralDualizing
public import WeilConjectures.AlgebraicGeometry.Finite.FiniteStageVerdierBiduality
public import WeilConjectures.AlgebraicGeometry.Ambient.AmbientExceptionalRightAdjoint

public import WeilConjectures.AlgebraicGeometry.ProEtale.Intrinsic.ProEtaleIntrinsicExtensionByZeroExact
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import WeilConjectures.Compactification.Refinement
public import WeilConjectures.Compactification.RefinementCategory
import WeilConjectures.SmoothPurity.Finite.FiniteTorAmplitudeSites
import WeilConjectures.SmoothPurity.Compact.CompactSupportCoefficientTransition
import WeilConjectures.SmoothPurity.Sf.SfDerivedCompleteLegacyComparison
import WeilConjectures.SixFunctors.Integral.IntegralResidueTor
import all WeilConjectures.SixFunctors.Integral.IntegralVerdier
import WeilConjectures.SixFunctors.FiniteExceptional.FiniteExceptional
import all WeilConjectures.AlgebraicGeometry.Intrinsic.IntrinsicFiniteTorsionConstructibility
import all WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantExact
import all WeilConjectures.AlgebraicGeometry.ProEtaleInverseImage
import all WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
import all WeilConjectures.AlgebraicGeometry.ProEtale.Finite.ProEtaleFiniteCoefficientDirectImage
import all WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantRingOperations
import all WeilConjectures.AlgebraicGeometry.Sf.SfIntrinsicRealizationTransport
import all WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import WeilConjectures.AlgebraicGeometry.ProEtale.Bounded.ProEtaleBoundedConstructibleTriangulated
import WeilConjectures.SixFunctors.Supporting.PullbackTorAmplitude
import WeilConjectures.AlgebraicGeometry.ProEtale.Finite.ProEtaleFiniteCoefficientDirectImageSupplement
import WeilConjectures.SixFunctors.Finite.FiniteConstructibleHom
import WeilConjectures.AlgebraicGeometry.Picard.IntrinsicSitePerfectHomWindow
import WeilConjectures.AlgebraicGeometry.Finite.Coefficient.FiniteCoefficientTensorCtf
import WeilConjectures.CategoryTheory.Ringed.Tensor.RingedTensorComparisonExtension
import WeilConjectures.Algebra.Homology.ProperBaseChange.KFlatResolutionGeneral
import WeilConjectures.CategoryTheory.Ringed.RingedDerivedClosedSymmetricMonoidal
import WeilConjectures.SixFunctors.IntegralVerdier.FiniteIntrinsicVerdierBounds
import WeilConjectures.SixFunctors.IntegralVerdier.FiniteIntrinsicVerdierBiduality
import WeilConjectures.SixFunctors.IntegralVerdier.IntegralVerdierSignedCalculus
import WeilConjectures.CategoryTheory.RingedHomUniverses.RingedInternalHomExactUniverses
import all WeilConjectures.SixFunctors.Integral.IntegralOperationsPreserveConstructible
import WeilConjectures.ProperBaseChange.IntegralFinitePullbackComposition
import WeilConjectures.SmoothPurity.Compact.CompactSupportRepresentativeIndependence
import WeilConjectures.SmoothPurity.Sf.SfIntegralConstructibleTriangulated
public import WeilConjectures.SmoothPurity.Supporting.LegacySitePerfectComplex
public import Mathlib.CategoryTheory.Adjunction.Unique
public import WeilConjectures.AlgebraicGeometry.ExplicitExceptionalPreservation
public import WeilConjectures.AlgebraicGeometry.Finite.Compact.FiniteCompactSupportScalarComparison
public import WeilConjectures.AlgebraicGeometry.Sf.SfFullCohomologicalDimension
public import WeilConjectures.SixFunctors.Coef.CoefFiniteHomSiteDescent
public import WeilConjectures.SixFunctors.Etale.Derived.WeilComplexDual
public import WeilConjectures.SixFunctors.Etale.EtaleGeometricBiduality
public import WeilConjectures.SixFunctors.Finite.Coefficient.FiniteCoefficientHomChange

/-! # Stability of the constructible finite-Tor domains

Source: current blueprint, sec-six-functors/sk-thm-sf-kunneth-verdier,
`thm-sf-ctf-stability` (blueprint: thm-sf-ctf-stability).
Positive coefficient exponents are written as `n + 1`.

## Main statements

- `finiteTor_stability`: pullback, tensor, general Hom, and both direct images.
- `finiteTor_stability_exceptional_verdier`: exceptional preservation and dimension bounds.
- `finiteTor_stability_constructible_adjunction`: the constructible exceptional adjunction.
- `finiteTor_stability_origin`: the origin counterexample to a dimension-free Hom bound.
- `finiteTor_stability_quotients`, `finiteTor_stability_geometric_quotients`: finite change.
- `finiteTor_stability_integral_hom`, `finiteTor_stability_integral_verdier`: integral duality.
- `finiteTor_stability_integral_adjunction`: integral exceptional adjunction and reductions.
- `finiteTor_stability_rational`, `finiteTor_stability_algebraicClosure`: coefficient passage.
-/

@[expose] public section


set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types true

universe u v

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme

namespace WeilConjectures

section Finite

variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
  (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
  (n : ℕ)


/-- Geometric Verdier duality with the actual comparison-defined exceptional
inverse image of the constant coefficient unit along the structure morphism.
Source: blueprint (vi) (blueprint: thm-sf-ctf-stability). -/
noncomputable def sfStabilityFiniteVerdier
    (X : Scheme.{u}) (aX : X ⟶ Spec (.of D.k))
    [IsSeparated aX] [LocallyOfFiniteType aX] [QuasiCompact aX] :
    ((proEtaleDerivedCategory X (Padic.coefficientExtensionRing l E (n + 1))))ᵒᵖ ⥤
      (proEtaleDerivedCategory X (Padic.coefficientExtensionRing l E (n + 1))) :=
  Prod.sectL ((proEtaleDerivedCategory X (Padic.coefficientExtensionRing l E (n + 1))))ᵒᵖ
    ((ProEtale.sfFiniteExceptional (Padic.coefficientExtensionRing l E (n + 1))
      (NagataCompactification aX)).obj
      (finiteIntrinsicClosed l E (Spec (.of D.k)) n).monoidal.tensorUnit) ⋙
        (finiteIntrinsicDerivedInternalHom l E X n)

private theorem sfStabilityTorOfIso
    (X : Scheme.{u}) (A : Type u) [CommRing A]
    {K L : proEtaleDerivedCategory X A} (e : K ≅ L) (a b : ℤ)
    (ht : HasProEtaleTorAmplitude X A K a b) : HasProEtaleTorAmplitude X A L a b := by
  refine ⟨ht.1, ?_⟩
  intro M P hM f hf hP N i hi
  exact ht.2 M P (hM.map (fun j ↦ j ≪≫ e.symm)) f hf hP N i hi

private theorem sfStabilityFiniteTorOfIso
    (X : Scheme.{u})
    {K L : proEtaleDerivedCategory X (Padic.coefficientExtensionRing l E (n + 1))}
    (e : K ≅ L) (hK : finiteTorConstructible l E (n + 1) (by omega) X K) :
    finiteTorConstructible l E (n + 1) (by omega) X L := by
  let : Finite (Padic.coefficientExtensionRing l E (n + 1)) :=
    Padic.finite_coefficientExtensionRing l E (n + 1) (by omega)
  have : ObjectProperty.IsClosedUnderIsomorphisms
      (intrinsicFiniteTorsionConstructible l E (n + 1) (by omega) X) :=
    (proEtale_bounded_constructible_isTriangulated X
      (Padic.coefficientExtensionRing l E (n + 1))).1
  refine ⟨ObjectProperty.prop_of_iso _ e hK.1, ?_⟩
  obtain ⟨a, b, ht⟩ := hK.2
  refine ⟨a, b, ht.1, ?_⟩
  intro M P hM f hf hP N i hi
  exact ht.2 M P (hM.map (fun j ↦ j ≪≫ e.symm)) f hf hP N i hi

private noncomputable def sfStabilityClosedUnitIso
    (X : Scheme.{u}) :
    (finiteIntrinsicClosed l E X n).monoidal.tensorUnit ≅
      (DerivedCategory.singleFunctor (scalarReductionTarget.{u, u} l E X n) 0).obj
        (SheafOfModules.unit (integralCoefficientSheaf l E X n)) := by
  let S := finiteIntrinsicClosed l E X n
  let h := ringedDerived_closed_symmetric_monoidal.{u + 1, u, u, u + 2}
    (ProEt.topology X) (integralCoefficientCommRingSheaf l E X n)
  let S₀ := h.choose
  let h₀ := h.choose_spec.choose_spec.choose_spec.some
  let U := S₀.monoidal.tensorUnit
  let e := (S.adjunction U).leftAdjointUniq (S₀.adjunction U)
  exact (S₀.monoidal.rightUnitor S.monoidal.tensorUnit).symm ≪≫
    (e.app S.monoidal.tensorUnit).symm ≪≫ S.monoidal.leftUnitor U ≪≫ h₀.unitIso

set_option backward.isDefEq.respectTransparency.types false in
private noncomputable def sfStabilityVerdierComparison
    (X : Scheme.{u}) [X.Over (Spec (.of D.k))]
    [IsSeparated (X ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))] :
    sfStabilityFiniteVerdier D l E n X (X ↘ Spec (.of D.k)) ≅
      FiniteExceptional.dual l E D X n := by
  let e := (ProEtale.sfFiniteExceptional (Padic.coefficientExtensionRing l E (n + 1))
    (NagataCompactification (X ↘ Spec (.of D.k)))).mapIso
      (sfStabilityClosedUnitIso l E n (Spec (.of D.k)))
  exact NatIso.ofComponents
    (fun K ↦ (finiteIntrinsicDerivedInternalHom l E X n).mapIso (Iso.prod (Iso.refl K) e))
    (by
      intro K L f
      change (finiteIntrinsicDerivedInternalHom l E X n).map _ ≫
        (finiteIntrinsicDerivedInternalHom l E X n).map _ =
          (finiteIntrinsicDerivedInternalHom l E X n).map _ ≫
            (finiteIntrinsicDerivedInternalHom l E X n).map _
      rw [← Functor.map_comp, ← Functor.map_comp]
      congr 1
      ext <;> simp)

include hl in
/-- Clauses (i)--(iv), including the general and the site-perfect Hom intervals.
The same assertion includes every ordered input interval; Tor already includes
its ordering condition. No site-perfectness is assumed in the general Hom clause.
Source: current blueprint (blueprint: thm-sf-ctf-stability).

Proof: pullback preserves the input interval. Tensor adds the intervals using
bounded flat models. Geometric Verdier duality gives constructibility of general
internal Hom and the dimension-dependent interval. A local bounded finite-projective
model for a site-perfect first input gives the sharper reversed interval and the
coefficient-dual tensor formula by evaluation. Finite direct-image vanishing in
degrees above twice the source dimension gives (iii). Factor a compactification
as an open immersion followed by a proper morphism; extension by zero preserves
constructibility and Tor bounds, and (iii) applies to the proper factor.
The inputs are lem-sf-pullback-tor-amplitude, lem-sf-tensor-ctf,
cor-weil-finite-constructible-hom, lem-sfb-ringed-site-perfect-duality,
lem-sf-site-perfect-tor-window, lem-sf-flat-model,
thm-sf-direct-image-tor-amplitude, cor-sf-direct-image-ctf-proetale,
lem-trf-open-ctf, and prop-compactification-coherence-detailed. -/
theorem finiteTor_stability
    (X Y : Over (Spec (.of D.k)))
    [IsSeparated X.hom] [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
    [IsSeparated Y.hom] [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom]
    (f : X ⟶ Y) [IsSeparated f.left] [LocallyOfFiniteType f.left] [QuasiCompact f.left] :
    (∀ K : (proEtaleDerivedCategory Y.left (Padic.coefficientExtensionRing l E (n + 1))),
      (finiteTorConstructible l E (n + 1) (Nat.succ_le_succ (Nat.zero_le n)) Y.left) K →
      (finiteTorConstructible l E (n + 1) (Nat.succ_le_succ (Nat.zero_le n)) X.left)
        ((finiteDerivedPullback l E n f.left).obj K)) ∧
    (∀ K L : (proEtaleDerivedCategory X.left (Padic.coefficientExtensionRing l E (n + 1))),
      (finiteTorConstructible l E (n + 1) (Nat.succ_le_succ (Nat.zero_le n)) X.left) K →
      (finiteTorConstructible l E (n + 1) (Nat.succ_le_succ (Nat.zero_le n)) X.left) L →
      (finiteTorConstructible l E (n + 1) (Nat.succ_le_succ (Nat.zero_le n)) X.left)
        (((finiteIntrinsicDerivedTensor l E X.left n)).obj (K, L)) ∧
      ∀ a b c d : ℤ, (HasProEtaleTorAmplitude X.left (Padic.coefficientExtensionRing l E (n + 1)))
        K a b → (HasProEtaleTorAmplitude X.left (Padic.coefficientExtensionRing l E (n + 1))) L c
        d →
        (HasProEtaleTorAmplitude X.left (Padic.coefficientExtensionRing l E (n + 1)))
          (((finiteIntrinsicDerivedTensor l E X.left n)).obj (K, L)) (a + c) (b + d)) ∧
    (∀ K L : (proEtaleDerivedCategory X.left (Padic.coefficientExtensionRing l E (n + 1))),
      (finiteTorConstructible l E (n + 1) (Nat.succ_le_succ (Nat.zero_le n)) X.left) K →
      (finiteTorConstructible l E (n + 1) (Nat.succ_le_succ (Nat.zero_le n)) X.left) L →
      (finiteTorConstructible l E (n + 1) (Nat.succ_le_succ (Nat.zero_le n)) X.left)
        (((finiteIntrinsicDerivedInternalHom l E X.left n)).obj (op K, L)) ∧
      (∀ (a b c d : ℤ) (m : ℕ),
        topologicalKrullDim X.left ≤ (m : WithBot ℕ∞) →
        (HasProEtaleTorAmplitude X.left (Padic.coefficientExtensionRing l E (n + 1))) K a b →
          (HasProEtaleTorAmplitude X.left (Padic.coefficientExtensionRing l E (n + 1))) L c d →
        (HasProEtaleTorAmplitude X.left (Padic.coefficientExtensionRing l E (n + 1)))
          (((finiteIntrinsicDerivedInternalHom l E X.left n)).obj (op K, L))
          (c - b - 2 * (m : ℤ)) (d - a + 2 * (m : ℤ))) ∧
      (IsFiniteCoefficientSitePerfect l E X.left n K →
        (Nonempty (((finiteIntrinsicDerivedTensor l E X.left n)).obj
          (((finiteIntrinsicDerivedInternalHom l E X.left n)).obj (op K, (finiteIntrinsicClosed l
            E X.left n).monoidal.tensorUnit), L) ≅
            ((finiteIntrinsicDerivedInternalHom l E X.left n)).obj (op K, L))) ∧
        ∀ a b c d : ℤ, (HasProEtaleTorAmplitude X.left (Padic.coefficientExtensionRing l E (n +
          1))) K a b → (HasProEtaleTorAmplitude X.left (Padic.coefficientExtensionRing l E (n +
          1))) L c d →
          (HasProEtaleTorAmplitude X.left (Padic.coefficientExtensionRing l E (n + 1)))
            (((finiteIntrinsicDerivedInternalHom l E X.left n)).obj (op K, L)) (c - b) (d - a))) ∧
    (∀ K : (proEtaleDerivedCategory X.left (Padic.coefficientExtensionRing l E (n + 1))),
      (finiteTorConstructible l E (n + 1) (Nat.succ_le_succ (Nat.zero_le n)) X.left) K →
      (finiteTorConstructible l E (n + 1) (Nat.succ_le_succ (Nat.zero_le n)) Y.left)
        ((proEtaleConstantDerivedDirectImage f.left (Padic.coefficientExtensionRing l E (n +
        1))).obj K) ∧
      ∀ (a b : ℤ) (d : ℕ), topologicalKrullDim X.left ≤ (d : WithBot ℕ∞) →
        (HasProEtaleTorAmplitude X.left (Padic.coefficientExtensionRing l E (n + 1))) K a b →
        (HasProEtaleTorAmplitude Y.left (Padic.coefficientExtensionRing l E (n + 1)))
          ((proEtaleConstantDerivedDirectImage f.left (Padic.coefficientExtensionRing l E (n +
          1))).obj K)
          a (b + 2 * (d : ℤ))) ∧
    (∀ (c : Compactification f.left) (K : (proEtaleDerivedCategory X.left
      (Padic.coefficientExtensionRing l E (n + 1)))), (finiteTorConstructible l E (n + 1)
      (Nat.succ_le_succ (Nat.zero_le n)) X.left) K →
      (finiteTorConstructible l E (n + 1) (Nat.succ_le_succ (Nat.zero_le n)) Y.left)
        ((sfIntrinsicCompactSupport c (Padic.coefficientExtensionRing l E (n + 1))).obj K))
        := by
  let : X.left.Over (Spec (.of D.k)) := ⟨X.hom⟩
  let : Y.left.Over (Spec (.of D.k)) := ⟨Y.hom⟩
  let : f.left.IsOver (Spec (.of D.k)) := ⟨Over.w f⟩
  have : LocallyOfFiniteType (X.left ↘ Spec (.of D.k)) := ‹LocallyOfFiniteType X.hom›
  have : QuasiCompact (X.left ↘ Spec (.of D.k)) := ‹QuasiCompact X.hom›
  have : IsSeparated (X.left ↘ Spec (.of D.k)) := ‹IsSeparated X.hom›
  have : LocallyOfFiniteType (Y.left ↘ Spec (.of D.k)) := ‹LocallyOfFiniteType Y.hom›
  have : QuasiCompact (Y.left ↘ Spec (.of D.k)) := ‹QuasiCompact Y.hom›
  have : IsSeparated (Y.left ↘ Spec (.of D.k)) := ‹IsSeparated Y.hom›
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro K hK
    exact sfStabilityFiniteTorOfIso l E n X.left
      ((sfStabilityPullbackComparison l E n f.left).app K)
      (sf_pullback_finiteTorConstructible D l hl E (n + 1) (by omega) X Y f K hK)
  · intro K L hK hL
    classical
    let A := Padic.coefficientExtensionRing l E (n + 1)
    let R := proEtaleConstantRing X.left A
    let C := proEtaleRingModules X.left R
    let : HasDerivedCategory C := HasDerivedCategory.standard C
    let Kc := (DerivedCategory.Q (C := C)).objPreimage K
    let Lc := (DerivedCategory.Q (C := C)).objPreimage L
    let eK := (DerivedCategory.Q (C := C)).objObjPreimageIso K
    let eL := (DerivedCategory.Q (C := C)).objObjPreimageIso L
    have hKc := sfStabilityFiniteTorOfIso l E n X.left eK.symm hK
    have hLc := sfStabilityFiniteTorOfIso l E n X.left eL.symm hL
    obtain ⟨P, g, hP, _, hg, _⟩ := CochainComplex.exists_isKFlatResolutionGeneral Kc
    obtain ⟨t, _, _⟩ := ringedTensorComparison_extension.{u + 1, u, u, u + 2}
      (ProEt.topology X.left) R
      (finiteIntrinsicClosed l E X.left n) (finiteIntrinsicTensorModels.{u} l E X.left n)
    have : IsIso (DerivedCategory.Q.map g) :=
      (DerivedCategory.isIso_Q_map_iff_quasiIso C g).2 hg
    let e : derivedTensor X.left A Kc Lc P g hg hP ≅
        (finiteIntrinsicDerivedTensor l E X.left n).obj (K, L) :=
      t P Lc (.inl hP) ≪≫
        (finiteIntrinsicDerivedTensor l E X.left n).mapIso
          (Iso.prod (asIso (DerivedCategory.Q.map g) ≪≫ eK) eL)
    have ht (a b c d : ℤ) (htK : HasProEtaleTorAmplitude X.left A K a b)
        (htL : HasProEtaleTorAmplitude X.left A L c d) :=
      (finiteCoefficient_tensor_ctf D l hl E (n + 1) (by omega) X.left
        Kc Lc P g hg hP a b hKc
        (sfStabilityTorOfIso X.left A eK.symm a b htK) hLc.1).2 c d hLc
        (sfStabilityTorOfIso X.left A eL.symm c d htL)
    refine ⟨?_, ?_⟩
    · obtain ⟨a, b, htK⟩ := hK.2
      obtain ⟨c, d, htL⟩ := hL.2
      exact sfStabilityFiniteTorOfIso l E n X.left e (ht a b c d htK htL).1
    · intro a b c d htK htL
      exact sfStabilityTorOfIso X.left A e (a + c) (b + d) (ht a b c d htK htL).2
  · intro K L hK hL
    obtain ⟨d, hd⟩ := exists_topologicalKrullDim_le X.hom
    obtain ⟨a, b, htK⟩ := hK.2
    obtain ⟨c, e, htL⟩ := hL.2
    have hh := finite_constructible_derivedHom_proEtale D l hl E (n + 1) (by omega)
      X.left d hd a b c e htK.1 htL.1 K L hK hL htK htL
    refine ⟨hh.1, ?_, ?_⟩
    · intro a b c e m hm htK htL
      exact (finite_constructible_derivedHom_proEtale D l hl E (n + 1) (by omega)
        X.left m hm a b c e htK.1 htL.1 K L hK hL htK htL).2
    · intro hperfect
      exact finiteIntrinsic_sitePerfect_hom_window l E X.left n K L hperfect
  · intro K hK
    obtain ⟨d, hd⟩ := exists_topologicalKrullDim_le X.hom
    obtain ⟨a, b, ht⟩ := hK.2
    have hh := ProEtale.finiteCoefficientDirectImage_boundedConstructible_torAmplitude
      D l hl E (n + 1) (by omega) X Y f d hd a b hK ht
    refine ⟨⟨hh.1, a, b + 2 * (d : ℤ), hh.2⟩, ?_⟩
    intro a b d hd ht
    exact (ProEtale.finiteCoefficientDirectImage_boundedConstructible_torAmplitude
      D l hl E (n + 1) (by omega) X Y f d hd a b hK ht).2
  · intro c K hK
    exact (FiniteExceptional.operations_preserve l E D hl f.left c n).1 ⟨K, hK⟩

include hl in
/-- Clauses (v)--(vi): the specified exceptional image preserves the constructible
finite-Tor domain, has the double-dimension interval, and agrees with the geometric
duality composite. The last predicate includes exactness and the canonical evaluation
biduality map, rather than merely an unspecified isomorphism to the double dual.
Source: current blueprint (blueprint: thm-sf-ctf-stability).

Proof: constructible exceptional preservation follows from local smooth/closed
factorizations and open-complement vanishing. Geometric finite-stage duality
identifies it with D_X f* D_Y. A duality on dimension at most e sends [u,v] to
[-v-2e,-u]; applying this twice gives [a-2dX,b+2dY]. General geometric biduality
supplies the exact anti-equivalence and invertibility of its evaluation transpose.
Empty schemes give the zero category and admit the dimension bound zero. -/
theorem finiteTor_stability_exceptional_verdier
    (X Y : Over (Spec (.of D.k)))
    [IsSeparated X.hom] [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
    [IsSeparated Y.hom] [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom]
    (f : X ⟶ Y) [IsSeparated f.left] [LocallyOfFiniteType f.left] [QuasiCompact f.left] :
    (∀ (c : Compactification f.left) (K : (proEtaleDerivedCategory Y.left
      (Padic.coefficientExtensionRing l E (n + 1)))), (finiteTorConstructible l E (n + 1)
      (Nat.succ_le_succ (Nat.zero_le n)) Y.left) K →
      (finiteTorConstructible l E (n + 1) (Nat.succ_le_succ (Nat.zero_le n)) X.left)
        ((ProEtale.sfFiniteExceptional (Padic.coefficientExtensionRing l E (n + 1)) c).obj K) ∧
      Nonempty ((ProEtale.sfFiniteExceptional (Padic.coefficientExtensionRing l E (n + 1)) c).obj
        K ≅
        (sfStabilityFiniteVerdier D l E n X.left X.hom).obj
          (op ((finiteDerivedPullback l E n f.left).obj
            ((sfStabilityFiniteVerdier D l E n Y.left Y.hom).obj (op K))))) ∧
      ∀ (a b : ℤ) (dX dY : ℕ),
        topologicalKrullDim X.left ≤ (dX : WithBot ℕ∞) →
        topologicalKrullDim Y.left ≤ (dY : WithBot ℕ∞) → (HasProEtaleTorAmplitude Y.left
          (Padic.coefficientExtensionRing l E (n + 1))) K a b →
        (HasProEtaleTorAmplitude X.left (Padic.coefficientExtensionRing l E (n + 1)))
          ((ProEtale.sfFiniteExceptional (Padic.coefficientExtensionRing l E (n + 1)) c).obj K)
          (a - 2 * (dX : ℤ)) (b + 2 * (dY : ℤ))) ∧
    FiniteProEtaleVerdierBiduality l E (n + 1)
      (Nat.succ_le_succ (Nat.zero_le n)) X.left X.hom ∧
    FiniteProEtaleVerdierBiduality l E (n + 1)
      (Nat.succ_le_succ (Nat.zero_le n)) Y.left Y.hom := by
  let : X.left.Over (Spec (.of D.k)) := ⟨X.hom⟩
  let : Y.left.Over (Spec (.of D.k)) := ⟨Y.hom⟩
  let : f.left.IsOver (Spec (.of D.k)) := ⟨Over.w f⟩
  have : LocallyOfFiniteType (X.left ↘ Spec (.of D.k)) := ‹LocallyOfFiniteType X.hom›
  have : QuasiCompact (X.left ↘ Spec (.of D.k)) := ‹QuasiCompact X.hom›
  have : IsSeparated (X.left ↘ Spec (.of D.k)) := ‹IsSeparated X.hom›
  have : LocallyOfFiniteType (Y.left ↘ Spec (.of D.k)) := ‹LocallyOfFiniteType Y.hom›
  have : QuasiCompact (Y.left ↘ Spec (.of D.k)) := ‹QuasiCompact Y.hom›
  have : IsSeparated (Y.left ↘ Spec (.of D.k)) := ‹IsSeparated Y.hom›
  refine ⟨?_, (finite_stage_verdier_biduality D l hl E (n + 1) (Nat.succ_pos n)
    X.left X.hom).2, (finite_stage_verdier_biduality D l hl E (n + 1) (Nat.succ_pos n)
      Y.left Y.hom).2⟩
  intro c K hK
  let VY := sfStabilityVerdierComparison D l E n Y.left
  let VX := sfStabilityVerdierComparison D l E n X.left
  let P := finiteDerivedPullback l E n f.left
  let e := (FiniteExceptional.dualFormulaIso l E D hl f.left c n).app ⟨K, hK⟩
  let e' := (FiniteExceptional.dual l E D X.left n).mapIso
    ((P.mapIso (VY.app (op K))).op) ≪≫
      (VX.app (op (P.obj ((sfStabilityFiniteVerdier D l E n Y.left Y.hom).obj (op K))))).symm
  refine ⟨(FiniteExceptional.operations_preserve l E D hl f.left c n).2 ⟨K, hK⟩,
    ⟨e ≪≫ e'⟩, ?_⟩
  intro a b dX dY hdX hdY ht
  have hY := IntegralVerdier.finiteIntrinsicVerdier_bounds D l hl E Y.left n K hK.1
    dY hdY a b ht
  have hP := sf_pullback_torAmplitude D l hl E (n + 1) (Nat.succ_pos n) X Y f
    ((FiniteExceptional.dual l E D Y.left n).obj (op K)) hY.1
      (-b - 2 * (dY : ℤ)) (-a) hY.2.1
  let ep := (sfStabilityPullbackComparison l E n f.left).app
    ((FiniteExceptional.dual l E D Y.left n).obj (op K))
  have hpctf := sfStabilityFiniteTorOfIso l E n X.left ep
    ⟨hP.1, -b - 2 * (dY : ℤ), -a, hP.2⟩
  have hptor := sfStabilityTorOfIso X.left _ ep _ _ hP.2
  have hX := IntegralVerdier.finiteIntrinsicVerdier_bounds D l hl E X.left n _ hpctf.1
    dX hdX (-b - 2 * (dY : ℤ)) (-a) hptor
  have htor := sfStabilityTorOfIso X.left _ e.symm _ _ hX.2.1
  have ha : - -a - 2 * (dX : ℤ) = a - 2 * (dX : ℤ) := by omega
  have hb : -(-b - 2 * (dY : ℤ)) = b + 2 * (dY : ℤ) := by omega
  change HasProEtaleTorAmplitude X.left _
    ((ProEtale.sfFiniteExceptional (Padic.coefficientExtensionRing l E (n + 1)) c).obj K)
      (- -a - 2 * (dX : ℤ)) (-(-b - 2 * (dY : ℤ))) at htor
  simpa only [ha, hb] using htor


open CategoryTheory.Pretriangulated.Opposite in
set_option backward.isDefEq.respectTransparency.types false in
include hl in
section Morphism

variable (X Y : Over (Spec (.of D.k)))
  [IsSeparated X.hom] [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
  [IsSeparated Y.hom] [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom]
  (f : X ⟶ Y) [IsSeparated f.left] [LocallyOfFiniteType f.left] [QuasiCompact f.left]

/-- Literal restriction of the comparison-defined finite exceptional image.
Source: blueprint (v) (blueprint: thm-sf-ctf-stability). -/
noncomputable def sfStabilityFiniteExceptional (c : Compactification f.left) :
    ((finiteTorConstructible l E (n + 1) (Nat.succ_le_succ (Nat.zero_le n))
      Y.left)).FullSubcategory ⥤ ((finiteTorConstructible l E (n + 1) (Nat.succ_le_succ
      (Nat.zero_le n)) X.left)).FullSubcategory :=
  ((finiteTorConstructible l E (n + 1) (Nat.succ_le_succ (Nat.zero_le n)) X.left)).lift
    (((finiteTorConstructible l E (n + 1) (Nat.succ_le_succ (Nat.zero_le n)) Y.left)).ι ⋙
    ProEtale.sfFiniteExceptional (Padic.coefficientExtensionRing l E (n + 1)) c)
    (fun K ↦ ((finiteTor_stability_exceptional_verdier D l hl E n X Y f).1
      c K.obj K.property).1)

/-- The normalized strict-tower quotient and the direct quotient factor induce
exactly the same scalar restriction. This fixes the normalization used in its mate.
Source: blueprint (vii), canonical finite quotients (blueprint: thm-sf-ctf-stability).
Proof: the tower quotient is a composite of adjacent coefficient quotient factors.
On a representative from the valuation ring, every factor sends its residue class
to the same residue class. Induct on the difference of the exponents, including
zero for the identity quotient, to identify the composite with the direct factor.
Constant sheafification and forgetting commutativity preserve this equality.
Restriction of module scalars and termwise derived localization then preserve it. -/
theorem sfStabilityQuotientRestrictionEquality
    (W : Scheme.{u}) {m n : ℕ} (h : n ≤ m) :
    normalizedDVRRes l E W h =
      (proEtaleCoefficientRestrictScalars W
        (compactSupportLevelQuotient l E m n h)).mapDerivedCategory := by
  dsimp only [normalizedDVRRes]
  congr 1
  exact compactSupportModuleRes_eq l E W h

/-- The canonical finite scalar adjunction, with its standard derived localizations
made explicit. The type annotation fixes the coefficient universe of restriction.
Source: Stacks 06YY (blueprint: thm-sf-ctf-stability). -/
noncomputable def sfStabilityCanonicalQuotientAdjunction
    (W : Scheme.{u}) {m n : ℕ} (h : n ≤ m) :
    pbcDerivedExtend (compactSupportLevelSheafQuotient l E W m n h) ⊣
      (@Functor.mapDerivedCategory.{u + 2, u + 2, u + 1, u + 1, u + 2, u + 2}
        (proEtaleRingModules W (proEtaleConstantRing W
          (Padic.coefficientExtensionRing l E (n + 1)))) _ _
        (HasDerivedCategory.standard _)
        (proEtaleRingModules W (proEtaleConstantRing W
          (Padic.coefficientExtensionRing l E (m + 1)))) _ _
        (HasDerivedCategory.standard _)
        (proEtaleCoefficientRestrictScalars W (compactSupportLevelQuotient l E m n h))
        inferInstance inferInstance inferInstance) :=
  pbcDerivedScalarAdjunction (compactSupportLevelSheafQuotient l E W m n h)

/-- The canonical scalar mate and its invertibility criterion, instantiated together
so that the same coefficient category data is shared by both projections.
Source: blueprint (vii) (blueprint: thm-sf-ctf-stability). -/
noncomputable def sfStabilitySupportReductionData
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    {m n : ℕ} (h : n ≤ m) :=
  ScalarMateTransport.certifiedTransport
    ((coefficientDerivedSystemEvaluationCalculus l E X).choose.quotientCalculus.adjunction h)
    (sfStabilityCanonicalQuotientAdjunction l E X h)
    ((coefficientDerivedSystemEvaluationCalculus l E Y).choose.quotientCalculus.adjunction h)
    (sfStabilityCanonicalQuotientAdjunction l E Y h)
    (sfStabilityQuotientRestrictionEquality l E X h)
    (sfStabilityQuotientRestrictionEquality l E Y h)
    (sfAmbientCompactSupportCandidate (Padic.coefficientExtensionRing l E (m + 1)) c)
    (sfAmbientCompactSupportCandidate (Padic.coefficientExtensionRing l E (n + 1)) c)
    (sfCompactSupportRestriction c (compactSupportLevelQuotient l E m n h)).hom

/-- Canonical finite-quotient compact-support comparison, obtained by scalar
adjunction from the normalized restriction square. This definition includes all
quotients, including the identity, and assumes no ambient exceptional adjunction.
Source: blueprint (vii) (blueprint: thm-sf-ctf-stability). -/
noncomputable def sfStabilitySupportReduction
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    {m n : ℕ} (h : n ≤ m) :
    sfIntrinsicCompactSupport c (Padic.coefficientExtensionRing l E (m + 1)) ⋙
        coefficientFiniteQuotientDerived l E Y h ⟶
      coefficientFiniteQuotientDerived l E X h ⋙
        sfIntrinsicCompactSupport c (Padic.coefficientExtensionRing l E (n + 1)) :=
  (sfStabilitySupportReductionData l E c h).val

/-- The quotient reduction of the geometric dualizing object. The first factor is
uniqueness of the left adjoint to the very same exact scalar restriction; the
second is the specified exceptional coefficient mate, normalized at the unit.
Source: blueprint (vii) (blueprint: thm-sf-ctf-stability). -/
noncomputable def sfStabilityDualizingReduction
    (X : Scheme.{u}) [X.Over (Spec (.of D.k))]
    [IsSeparated (X ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
    {m n : ℕ} (h : n ≤ m) :
    (coefficientFiniteQuotientDerived l E X h).obj
        (integralDualizingFiniteTerm l E D X m) ⟶ integralDualizingFiniteTerm l E D X n :=
  (Adjunction.leftAdjointUniq
    ((coefficientDerivedSystemEvaluationCalculus l E X).choose.quotientCalculus.adjunction h)
    (Adjunction.ofIsRightAdjoint (normalizedDVRRes l E X h))).hom.app _ ≫
      integralDualizingFiniteComparison l E D X hl h

/-- The actual Verdier coefficient arrow is reduced evaluation followed by the
normalized dualizing-object comparison. Thus evaluation, not an arbitrary object
isomorphism, determines its value and its tensor-Hom transpose.
Source: blueprint (vii) (blueprint: thm-sf-ctf-stability). -/
noncomputable def sfStabilityVerdierReduction
    (X : Scheme.{u}) [X.Over (Spec (.of D.k))]
    [IsSeparated (X ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
    {m n : ℕ} (h : n ≤ m)
    (K : proEtaleDerivedCategory X (Padic.coefficientExtensionRing l E (m + 1))) :
    (coefficientFiniteQuotientDerived l E X h).obj
        ((finiteIntrinsicDerivedInternalHom l E X m).obj
          (op K, integralDualizingFiniteTerm l E D X m)) ⟶
      (finiteIntrinsicDerivedInternalHom l E X n).obj
        (op ((coefficientFiniteQuotientDerived l E X h).obj K),
          integralDualizingFiniteTerm l E D X n) :=
  finiteIntrinsicReductionHom l E X h K (integralDualizingFiniteTerm l E D X m) ≫
    (finiteIntrinsicDerivedInternalHom l E X n).map
      (Prod.mkHom (𝟙 _) (sfStabilityDualizingReduction D l hl E X h))

private theorem sfStabilityCanonicalQuotientPreserves
    (W : Scheme.{u}) {m n : ℕ} (h : n ≤ m) (K : normalizedDVRDerived l E W m)
    (hK : finiteTorConstructible l E (m + 1) (Nat.succ_pos m) W K) :
    finiteTorConstructible l E (n + 1) (Nat.succ_pos n) W
      ((pbcDerivedExtend (compactSupportLevelSheafQuotient l E W m n h)).obj K) := by
  have he : FiniteExceptional.reduction l E W h =
      pbcDerivedExtend (compactSupportLevelSheafQuotient l E W m n h) := by
    apply congrArg (reductionDerivedChange W)
    rfl
  rw [← he]
  exact FiniteExceptional.reduction_preserves l E W h ⟨K, hK⟩

private theorem sfStabilityQuotientPreserves
    (W : Scheme.{u}) {m n : ℕ} (h : n ≤ m) (K : normalizedDVRDerived l E W m)
    (hK : finiteTorConstructible l E (m + 1) (Nat.succ_pos m) W K) :
    finiteTorConstructible l E (n + 1) (Nat.succ_pos n) W
      ((coefficientFiniteQuotientDerived l E W h).obj K) := by
  let e := Adjunction.leftAdjointUniq
    (Adjunction.ofNatIsoRight
      ((coefficientDerivedSystemEvaluationCalculus l E W).choose.quotientCalculus.adjunction h)
      (eqToIso (sfStabilityQuotientRestrictionEquality l E W h)))
    (pbcDerivedScalarAdjunction (compactSupportLevelSheafQuotient l E W m n h))
  exact sfStabilityFiniteTorOfIso l E n W (e.app K).symm
    (sfStabilityCanonicalQuotientPreserves l E W h K hK)

private theorem sfStabilityFiniteDualizingConstructible
    (X : Scheme.{u}) [X.Over (Spec (.of D.k))]
    [IsSeparated (X ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
    (m : ℕ) : finiteTorConstructible l E (m + 1) (Nat.succ_pos m) X
      (integralDualizingFiniteTerm l E D X m) := by
  classical
  let A := ULift.{u + 1, u} (Padic.coefficientExtensionRing l E (m + 1))
  let : Finite (Padic.coefficientExtensionRing l E (m + 1)) :=
    Padic.finite_coefficientExtensionRing l E _ (Nat.succ_pos m)
  let : HasInvertibleExponent A (Spec (.of D.k)) :=
    coefficient_invertible_exponent D l hl E (m + 1)
  let := (finiteDualizingCompactification D X).hasCompactification
  let ωe := finiteDualizingEtaleTerm l E D X m
  have hω : finiteTorConstructibleEtale l E (m + 1) (Nat.succ_pos m) X ωe := by
    apply (finiteTorConstructibleEtale_iff_source l E (m + 1) (Nat.succ_pos m) X ωe).2
    exact Etale.constructibleFiniteTor_dualizingComplex A (𝟙 _) _
      (Etale.constructibleFiniteTor_unit A)
  let eω : (finiteHomNu l E X m).obj ωe ≅ integralDualizingFiniteTerm l E D X m :=
    (@Functor.mapDerivedCategoryCompIso.{u + 2, u + 2, u + 2,
        u + 1, u + 1, u + 1, u + 1, u + 1, u + 2}
      (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A))
      (Sheaf (ProEt.topology X) (ModuleCat.{u + 1} A))
      (scalarReductionTarget.{u, u} l E X m)
      _ _ _ _ _ _
      (HasDerivedCategory.ofIsGrothendieckAbelian.{u + 1} _)
      (HasDerivedCategory.ofIsGrothendieckAbelian.{u + 1} _)
      (HasDerivedCategory.standard _)
      (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) X)
      (ProEtale.finiteCoefficientIntrinsicRealization X
        (Padic.coefficientExtensionRing l E (m + 1)))
      inferInstance
      (ProEtale.finiteCoefficientIntrinsicRealization_exact X
        (Padic.coefficientExtensionRing l E (m + 1))).2.1
      inferInstance inferInstance
      (ProEtale.finiteCoefficientIntrinsicRealization_exact X
        (Padic.coefficientExtensionRing l E (m + 1))).2.2.1
      (ProEtale.finiteCoefficientIntrinsicRealization_exact X
        (Padic.coefficientExtensionRing l E (m + 1))).2.2.2).app ωe ≪≫
      finiteDualizingOrigin l E D X m
  have hωp := ((coefFiniteHomSiteDescent D l hl E X).1 m).2.2.2.2 ωe hω |>.1
  exact sfStabilityFiniteTorOfIso l E m X eω hωp

private theorem sfStabilityCanonicalSupportReductionIsIso
    (X : Scheme.{u}) [X.Over (Spec (.of D.k))]
    [IsSeparated (X ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
    (Y : Scheme.{u}) [Y.Over (Spec (.of D.k))]
    [IsSeparated (Y ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of D.k))] [QuasiCompact (Y ↘ Spec (.of D.k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of D.k))]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (c : Compactification f) {m n : ℕ} (h : n ≤ m)
    (K : normalizedDVRDerived l E X m)
    (hK : finiteTorConstructible l E (m + 1) (Nat.succ_pos m) X K) :
    IsIso (((sfStabilityCanonicalQuotientAdjunction l E Y h).homEquiv _ _).symm
      ((sfAmbientCompactSupportCandidate (Padic.coefficientExtensionRing l E (m + 1)) c).map
          ((sfStabilityCanonicalQuotientAdjunction l E X h).unit.app K) ≫
        (sfCompactSupportRestriction c (compactSupportLevelQuotient l E m n h)).hom.app
          ((pbcDerivedExtend (compactSupportLevelSheafQuotient l E X m n h)).obj K))) := by
  exact finiteCompactSupportScalarComparison l E D.k (finiteFieldDatumPrimeUnit D l hl)
    (m + 1) (Nat.succ_pos m) (n + 1) (Nat.succ_pos n)
    (Nat.add_le_add_right h 1) f c K hK.1 (sfStabilityCanonicalQuotientPreserves l E X h K hK).1

private theorem sfStabilitySupportReductionIsIso
    (X : Scheme.{u}) [X.Over (Spec (.of D.k))]
    [IsSeparated (X ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
    (Y : Scheme.{u}) [Y.Over (Spec (.of D.k))]
    [IsSeparated (Y ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of D.k))] [QuasiCompact (Y ↘ Spec (.of D.k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of D.k))]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (c : Compactification f) {m n : ℕ} (h : n ≤ m)
    (K : proEtaleDerivedCategory X (Padic.coefficientExtensionRing l E (m + 1)))
    (hK : finiteTorConstructible l E (m + 1) (Nat.succ_pos m) X K) :
    IsIso ((sfStabilitySupportReduction l E c h).app K) := by
  exact (sfStabilitySupportReductionData l E c h).property K
    (sfStabilityCanonicalSupportReductionIsIso D l hl E X Y f c h K hK)

/-- Finite quotient change preserves the finite-Tor domain and commutes with
its actual internal Hom, tensor, Verdier duality and compact-support direct image.
The displayed evaluation compatibility includes naturality, every transpose and
internal composition; the tensor comparison is fixed on K-flat pure tensors.
Source: blueprint (vii) (blueprint: thm-sf-ctf-stability).

Proof: scalar extension on bounded flat models preserves the constructible Tor
domain. The tensor comparison is the normalized derived balancing comparison.
For general Hom use geometric Verdier duality and the finite Hom coefficient
theorem, which identifies exactly the transpose of reduced evaluation. Apply
exceptional coefficient change at the coefficient unit for the dualizing object;
composition with Hom reduction gives Verdier change. Compact support is open
extension followed by proper direct image, and both coefficient comparisons are
the canonical scalar mates of the normalized restriction squares. -/
theorem finiteTor_stability_quotients
    (X : Scheme.{u}) [X.Over (Spec (.of D.k))]
    [IsSeparated (X ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
    {m n : ℕ} (h : n ≤ m) :
    (∀ K : proEtaleDerivedCategory X (Padic.coefficientExtensionRing l E (m + 1)),
      finiteTorConstructible l E (m + 1) (Nat.le_add_left 1 m) X K →
      finiteTorConstructible l E (n + 1) (Nat.le_add_left 1 n) X
        ((coefficientFiniteQuotientDerived l E X h).obj K)) ∧
    (∀ K L : proEtaleDerivedCategory X (Padic.coefficientExtensionRing l E (m + 1)),
      finiteTorConstructible l E (m + 1) (Nat.le_add_left 1 m) X K →
      finiteTorConstructible l E (m + 1) (Nat.le_add_left 1 m) X L →
      IsIso (finiteIntrinsicReductionHom l E X h K L)) ∧
    CoefficientEvaluationCompatible (finiteIntrinsicClosed l E X m)
      (finiteIntrinsicClosed l E X n) (coefficientFiniteQuotientDerived l E X h)
      ((coefficientDerivedSystemEvaluationCalculus l E X).choose.quotientCalculus.tensor h) ∧
    (∀ K : proEtaleDerivedCategory X (Padic.coefficientExtensionRing l E (m + 1)),
      finiteTorConstructible l E (m + 1) (Nat.le_add_left 1 m) X K →
      IsIso (sfStabilityVerdierReduction D l hl E X h K)) ∧
    ∀ (Y : Scheme.{u}) [Y.Over (Spec (.of D.k))]
      [IsSeparated (Y ↘ Spec (.of D.k))]
      [LocallyOfFiniteType (Y ↘ Spec (.of D.k))] [QuasiCompact (Y ↘ Spec (.of D.k))]
      (f : X ⟶ Y) [f.IsOver (Spec (.of D.k))]
      [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
      (c : Compactification f)
      (K : proEtaleDerivedCategory X (Padic.coefficientExtensionRing l E (m + 1))),
      finiteTorConstructible l E (m + 1) (Nat.le_add_left 1 m) X K →
      IsIso ((sfStabilitySupportReduction l E c h).app K) := by
  have hHom := finiteCoefficient_derivedHom_change D l hl E X m n h
  have hhom (K L : normalizedDVRDerived l E X m)
      (hK : finiteTorConstructible l E (m + 1) (Nat.succ_pos m) X K)
      (hL : finiteTorConstructible l E (m + 1) (Nat.succ_pos m) X L) :
      IsIso (finiteIntrinsicReductionHom l E X h K L) :=
    (hHom.2.2.2.2.2.1 K L hK hL).2.2
  refine ⟨sfStabilityQuotientPreserves l E X h, hhom, hHom.2.2.2.1, ?_, ?_⟩
  · intro K hK
    have := hhom K _ hK (sfStabilityFiniteDualizingConstructible D l hl E X m)
    have := (finiteDualizingCoefficientComparisons l E D X hl).2.2.2.1 h
    have : IsIso (sfStabilityDualizingReduction D l hl E X h) := by
      dsimp only [sfStabilityDualizingReduction]
      infer_instance
    have : IsIso (Prod.mkHom (𝟙 (op ((coefficientFiniteQuotientDerived l E X h).obj K)))
        (sfStabilityDualizingReduction D l hl E X h)) :=
      (isIso_prod_iff (f := Prod.mkHom
        (𝟙 (op ((coefficientFiniteQuotientDerived l E X h).obj K)))
        (sfStabilityDualizingReduction D l hl E X h))).mpr
        ⟨inferInstance, inferInstance⟩
    dsimp only [sfStabilityVerdierReduction]
    infer_instance
  · intro Y _ _ _ _ f _ _ _ _ c K hK
    exact sfStabilitySupportReductionIsIso D l hl E X Y f c h K hK

end Morphism

end Finite

section Quotients

variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
  (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

include hl in
end Quotients

section Integral

variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
  (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

/-- The integral dualizing object from the normalized finite exceptional tower.
It is characterized by its compact-support representing property; the choice is
only between canonically isomorphic representatives of that object.
Source: blueprint (vii), integral paragraph (blueprint: thm-sf-ctf-stability). -/
noncomputable def sfStabilityIntegralDualizing
    (X : Scheme.{u}) [X.Over (Spec (.of D.k))]
    [IsSeparated (X ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))] :
    sfIntegralConstructibleCategory l E X :=
  let hd := exists_topologicalKrullDim_le (X ↘ Spec (.of D.k))
  (prop_coef_integral_dualizing D l hl E X hd.choose hd.choose_spec).choose

/-- Geometric integral Verdier duality, using the ambient K-injective sheaf Hom
into the canonical integral dualizing object.
Source: blueprint (vii) (blueprint: thm-sf-ctf-stability). -/
noncomputable def sfStabilityIntegralVerdier
    (X : Scheme.{u}) [X.Over (Spec (.of D.k))]
    [IsSeparated (X ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))] :
    (DerivedCategory (scalarReductionSource.{u, u} l E X))ᵒᵖ ⥤
      DerivedCategory (scalarReductionSource.{u, u} l E X) :=
  Prod.sectL _ (sfStabilityIntegralDualizing D l hl E X).obj ⋙
    integralDerivedInternalHom l E X

include hl in
attribute [local irreducible] integralDerivedPullback integralDerivedInternalHom
  scalarReductionExistence scalarReductionDerivedExistence sfStabilityIntegralVerdier
  sfIntegralCompactSupportValue sfRationalCompactSupportValue

section Morphism

variable (X Y : Scheme.{u}) [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))]
  [IsSeparated (X ↘ Spec (.of D.k))] [IsSeparated (Y ↘ Spec (.of D.k))]
  [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
  [LocallyOfFiniteType (Y ↘ Spec (.of D.k))] [QuasiCompact (Y ↘ Spec (.of D.k))]
  (f : X ⟶ Y) [f.IsOver (Spec (.of D.k))]
  [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]

/-- Integral support on maps: apply the published coherent support-reduction tower,
then the total right derived inverse limit. The same chosen compactification is used
at every level. This is the general-morphism version of integralDualizingCompactTower,
using its exact same published tower construction, not an objectwise limit choice.
Source: blueprint (iv),(vii) (blueprint: thm-sf-ctf-stability). -/
noncomputable def sfStabilityIntegralSupportAmbient (c : Compactification f) :
    DerivedCategory (scalarReductionSource.{u, u} l E X) ⥤
      DerivedCategory (scalarReductionSource.{u, u} l E Y) := by
  let h := exists_compactSupportReductionTower l E D.k X Y f
    (finiteFieldDatumPrimeUnit D l hl) c
  letI := h.choose
  letI := h.choose_spec.choose
  exact h.choose_spec.choose_spec.2.2.choose ⋙ integralDualizingLimit l E Y

omit [IsSeparated (X ↘ Spec (.of D.k))] [IsSeparated (Y ↘ Spec (.of D.k))] in
attribute [local irreducible] sfStabilityIntegralSupportAmbient

end Morphism

end Integral

section AlgebraicClosure

variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
  (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]
  (X Y : Scheme.{u}) [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))]
  [IsSeparated (X ↘ Spec (.of D.k))] [IsSeparated (Y ↘ Spec (.of D.k))]
  [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
  [LocallyOfFiniteType (Y ↘ Spec (.of D.k))] [QuasiCompact (Y ↘ Spec (.of D.k))]
  (f : X ⟶ Y) [f.IsOver (Spec (.of D.k))]
  [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]

end AlgebraicClosure

end WeilConjectures
