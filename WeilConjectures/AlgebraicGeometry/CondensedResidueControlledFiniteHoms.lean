/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.FiniteFieldFiberSupplement
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
public import Mathlib.RingTheory.Ideal.Quotient.Index
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.Topology.KrullDimension
public import Mathlib.CategoryTheory.Monoidal.Mon
public import WeilConjectures.SixFunctors.ProEtale.DerivedCompletionSupplement
public import WeilConjectures.AlgebraicGeometry.BoundedConstructibleConeCounterexample
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Hom
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Hom
public import WeilConjectures.AlgebraicGeometry.CondensedFiniteTorConstructible
public import WeilConjectures.AlgebraicGeometry.ProfiniteFiniteConstantLocalModel
import Mathlib.AlgebraicGeometry.Noetherian
import all WeilConjectures.AlgebraicGeometry.IntegralPositiveReductionConstructible
import all WeilConjectures.AlgebraicGeometry.FiniteConstructibleHom
import all WeilConjectures.AlgebraicGeometry.IntegralCriterionReductionsSupplement
import all WeilConjectures.AlgebraicGeometry.IntegralTensorConstructibility
import WeilConjectures.SixFunctors.ProEtale.IntegralResidueCriterion
import WeilConjectures.AlgebraicGeometry.IntegralResidueTor
import WeilConjectures.AlgebraicGeometry.FiniteDiscreteEncodingTensorTor
import WeilConjectures.SixFunctors.FiniteDualitySiteComparison
import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Closed.Basic

/-!
# Condensed finite-reduction internal-Hom estimate

Source: latest blueprint, sec-smooth-purity/sk-lem-sp-tower,
cor-coef-integral-internal-hom.proof.md, sentences 2–3
(blueprint: lem-coef-condensed-residue-controlled-finite-homs).

All complexes belong to the ordinary unbounded derived categories of internal modules.
The inputs are bounded constructible; no derived completeness condition is imposed.
The index n denotes exponent n+1, so index zero is the residue reduction. The quotient
coefficient rings use the existing continuous construction; their positive-level quotient
topology is discrete, as in the finite coefficient comparison.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

/-- Residue cohomology controls the constructibility and one uniform Tor interval of
all finite-level internal Homs in the native condensed module presentation.
Source: latest blueprint, cor-coef-integral-internal-hom.proof.md, sentences 2–3
(blueprint: lem-coef-condensed-residue-controlled-finite-homs).

Proof:
1. Finite type over the field makes X Noetherian. The integral locally finitely
presented/constant-model comparison, transported along the canonical continuous
coefficient isomorphism, gives constant-model bounded constructibility of K and L.
2. The internal integral residue criterion derives completeness and constructibility
of the first reductions. The first-reduction criterion gives integral constructibility
of their section-action images. The normalized section squares identify ordinary
quotient reductions with the actual native reductions under the finite encoding.
Exact homology comparison transports the specified residue bounds.
3. The scalar l is a unit in the base field and therefore in every residue field of X.
Apply integral_residue_tor and transport its intervals back through the normalized
reduction comparison and encoding_tensor_tor. Positive reduction constructibility
gives bounded constant models for both native reductions.
4. The fixed coefficient constructibility criterion supplies etale origins of the
encoded reductions. Site comparison reflects their precise Tor intervals. Apply the
etale finite-constructible Hom estimate to obtain bounded constructibility and the
interval [c-b-2d,e-a+2d].
5. The finite duality site comparison identifies pullback of this etale Hom with Hom
of its pro-etale images. Compose with the chosen origin isomorphisms. The strong
monoidal equivalence preserves internal Hom by Functor.Monoidal.commIhom, identifying
the resulting object with the image of the specified native Hom.
6. Site comparison preserves constructibility and the output Tor interval. Transport
both along this composite isomorphism and reflect them through the finite encoding. -/
theorem condensed_residue_controlled_finite_homs
    (D : WeilConjectures.FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (_hl : l ≠ D.p)
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (X : Scheme.{u}) [X.Over (Spec (.of D.k))]
    [IsSeparated (X ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
    (d : ℕ) (_hd : topologicalKrullDim X ≤ (d : WithBot ℕ∞))
    (K L : DerivedCategory (AdicCompletion.Modules l E X))
    (_hK : boundedConstructible (AdicCompletion.ring l E X) K)
    (_hL : boundedConstructible (AdicCompletion.ring l E X) L)
    (a b c e : ℤ) (_hab : a ≤ b) (_hce : c ≤ e)
    (_hK₁ : ∀ i : ℤ, (i < a ∨ b < i) →
      IsZero ((DerivedCategory.homologyFunctor _ i).obj
        ((AdicCompletion.derivedReduction l E X 0).obj K)))
    (_hL₁ : ∀ i : ℤ, (i < c ∨ e < i) →
      IsZero ((DerivedCategory.homologyFunctor _ i).obj
        ((AdicCompletion.derivedReduction l E X 0).obj L))) :
    ∀ n : ℕ,
      constantModelBoundedConstructible (DerivedNakayama.quotientRing l E (n + 1)) X
        (((CondensedRing.derivedHom (DerivedNakayama.quotientRing l E (n + 1)) X).obj
          (op ((AdicCompletion.derivedReduction l E X n).obj K))).obj
            ((AdicCompletion.derivedReduction l E X n).obj L)) ∧
      _root_.DerivedCategory.torAmplitudeIn
        (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
          (AdicCompletion.finiteRing l E X n))
        (c - b - 2 * (d : ℤ)) (e - a + 2 * (d : ℤ))
        (((CondensedRing.derivedHom (DerivedNakayama.quotientRing l E (n + 1)) X).obj
          (op ((AdicCompletion.derivedReduction l E X n).obj K))).obj
            ((AdicCompletion.derivedReduction l E X n).obj L)) := by
  classical
  let : EssentiallySmall.{u + 1} X.ProEt := essentiallySmallSelf.{0} _
  let := (Padic.coefficientExtensionAbsoluteValue l E).toNormedField
  let : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace
    (X ↘ Spec (.of D.k))
  let : IsLocallyNoetherian X :=
    LocallyOfFiniteType.isLocallyNoetherian (X ↘ Spec (.of D.k))
  let : IsNoetherian X := ⟨⟩
  have integralModels (M : DerivedCategory (AdicCompletion.Modules l E X))
      (hM : boundedConstructible (AdicCompletion.ring l E X) M) :
      constantModelBoundedConstructible (DerivedNakayama.integerRing l E) X M :=
    ⟨hM.1, fun q ↦ (integerConstructibleComparison l E X _).mp (hM.2 q)⟩
  have integralCriterion := (internal_integral_residue_criterion l E X).1
  have hKc := (integralCriterion K).mp (integralModels K _hK)
  have hLc := (integralCriterion L).mp (integralModels L _hL)
  have hKs := (sfIntegralConstructible_iff_first_reduction l E X K hKc.1).mpr hKc.2.1
  have hLs := (sfIntegralConstructible_iff_first_reduction l E X L hLc.1).mpr hLc.2.1
  let A := integralEncoding l E X
  obtain ⟨enc, sq, hsq⟩ := IntegralPresentation.fixed_integral_section_squares l E X A
    (integralLimitAbComparison l E X)
    (integralLimitAbComparison_existsUnique l E X).exists.choose_spec
    (integralSectionAbIdentifications l E X).1
    (integralSectionAbIdentifications l E X).2
    (integralSectionRingIso_existsUnique l E X).exists.choose_spec
  have hb (n : ℕ) := IntegralPresentation.finiteComparison_existsUnique l E X A n
    (enc n) (sq n)
  choose redIso _ _ using hb
  let (n : ℕ) : Finite (Padic.coefficientExtensionRing l E (n + 1)) :=
    Padic.finite_coefficientExtensionRing l E (n + 1) (by omega)
  let (n : ℕ) : DiscreteTopology (Padic.coefficientExtensionRing l E (n + 1)) :=
    finiteTopology_discrete l E n
  have vanish (M : DerivedCategory (AdicCompletion.Modules l E X)) (n : ℕ) (q : ℤ) :
      IsZero ((DerivedCategory.homologyFunctor _ q).obj
          ((AdicCompletion.derivedReduction l E X n).obj M)) ↔
        IsZero ((DerivedCategory.homologyFunctor _ q).obj
          ((WeilConjectures.scalarReductionDerivedExtension l E X n).obj
            (A.derived.functor.obj M))) := by
    exact (show IsZero ((DerivedCategory.homologyFunctor _ q).obj
        ((AdicCompletion.derivedReduction l E X n).obj M)) ↔
      IsZero ((DerivedCategory.homologyFunctor _ q).obj
        ((enc n).ordinaryDerived.functor.obj
          ((AdicCompletion.derivedReduction l E X n).obj M))) from
      ⟨(enc n).ordinary.functor.isZero_homologyFunctor_mapDerivedCategory_obj,
        Functor.isZero_homologyFunctor_of_isZero_homologyFunctor_mapDerivedCategory_obj
          (enc n).ordinary.functor⟩).trans
      ((DerivedCategory.homologyFunctor _ q).mapIso ((redIso n).app M)).isZero_iff.symm
  have hunit : IsUnit (l : D.k) := by
    let := Fintype.ofFinite D.k₀
    let : Fact D.p.Prime := ⟨D.prime⟩
    have : CharP D.k₀ D.p := charP_of_card_eq_prime_pow
      ((Nat.card_eq_fintype_card (α := D.k₀)).symm.trans
        (D.card_base.trans D.cardinality_eq))
    have : CharP D.k D.p :=
      charP_of_injective_algebraMap (algebraMap D.k₀ D.k).injective D.p
    exact (CharP.isUnit_natCast_iff (R := D.k) D.prime).2
      (fun h ↦ _hl ((Nat.prime_dvd_prime_iff_eq D.prime (Fact.out : l.Prime)).1 h).symm)
  let residueMap (x : X) : D.k →+* X.residueField x :=
    ((Scheme.ΓSpecIso (.of D.k)).inv ≫
      (X ↘ Spec (.of D.k)).appTop ≫ X.Γevaluation x).hom
  let : ∀ x : X, Invertible (l : X.residueField x) := fun x ↦
    (map_natCast (residueMap x) l) ▸ (hunit.map (residueMap x)).invertible
  have hKt := (WeilConjectures.integral_residue_tor D l _hl E X).1
    (A.derived.functor.obj K) hKs a b _hab (fun q hq ↦ by
      by_contra h
      exact hq ((vanish K 0 q).mp (_hK₁ q (by omega))))
  have hLt := (WeilConjectures.integral_residue_tor D l _hl E X).1
    (A.derived.functor.obj L) hLs c e _hce (fun q hq ↦ by
      by_contra h
      exact hq ((vanish L 0 q).mp (_hL₁ q (by omega))))
  intro n
  let B := Padic.coefficientExtensionRing l E (n + 1)
  let R := AdicCompletion.derivedReduction l E X n
  let F := (enc n).fixedDerived.functor
  have htensor := FiniteDiscreteOrdinary.encoding_tensor_tor B X (enc n)
  let := htensor.1.some
  have hKR : _root_.DerivedCategory.torAmplitudeIn
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
        (AdicCompletion.finiteRing l E X n)) a b (R.obj K) := by
    apply (htensor.2.1 _ a b _hab).mpr
    exact WeilConjectures.torAmplitude_iso.{u} X B ((redIso n).app K) a b (hKt n)
  have hLR : _root_.DerivedCategory.torAmplitudeIn
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
        (AdicCompletion.finiteRing l E X n)) c e (R.obj L) := by
    apply (htensor.2.1 _ c e _hce).mpr
    exact WeilConjectures.torAmplitude_iso.{u} X B ((redIso n).app L) c e (hLt n)
  have hKB := integralReduction_constantModelBoundedConstructible l E X K
    (integralModels K _hK) n
  have hLB := integralReduction_constantModelBoundedConstructible l E X L
    (integralModels L _hL) n
  obtain ⟨K', hK', ⟨iK⟩⟩ := (fixedCriterion B X (enc n) _).mp hKB
  obtain ⟨L', hL', ⟨iL⟩⟩ := (fixedCriterion B X (enc n) _).mp hLB
  let Λ := ULift.{u + 1} B
  let C := comparisonUpperStar (ModuleCat.{u + 1} Λ) X
  have hK't := (DerivedCategory.torAmplitudeIn_mapDerivedCategory_iff a b K').mp
    (( _root_.DerivedCategory.torAmplitudeIn _ a b).prop_of_iso iK.symm
      ((htensor.2.2 _ a b _hab).mp hKR))
  have hL't := (DerivedCategory.torAmplitudeIn_mapDerivedCategory_iff c e L').mp
    (( _root_.DerivedCategory.torAmplitudeIn _ c e).prop_of_iso iL.symm
      ((htensor.2.2 _ c e _hce).mp hLR))
  have hK'bc := (WeilConjectures.boundedConstructible_iff_source Λ X K').mpr hK'
  have hL'bc := (WeilConjectures.boundedConstructible_iff_source Λ X L').mpr hL'
  have hHom := WeilConjectures.finite_constructible_derivedHom_etale D l _hl E
    (n + 1) (by omega) X d _hd a b c e _hab _hce K' L' hK'bc hL'bc hK't hL't
  have hc := WeilConjectures.finite_duality_site_comparison D l _hl E (n + 1)
    (by omega) X
  dsimp only [WeilConjectures.FiniteDualitySiteComparison, FiniteDualityComparisonData] at hc
  have hi := hc.1 K' L' ⟨hK'bc, a, b, _hab,
    Etale.DerivedCategory.hasTorAmplitudeIn_iff_torAmplitudeIn.mpr hK't⟩ hL'bc
  let I := CondensedRing.derivedHom (DerivedNakayama.quotientRing l E (n + 1)) X
  let J := derivedHom (ModuleCat.{u + 1} Λ) X
  let H := ((Etale.derivedHom (ModuleCat.{u + 1} Λ) X).obj (op K')).obj L'
  let t : C.mapDerivedCategory.obj H ≅ F.obj ((I.obj (op (R.obj K))).obj (R.obj L)) :=
    asIso (siteComparisonEvaluationHom (ModuleCat.{u + 1} Λ) X K' L') ≪≫
      (J.mapIso iK.op.symm).app _ ≪≫ (J.obj _).mapIso iL ≪≫
      ((Functor.Monoidal.commIhom F (R.obj K)).app (R.obj L)).symm
  have hBC : DerivedCategory.boundedConstructible (ModuleCat.{u + 1} Λ) X
      (F.obj ((I.obj (op (R.obj K))).obj (R.obj L))) :=
    (DerivedCategory.boundedConstructible _ X).prop_of_iso t
      (DerivedCategory.boundedConstructible_comparisonUpperStar_mapDerivedCategory_obj
        ((WeilConjectures.boundedConstructible_iff_source Λ X H).mp hHom.1))
  have hTor := (_root_.DerivedCategory.torAmplitudeIn _
    (c - b - 2 * (d : ℤ)) (e - a + 2 * (d : ℤ))).prop_of_iso t
      (DerivedCategory.torAmplitudeIn_mapDerivedCategory Λ hHom.2)
  refine ⟨(fixedCriterion B X (enc n) _).mpr hBC, ?_⟩
  exact (htensor.2.2 _ _ _ (by omega)).mpr hTor

end AlgebraicGeometry.ProEtale
