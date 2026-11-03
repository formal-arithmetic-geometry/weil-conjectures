/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import WeilConjectures.AlgebraicGeometry.ProEtaleIntegralCoefficientLimit
public import WeilConjectures.AlgebraicGeometry.CoefficientBoundedConstructibleProEtale
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedModuleDerivedPushpull
public import WeilConjectures.AlgebraicGeometry.ProEtaleCoefficients.ProfiniteFiniteConstantLocalModel
public import WeilConjectures.AlgebraicGeometry.ConstantModelTorAmplitude
public import WeilConjectures.AlgebraicGeometry.AdicCompletion.DerivedCompletionSupplement
public import WeilConjectures.AlgebraicGeometry.FreeParameterEvaluation.FreeParameterScalarMaps
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Hom
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients

import WeilConjectures.AlgebraicGeometry.CondensedIntegralCriterion
import WeilConjectures.AlgebraicGeometry.Integral.IntegralDirectImageLimits
import WeilConjectures.AlgebraicGeometry.Integral.IntegralReductionPullbackNormalization
import WeilConjectures.AlgebraicGeometry.OpenDirectImageFieldFiniteness2
import WeilConjectures.NumberTheory.Padics.ExtensionIntegersDvr

/-! # Integral open direct image in the standing field setting

Source: literature/blueprint/latest/blueprint/part-six-operations/
sec-constructibility-upper-shriek/sec-ladic-summary/sec-i-heart/sk-thm-sf-pf-adic/
sk-thm-sf-pf-adic-open.md and its proof, all four paragraphs; standing field convention
det-def-sfb-dc-setting (part-six-operations/sec-reduction-finite-coefficients/
sec-proper-direct-image/sk-thm-sfb-proper-base-change/det-def-sfb-dc-setting.md);
Stacks Tags 099L, 09A6 and 09C1.
(blueprint: det-thm-sf-pf-adic-open).
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

set_option maxHeartbeats 2000000 in
-- Normalizing the two scalar-mate presentations unfolds several derived adjunctions.
/-- Integral direct image along a quasi-compact open immersion is derived complete,
commutes with residue reduction by the canonical coefficient-change comparison, and
preserves bounded constructibility. Integral Dbc equals its finite-Tor subcategory.

Source: literature/blueprint/latest/blueprint/part-six-operations/
sec-constructibility-upper-shriek/sec-ladic-summary/sec-i-heart/sk-thm-sf-pf-adic/
sk-thm-sf-pf-adic-open.md, entire statement and four proof paragraphs, with the
standing field convention det-def-sfb-dc-setting;
Stacks Tags 099L, 09A6 and 09C1 (blueprint: det-thm-sf-pf-adic-open).

Proof:
1. The spectrum of k is Noetherian. Finite type makes U and X Noetherian and qcqs.
2. The integral criterion on U makes K derived complete and its first reduction K_1
   bounded constructible. Completeness identifies K with its canonical reduction limit.
3. The internal integral direct-image-limits theorem, applied to that reduction tower,
   makes H = Rj_* K complete, including compatibility with the completion augmentation.
4. Its scalar pullback mate is invertible. The geometric adjunct of its inverse followed
   by reduction of the integral counit is the canonical residue comparison. The scalar
   mate is the specified scalar/pullback comparison `scalarPullComparison` of
   def-sfb-free-parameter-scalar-maps for integerRing -> quotientRing 1. The displayed
   counit equation uniquely characterizes this adjunct, which that theorem makes invertible.
   This is the uniformizer-cone argument in the residue-module category, with its action.
5. The DVR theorem identifies the uniformizer ideal with the maximal ideal and makes the
   residue field finite. The l-adic norm gives l in the maximal ideal, so l kills the residue
   field. Its topology is discrete, and l is invertible in k because ringChar k differs from l.
6. The finite-coefficient open-finiteness theorem on the given separated finite-type
   schemes over the finite or algebraically closed field k makes Rj_* K_1 bounded
   constructible. This theorem includes the required etale/pro-etale comparison.
7. Transfer bounded constructibility through the residue isomorphism. Together with
   completeness, the integral criterion on X gives bounded constructibility of H.
   Its fourth equivalent condition gives Dbc = Dctf on X. Empty opens, zero complexes,
   identity immersions and torsion integral complexes require no separate restriction.
-/
theorem integral_open_direct_image_current
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    {U X : Scheme.{u}} (j : U ⟶ X)
    (k : Type u) [Field k] (_hbase : Finite k ∨ IsAlgClosed k)
    [Fact (ringChar k).Prime] (_hchar : ringChar k ≠ l)
    [U.Over (Spec (.of k))] [X.Over (Spec (.of k))]
    [LocallyOfFiniteType (U ↘ Spec (.of k))] [QuasiCompact (U ↘ Spec (.of k))]
    [IsSeparated (U ↘ Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))] [j.IsOver (Spec (.of k))]
    [IsOpenImmersion j] [QuasiCompact j]
    (K : DerivedCategory (AdicCompletion.Modules l E U))
    (hK : constantModelBoundedConstructible (DerivedNakayama.integerRing l E) U K) :
    IsDerivedComplete l E X
        ((CondensedRing.moduleObjectDerivedPushforward (DerivedNakayama.integerRing l E) j).obj
          K) ∧
      (∃! c :
          (AdicCompletion.derivedReduction l E X 0).obj
              ((CondensedRing.moduleObjectDerivedPushforward
                (DerivedNakayama.integerRing l E) j).obj K) ⟶
            (CondensedRing.moduleObjectDerivedPushforward
              (DerivedNakayama.quotientRing l E 1) j).obj
                ((AdicCompletion.derivedReduction l E U 0).obj K),
        IsIso c ∧
          FreeParameterEvaluation.scalarPullComparison
              (Mon.mk (DerivedNakayama.integerRing l E))
              (Mon.mk (DerivedNakayama.quotientRing l E 1))
              (DerivedNakayama.reductionRing l E 1) j
              ((CondensedRing.moduleObjectDerivedPushforward
                (DerivedNakayama.integerRing l E) j).obj K) ≫
            (CondensedRing.upperStar (DerivedNakayama.quotientRing l E 1) j).mapDerivedCategory.map
              c ≫
            ((CondensedRing.derivedUpperStarLowerStarAdjunction
                (DerivedNakayama.quotientRing l E 1) j).ofNatIsoLeft
                  (CondensedRing.leftDerivedUpperStarIsoMapDerivedCategory
                    (DerivedNakayama.quotientRing l E 1) j)).counit.app
              ((AdicCompletion.derivedReduction l E U 0).obj K) =
            (AdicCompletion.derivedReduction l E U 0).map
              (((CondensedRing.derivedUpperStarLowerStarAdjunction
                  (DerivedNakayama.integerRing l E) j).ofNatIsoLeft
                    (CondensedRing.leftDerivedUpperStarIsoMapDerivedCategory
                      (DerivedNakayama.integerRing l E) j)).counit.app K)) ∧
      constantModelBoundedConstructible (DerivedNakayama.integerRing l E) X
        ((CondensedRing.moduleObjectDerivedPushforward (DerivedNakayama.integerRing l E) j).obj
          K) ∧
      constantModelBoundedConstructible (DerivedNakayama.integerRing l E) X =
        (constantModelBoundedConstructible (DerivedNakayama.integerRing l E) X ⊓
          DerivedCategory.finiteTorAmplitude (AdicCompletion.Modules l E X)) := by
  classical
  have : IsLocallyNoetherian U :=
    LocallyOfFiniteType.isLocallyNoetherian (U ↘ Spec (.of k))
  have : CompactSpace U := QuasiCompact.compactSpace_of_compactSpace (U ↘ Spec (.of k))
  have : IsNoetherian U := {}
  have : IsLocallyNoetherian X :=
    LocallyOfFiniteType.isLocallyNoetherian (X ↘ Spec (.of k))
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace (X ↘ Spec (.of k))
  have : IsNoetherian X := {}
  have hKU := ((condensed_integral_criterion l E U K).out 0 1).mp hK
  obtain ⟨hχ, hlimits⟩ := internal_integral_direct_image_limits l E j
  let χ := integralReductionPullbackMap l E j 0
  have : IsIso χ := hχ
  let H := (CondensedRing.moduleObjectDerivedPushforward
    (DerivedNakayama.integerRing l E) j).obj K
  let K₁ := (AdicCompletion.derivedReduction l E U 0).obj K
  let adj := (CondensedRing.derivedUpperStarLowerStarAdjunction
    (DerivedNakayama.quotientRing l E 1) j).ofNatIsoLeft
      (CondensedRing.leftDerivedUpperStarIsoMapDerivedCategory
        (DerivedNakayama.quotientRing l E 1) j)
  let a := χ.app H
  let v := (AdicCompletion.derivedReduction l E U 0).map
    (((CondensedRing.derivedUpperStarLowerStarAdjunction
      (DerivedNakayama.integerRing l E) j).ofNatIsoLeft
        (CondensedRing.leftDerivedUpperStarIsoMapDerivedCategory
          (DerivedNakayama.integerRing l E) j)).counit.app K)
  let c := (adj.homEquiv _ _) (inv a ≫ v)
  have hc : IsIso c := (hlimits K).2
  have hcomplete : IsDerivedComplete l E X H := (hlimits K).1 hKU.1
  have heq : a ≫ (adj.homEquiv _ _).symm c = v := by
    simp only [c, Equiv.symm_apply_apply, ← Category.assoc, IsIso.hom_inv_id,
      Category.id_comp]
  have hcanonical : ∃! d, IsIso d ∧
      a ≫ (adj.homEquiv _ _).symm d = v := by
    refine ⟨c, ⟨hc, heq⟩, ?_⟩
    intro d hd
    apply (adj.homEquiv _ _).symm.injective
    exact (cancel_epi a).mp (hd.2.trans heq.symm)
  let := (Padic.coefficientExtensionAbsoluteValue l E).toNormedField
  have : Finite (Padic.coefficientExtensionRing l E 1) :=
    Padic.finite_coefficientExtensionRing l E 1 le_rfl
  have : DiscreteTopology (Padic.coefficientExtensionRing l E 1) :=
    DerivedNakayama.quotientDiscrete l E 1
  have hA : (l ^ 1 : Padic.coefficientExtensionRing l E 1) = 0 := by
    let O := Padic.coefficientExtensionIntegers l E
    let π := Padic.coefficientExtensionUniformizer l E
    have h := (Padic.extension_integers_dvr l E (Padic.coefficientExtensionAbsoluteValue l E)
      (spectralNorm_extends (K := Padic l) (L := E))).choose_spec.choose_spec
    have hgen : Ideal.span ({π} : Set O) = Padic.coefficientExtensionMaximalIdeal l E :=
      h.2.2.2.2.2.2.2.2.2.2.2.2.2.1.choose_spec
    have hval : Padic.coefficientExtensionAbsoluteValue l E (l : E) < 1 := by
      have hext := spectralNorm_extends (K := Padic l) (L := E) (l : Padic l)
      change spectralNorm (Padic l) E (l : E) < 1
      simpa only [map_natCast] using hext.trans_lt (Padic.norm_p_lt_one (p := l))
    have hl : (l : O) ∈ Ideal.span ({π} : Set O) := by
      rw [hgen]
      exact (h.2.1 (l : O)).mpr hval
    have hp : (l : O) ^ 1 ∈ Padic.coefficientExtensionIdeal l E 1 :=
      Ideal.pow_mem_pow hl 1
    have hz := Ideal.Quotient.eq_zero_iff_mem.mpr hp
    simpa only [map_pow, map_natCast] using hz
  have hfinite := (openDirectImage_field_finiteness_and_baseChange_current
    k _hbase l _hchar (Padic.coefficientExtensionRing l E 1) 1 le_rfl hA
    (U ↘ Spec (.of k)) (X ↘ Spec (.of k)) j (comp_over j (Spec (.of k))) K₁ hKU.2).1
  have : (constantModelBoundedConstructible
      (DerivedNakayama.quotientRing l E 1) X).IsClosedUnderIsomorphisms :=
    (constantModelConstructibleFiniteTor_wellDefined
      (DerivedNakayama.quotientRing l E 1) X).2.1
  have hred := ObjectProperty.prop_of_iso
    (constantModelBoundedConstructible (DerivedNakayama.quotientRing l E 1) X)
    (asIso c).symm hfinite
  have hHX : constantModelBoundedConstructible (DerivedNakayama.integerRing l E) X H :=
    ((condensed_integral_criterion l E X H).out 0 1).mpr
      (show IsDerivedComplete l E X H ∧
        constantModelBoundedConstructible (DerivedNakayama.quotientRing l E 1) X
          ((AdicCompletion.derivedReduction l E X 0).obj H) from ⟨hcomplete, hred⟩)
  refine ⟨hcomplete, ?_, hHX, ?_⟩
  · simpa only [a, χ, integralReductionPullbackMap,
      FreeParameterEvaluation.scalarPullComparison, AdicCompletion.quotient,
      coefficientMap, CondensedRing.moduleObjectDerivedPushforward,
      Nat.zero_add, H, adj, v, Functor.id_obj,
      Adjunction.homEquiv_counit, Category.assoc] using hcanonical
  · funext M
    apply propext
    exact (condensed_integral_criterion l E X M).out 0 3

end AlgebraicGeometry.ProEtale
