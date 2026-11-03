/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.SixFunctors.Etale.Derived.Dualizing
public import WeilConjectures.SixFunctors.ProEtale.Comparison.Defs
public import WeilConjectures.Compactification.NagataCompactification

import WeilConjectures.AlgebraicGeometry.FiniteRingGeometricDualityFiniteField
import WeilConjectures.SixFunctors.Etale.Derived.VerdierBiduality
import WeilConjectures.SixFunctors.Etale.Derived.Shift
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Comparison

/-!
# No negative self-Hom for finite dualizing objects

Source: current blueprint, `part-duality-trace-formula/sec-smooth-purity/`
`sec-sp-grp-ladic-summary/sec-towers-and-integral-coefficients/sk-lem-sp-tower/`
`lem-coef-integral-finite-extension.proof.md`, paragraph beginning
"Their quotient compatibility", finite foundational rigidity sub-step.
(blueprint: lem-sf-finite-dualizing-negative-self-hom)

The finite pro-etale realization is the exact site pullback of the ordinary etale
dualizing complex. This is the same object used in the general-field finite dualizing
coefficient-change package, with the exceptional-adjunction counit normalization.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory Limits MonoidalCategory Opposite

namespace AlgebraicGeometry.Etale

/-- The finite dualizing object has no self-morphisms of degree minus one.

Source: current blueprint `part-duality-trace-formula/sec-smooth-purity/`
`sec-sp-grp-ladic-summary/sec-towers-and-integral-coefficients/sk-lem-sp-tower/`
`lem-coef-integral-finite-extension.proof.md`, coherent derived-tower paragraph;
the finite foundational rigidity input isolated by
(blueprint: lem-sf-finite-dualizing-negative-self-hom).

Proof:
1. `A = R/t^n` is killed by `ell^n`: the spectral norm of `ell` is `< 1`, so `ell` lies in
the maximal ideal `(t)` and `ell^n` in `(t)^n`. As `ell ≠ p`, `ell^n` is invertible on
`Spec k`, hence on `X`. The etale tensor unit `U = A_X` is the degree-zero single of a flat
object, so it is bounded constructible with Tor amplitude [0,0].
2. Finite geometric biduality makes `delta_U` invertible: over an algebraically closed
field by `lem-sf-finite-ring-geometric-duality`, over a finite field by
`lem-sf-finite-ring-geometric-duality-finite-field` (field-extension descent).
With the closed-category unit isomorphism `D(U) ≅ omega` (`def-sf-finite-etale-duality`)
this gives `D(omega) = RHom(omega, omega) ≅ U`.
3. On the ordinary etale derived category, shift adjunction, `omega ⊗ U[1] ≅ omega[1]`
and tensor-Hom adjunction identify `Hom(omega, omega[-1])` with `Hom(U[1], U)`, which is
zero by orthogonality of the standard t-structure (`U[1]` in `D≤-1`, `U` in `D≥0`).
4. Both allowed fields are perfect, so Verdier preservation puts `D(U) ≅ omega` in the
bounded constructible finite-Tor objects; thus `omega[-1]` is bounded below. Full
faithfulness of the exact comparison pullback on bounded-below targets
(`lem-weil-pbc-fixed-module-derived-hom-bijection`, Stacks Tag 099V) and its commutation
with shifts transport the vanishing to the stated pro-etale realization.
-/
theorem finiteDualizing_negative_self_hom
    (k : Type u) [Field k] (p l : ℕ) (_hp : p.Prime) (_hchar : ringChar k = p)
    (_hk : Finite k ∨ IsAlgClosed k) [Fact l.Prime] (_hlp : l ≠ p)
    (E : Type (u + 1)) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    {X : Scheme.{u}} (a : X ⟶ Spec (CommRingCat.of k))
    [IsSeparated a] [LocallyOfFiniteType a] [QuasiCompact a]
    (n : ℕ) (hn : 1 ≤ n) :
    letI : Finite (Padic.coefficientExtensionRing l E n) :=
      Padic.finite_coefficientExtensionRing l E n hn
    let ω := (ProEtale.comparisonUpperStar
      (ModuleCat.{u + 1} (Padic.coefficientExtensionRing l E n)) X).mapDerivedCategory.obj
        (dualizingComplex (Padic.coefficientExtensionRing l E n) a)
    Subsingleton (ω ⟶ ω⟦(-1 : ℤ)⟧) := by
  let A := Padic.coefficientExtensionRing l E n
  let : Finite A := Padic.finite_coefficientExtensionRing l E n hn
  let : HasCompactification a := (NagataCompactification a).hasCompactification
  -- The coefficient quotient is killed by a power of the coefficient prime.
  have hkill : (l ^ n : A) = 0 := by
    have h := (Padic.extension_integers_dvr l E (Padic.coefficientExtensionAbsoluteValue l E)
      (spectralNorm_extends (K := Padic l) (L := E))).choose_spec.choose_spec
    have habv : Padic.coefficientExtensionAbsoluteValue l E (l : E) < 1 := by
      calc
        Padic.coefficientExtensionAbsoluteValue l E (l : E) = ‖(l : Padic l)‖ := by
          change spectralNorm (Padic l) E (l : E) = ‖(l : Padic l)‖
          simpa only [map_natCast] using
            (spectralNorm_extends (K := Padic l) (L := E) (l : Padic l))
        _ < 1 := Padic.norm_p_lt_one
    have hlm : (l : Padic.coefficientExtensionIntegers l E) ∈
        Padic.coefficientExtensionMaximalIdeal l E :=
      (h.2.1 _).2 (by simpa only [SubringClass.coe_natCast] using habv)
    have hgen : Ideal.span ({Padic.coefficientExtensionUniformizer l E} :
        Set (Padic.coefficientExtensionIntegers l E)) =
        Padic.coefficientExtensionMaximalIdeal l E :=
      h.2.2.2.2.2.2.2.2.2.2.2.2.2.1.choose_spec
    have hpow : (l : Padic.coefficientExtensionIntegers l E) ^ n ∈
        Padic.coefficientExtensionIdeal l E n := by
      change _ ∈ Ideal.span ({Padic.coefficientExtensionUniformizer l E} :
        Set (Padic.coefficientExtensionIntegers l E)) ^ n
      rw [hgen]
      exact Ideal.pow_mem_pow hlm n
    rw [← Nat.cast_pow]
    change ((l ^ n : ℕ) :
      Padic.coefficientExtensionIntegers l E ⧸ Padic.coefficientExtensionIdeal l E n) = 0
    rw [← map_natCast (Ideal.Quotient.mk (Padic.coefficientExtensionIdeal l E n)),
      Ideal.Quotient.eq_zero_iff_mem]
    simpa only [Nat.cast_pow] using hpow
  have hell : (l : k) ≠ 0 := by
    intro hz
    exact _hlp ((CharP.ringChar_of_prime_eq_zero (Fact.out : l.Prime) hz).symm.trans _hchar)
  let : HasInvertibleExponent A (Spec (.of k)) := by
    refine ⟨l ^ n, pow_pos (Fact.out : l.Prime).pos n, ?_, ?_⟩
    · simpa only [Nat.cast_pow] using hkill
    · simpa only [map_pow, map_natCast, Nat.cast_pow] using
        ((isUnit_iff_ne_zero.mpr hell).pow n).map (Scheme.ΓSpecIso (.of k)).inv.hom
  let : HasInvertibleExponent A X := .of_hom a
  let U : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)) := 𝟙_ _
  let W := dualizingComplex A a
  have hU : DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} A) X U :=
    ⟨(DerivedCategory.boundedConstructible _ _).prop_of_iso
        (_root_.DerivedCategory.singleFunctorObjUnitIso _)
        (DerivedCategory.boundedConstructible_singleFunctor_obj _ 0), 0, 0,
      (DerivedCategory.torAmplitudeIn _ _ 0 0).prop_of_iso
        (_root_.DerivedCategory.singleFunctorObjUnitIso _)
        (_root_.DerivedCategory.torAmplitudeIn_singleFunctor_obj_of_flat
          (ObjectProperty.flat_of_isDualizable isDualizable_unit))⟩
  -- Biduality at the unit identifies RHom(W, W) with the unit.
  have hδ : IsIso ((verdierDualDoubleDual A a).app U) := by
    rcases _hk with hk | hk
    · let : Finite k := hk
      let : Fact p.Prime := ⟨_hp⟩
      let : CharP k p := _hchar ▸ inferInstanceAs (CharP k (ringChar k))
      exact isIso_verdierDualDoubleDual_app_finiteField p l (Ne.symm _hlp) k A
        ⟨n, hn, fun x ↦ by simp only [nsmul_eq_mul, Nat.cast_pow, hkill, zero_mul]⟩ a hU
    · let : IsAlgClosed k := hk
      exact isIso_verdierDualDoubleDual_app A a hU
  let := hδ
  let eU : (verdierDual A a).obj (op U) ≅ W := MonoidalClosed.unitIsoSelf W
  let eW : (verdierDual A a).obj (op W) ≅ U :=
    (verdierDual A a).mapIso eU.op ≪≫ (asIso ((verdierDualDoubleDual A a).app U)).symm
  -- Shift and curry to reduce the negative Hom to Hom(U[1], U).
  have hle : U.IsLE 0 :=
    _root_.DerivedCategory.TStructure.t.isLE_of_iso
      (_root_.DerivedCategory.singleFunctorObjUnitIso _) 0
  have hge : U.IsGE 0 :=
    _root_.DerivedCategory.TStructure.t.isGE_of_iso
      (_root_.DerivedCategory.singleFunctorObjUnitIso _) 0
  let := hle
  let := hge
  let : (U⟦(1 : ℤ)⟧).IsLE (-1) :=
    _root_.DerivedCategory.TStructure.t.isLE_shift U 0 1 (-1)
  have hz : Subsingleton (U⟦(1 : ℤ)⟧ ⟶ U) := ⟨fun f g ↦ by
    rw [_root_.DerivedCategory.TStructure.t.zero f (-1) 0,
      _root_.DerivedCategory.TStructure.t.zero g (-1) 0]⟩
  let := hz
  let t : W ⊗ U⟦(1 : ℤ)⟧ ≅ W⟦(1 : ℤ)⟧ :=
    (((derivedTensor (ModuleCat.{u + 1} A) X).obj W).commShiftIso 1).app U ≪≫
      (shiftFunctor _ (1 : ℤ)).mapIso (ρ_ W)
  let e := ((shiftEquiv _ (1 : ℤ)).toAdjunction.homEquiv W W).symm.trans
    ((Iso.homCongr t.symm (Iso.refl W)).trans
      (((derivedTensorHomAdjunction (ModuleCat.{u + 1} A) W).homEquiv _ W).trans
        (Iso.homCongr (Iso.refl _) eW)))
  have hW : Subsingleton (W ⟶ W⟦(-1 : ℤ)⟧) := e.injective.subsingleton
  let := hW
  -- Transport the external Hom through comparison on bounded-below targets.
  have hperfect : PerfectField k := by
    rcases _hk with hk | hk
    · let : Finite k := hk
      infer_instance
    · let : IsAlgClosed k := hk
      infer_instance
  let := hperfect
  have hbc := (DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} A) X).prop_of_iso
    eU (constructibleFiniteTor_verdierDual A a hU)
  have hplus : _root_.DerivedCategory.TStructure.t.plus (W⟦(-1 : ℤ)⟧) := by
    obtain ⟨m, hm⟩ := hbc.1.1.1
    let := hm
    exact ⟨m + 1, _root_.DerivedCategory.TStructure.t.isGE_shift W m (-1) (m + 1)⟩
  let F := (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) X).mapDerivedCategory
  let eF := Equiv.ofBijective (fun f : W ⟶ W⟦(-1 : ℤ)⟧ ↦ F.map f)
    (ProEtale.bijective_comparisonUpperStar_mapDerivedCategory_map W _ hplus)
  let eS := Iso.homCongr (Iso.refl (F.obj W)) ((F.commShiftIso (-1)).app W)
  exact (eS.symm.trans eF.symm).injective.subsingleton

end AlgebraicGeometry.Etale
