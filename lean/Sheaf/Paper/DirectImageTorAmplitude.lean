/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NQ
-/
module

public import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
public import Sheaf.AlgebraicGeometry.BoundedConstructibleComplexes
public import Sheaf.AlgebraicGeometry.DerivedCategories
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import WeilConjectures.Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import WeilConjectures.SixFunctors.Etale.Derived.Coefficients
public import WeilConjectures.AlgebraicGeometry.IsConstructibleEtaleModuleSheaf
public import WeilConjectures.AlgebraicGeometry.IsConstructibleEtaleModuleSheaf
public import Sheaf.AlgebraicGeometry.EtaleTorAmplitude
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStarCoherence
public import WeilConjectures.SixFunctors.Etale.Derived.Tensor
import Sheaf.CategoryTheory.RightDerivedFunctorUpperBound
import WeilConjectures.SixFunctors.Etale.Derived.Finiteness.ConstructibleDirectImage
import Mathlib.RingTheory.Noetherian.Basic
import Mathlib.Algebra.CharP.Basic
import Sheaf.NumberTheory.Padics.ExtensionIntegersDvr
import Sheaf.AlgebraicGeometry.FiniteTypeDirectImageConstructibility
import Sheaf.AlgebraicGeometry.FiniteConstantProjectionFormula
import Sheaf.AlgebraicGeometry.ResidueTorAmplitudeTest
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian

/-!
# Direct image and finite Tor amplitude

Source: Weil conjectures blueprint, sec-six-functors/sk-prop-sf-rf-shriek-preservation,
`thm-sf-direct-image-tor-amplitude.md` (blueprint: thm-sf-direct-image-tor-amplitude).

The uniform cohomological-dimension hypothesis tests all ordinary etale module sheaves
for the present field. Both conclusions concern the ordinary derived direct image.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Etale

attribute [local irreducible] derivedTensor
-- Use the canonical ring instance when specializing generic lemmas to quotient coefficients.
-- Alternate instance paths otherwise make kernel checking unfold the quotient repeatedly.
attribute [local instance 20000] CommRing.toRing
-- Match the braidings in the existing derived tensor and residue-test constructions.
attribute [local instance 20000] SymmetricCategory.toBraidedCategory sheafBraidedCategory

private theorem torAmplitude_cohomology
    (A : Type (u + 1)) [CommRing A] (X : Scheme.{u}) (a b : ℤ)
    (K : DerivedCategoryModule A X) (hK : DerivedCategory.hasTorAmplitudeIn A X a b K)
    (M : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)) :
    ∀ i : ℤ, i < a ∨ b < i →
      IsZero ((_root_.DerivedCategory.homologyFunctor _ i).obj
        (((derivedTensor (ModuleCat.{u + 1} A) X).obj K).obj
          ((_root_.DerivedCategory.singleFunctor _ 0).obj M))) :=
  hK M

private theorem directImage_tensor_vanishing
    (A : Type (u + 1)) [CommRing A] [IsNoetherianRing A]
    {X Y : Scheme.{u}} (f : X ⟶ Y) (N : ℤ) (hN : 0 ≤ N)
    (hUDV : ∀ (M : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)) (r : ℤ), N < r →
      IsZero ((_root_.DerivedCategory.homologyFunctor _ r).obj
        ((rightDerivedLowerStar (ModuleCat.{u + 1} A) f).obj
          ((_root_.DerivedCategory.singleFunctor _ 0).obj M))))
    (a b : ℤ) (K : DerivedCategoryModule A X)
    (hTor : DerivedCategory.hasTorAmplitudeIn A X a b K)
    (hKle : ∃ c : ℤ, ∀ i : ℤ, c < i →
      IsZero ((_root_.DerivedCategory.homologyFunctor _ i).obj K))
    (M : ModuleCat.{u + 1} A) [Module.FinitePresentation A M] :
    ∀ i : ℤ, i < a ∨ b + N < i →
      IsZero ((_root_.DerivedCategory.homologyFunctor _ i).obj
        (((derivedTensor (ModuleCat.{u + 1} A) Y).obj
          ((rightDerivedLowerStar (ModuleCat.{u + 1} A) f).obj K)).obj
          ((_root_.DerivedCategory.singleFunctor _ 0).obj
            ((constantSheaf Y.smallEtaleTopology (ModuleCat.{u + 1} A)).obj M)))) := by
  classical
  let L := ((derivedTensor (ModuleCat.{u + 1} A) X).obj K).obj
    ((_root_.DerivedCategory.singleFunctor _ 0).obj
      ((constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)).obj M))
  have hL : ∀ i : ℤ, i < a ∨ b < i →
      IsZero ((_root_.DerivedCategory.homologyFunctor _ i).obj L) :=
    torAmplitude_cohomology A X a b K hTor
      ((constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)).obj M)
  let F := lowerStar (ModuleCat.{u + 1} A) f
  have hcd : ∀ (S : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)) (q : ℕ),
      N.toNat < q → IsZero ((F.rightDerived q).obj S) := by
    intro S q hq
    exact F.isZero_rightDerived_of_isZero_homology S q (hUDV S q (by omega))
  have hLge : L.IsGE a := (_root_.DerivedCategory.isGE_iff L a).2
    (fun i hi ↦ hL i (Or.inl hi))
  have hLle : L.IsLE b := (_root_.DerivedCategory.isLE_iff L b).2
    (fun i hi ↦ hL i (Or.inr hi))
  have hRge := F.isGE_rightDerivedFunctor_obj L a
  have hRle := F.isLE_rightDerivedFunctor_obj_of_dimension N.toNat hcd L b hLle
  have hR : ∀ i : ℤ, i < a ∨ b + N < i →
      IsZero ((_root_.DerivedCategory.homologyFunctor _ i).obj
        (F.rightDerivedFunctor.obj L)) := by
    intro i hi
    rcases hi with hi | hi
    · exact (_root_.DerivedCategory.isGE_iff _ a).1 hRge i hi
    · exact (_root_.DerivedCategory.isLE_iff _ (b + N.toNat)).1 hRle i (by omega)
  have : IsIso ((finiteConstantProjectionMap A f K).app M) :=
    isIso_finiteConstantProjectionMap A f N.toNat
      (fun S q hq ↦ hUDV S q (by omega)) K hKle M
  let e : ((derivedTensor (ModuleCat.{u + 1} A) Y).obj
      (F.rightDerivedFunctor.obj K)).obj
        ((_root_.DerivedCategory.singleFunctor _ 0).obj
          ((constantSheaf Y.smallEtaleTopology (ModuleCat.{u + 1} A)).obj M)) ≅
      F.rightDerivedFunctor.obj L :=
    asIso ((finiteConstantProjectionMap A f K).app M)
  intro i hi
  exact (hR i hi).of_iso ((_root_.DerivedCategory.homologyFunctor _ i).mapIso e)

private theorem coefficient_hcoeff
    (k : Type u) [Field k] [IsAlgClosed k]
    (l : ℕ) [Fact l.Prime] (_hl : l ≠ ringChar k)
    (E : Type (u + 1)) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (n : ℕ) (hn : 1 ≤ n) :
    IsSmoothBaseChangeCoefficients (l ^ n)
      (Padic.coefficientExtensionRing l E n) (Spec (.of k)) := by
  have := Padic.finite_coefficientExtensionRing l E n hn
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
  have hkill : ((l ^ n : ℕ) : Padic.coefficientExtensionRing l E n) = 0 := by
    change ((l ^ n : ℕ) :
      Padic.coefficientExtensionIntegers l E ⧸ Padic.coefficientExtensionIdeal l E n) = 0
    rw [← map_natCast (Ideal.Quotient.mk (Padic.coefficientExtensionIdeal l E n)),
      Ideal.Quotient.eq_zero_iff_mem]
    simpa only [Nat.cast_pow] using hpow
  have hlk : (l : k) ≠ 0 := fun hz ↦
    _hl (CharP.ringChar_of_prime_eq_zero (Fact.out : l.Prime) hz).symm
  have hu : IsUnit ((l ^ n : ℕ) : k) := by
    rw [Nat.cast_pow]
    exact (isUnit_iff_ne_zero.mpr hlk).pow n
  exact ⟨pow_pos (Fact.out : l.Prime).pos n, inferInstance, hkill,
    by simpa only [map_natCast] using hu.map (Scheme.ΓSpecIso (.of k)).inv.hom⟩

private theorem residue_finite
    (l : ℕ) [Fact l.Prime] (E : Type (u + 1)) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (n : ℕ) (hn : 1 ≤ n) :
    Finite (Padic.coefficientExtensionResidueModule l E n) := by
  have := Padic.finite_coefficientExtensionRing l E n hn
  dsimp [Padic.coefficientExtensionResidueModule]
  exact Finite.of_surjective
    (Ideal.Quotient.mk
      (Ideal.span ({Ideal.Quotient.mk (Padic.coefficientExtensionIdeal l E n)
        (Padic.coefficientExtensionUniformizer l E)} : Set
          (Padic.coefficientExtensionRing l E n))))
    Ideal.Quotient.mk_surjective

private theorem directImage_torAmplitude_of_residue_test
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} (f : X ⟶ Y) (N : ℤ) (hN : 0 ≤ N)
    (hUDV : ∀ (M : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)) (r : ℤ), N < r →
      IsZero ((_root_.DerivedCategory.homologyFunctor _ r).obj
        ((rightDerivedLowerStar (ModuleCat.{u + 1} A) f).obj
          ((_root_.DerivedCategory.singleFunctor _ 0).obj M))))
    (a b : ℤ) (K : DerivedCategoryModule A X)
    (hK : DerivedCategory.isBoundedConstructible A X K)
    (hTor : DerivedCategory.hasTorAmplitudeIn A X a b K)
    (M : ModuleCat.{u + 1} A) [Finite M]
    (htest : (∀ i : ℤ, i < a ∨ b + N < i →
      IsZero ((_root_.DerivedCategory.homologyFunctor _ i).obj
        (((derivedTensor (ModuleCat.{u + 1} A) Y).obj
          ((rightDerivedLowerStar (ModuleCat.{u + 1} A) f).obj K)).obj
          ((_root_.DerivedCategory.singleFunctor _ 0).obj
            ((constantSheaf Y.smallEtaleTopology (ModuleCat.{u + 1} A)).obj M))))) →
      DerivedCategory.hasTorAmplitudeIn A Y a (b + N)
        ((rightDerivedLowerStar (ModuleCat.{u + 1} A) f).obj K)) :
    DerivedCategory.hasTorAmplitudeIn A Y a (b + N)
      ((rightDerivedLowerStar (ModuleCat.{u + 1} A) f).obj K) := by
  have : IsNoetherianRing A := isNoetherian_of_finite A A
  have : Module.Finite A M := Module.Finite.of_finite
  have : Module.FinitePresentation A M := Module.finitePresentation_of_finite A M
  obtain ⟨c, d, _, hvan⟩ := hK.2
  exact htest (directImage_tensor_vanishing A f N hN hUDV a b K hTor
    ⟨d, fun i hi ↦ hvan i (Or.inr hi)⟩ M)

/-- Direct image sends a bounded constructible complex of Tor amplitude `[a,b]` to a
bounded constructible complex of Tor amplitude `[a,b+N]`, assuming uniform vanishing
above `N` on every module sheaf.
Source: Weil blueprint, sec-six-functors/sk-prop-sf-rf-shriek-preservation,
`thm-sf-direct-image-tor-amplitude.md` (blueprint: thm-sf-direct-image-tor-amplitude).

Proof:
1. The coefficient conventions and lem-weil-l-adic-extension-integers-dvr put l in
   the maximal ideal generated by the uniformizer. Thus l^n annihilates A, and l^n
   is invertible in k. By lem-weil-valued-dvr-finite-quotients, A is finite and hence
   Noetherian. Finite-type constructibility gives bounded constructibility of Rf_*K.
2. Put L = K tensor^L kappa_X. The Tor-amplitude hypothesis makes L lie in degrees
   [a,b]. Convert the uniform vanishing hypothesis to classical right-derived
   vanishing. Apply lem-etale-derived-functor-upper-amplitude for the upper bound
   b+N and left t-exactness for the lower bound a. This bounds Rf_*L in [a,b+N].
3. The residue module kappa is a quotient of finite A, hence finitely presented
   over Noetherian A. Bounded constructibility of K supplies its upper bound.
   Apply lem-sf-projection-finite-constant to identify Rf_*K tensor^L kappa_Y with
   Rf_*L, and transport the cohomology vanishing along this isomorphism.
4. Apply lem-exc-residue-tor-test to the bounded constructible Rf_*K to obtain
   its Tor amplitude [a,b+N]. Together with Step 1 this proves both clauses. -/
theorem sf_directImage_torAmplitude
    (k : Type u) [Field k] [IsAlgClosed k]
    (l : ℕ) [Fact l.Prime] (_hl : l ≠ ringChar k)
    (E : Type (u + 1)) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (n : ℕ) (hn : 1 ≤ n)
    {X Y : Scheme.{u}} (aX : X ⟶ Spec (.of k)) (aY : Y ⟶ Spec (.of k))
    [LocallyOfFiniteType aX] [QuasiCompact aX]
    [LocallyOfFiniteType aY] [QuasiCompact aY]
    (f : X ⟶ Y) (_hf : f ≫ aY = aX)
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (N : ℤ) (_hN : 0 ≤ N)
    (_hUDV : ∀ (M : Sheaf X.smallEtaleTopology
        (ModuleCat.{u + 1} (Padic.coefficientExtensionRing l E n))) (r : ℤ), N < r →
      IsZero ((_root_.DerivedCategory.homologyFunctor _ r).obj
        ((rightDerivedLowerStar
          (ModuleCat.{u + 1} (Padic.coefficientExtensionRing l E n)) f).obj
            ((_root_.DerivedCategory.singleFunctor _ 0).obj M))))
    (a b : ℤ) (_hab : a ≤ b)
    (K : DerivedCategoryModule (Padic.coefficientExtensionRing l E n) X)
    (_hK : @DerivedCategory.isBoundedConstructible (Padic.coefficientExtensionRing l E n)
      _ (Padic.finite_coefficientExtensionRing l E n hn) X K)
    (_hTor : DerivedCategory.hasTorAmplitudeIn (Padic.coefficientExtensionRing l E n) X a b K) :
    @DerivedCategory.isBoundedConstructible (Padic.coefficientExtensionRing l E n)
        _ (Padic.finite_coefficientExtensionRing l E n hn) Y
        ((rightDerivedLowerStar
          (ModuleCat.{u + 1} (Padic.coefficientExtensionRing l E n)) f).obj K) ∧
      DerivedCategory.hasTorAmplitudeIn (Padic.coefficientExtensionRing l E n) Y a (b + N)
        ((rightDerivedLowerStar
          (ModuleCat.{u + 1} (Padic.coefficientExtensionRing l E n)) f).obj K) := by
  have : Finite (Padic.coefficientExtensionRing l E n) :=
    Padic.finite_coefficientExtensionRing l E n hn
  have hR := isBoundedConstructible_rightDerivedLowerStar_of_finiteType_over_field
    k (Padic.coefficientExtensionRing l E n) (l ^ n)
    (coefficient_hcoeff k l _hl E n hn) aX aY f _hf K _hK
  refine ⟨hR, ?_⟩
  have : Finite (Padic.coefficientExtensionResidueModule l E n) :=
    residue_finite l E n hn
  exact directImage_torAmplitude_of_residue_test (Padic.coefficientExtensionRing l E n)
    f N _hN _hUDV a b K _hK _hTor (Padic.coefficientExtensionResidueModule l E n)
    (residue_tor_amplitude_test l E n hn Y a (b + N) _ hR).2

end AlgebraicGeometry.Etale
