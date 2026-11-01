/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.IntegralFiniteExtension.CoefIntegralFiniteExtensionModels
public import WeilConjectures.AlgebraicGeometry.DualizingOpenMate.DualizingOpenMate
import WeilConjectures.AlgebraicGeometry.Etale.EtaleSystemQuotientNormalization
import WeilConjectures.AlgebraicGeometry.Sf.SfBcAdicRingDomain

/-! # The cross-field dualizing counit on an affine scheme

Source: current blueprint lem-coef-integral-finite-extension.proof.md, paragraph 2,
and lem-coef-finite-dualizing.proof.md, affine closed-chart argument.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option linter.style.haveILetI false
universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.IntegralFiniteExtension

/-- On an affine finite-type scheme, the coefficient-extension mate of the dualizing
counit is invertible, including the native (possibly nonflat) quotient levels.

Source: current blueprint lem-coef-integral-finite-extension.proof.md, paragraph 2,
and lem-coef-finite-dualizing.proof.md, paragraphs 2--3.
(blueprint: lem-sf-integral-finite-extension-affine-counit)

Proof: write R = O_E and S = O_L, and let e be the ramification index.
The quotient S/(pi_E^(n+1)) is finite free over R/(pi_E^(n+1)).
Apply the finite-free exceptional counit comparison at this cofinal level.
Identify its upper coefficient ring with S/(pi_L^(e*(n+1))) using the
unit-times-uniformizer relation. The finite dualizing quotient theorem over L
then reduces from exponent e*(n+1) to exponent n+1. The counit composition
identity identifies the composite of these two invertible comparisons with the
native quotient comparison induced by ι. Scalar extension preserves the first
isomorphism, so the composite is invertible. This also explains why no flatness
of the native quotient map R/(pi_E^(n+1)) -> S/(pi_L^(n+1)) is asserted.
Transfer from the canonical exceptional adjoints to GA and GB using uniqueness
of right adjoints. Their counit equations identify the transported comparison
with exactly globalMate for c. The affine quotient calculation can equivalently
be computed in a closed affine-space chart by the finite-dualizing proof;
no open-cover descent or intrinsic site normalization is part of this lemma.
For Y empty the categories are zero. For an identity embedding the same
composition and adjunction identities give the identity comparison.
-/
theorem affineCounit_isIso
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
    (E L : Type u) [Field E] [Field L]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    [Algebra (Padic l) L] [FiniteDimensional (Padic l) L]
    (ι : E →ₐ[Padic l] L) (n : ℕ)
    (Y : Scheme.{u}) [IsAffine Y] (aY : Y ⟶ Spec (.of D.k))
    [IsSeparated aY] [LocallyOfFiniteType aY] [QuasiCompact aY]
    (c : Compactification aY)
    (GA : Etale.DerivedCategoryModule (finiteDualizingCoeff l E n) (Spec (.of D.k)) ⥤
      Etale.DerivedCategoryModule (finiteDualizingCoeff l E n) Y)
    (GB : Etale.DerivedCategoryModule (finiteDualizingCoeff l L n) (Spec (.of D.k)) ⥤
      Etale.DerivedCategoryModule (finiteDualizingCoeff l L n) Y)
    (aA : Etale.rightDerivedLowerShriekOfCompactification
      (ModuleCat.{u + 1} (finiteDualizingCoeff l E n)) c ⊣ GA)
    (aB : Etale.rightDerivedLowerShriekOfCompactification
      (ModuleCat.{u + 1} (finiteDualizingCoeff l L n)) c ⊣ GB) :
    IsIso (Etale.DualizingOpenMate.globalMate
      (RingHom.ulift.{u + 1, u + 1} (integralScalarQuotientMap l E L ι n))
      c GA GB aA aB) := by
  let A := finiteDualizingCoeff l E n
  let B := finiteDualizingCoeff l L n
  let φ : A →+* B :=
    RingHom.ulift.{u + 1, u + 1} (integralScalarQuotientMap l E L ι n)
  let : Finite A := Equiv.ulift.finite_iff.mpr
    (Padic.finite_coefficientExtensionRing l E (n + 1) (Nat.succ_pos n))
  let : Finite B := Equiv.ulift.finite_iff.mpr
    (Padic.finite_coefficientExtensionRing l L (n + 1) (Nat.succ_pos n))
  have hA : ∃ r : ℕ, (l ^ r : A) = 0 := by
    refine ⟨n + 1, ?_⟩
    apply ULift.down_injective
    have hz := (Scheme.sf_bc_adic_ring_domain l E).2.2.2.2.2.2.2.2.2
      (n + 1) (Nat.succ_pos n)
    change (l : Padic.coefficientExtensionRing l E (n + 1)) ^ (n + 1) = 0
    simpa only [nsmul_eq_mul, mul_one, Nat.cast_pow] using hz.2.1 1
  have hB : ∃ r : ℕ, (l ^ r : B) = 0 := by
    refine ⟨n + 1, ?_⟩
    apply ULift.down_injective
    change (l : Padic.coefficientExtensionRing l L (n + 1)) ^ (n + 1) = 0
    have hz := (Scheme.sf_bc_adic_ring_domain l L).2.2.2.2.2.2.2.2.2
      (n + 1) (Nat.succ_pos n)
    simpa only [nsmul_eq_mul, mul_one, Nat.cast_pow] using hz.2.1 1
  letI : (Spec (.of D.k)).Over (Spec (.of D.k)) := ⟨𝟙 _⟩
  letI : Y.Over (Spec (.of D.k)) := ⟨aY⟩
  have : LocallyOfFiniteType (Y ↘ Spec (.of D.k)) := ‹LocallyOfFiniteType aY›
  have : QuasiCompact (Y ↘ Spec (.of D.k)) := ‹QuasiCompact aY›
  have : aY.IsOver (Spec (.of D.k)) := ⟨by change aY ≫ 𝟙 _ = aY; exact Category.comp_id _⟩
  obtain ⟨q, hq, _, _, _, _, _, b, _, hc, _⟩ :=
    Etale.etaleCoefficientQuotientNormalization D l hl aY c A B hA hB φ GA GB aA aB
  have hi : IsIso (Etale.ExceptionalCoefficients.compactSupportMap φ c
      (GA.obj (Etale.constantComplex A (Spec (.of D.k))))) := by
    change IsIso ((Etale.compactScalarMap φ c).app _)
    rw [← hq]
    infer_instance
  have hinv : Etale.ExceptionalCoefficients.comparisonInverse φ c
      (GA.obj (Etale.constantComplex A (Spec (.of D.k)))) =
        q.inv.app (GA.obj (Etale.constantComplex A (Spec (.of D.k)))) := by
    unfold Etale.ExceptionalCoefficients.comparisonInverse
    rw [dif_pos hi]
    apply IsIso.inv_eq_of_hom_inv_id
    change (Etale.compactScalarMap φ c).app _ ≫ q.inv.app _ = _
    rw [← hq]
    exact q.hom_inv_id_app _
  have hb : aB.homEquiv _ _
      (q.inv.app (GA.obj (Etale.constantComplex A (Spec (.of D.k)))) ≫
        (Etale.scalarExtension φ (Spec (.of D.k))).map
          (aA.counit.app (Etale.constantComplex A (Spec (.of D.k))))) =
      b.hom.app (Etale.constantComplex A (Spec (.of D.k))) := by
    apply (aB.homEquiv _ _).symm.injective
    rw [Equiv.symm_apply_apply, Adjunction.homEquiv_counit]
    exact (hc _).symm
  have he : Etale.DualizingOpenMate.globalMate φ c GA GB aA aB =
      b.hom.app (Etale.constantComplex A (Spec (.of D.k))) ≫
        GB.map (Etale.ExceptionalCoefficients.unitIso φ (Spec (.of D.k))).hom := by
    unfold Etale.DualizingOpenMate.globalMate
    rw [hinv, ← Category.assoc, aB.homEquiv_naturality_right, hb]
  change IsIso (Etale.DualizingOpenMate.globalMate φ c GA GB aA aB)
  rw [he]
  infer_instance

end WeilConjectures.IntegralFiniteExtension
