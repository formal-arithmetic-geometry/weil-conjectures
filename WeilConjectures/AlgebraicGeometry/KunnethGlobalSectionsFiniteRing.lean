/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.KunnethGlobalSections
public import WeilConjectures.Compactification.FiniteFieldDatum.FiniteFieldFiberSupplement
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import WeilConjectures.NumberTheory.Padics.ExtensionIntegersDvr

/-!
# Ordinary Künneth at a finite coefficient ring

The exterior-product map is the canonical Künneth map `kunnethGlobalSectionsMap`, on the
unbounded derived categories `DerivedCategoryModule`, with the ordinary derived tensor
`derivedTensor`, at the coefficient ring
`Padic.coefficientExtensionRing l E n = 𝒪_E / ϖ_E ^ n`.

## Main statements

- `isIso_kunnethGlobalSectionsMap_finiteCoefficientRing`: the exterior-product map is an
  isomorphism for arbitrary unbounded complexes.

## Implementation details

The separable closedness of `D.k` used to form the map comes from its specified algebraic
closure structure (a proposition; any proof gives the same map).

## References

* Stacks Project, Tag 0F1P.
-/

@[expose] public section

set_option autoImplicit false
set_option linter.style.haveILetI false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Etale

attribute [local instance 2000] CommRing.toRing

/-- Ordinary Künneth at a finite coefficient ring. Let `k = D.k` be the algebraically closed
field of the finite-field datum `D`, let `X, Y` be separated finite-type `k`-schemes, let
`A = 𝒪_E / ϖ_E ^ n` for a finite extension `E / ℚ_l` and `n ≥ 1`, with `l ≠ char k`. For
`K ∈ D(X_ét, A)` and `M ∈ D(Y_ét, A)`, the exterior-product map
`RΓ(X, K) ⊗ᴸ_A RΓ(Y, M) ⟶ RΓ(X ×_k Y, p_X^* K ⊗ᴸ_A p_Y^* M)` is an isomorphism
(Stacks, Tag 0F1P). -/
theorem isIso_kunnethGlobalSectionsMap_finiteCoefficientRing
    (D : WeilConjectures.FiniteFieldDatum.{u})
    (l : ℕ) [Fact l.Prime] (hl : l ≠ ringChar D.k)
    (E : Type (u + 1)) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (n : ℕ) (hn : 1 ≤ n)
    (X Y : Over (Spec (CommRingCat.of D.k)))
    [IsSeparated X.hom] [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
    [IsSeparated Y.hom] [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom]
    (K : DerivedCategoryModule (Padic.coefficientExtensionRing l E n) X.left)
    (M : DerivedCategoryModule (Padic.coefficientExtensionRing l E n) Y.left) :
    letI : IsAlgClosed D.k := IsAlgClosure.isAlgClosed D.k₀
    IsIso (kunnethGlobalSectionsMap (Padic.coefficientExtensionRing l E n)
      (pullback.fst X.hom Y.hom) (pullback.snd X.hom Y.hom) X.hom Y.hom
      pullback.condition.symm K M) := by
  let Λ := Padic.coefficientExtensionRing l E n
  letI : IsAlgClosed D.k := IsAlgClosure.isAlgClosed D.k₀
  letI : Finite Λ := Padic.finite_coefficientExtensionRing l E n hn
  have hInv : HasInvertibleExponent Λ (Spec (CommRingCat.of D.k)) := by
    have hdvr := (Padic.coefficientExtensionIntegers_dvr l E).choose_spec
    have hm : (l : Padic.coefficientExtensionIntegers l E) ∈
        Padic.coefficientExtensionMaximalIdeal l E := by
      refine (hdvr.2.1 _).2 ?_
      change spectralNorm (Padic l) E (l : E) < 1
      rw [← map_natCast (algebraMap (Padic l) E),
        spectralNorm_extends (K := Padic l) (L := E)]
      exact Padic.norm_p_lt_one
    have hgen : Ideal.span ({Padic.coefficientExtensionUniformizer l E} :
        Set (Padic.coefficientExtensionIntegers l E)) =
        Padic.coefficientExtensionMaximalIdeal l E :=
      hdvr.2.2.2.2.2.2.2.2.2.2.2.2.2.1.choose_spec
    have hkill : ((l ^ n : ℕ) : Λ) = 0 := by
      rw [← map_natCast (Ideal.Quotient.mk _), Ideal.Quotient.eq_zero_iff_mem]
      rw [Nat.cast_pow]
      change (l : Padic.coefficientExtensionIntegers l E) ^ n ∈
        Ideal.span ({Padic.coefficientExtensionUniformizer l E} :
          Set (Padic.coefficientExtensionIntegers l E)) ^ n
      rw [hgen]
      exact Ideal.pow_mem_pow hm n
    have hlk : (l : D.k) ≠ 0 := fun hz ↦
      hl (CharP.ringChar_of_prime_eq_zero (Fact.out : l.Prime) hz).symm
    refine ⟨l ^ n, pow_pos (Nat.Prime.pos Fact.out) _, hkill, ?_⟩
    simpa only [map_pow, map_natCast, Nat.cast_pow] using
      ((Ne.isUnit hlk).pow n).map (Scheme.ΓSpecIso (.of D.k)).inv.hom
  have h := isIso_kunnethMap_of_isSepClosed (Λ := Λ) X.hom Y.hom
    (pullback.fst X.hom Y.hom) (pullback.snd X.hom Y.hom)
    (IsPullback.of_hasPullback X.hom Y.hom) K M
  letI := hInv
  unfold kunnethGlobalSectionsMap
  infer_instance

end AlgebraicGeometry.Etale
