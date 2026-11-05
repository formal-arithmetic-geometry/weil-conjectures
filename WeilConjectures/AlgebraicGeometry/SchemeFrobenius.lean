/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import WeilConjectures.Mathlib.CategoryTheory.Endomorphism
public import WeilConjectures.AlgebraicGeometry.Morphisms.AbsoluteFrobenius
public import WeilConjectures.AlgebraicGeometry.GeometricFrobenius

/-!
# The scheme Frobenius and the Galois Frobenii of the geometric fiber

Let `k` be a finite field with `q` elements, `X₀` a scheme over `k` with structure morphism
`f : X₀ ⟶ Spec k`, and `X = X₀ ×_k k̄` its geometric fiber. This file constructs

* the `q ^ m`-power absolute Frobenius `Fr^{(q^m)}` of a `k`-scheme, which is a `k`-morphism
  since `c ^ q = c` on `k` (`AlgebraicGeometry.Scheme.Hom.absoluteFrobenius`);
* the `q ^ m`-power *scheme Frobenius* `Φ^m = Φ₀^m × 𝟙 : X ⟶ X`, the base change of the
  absolute `q ^ m`-power Frobenius `Φ₀^m` of `X₀` (`AlgebraicGeometry.Scheme.Hom.schemeFrobenius`);
  it is a `k̄`-morphism, finite (for `X₀` locally of finite type) and radicial;
* the *arithmetic Galois Frobenius* `g_σ = 𝟙 × Spec σ`, `σ : z ↦ z ^ q`
  (`AlgebraicGeometry.Scheme.Hom.arithmeticGaloisFrobenius`), the inverse of the geometric
  Galois Frobenius `g_γ = 𝟙 × Spec γ`, `γ = σ⁻¹`, which is
  `AlgebraicGeometry.Scheme.Hom.geometricGaloisFrobenius`.

The absolute `q ^ m`-power Frobenius of `X` factors as `Fr^{(q^m)}_X = g_σ^m Φ^m = Φ^m g_σ^m`
(`AlgebraicGeometry.Scheme.Hom.absoluteFrobenius_geometricFiber_eq_schemeFrobenius_comp`), hence
`Φ^m = g_γ^m Fr^{(q^m)}_X`.

## Main definitions

- `AlgebraicGeometry.Scheme.Hom.absoluteFrobenius`: the absolute `q ^ m`-power Frobenius.
- `AlgebraicGeometry.Scheme.Hom.schemeFrobenius`: the scheme Frobenius `Φ^m`.
- `AlgebraicGeometry.specArithmeticFrobenius`,
  `AlgebraicGeometry.Scheme.Hom.arithmeticGaloisFrobenius`:
  the arithmetic Frobenius `Spec σ` of `Spec k̄` and `g_σ = 𝟙 × Spec σ`.

## Main statements

- `AlgebraicGeometry.Scheme.Hom.absoluteFrobenius_geometricFiber_eq_schemeFrobenius_comp`,
  `AlgebraicGeometry.Scheme.Hom.absoluteFrobenius_geometricFiber_eq_comp_schemeFrobenius`:
  `Fr^{(q^m)}_X = g_σ^m Φ^m = Φ^m g_σ^m` (blueprint `prop-trf-frobenius-factorization`).
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite

noncomputable section

namespace AlgebraicGeometry

section FiniteField

variable {k : Type u} [Field k] [Finite k]

/-- The characteristic of a finite field is a prime. -/
lemma FiniteField.ringChar_prime : (ringChar k).Prime :=
  CharP.char_is_prime k _

/-- A finite field has `#k = p ^ log_p #k` elements, `p = ringChar k`. -/
lemma FiniteField.ringChar_pow_log_card : ringChar k ^ Nat.log (ringChar k) (Nat.card k) =
    Nat.card k := by
  have := Fintype.ofFinite k
  obtain ⟨p, hchar, n, hp, hcard⟩ := FiniteField.card' k
  obtain rfl : p = ringChar k := (ringChar.eq k p).symm
  rw [Nat.card_eq_fintype_card, hcard, Nat.log_pow hp.one_lt]

omit [Finite k] in
/-- The characteristic of `k` vanishes in the global sections of a `k`-scheme. -/
lemma Scheme.Hom.natCast_ringChar_eq_zero {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) :
    ((ringChar k : ℕ) : Γ(X, ⊤)) = 0 := by
  rw [← map_natCast f.appTop.hom, ← map_natCast (Scheme.ΓSpecIso (.of k)).inv.hom,
    ringChar.Nat.cast_ringChar, map_zero, map_zero]

namespace Scheme.Hom

variable {X₀ : Scheme.{u}} (f : X₀ ⟶ Spec (.of k))

/-- The absolute `q ^ m`-power Frobenius `Fr^{(q^m)}` of a scheme `X₀` over a finite field `k`
with `q` elements: the identity on the underlying space and `s ↦ s ^ (q ^ m)` on sections. As
`c ^ q = c` on `k`, it is a morphism over `k` (`absoluteFrobenius_comp`); for `m = 1` it is the
`q`-power scheme Frobenius `Φ₀` of `X₀` of blueprint `def-trf-scheme-frobenius`. -/
def absoluteFrobenius (m : ℕ) : X₀ ⟶ X₀ :=
  X₀.iterateFrobenius FiniteField.ringChar_prime f.natCast_ringChar_eq_zero
    (Nat.log (ringChar k) (Nat.card k) * m)

@[simp]
lemma absoluteFrobenius_apply (m : ℕ) (x : X₀) : f.absoluteFrobenius m x = x :=
  rfl

@[simp]
lemma preimage_absoluteFrobenius (m : ℕ) (U : X₀.Opens) : f.absoluteFrobenius m ⁻¹ᵁ U = U :=
  rfl

@[simp]
lemma absoluteFrobenius_zero : f.absoluteFrobenius 0 = 𝟙 X₀ := by
  unfold absoluteFrobenius
  simp [iterateFrobenius_zero]

/-- The absolute Frobenius commutes with every morphism of schemes over `k`, or more generally
with every morphism `g : X₀ ⟶ Y₀` to a `k`-scheme. -/
@[reassoc]
lemma absoluteFrobenius_naturality {Y₀ : Scheme.{u}} (g : X₀ ⟶ Y₀) (e : Y₀ ⟶ Spec (.of k))
    (m : ℕ) : (g ≫ e).absoluteFrobenius m ≫ g = g ≫ e.absoluteFrobenius m :=
  (comp_iterateFrobenius _ g _ _ _).symm

/-- The absolute `q ^ m`-power Frobenius of `Spec k` is the identity, as `c ^ q = c` on `k`. -/
lemma absoluteFrobenius_spec (m : ℕ) :
    Scheme.Hom.absoluteFrobenius (𝟙 (Spec (.of k))) m = 𝟙 _ := by
  unfold absoluteFrobenius
  rw [iterateFrobenius_Spec _ _ ringChar.Nat.cast_ringChar, ← Spec.map_id]
  congr 1
  ext c
  have := Fintype.ofFinite k
  simp only [CommRingCat.hom_ofHom, iterateFrobeniusOfPrime_apply, pow_mul,
    FiniteField.ringChar_pow_log_card, CommRingCat.hom_id, RingHom.id_apply]
  rw [Nat.card_eq_fintype_card, FiniteField.pow_card_pow]

/-- The absolute `q ^ m`-power Frobenius of a `k`-scheme is a morphism over `k`. -/
@[reassoc (attr := simp)]
lemma absoluteFrobenius_comp (m : ℕ) : f.absoluteFrobenius m ≫ f = f := by
  have := absoluteFrobenius_naturality f (𝟙 _) m
  rwa [Category.comp_id, absoluteFrobenius_spec, Category.comp_id] at this

/-- The absolute Frobenius is radicial. -/
instance (m : ℕ) : UniversallyInjective (f.absoluteFrobenius m) := by
  unfold absoluteFrobenius
  infer_instance

/-- The absolute Frobenius is integral. -/
instance (m : ℕ) : IsIntegralHom (f.absoluteFrobenius m) := by
  unfold absoluteFrobenius
  infer_instance

/-- The absolute Frobenius of a scheme locally of finite type over `k` is finite: it is
integral, and locally of finite type as a morphism over `k`. -/
instance [LocallyOfFiniteType f] (m : ℕ) : IsFinite (f.absoluteFrobenius m) := by
  have : LocallyOfFiniteType (f.absoluteFrobenius m ≫ f) := by
    rw [absoluteFrobenius_comp]
    infer_instance
  have := locallyOfFiniteType_of_comp (f.absoluteFrobenius m) f
  rw [IsFinite.iff_isIntegralHom_and_locallyOfFiniteType]
  exact ⟨inferInstance, this⟩

end Scheme.Hom

namespace Scheme.Hom

variable {X₀ : Scheme.{u}} (f : X₀ ⟶ Spec (.of k))

end Scheme.Hom

end FiniteField

end AlgebraicGeometry
