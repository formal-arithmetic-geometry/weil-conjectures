/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyInjective
public import Mathlib.FieldTheory.PurelyInseparable.Basic
public import Mathlib.RingTheory.RingHom.PurelyInseparable
public import WeilConjectures.AlgebraicGeometry.AbsoluteFrobenius
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

- `AlgebraicGeometry.Scheme.iterateFrobenius_naturality`: the absolute Frobenius is natural.
- `AlgebraicGeometry.Scheme.Hom.absoluteFrobenius_geometricFiber_eq_schemeFrobenius_comp`,
  `AlgebraicGeometry.Scheme.Hom.absoluteFrobenius_geometricFiber_eq_comp_schemeFrobenius`:
  `Fr^{(q^m)}_X = g_σ^m Φ^m = Φ^m g_σ^m` (blueprint `prop-trf-frobenius-factorization`).
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite

noncomputable section

namespace AlgebraicGeometry

namespace Scheme

variable {p : ℕ} (hp : p.Prime)

/-- The absolute Frobenius is natural: `F_X ≫ g = g ≫ F_Y` for every morphism `g : X ⟶ Y` of
schemes in which `p` vanishes. -/
@[reassoc]
lemma iterateFrobenius_naturality {X Y : Scheme.{u}} (g : X ⟶ Y) (hX : (p : Γ(X, ⊤)) = 0)
    (hY : (p : Γ(Y, ⊤)) = 0) (n : ℕ) :
    X.iterateFrobenius hp hX n ≫ g = g ≫ Y.iterateFrobenius hp hY n := by
  refine Scheme.Hom.ext (by simp [Scheme.Hom.comp_base]; rfl) fun U ↦ ?_
  rw [Scheme.Hom.comp_app, Scheme.Hom.comp_app]
  ext s
  simp only [eqToHom_refl, op_id, CommRingCat.comp_apply]
  erw [X.presheaf.map_id, CommRingCat.id_apply]
  exact (map_pow (g.app U).hom s _).symm

/-- The `p ^ 0`-power Frobenius is the identity. -/
@[simp]
lemma iterateFrobenius_zero (X : Scheme.{u}) (hX : (p : Γ(X, ⊤)) = 0) :
    X.iterateFrobenius hp hX 0 = 𝟙 X := by
  refine Scheme.Hom.ext rfl fun U ↦ ?_
  ext s
  simp only [eqToHom_refl, op_id, CommRingCat.comp_apply, Scheme.Hom.id_app]
  erw [X.presheaf.map_id, CommRingCat.id_apply, CommRingCat.id_apply]
  exact pow_one s

/-- The Frobenius powers compose: `F^{p^m} ≫ F^{p^n} = F^{p^(m+n)}`. -/
lemma iterateFrobenius_add (X : Scheme.{u}) (hX : (p : Γ(X, ⊤)) = 0) (m n : ℕ) :
    X.iterateFrobenius hp hX (m + n) =
      X.iterateFrobenius hp hX m ≫ X.iterateFrobenius hp hX n := by
  refine Scheme.Hom.ext rfl fun U ↦ ?_
  rw [Scheme.Hom.comp_app]
  ext s
  simp only [eqToHom_refl, op_id, CommRingCat.comp_apply]
  erw [X.presheaf.map_id, CommRingCat.id_apply]
  exact (by rw [← pow_mul, ← pow_add, add_comm] : s ^ p ^ (m + n) = (s ^ p ^ n) ^ p ^ m)

/-- The absolute Frobenius of an affine scheme `Spec R` is `Spec` of the Frobenius of `R`. -/
lemma iterateFrobenius_Spec (R : CommRingCat.{u}) (hR : (p : R) = 0)
    (hX : (p : Γ(Spec R, ⊤)) = 0) (n : ℕ) :
    (Spec R).iterateFrobenius hp hX n =
      Spec.map (CommRingCat.ofHom (iterateFrobeniusOfPrime R hp hR n)) := by
  refine ext_of_isAffine ?_
  rw [← cancel_mono (ΓSpecIso R).hom, ΓSpecIso_naturality]
  ext s
  exact map_pow (ΓSpecIso R).hom.hom s _

/-- The residue field maps of the absolute Frobenius are the Frobenius of the residue
fields. -/
lemma iterateFrobenius_residueFieldMap_apply (X : Scheme.{u}) (hX : (p : Γ(X, ⊤)) = 0) (n : ℕ)
    (x : X) (a : X.residueField x) :
    (X.iterateFrobenius hp hX n).residueFieldMap x a = a ^ p ^ n := by
  obtain ⟨a, rfl⟩ := X.residue_surjective x a
  obtain ⟨U, hxU, s, rfl⟩ := X.presheaf.exists_germ_eq a
  have := congr($(Scheme.Hom.residue_residueFieldMap (X.iterateFrobenius hp hX n) x)
    (X.presheaf.germ U x hxU s))
  simp only [CommRingCat.comp_apply] at this
  rw [this, Scheme.Hom.germ_stalkMap_apply, iterateFrobenius_app_apply, map_pow, map_pow]
  rfl

/-- The absolute Frobenius is radicial (universally injective): it is the identity on points and
purely inseparable on residue fields. -/
instance (X : Scheme.{u}) (hX : (p : Γ(X, ⊤)) = 0) (n : ℕ) :
    UniversallyInjective (X.iterateFrobenius hp hX n) := by
  refine ((tfae_universallyInjective _).out 0 2).mpr ⟨fun x y h ↦ h, fun x ↦ ?_⟩
  have hκ : (p : X.residueField x) = 0 := by
    obtain ⟨U, hxU⟩ : ∃ U : X.Opens, x ∈ U := ⟨⊤, trivial⟩
    rw [← map_natCast (X.evaluation U x hxU).hom, natCast_eq_zero_of_natCast_top_eq_zero hX,
      map_zero]
  have : CharP (X.residueField x) p := (CharP.charP_iff_prime_eq_zero hp).2 hκ
  have : ExpChar (X.residueField x) p := .prime hp
  algebraize [((X.iterateFrobenius hp hX n).residueFieldMap x).hom]
  refine (isPurelyInseparable_iff_pow_mem _ p).mpr fun a ↦ ⟨n, a, ?_⟩
  exact iterateFrobenius_residueFieldMap_apply hp X hX n x a

/-- The absolute Frobenius is integral: every section `s` is a root of `T ^ (p ^ n) - s ^ (p ^ n)`
over the image. -/
instance (X : Scheme.{u}) (hX : (p : Γ(X, ⊤)) = 0) (n : ℕ) :
    IsIntegralHom (X.iterateFrobenius hp hX n) where
  isIntegral_app U _ s := by
    refine ⟨Polynomial.X ^ p ^ n - Polynomial.C s, Polynomial.monic_X_pow_sub_C _
      (pow_ne_zero _ hp.ne_zero), ?_⟩
    simp [iterateFrobenius_app_apply]

end Scheme

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

lemma absoluteFrobenius_eq_iterateFrobenius (m : ℕ) {p : ℕ} (hp : p.Prime)
    (hX : (p : Γ(X₀, ⊤)) = 0) (a : ℕ) (hq : Nat.card k = p ^ a) :
    f.absoluteFrobenius m = X₀.iterateFrobenius hp hX (a * m) := by
  have := Fintype.ofFinite k
  obtain ⟨p', hchar, n, hp', hcard⟩ := FiniteField.card' k
  rw [← Nat.card_eq_fintype_card, hq] at hcard
  obtain ⟨rfl, rfl⟩ := Nat.Prime.pow_inj hp hp' hcard
  obtain rfl : p = ringChar k := (ringChar.eq k p).symm
  rw [absoluteFrobenius, hq, Nat.log_pow hp.one_lt]

@[simp]
lemma absoluteFrobenius_apply (m : ℕ) (x : X₀) : f.absoluteFrobenius m x = x :=
  rfl

@[simp]
lemma preimage_absoluteFrobenius (m : ℕ) (U : X₀.Opens) : f.absoluteFrobenius m ⁻¹ᵁ U = U :=
  rfl

lemma absoluteFrobenius_app_apply (m : ℕ) (U : X₀.Opens) (s : Γ(X₀, U)) :
    (f.absoluteFrobenius m).app U s = s ^ (Nat.card k ^ m) := by
  rw [absoluteFrobenius, iterateFrobenius_app_apply, pow_mul, FiniteField.ringChar_pow_log_card]

@[simp]
lemma absoluteFrobenius_zero : f.absoluteFrobenius 0 = 𝟙 X₀ := by
  simp [absoluteFrobenius]

lemma absoluteFrobenius_add (m n : ℕ) :
    f.absoluteFrobenius (m + n) = f.absoluteFrobenius m ≫ f.absoluteFrobenius n := by
  simp only [absoluteFrobenius, mul_add, iterateFrobenius_add]

/-- The absolute Frobenius commutes with every morphism of schemes over `k`, or more generally
with every morphism `g : X₀ ⟶ Y₀` to a `k`-scheme. -/
@[reassoc]
lemma absoluteFrobenius_naturality {Y₀ : Scheme.{u}} (g : X₀ ⟶ Y₀) (e : Y₀ ⟶ Spec (.of k))
    (m : ℕ) : (g ≫ e).absoluteFrobenius m ≫ g = g ≫ e.absoluteFrobenius m :=
  iterateFrobenius_naturality _ _ _ _ _

/-- The absolute `q ^ m`-power Frobenius of `Spec k` is the identity, as `c ^ q = c` on `k`. -/
lemma absoluteFrobenius_spec (m : ℕ) : (𝟙 (Spec (.of k))).absoluteFrobenius m = 𝟙 _ := by
  rw [absoluteFrobenius, iterateFrobenius_Spec _ _ ringChar.Nat.cast_ringChar, ← Spec.map_id]
  congr 1
  ext c
  have := Fintype.ofFinite k
  simp only [CommRingCat.hom_ofHom, iterateFrobeniusOfPrime_apply, pow_mul,
    FiniteField.ringChar_pow_log_card, CommRingCat.hom_id, RingHom.id_apply,
    Nat.card_eq_fintype_card, FiniteField.pow_card_pow]

/-- The absolute `q ^ m`-power Frobenius of a `k`-scheme is a morphism over `k`. -/
@[reassoc (attr := simp)]
lemma absoluteFrobenius_comp (m : ℕ) : f.absoluteFrobenius m ≫ f = f := by
  have := absoluteFrobenius_naturality f (𝟙 _) m
  rwa [Category.comp_id, absoluteFrobenius_spec, Category.comp_id] at this

/-- The absolute Frobenius is radicial. -/
instance (m : ℕ) : UniversallyInjective (f.absoluteFrobenius m) := by
  unfold absoluteFrobenius
  infer_instance

/-- The absolute Frobenius of a scheme locally of finite type over `k` is finite: it is
integral, and locally of finite type as a morphism over `k`. -/
instance [LocallyOfFiniteType f] (m : ℕ) : IsFinite (f.absoluteFrobenius m) := by
  have : LocallyOfFiniteType (f.absoluteFrobenius m ≫ f) := by
    rw [absoluteFrobenius_comp]
    infer_instance
  have : LocallyOfFiniteType (f.absoluteFrobenius m) := .of_comp _ f
  have : IsIntegralHom (f.absoluteFrobenius m) := by
    unfold absoluteFrobenius
    infer_instance
  exact IsFinite.iff_isIntegralHom_and_locallyOfFiniteType.mpr ⟨inferInstance, inferInstance⟩

/-- Blueprint `def-trf-scheme-frobenius`: Scheme and Galois Frobenius of the geometric fiber.

Let `k` be a finite field with `q` elements, `X₀` a `k`-scheme and `X = X₀ ×_k k̄`. The
`q ^ m`-power *scheme Frobenius* `Φ^m := Φ₀^m × 𝟙 : X ⟶ X` is the base change to `k̄` of the
`q ^ m`-power Frobenius `Φ₀^m` of `X₀` (affine incarnation `a ⊗ b ↦ a ^ (q ^ m) ⊗ b`); it is a
`k̄`-morphism, the `m`-fold iterate of `Φ = Φ^1` (`schemeFrobenius_eq_pow`), finite for `X₀`
locally of finite type and radicial. The Galois automorphisms of the node are
`g_σ = arithmeticGaloisFrobenius` and `g_γ = geometricGaloisFrobenius`. -/
def schemeFrobenius (m : ℕ) : f.geometricFiber ⟶ f.geometricFiber :=
  geometricFiberMap (f.absoluteFrobenius m) (f.absoluteFrobenius_comp m)

/-- The scheme Frobenius lies over the Frobenius of the model: `Φ^m ≫ p_X = p_X ≫ Φ₀^m`. -/
@[reassoc (attr := simp)]
lemma schemeFrobenius_comp_geometricFiberProj (m : ℕ) :
    f.schemeFrobenius m ≫ f.geometricFiberProj = f.geometricFiberProj ≫ f.absoluteFrobenius m :=
  geometricFiberMap_comp_geometricFiberProj _ _

/-- The scheme Frobenius is a morphism over `k̄`: `Φ^m ≫ a_X = a_X`. -/
@[reassoc (attr := simp)]
lemma schemeFrobenius_comp_geometricFiberToAlgebraicClosure (m : ℕ) :
    f.schemeFrobenius m ≫ f.geometricFiberToAlgebraicClosure =
      f.geometricFiberToAlgebraicClosure :=
  geometricFiberMap_comp_geometricFiberToAlgebraicClosure _ _

@[simp]
lemma schemeFrobenius_zero : f.schemeFrobenius 0 = 𝟙 _ := by
  ext <;> simp

lemma schemeFrobenius_add (m n : ℕ) :
    f.schemeFrobenius (m + n) = f.schemeFrobenius m ≫ f.schemeFrobenius n := by
  ext <;> simp [absoluteFrobenius_add]

/-- `Φ^m` is the `m`-fold iterate of the scheme Frobenius `Φ = Φ^1`. -/
lemma schemeFrobenius_eq_pow (m : ℕ) :
    (f.schemeFrobenius m : End f.geometricFiber) = (f.schemeFrobenius 1 : End _) ^ m := by
  induction m with
  | zero => exact f.schemeFrobenius_zero
  | succ m ih => rw [pow_succ', End.mul_def, ← ih, ← schemeFrobenius_add]

/-- The scheme Frobenius is radicial, being a base change of the absolute Frobenius. -/
instance (m : ℕ) : UniversallyInjective (f.schemeFrobenius m) :=
  geometricFiberMap_of_isStableUnderBaseChange (P := @UniversallyInjective) _ _ inferInstance

/-- The scheme Frobenius of a scheme locally of finite type over `k` is finite, being a base
change of the absolute Frobenius. -/
instance [LocallyOfFiniteType f] (m : ℕ) : IsFinite (f.schemeFrobenius m) :=
  geometricFiberMap_of_isStableUnderBaseChange (P := @IsFinite) _ _ inferInstance

end Scheme.Hom

variable (k) in
/-- The automorphism `Spec σ` of `Spec k̄` induced by the arithmetic Frobenius `σ : z ↦ z ^ q` of
the algebraic closure of the finite field `k` with `q` elements. -/
def specArithmeticFrobenius : Aut (Spec (.of (AlgebraicClosure k))) :=
  letI := Fintype.ofFinite k
  Scheme.Spec.mapIso
    (FiniteField.frobeniusAlgEquivOfAlgebraic k
      (AlgebraicClosure k)).toRingEquiv.toCommRingCatIso.op

lemma specArithmeticFrobenius_pow_hom [Fintype k] (m : ℕ) :
    (specArithmeticFrobenius k ^ m).hom =
      Spec.map (CommRingCat.ofHom (FiniteField.frobeniusAlgEquivOfAlgebraic k
        (AlgebraicClosure k) ^ m).toRingEquiv.toRingHom) := by
  obtain rfl : ‹Fintype k› = Fintype.ofFinite k := Subsingleton.elim _ _
  induction m with
  | zero => exact (Spec.map_id _).symm
  | succ m ih =>
    rw [pow_succ, Aut.Aut_mul_def, Iso.trans_hom, ih, ← Spec.map_comp, pow_succ']
    rfl

/-- The arithmetic Frobenius of `Spec k̄` is the inverse of the geometric Frobenius. -/
lemma specArithmeticFrobenius_eq_inv :
    specArithmeticFrobenius k = (specGeometricFrobenius k)⁻¹ := by
  let := Fintype.ofFinite k
  rw [eq_inv_iff_mul_eq_one]
  ext1
  have h1 := specArithmeticFrobenius_pow_hom (k := k) 1
  have h2 := specGeometricFrobenius_pow_hom k 1
  rw [pow_one] at h1 h2
  rw [Aut.Aut_mul_def, Iso.trans_hom, h1, h2, ← Spec.map_comp, Aut.one_def, Iso.refl_hom,
    ← Spec.map_id]
  congr 1
  ext z
  simp

/-- The arithmetic Frobenius of `Spec k̄` lies over `Spec k`. -/
@[reassoc (attr := simp)]
lemma specArithmeticFrobenius_hom_comp_specAlgebraicClosure :
    (specArithmeticFrobenius k).hom ≫ (Scheme.specAlgebraicClosure k).hom =
      (Scheme.specAlgebraicClosure k).hom := by
  rw [specArithmeticFrobenius_eq_inv, Aut.inv_def, Iso.symm_hom, Iso.inv_comp_eq,
    specGeometricFrobenius_hom_comp_specAlgebraicClosure]

namespace Scheme.Hom

variable {X₀ : Scheme.{u}} (f : X₀ ⟶ Spec (.of k))

/-- The arithmetic Galois automorphism `g_σ = 𝟙 × Spec σ` of the geometric fiber
`X = X₀ ×_k k̄`, `σ : z ↦ z ^ q` the arithmetic Frobenius of `k̄` (blueprint
`def-trf-scheme-frobenius`). It is the inverse of the geometric Galois Frobenius
`g_γ = geometricGaloisFrobenius` (`arithmeticGaloisFrobenius_eq_inv`). -/
def arithmeticGaloisFrobenius : Aut f.geometricFiber :=
  asIso (pullback.map f (Scheme.specAlgebraicClosure k).hom f
    (Scheme.specAlgebraicClosure k).hom (𝟙 X₀) (specArithmeticFrobenius k).hom
    (𝟙 (Spec (.of k))) (by simp) (by simp))

@[reassoc (attr := simp)]
lemma arithmeticGaloisFrobenius_hom_comp_geometricFiberProj :
    f.arithmeticGaloisFrobenius.hom ≫ f.geometricFiberProj = f.geometricFiberProj := by
  simp [arithmeticGaloisFrobenius, geometricFiberProj]

@[reassoc (attr := simp)]
lemma arithmeticGaloisFrobenius_hom_comp_geometricFiberToAlgebraicClosure :
    f.arithmeticGaloisFrobenius.hom ≫ f.geometricFiberToAlgebraicClosure =
      f.geometricFiberToAlgebraicClosure ≫ (specArithmeticFrobenius k).hom := by
  simp [arithmeticGaloisFrobenius, geometricFiberToAlgebraicClosure]

/-- `g_σ = g_γ⁻¹`. -/
lemma arithmeticGaloisFrobenius_eq_inv :
    f.arithmeticGaloisFrobenius = f.geometricGaloisFrobenius⁻¹ := by
  rw [eq_inv_iff_mul_eq_one]
  ext1
  rw [Aut.Aut_mul_def, Iso.trans_hom, Aut.one_def, Iso.refl_hom]
  ext
  · simp
  · simp only [Category.assoc, geometricGaloisFrobenius_hom_comp_geometricFiberToAlgebraicClosure,
      arithmeticGaloisFrobenius_hom_comp_geometricFiberToAlgebraicClosure_assoc, Category.id_comp]
    rw [← Iso.trans_hom, ← Aut.Aut_mul_def, specArithmeticFrobenius_eq_inv, inv_mul_cancel,
      Aut.one_def, Iso.refl_hom, Category.comp_id]

@[reassoc (attr := simp)]
lemma arithmeticGaloisFrobenius_pow_hom_comp_geometricFiberProj (m : ℕ) :
    (f.arithmeticGaloisFrobenius ^ m).hom ≫ f.geometricFiberProj = f.geometricFiberProj := by
  induction m with
  | zero => exact Category.id_comp _
  | succ m ih =>
    rw [pow_succ', Aut.Aut_mul_def, Iso.trans_hom, Category.assoc,
      arithmeticGaloisFrobenius_hom_comp_geometricFiberProj, ih]

@[reassoc (attr := simp)]
lemma arithmeticGaloisFrobenius_pow_hom_comp_geometricFiberToAlgebraicClosure (m : ℕ) :
    (f.arithmeticGaloisFrobenius ^ m).hom ≫ f.geometricFiberToAlgebraicClosure =
      f.geometricFiberToAlgebraicClosure ≫ (specArithmeticFrobenius k ^ m).hom := by
  induction m with
  | zero => exact (Category.id_comp _).trans (Category.comp_id _).symm
  | succ m ih =>
    rw [pow_succ', Aut.Aut_mul_def, Iso.trans_hom, Category.assoc,
      arithmeticGaloisFrobenius_hom_comp_geometricFiberToAlgebraicClosure, reassoc_of% ih,
      pow_succ', Aut.Aut_mul_def, Iso.trans_hom]

/-- The scheme Frobenius commutes with the arithmetic Galois automorphism. -/
@[reassoc]
lemma schemeFrobenius_comp_arithmeticGaloisFrobenius_pow (m n : ℕ) :
    f.schemeFrobenius m ≫ (f.arithmeticGaloisFrobenius ^ n).hom =
      (f.arithmeticGaloisFrobenius ^ n).hom ≫ f.schemeFrobenius m := by
  ext <;> simp

/-- The scheme Frobenius commutes with the geometric Galois Frobenius. -/
@[reassoc]
lemma schemeFrobenius_comp_geometricGaloisFrobenius_pow (m n : ℕ) :
    f.schemeFrobenius m ≫ (f.geometricGaloisFrobenius ^ n).hom =
      (f.geometricGaloisFrobenius ^ n).hom ≫ f.schemeFrobenius m := by
  ext <;> simp

/-- The absolute `q ^ m`-power Frobenius of the geometric fiber `X = X₀ ×_k k̄` lies over
`Spec σ^m` on `Spec k̄`. -/
lemma absoluteFrobenius_geometricFiber_comp_geometricFiberToAlgebraicClosure (m : ℕ) :
    (f.geometricFiberProj ≫ f).absoluteFrobenius m ≫ f.geometricFiberToAlgebraicClosure =
      f.geometricFiberToAlgebraicClosure ≫ (specArithmeticFrobenius k ^ m).hom := by
  let := Fintype.ofFinite k
  rw [geometricFiber_condition, absoluteFrobenius_naturality, absoluteFrobenius,
    iterateFrobenius_Spec _ _ (by simp [ringChar.Nat.cast_ringChar]),
    specArithmeticFrobenius_pow_hom]
  congr 2
  ext z
  simp only [CommRingCat.hom_ofHom, iterateFrobeniusOfPrime_apply, pow_mul,
    FiniteField.ringChar_pow_log_card, RingEquiv.toRingHom_eq_coe, AlgEquiv.toRingEquiv_eq_coe,
    RingHom.coe_coe, AlgEquiv.coe_ringEquiv, AlgEquiv.coe_pow,
    FiniteField.coe_frobeniusAlgEquivOfAlgebraic_iterate, Nat.card_eq_fintype_card]

/-- Blueprint `prop-trf-frobenius-factorization`: Factorization of the absolute Frobenius.

For every `m`, the absolute `q ^ m`-power Frobenius of the geometric fiber `X = X₀ ×_k k̄`,
`a ⊗ b ↦ a ^ (q ^ m) ⊗ b ^ (q ^ m)`, factors as `Fr^{(q^m)}_X = g_σ^m ∘ Φ^m`. -/
theorem absoluteFrobenius_geometricFiber_eq_schemeFrobenius_comp (m : ℕ) :
    (f.geometricFiberProj ≫ f).absoluteFrobenius m =
      f.schemeFrobenius m ≫ (f.arithmeticGaloisFrobenius ^ m).hom := by
  ext
  · rw [absoluteFrobenius_naturality]
    simp
  · rw [absoluteFrobenius_geometricFiber_comp_geometricFiberToAlgebraicClosure]
    simp

/-- Blueprint `prop-trf-frobenius-factorization`, second factorization:
`Fr^{(q^m)}_X = Φ^m ∘ g_σ^m`. -/
theorem absoluteFrobenius_geometricFiber_eq_comp_schemeFrobenius (m : ℕ) :
    (f.geometricFiberProj ≫ f).absoluteFrobenius m =
      (f.arithmeticGaloisFrobenius ^ m).hom ≫ f.schemeFrobenius m := by
  rw [absoluteFrobenius_geometricFiber_eq_schemeFrobenius_comp,
    schemeFrobenius_comp_arithmeticGaloisFrobenius_pow]

/-- The scheme Frobenius is the absolute Frobenius followed by the geometric Galois Frobenius:
`Φ^m = g_γ^m ∘ Fr^{(q^m)}_X`. -/
theorem schemeFrobenius_eq_absoluteFrobenius_comp (m : ℕ) :
    f.schemeFrobenius m =
      (f.geometricFiberProj ≫ f).absoluteFrobenius m ≫ (f.geometricGaloisFrobenius ^ m).hom := by
  rw [absoluteFrobenius_geometricFiber_eq_schemeFrobenius_comp, Category.assoc, ← Iso.trans_hom,
    ← Aut.Aut_mul_def, arithmeticGaloisFrobenius_eq_inv, ← mul_pow, inv_mul_cancel, one_pow,
    Aut.one_def, Iso.refl_hom, Category.comp_id]

end Scheme.Hom

end FiniteField

end AlgebraicGeometry
