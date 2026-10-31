/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.Dynamics.Newton
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.KrullDimension.Zero
public import Mathlib.RingTheory.Nilpotent.Lemmas
public import Mathlib.FieldTheory.IsSepClosed
public import WeilConjectures.Mathlib.RingTheory.Etale.StandardEtale
public import Mathlib.RingTheory.SimpleRing.Principal
public import WeilConjectures.Mathlib.FieldTheory.IsSepClosed
public import WeilConjectures.Mathlib.Algebra.Polynomial.Inductions
public import Mathlib.Algebra.Polynomial.Reverse

/-!
# Henselian rings and strictly henselian local rings via sections of étale algebras

The zero ideal of any commutative ring is henselian (`HenselianRing.bot`).

A local ring `R` such that every étale `R`-algebra `B` has, through every prime of `B` over the
closed point, an `R`-algebra section `B →ₐ[R] R`, is henselian with separably closed residue
field. Both statements are tested on standard étale algebras `R[X][1/f']/(f)` for a monic `f`:
a section sends `X` to a root of `f`.

## Main results

- `HenselianRing.bot`: the zero ideal of any ring is henselian.
- `HenselianLocalRing.of_exists_algHom_comap_maximalIdeal_eq`: such a local ring is henselian.
- `IsLocalRing.isSepClosed_residueField_of_exists_algHom_comap_maximalIdeal_eq`: such a local
  ring has separably closed residue field.
- `HenselianRing.exists_isRoot_sub_mem`: Hensel's lemma over a henselian pair, without
  monicity.
- `HenselianRing.exists_isRoot_of_eval_eq_sq_mul`: Newton's lemma over a henselian pair.

The henselian pairs `(A, I)` of the blueprint (`def-weil-pbc-henselian-terminology`) are
Mathlib's `HenselianRing A I`; a henselian local ring is `HenselianLocalRing`, and it is
strictly henselian when moreover `IsSepClosed (IsLocalRing.ResidueField A)`.
-/

@[expose] public section

/-- The zero ideal of any ring is henselian. -/
instance HenselianRing.bot (R : Type*) [CommRing R] : HenselianRing R ⊥ where
  jac := bot_le
  is_henselian f _ a₀ h _ := ⟨a₀, by simpa using h, by simp⟩

universe u

open Polynomial IsLocalRing

variable {R : Type u} [CommRing R] [IsLocalRing R]

/-- Let `R` be a local ring such that every prime of an étale `R`-algebra lying over the maximal
ideal is the preimage of the maximal ideal under an `R`-algebra map to `R`. If `K` is a field
over `R` whose structure map has kernel the maximal ideal, then every simple root `x : K` of a
monic `f : R[X]` is the image of a root of `f` in `R`. -/
theorem IsLocalRing.exists_isRoot_algebraMap_eq_of_exists_algHom_comap_maximalIdeal_eq
    (H : ∀ (B : Type u) [CommRing B] [Algebra R B] [Algebra.Etale R B] (q : Ideal B) [q.IsPrime],
      q.comap (algebraMap R B) = maximalIdeal R →
        ∃ ψ : B →ₐ[R] R, (maximalIdeal R).comap ψ = q)
    {K : Type*} [Field K] [Algebra R K] (hK : RingHom.ker (algebraMap R K) = maximalIdeal R)
    {f : R[X]} (hf : f.Monic) {x : K} (hx : aeval x f = 0) (hx' : aeval x (derivative f) ≠ 0) :
    ∃ a : R, f.IsRoot a ∧ algebraMap R K a = x := by
  let P := StandardEtalePair.ofMonic hf 1
  have hP : P.HasMap x := ⟨hx, by simpa [P, StandardEtalePair.ofMonic] using hx'⟩
  let χ := P.lift x hP
  have hq : (RingHom.ker χ).comap (algebraMap R P.Ring) = maximalIdeal R := by
    ext r
    rw [← hK, Ideal.mem_comap, RingHom.mem_ker, RingHom.mem_ker, AlgHom.commutes]
  have := RingHom.ker_isPrime χ
  obtain ⟨ψ, hψ⟩ := H P.Ring (RingHom.ker χ) hq
  refine ⟨ψ P.X, ?_, ?_⟩
  · have h := congr_arg ψ (StandardEtalePair.hasMap_X (P := P)).1
    rwa [← aeval_algHom_apply, map_zero, aeval_def, Algebra.algebraMap_self, eval₂_id] at h
  · have hmem : P.X - algebraMap R P.Ring (ψ P.X) ∈ (maximalIdeal R).comap ψ := by
      simp [Ideal.mem_comap]
    rw [hψ, RingHom.mem_ker, map_sub, AlgHom.commutes, sub_eq_zero] at hmem
    rw [← hmem]
    exact P.lift_X x hP

/-- A local ring `R` is henselian if every prime `q` lying over the maximal ideal of an étale
`R`-algebra `B` is the preimage of the maximal ideal under an `R`-algebra map `B →ₐ[R] R`. -/
theorem HenselianLocalRing.of_exists_algHom_comap_maximalIdeal_eq
    (H : ∀ (B : Type u) [CommRing B] [Algebra R B] [Algebra.Etale R B] (q : Ideal B) [q.IsPrime],
      q.comap (algebraMap R B) = maximalIdeal R →
        ∃ ψ : B →ₐ[R] R, (maximalIdeal R).comap ψ = q) :
    HenselianLocalRing R := by
  refine ((HenselianLocalRing.TFAE R).out 1 0).mp fun f hf a₀ h₁ h₂ ↦ ?_
  have hK : RingHom.ker (algebraMap R (ResidueField R)) = maximalIdeal R := by
    rw [ResidueField.algebraMap_eq, ker_residue]
  simpa [ResidueField.algebraMap_eq] using
    exists_isRoot_algebraMap_eq_of_exists_algHom_comap_maximalIdeal_eq H hK hf h₁ h₂

/-- A local ring `R` has separably closed residue field if every prime `q` lying over the
maximal ideal of an étale `R`-algebra `B` is the preimage of the maximal ideal under an
`R`-algebra map `B →ₐ[R] R`. -/
theorem IsLocalRing.isSepClosed_residueField_of_exists_algHom_comap_maximalIdeal_eq
    (H : ∀ (B : Type u) [CommRing B] [Algebra R B] [Algebra.Etale R B] (q : Ideal B) [q.IsPrime],
      q.comap (algebraMap R B) = maximalIdeal R →
        ∃ ψ : B →ₐ[R] R, (maximalIdeal R).comap ψ = q) :
    IsSepClosed (ResidueField R) := by
  refine IsSepClosed.of_exists_root _ fun h hm hirr hsep ↦ ?_
  obtain ⟨f, rfl, -, hf⟩ := lifts_and_natDegree_eq_and_monic
    (map_surjective _ residue_surjective h) hm
  have := Fact.mk hirr
  have hK : RingHom.ker (algebraMap R (AdjoinRoot (f.map (residue R)))) = maximalIdeal R := by
    ext r
    rw [← ker_residue, RingHom.mem_ker, RingHom.mem_ker,
      IsScalarTower.algebraMap_apply R (ResidueField R),
      map_eq_zero, ResidueField.algebraMap_eq]
  have hroot₀ : aeval (AdjoinRoot.root (f.map (residue R))) (f.map (residue R)) = 0 :=
    AdjoinRoot.aeval_eq _ |>.trans AdjoinRoot.mk_self
  have hroot : aeval (AdjoinRoot.root (f.map (residue R))) f = 0 := by
    rw [← aeval_map_algebraMap (ResidueField R), ResidueField.algebraMap_eq]
    exact hroot₀
  have hroot' : aeval (AdjoinRoot.root (f.map (residue R))) (derivative f) ≠ 0 := by
    rw [← aeval_map_algebraMap (ResidueField R), ResidueField.algebraMap_eq, ← derivative_map]
    exact hsep.aeval_derivative_ne_zero hroot₀
  obtain ⟨a, ha, -⟩ := exists_isRoot_algebraMap_eq_of_exists_algHom_comap_maximalIdeal_eq H hK hf
    hroot hroot'
  exact ⟨residue R a, by simpa using congr(residue R $ha)⟩

/-! ### Ported from the `proetale` package (`Proetale.Mathlib.RingTheory.Henselian`) -/

/-- A local ring is strictly henselian if it is henselian with separably closed residue field. -/
class IsStrictlyHenselianLocalRing (R : Type*) [CommRing R] : Prop
    extends HenselianLocalRing R where
  isSepClosed_residueField : IsSepClosed (IsLocalRing.ResidueField R)

instance (R : Type*) [CommRing R] [IsStrictlyHenselianLocalRing R] :
    IsSepClosed (IsLocalRing.ResidueField R) :=
  IsStrictlyHenselianLocalRing.isSepClosed_residueField

/-- A local ring is strictly Henselian if and only if it is Henselian and its residue
field is separably closed. -/
theorem isStrictlyHenselianLocalRing_iff_henselianLocalRing_and_isSepClosed
    (R : Type*) [CommRing R] [IsLocalRing R] :
    IsStrictlyHenselianLocalRing R ↔
      HenselianLocalRing R ∧ IsSepClosed (IsLocalRing.ResidueField R) :=
  ⟨fun _ ↦ ⟨inferInstance, inferInstance⟩,
    fun h ↦ have := h.1; ⟨h.2⟩⟩

/-- `HenselianLocalRing` transfers along a ring isomorphism. -/
theorem HenselianLocalRing.of_ringEquiv {R S : Type*} [CommRing R] [CommRing S]
    [HenselianLocalRing R] (e : R ≃+* S) : HenselianLocalRing S := by
  have : IsLocalRing S := e.isLocalRing
  refine HenselianLocalRing.mk fun f hf a₀ hmem hunit => ?_
  let f' : Polynomial R := f.map e.symm.toRingHom
  have heval : f'.eval (e.symm a₀) = e.symm (f.eval a₀) :=
    Polynomial.eval_map_apply (p := f) e.symm.toRingHom a₀
  have hderiv : f'.derivative.eval (e.symm a₀) = e.symm (f.derivative.eval a₀) := by
    rw [Polynomial.derivative_map (f := e.symm.toRingHom)]
    exact Polynomial.eval_map_apply (p := f.derivative) e.symm.toRingHom a₀
  have hmem' : f'.eval (e.symm a₀) ∈ IsLocalRing.maximalIdeal R := by
    rw [IsLocalRing.mem_maximalIdeal] at hmem
    rw [heval, IsLocalRing.mem_maximalIdeal]
    intro hu
    exact hmem (by simpa using hu.map e)
  have hunit' : IsUnit (f'.derivative.eval (e.symm a₀)) :=
    hderiv ▸ hunit.map e.symm.toRingHom
  obtain ⟨a, ha_root, ha_diff⟩ :=
    HenselianLocalRing.is_henselian f' (hf.map _) (e.symm a₀) hmem' hunit'
  refine ⟨e a, ?_, ?_⟩
  · have hf_eq : f'.map e.toRingHom = f := by
      simp [f', Polynomial.map_map]
    have key : f.eval (e a) = e (f'.eval a) := by
      rw [← hf_eq]; exact Polynomial.eval_map_apply (p := f') e.toRingHom a
    rw [Polynomial.IsRoot.def, key, Polynomial.IsRoot.def.mp ha_root, map_zero]
  · rw [IsLocalRing.mem_maximalIdeal] at ha_diff ⊢
    intro hu
    apply ha_diff
    have : a - e.symm a₀ = e.symm (e a - a₀) := by simp
    rw [this]
    exact hu.map e.symm.toRingHom

/-- `IsStrictlyHenselianLocalRing` transfers along a ring isomorphism. -/
theorem IsStrictlyHenselianLocalRing.of_ringEquiv {R S : Type*} [CommRing R] [CommRing S]
    [IsStrictlyHenselianLocalRing R] (e : R ≃+* S) : IsStrictlyHenselianLocalRing S :=
  have : HenselianLocalRing S := .of_ringEquiv e
  ⟨IsSepClosed.of_ringEquiv (IsLocalRing.ResidueField.mapEquiv e)⟩

/-- A local ring with nil maximal ideal satisfies simple-root lifting.
Source: Mathlib.Dynamics.Newton, `Polynomial.existsUnique_nilpotent_sub_and_aeval_eq_zero`;
Stacks Project, Algebra, Tag 06RS
(blueprint: lem-weil-pbc-henselian-of-nil-maximal-ideal).

Proof: For a polynomial f and an approximate root x, f(x) lies in the maximal ideal,
hence is nilpotent. Since f'(x) is a unit, finite Newton iteration gives a root a with
x - a nilpotent: each iteration squares the error, so a sufficiently high iteration
has zero error. The derivative remains a unit since the correction is nilpotent.
The nilpotent difference a - x belongs to every prime ideal, in particular the maximal
ideal. This gives the defining simple-root lifting condition for a henselian local ring.
No uniform nilpotence exponent for the maximal ideal is required. -/
theorem henselianLocalRing_of_maximalIdeal_le_nilradical
    (R : Type*) [CommRing R] [IsLocalRing R]
    (hnil : IsLocalRing.maximalIdeal R ≤ nilradical R) : HenselianLocalRing R := by
  constructor
  intro f _ x hx hderiv
  obtain ⟨a, ha, _⟩ := Polynomial.existsUnique_nilpotent_sub_and_aeval_eq_zero
    (show IsNilpotent (Polynomial.aeval x f) by simpa using mem_nilradical.mp (hnil hx))
    (show IsUnit (Polynomial.aeval x f.derivative) by simpa using hderiv)
  refine ⟨a, ?_, ?_⟩
  · simpa [Polynomial.IsRoot] using ha.2
  · exact nilradical_le_prime (IsLocalRing.maximalIdeal R)
      (by simpa only [mem_nilradical, neg_sub] using ha.1.neg)

/-- A local ring of Krull dimension zero (e.g. an artinian local ring) is henselian: its maximal
ideal is its nilradical. (blueprint: `lem-weil-pbc-local-dimension-zero-henselian`) -/
theorem HenselianLocalRing.of_krullDimLE_zero {R : Type*} [CommRing R]
    [IsLocalRing R] [Ring.KrullDimLE 0 R] : HenselianLocalRing R :=
  henselianLocalRing_of_maximalIdeal_le_nilradical R
    (Ring.KrullDimLE.nilradical_eq_maximalIdeal (R := R)).ge

/-- **Uniqueness of simple roots in a residue class.** Let `R` be a local ring with maximal ideal
`𝔪`, `f : R[X]` and `a b : R` roots of `f` with `a - b ∈ 𝔪` and `f'(a) ∉ 𝔪`. Then `a = b`.
This is mathlib's `IsLocalRing.eq_of_eval_eq_zero_of_not_isUnit_sub`, phrased with `𝔪`.
(blueprint: `lem-weil-pbc-simple-root-uniqueness`) -/
@[stacks 06RR]
theorem IsLocalRing.eq_of_eval_eq_zero_of_sub_mem_maximalIdeal {R : Type*} [CommRing R]
    [IsLocalRing R] {f : R[X]} {a b : R} (ha : f.eval a = 0) (hb : f.eval b = 0)
    (hab : a - b ∈ maximalIdeal R) (h' : f.derivative.eval a ∉ maximalIdeal R) : a = b :=
  eq_of_eval_eq_zero_of_not_isUnit_sub ha hb ((mem_maximalIdeal _).1 hab)
    (notMem_maximalIdeal.1 h')

/-! ### Hensel's and Newton's lemmas without monicity

Mathlib's `HenselianRing R I` asks for roots of monic polynomials only. Over a henselian pair
`(R, I)` we prove:

* **Hensel's lemma** (`HenselianRing.exists_isRoot_sub_mem`): a polynomial `f`, monic or not, with
  `f(a₀) ∈ I` and `f'(a₀)` a unit has a root `a ≡ a₀ (mod I)`. After a translation and the
  rescaling `X ↦ f(a₀) X`, the polynomial is `1 + c₁ X + (terms in I)`, whose reflection is monic
  with the simple root `-c₁` modulo `I`.
* **Newton's lemma** (`HenselianRing.exists_isRoot_of_eval_eq_sq_mul`): if `f(a) = f'(a)² c` with
  `c ∈ I`, then `f` has a root `b` with `b - a ∈ f'(a) I`. This is the form of Hensel's lemma for
  roots that are not simple modulo `I`, used to compare separable extensions of a henselian
  discretely valued field with those of its completion (SGA 4½, [Th. finitude], Lemme 3.3).

For a henselian local ring, take `I = maximalIdeal R`.
-/

namespace HenselianRing

variable {R : Type*} [CommRing R] {I : Ideal R} [HenselianRing R I]

/-- A polynomial `1 + c₁ X + (terms of degree ≥ 2 in I)` with `c₁` a unit over a henselian pair
`(R, I)` has a root which is a unit. -/
theorem exists_isUnit_isRoot_of_coeff_zero_eq_one (k : R[X]) (h₀ : k.coeff 0 = 1)
    (h₁ : IsUnit (k.coeff 1)) (h₂ : ∀ i, 2 ≤ i → k.coeff i ∈ I) :
    ∃ w, IsUnit w ∧ k.IsRoot w := by
  rcases subsingleton_or_nontrivial R with hR | hR
  · exact ⟨1, isUnit_one, IsRoot.def.2 (Subsingleton.elim _ _)⟩
  set c := k.coeff 1
  have hdeg : 1 ≤ k.natDegree := le_natDegree_of_ne_zero h₁.ne_zero
  set n := k.natDegree
  let M := reflect (n + 1) k
  have hM : M.Monic := by
    refine monic_of_natDegree_le_of_coeff_eq_one (n + 1) ?_ ?_
    · exact natDegree_reflect_le.trans (by omega)
    · rw [coeff_reflect, revAt_le le_rfl, Nat.sub_self, h₀]
  have hk : k.map (Ideal.Quotient.mk I) = C 1 + C (Ideal.Quotient.mk I c) * X := by
    ext i
    rw [coeff_map]
    rcases i with _ | _ | i
    · simp [h₀]
    · simp [c, coeff_one]
    · rw [Ideal.Quotient.eq_zero_iff_mem.2 (h₂ _ (by omega))]
      simp [coeff_one]
  have hMmap : M.map (Ideal.Quotient.mk I) = X ^ n * (X + C (Ideal.Quotient.mk I c)) := by
    rw [← reflect_map, hk, reflect_add, reflect_C, ← pow_one (X : (R ⧸ I)[X]),
      reflect_C_mul_X_pow, revAt_le (by omega)]
    obtain ⟨m, hm⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    rw [hm, show m + 1 + 1 - 1 = m + 1 by omega]
    simp only [map_one, one_mul]
    ring
  have hc : IsUnit (Ideal.Quotient.mk I c) := h₁.map _
  obtain ⟨v, hv, hvc⟩ := HenselianRing.is_henselian M hM (-c)
    ((Ideal.Quotient.eq_zero_iff_mem (I := I)).1 (by simp [← eval_map_apply, hMmap]))
    (by
      rw [← eval_map_apply, ← derivative_map, hMmap, derivative_mul]
      simp only [map_neg, eval_add, eval_mul, eval_X, eval_C, eval_pow, neg_add_cancel, mul_zero,
        zero_add, derivative_add, derivative_X, derivative_C, add_zero, mul_one]
      exact hc.neg.pow n)
  have hvu : IsUnit v := by
    have hj : v + c ∈ Ideal.jacobson ⊥ := HenselianRing.jac (I := I) (sub_neg_eq_add v c ▸ hvc)
    have h₃ : -((v + c) * -↑h₁.unit⁻¹ + 1) = v * ↑h₁.unit⁻¹ := by
      linear_combination h₁.mul_val_inv
    exact isUnit_of_mul_isUnit_left (h₃ ▸ (Ideal.mem_jacobson_bot.1 hj _).neg)
  let w := hvu.unit⁻¹
  have : Invertible (w : R) := w.invertible
  have h := (eval₂_reflect_eq_zero_iff (RingHom.id R) (w : R) (n + 1) k (by omega)).1
  have hw : ⅟(w : R) = v := by simp [w]
  exact ⟨w, w.isUnit, h (hw ▸ hv)⟩

/-- **Hensel's lemma without monicity**: over a henselian pair `(R, I)`, a polynomial `f` with
`f(a₀) ∈ I` and `f'(a₀)` a unit has a root `a ≡ a₀ (mod I)`. -/
theorem exists_isRoot_sub_mem (f : R[X]) (a₀ : R) (h₁ : f.eval a₀ ∈ I)
    (h₂ : IsUnit (f.derivative.eval a₀)) : ∃ a, f.IsRoot a ∧ a - a₀ ∈ I := by
  set g := taylor a₀ f
  set c₀ := g.coeff 0
  set c₁ := g.coeff 1
  have hc₀ : c₀ = f.eval a₀ := taylor_coeff_zero a₀ f
  have hc₁ : c₁ = f.derivative.eval a₀ := taylor_coeff_one a₀ f
  set G := g.divX.divX
  let k : R[X] := 1 + C c₁ * X + C c₀ * (X ^ 2 * G.comp (C c₀ * X))
  have hgk : g.comp (C c₀ * X) = C c₀ * k := by
    conv_lhs => rw [g.eq_C_add_X_mul_C_add_X_mul]
    simp only [add_comp, mul_comp, C_comp, X_comp, k]
    ring
  have hk₀ : k.coeff 0 = 1 := by simp [k, coeff_one]
  have hk₁ : k.coeff 1 = c₁ := by simp [k, coeff_one, coeff_C_mul, coeff_X_pow_mul']
  have hk₂ : ∀ i, 2 ≤ i → k.coeff i ∈ I := by
    intro i hi
    have : k.coeff i = c₀ * (X ^ 2 * G.comp (C c₀ * X)).coeff i := by
      simp [k, coeff_one, coeff_C_mul, coeff_X, show i ≠ 0 by omega, show 1 ≠ i by omega]
    rw [this]
    exact Ideal.mul_mem_right _ _ (hc₀ ▸ h₁)
  obtain ⟨w, -, hw⟩ := exists_isUnit_isRoot_of_coeff_zero_eq_one k hk₀ (hk₁ ▸ hc₁ ▸ h₂) hk₂
  refine ⟨c₀ * w + a₀, ?_, by simpa using Ideal.mul_mem_right w _ (hc₀ ▸ h₁)⟩
  have := congrArg (eval w) hgk
  rwa [eval_comp, eval_mul, eval_C, eval_X, eval_mul, eval_C, hw.eq_zero, mul_zero,
    taylor_eval] at this

/-- **Newton's lemma over a henselian pair** `(R, I)`: if `f(a) = f'(a)² c` with `c ∈ I`, then `f`
has a root `b` with `b - a = f'(a) y` for some `y ∈ I`. -/
theorem exists_isRoot_of_eval_eq_sq_mul (f : R[X]) (a c : R) (hc : c ∈ I)
    (h : f.eval a = f.derivative.eval a ^ 2 * c) :
    ∃ b, f.IsRoot b ∧ ∃ y ∈ I, b - a = f.derivative.eval a * y := by
  set d := f.derivative.eval a
  set g := taylor a f
  have hg₀ : g.coeff 0 = d ^ 2 * c := by rw [taylor_coeff_zero, h]
  have hg₁ : g.coeff 1 = d := taylor_coeff_one a f
  set G := g.divX.divX
  let k : R[X] := C c + X + X ^ 2 * G.comp (C d * X)
  have hgk : g.comp (C d * X) = C (d ^ 2) * k := by
    conv_lhs => rw [g.eq_C_add_X_mul_C_add_X_mul, hg₀, hg₁]
    simp only [add_comp, mul_comp, C_comp, X_comp, k, C_mul, C_pow, pow_comp]
    ring
  obtain ⟨y, hy, hy₀⟩ := exists_isRoot_sub_mem (I := I) k 0 (by simpa [k] using hc)
    (by simp [k])
  rw [sub_zero] at hy₀
  refine ⟨d * y + a, ?_, y, hy₀, by rw [add_sub_cancel_right]⟩
  have := congrArg (eval y) hgk
  rwa [eval_comp, eval_mul, eval_C, eval_X, eval_mul, eval_C, hy.eq_zero, mul_zero,
    taylor_eval] at this

end HenselianRing
