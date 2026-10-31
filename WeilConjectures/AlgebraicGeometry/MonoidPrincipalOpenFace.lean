/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.FineFanBlowup

/-!
# Principal faces and restrictions on monoid spectra

Source: Illusie--Laszlo--Orgogozo, Exposé VIII, 3.1.1--3.1.4, printed p. 98
(blueprint: lem-trf-monoid-principal-open-face).

We use the multiplicative notation of the recorded fine-fan interface. Thus `1`
is additive zero, `c * d = a ^ n` means `c + d = n a`, and fractions in
`Algebra.faceLocalization P (Submonoid.powers a)` are the elements `p - m a`.
-/

@[expose] public section

set_option autoImplicit false

universe u

open TopologicalSpace

namespace AlgebraicGeometry.FineFan

/-- The principal face consists of the divisors of powers, including the zeroth power.
This is the set `F_a` in additive notation, before its face properties are asserted.
Source: ILO VIII, 3.1.2--3.1.4, printed p. 98
(blueprint: lem-trf-monoid-principal-open-face). -/
def principalFace {P : Type u} [CommMonoid P] (a : P) : Set P :=
  {c | ∃ (d : P) (n : ℕ), c * d = a ^ n}

private theorem principalFace_one {P : Type u} [CommMonoid P] (a : P) :
    1 ∈ principalFace a := ⟨1, 0, by simp⟩

private theorem principalFace_self {P : Type u} [CommMonoid P] (a : P) :
    a ∈ principalFace a := ⟨1, 1, by simp⟩

private theorem principalFace_mul {P : Type u} [CommMonoid P] (a x y : P)
    (hx : x ∈ principalFace a) (hy : y ∈ principalFace a) :
    x * y ∈ principalFace a := by
  obtain ⟨d, n, hd⟩ := hx
  obtain ⟨e, m, he⟩ := hy
  refine ⟨d * e, n + m, ?_⟩
  rw [pow_add, ← hd, ← he]
  ac_rfl

private theorem principalFace_factors {P : Type u} [CommMonoid P] (a x y : P)
    (h : x * y ∈ principalFace a) : x ∈ principalFace a ∧ y ∈ principalFace a := by
  obtain ⟨d, n, hd⟩ := h
  exact ⟨⟨y * d, n, by simpa [mul_assoc] using hd⟩,
    ⟨x * d, n, by simpa [mul_assoc, mul_left_comm] using hd⟩⟩

private theorem prime_one_not_mem {P : Type u} [CommMonoid P] (q : MonoidPrime P) :
    1 ∉ q.carrier := by
  intro h
  apply q.proper
  apply Set.eq_univ_of_forall
  intro x
  simpa using q.smul_mem' x h

private theorem prime_pow_not_mem {P : Type u} [CommMonoid P] (q : MonoidPrime P)
    (a : P) (ha : a ∉ q.carrier) (n : ℕ) : a ^ n ∉ q.carrier := by
  induction n with
  | zero => simpa using prime_one_not_mem q
  | succ n ih => simpa [pow_succ] using q.complement_mul _ _ ih ha

private theorem prime_avoids_face {P : Type u} [CommMonoid P] (q : MonoidPrime P)
    (a : P) (ha : a ∉ q.carrier) (x : P) (hx : x ∈ principalFace a) :
    x ∉ q.carrier := by
  obtain ⟨d, n, hd⟩ := hx
  intro h
  apply prime_pow_not_mem q a ha n
  rw [← hd, mul_comm]
  exact q.smul_mem' d h

private theorem open_downward {P : Type u} [CommMonoid P]
    (q m : MonoidPrime P) (hqm : q.carrier ⊆ m.carrier)
    (U : Opens (MonoidPrime P)) (hm : m ∈ U) : q ∈ U := by
  have h : ∀ V : Set (MonoidPrime P), TopologicalSpace.GenerateOpen
      (Set.range (fun a : P ↦ {p : MonoidPrime P | a ∉ p.carrier})) V →
      m ∈ V → q ∈ V := by
    intro V hV
    induction hV with
    | basic V hV =>
        obtain ⟨b, rfl⟩ := hV
        exact fun hm h ↦ hm (hqm h)
    | univ => exact fun _ ↦ trivial
    | inter V W hV hW ihV ihW => exact fun hm ↦ ⟨ihV hm.1, ihW hm.2⟩
    | sUnion S hS ih =>
        rintro ⟨V, hV, hmV⟩
        exact ⟨V, hV, ih V hV hmV⟩
  exact h U U.isOpen hm

private theorem principalFace_prime {P : Type u} [CommMonoid P] (a : P) :
    ∃ m : MonoidPrime P, m.carrier = (principalFace a)ᶜ ∧ m ∈ basicOpen a ∧
      (∀ q : MonoidPrime P, q ∈ basicOpen a → q.carrier ⊆ m.carrier) ∧
      (∀ U : Opens (MonoidPrime P), m ∈ U → basicOpen a ≤ U) := by
  classical
  let m : MonoidPrime P :=
    { carrier := (principalFace a)ᶜ
      smul_mem' := fun x y hy hxy ↦ hy (principalFace_factors a x y hxy).2
      proper := fun h ↦ by
        have : (1 : P) ∈ (principalFace a)ᶜ := h.symm ▸ Set.mem_univ 1
        exact this (principalFace_one a)
      complement_mul := fun x y hx hy ↦ by
        simp only [Set.mem_compl_iff, not_not] at hx hy ⊢
        exact principalFace_mul a x y hx hy }
  have hgreat : ∀ q : MonoidPrime P, q ∈ basicOpen a → q.carrier ⊆ m.carrier := by
    intro q hq x hx hface
    exact prime_avoids_face q a hq x hface hx
  refine ⟨m, rfl, ?_, hgreat, ?_⟩
  · exact not_not.mpr (principalFace_self a)
  · intro U hm q hq
    exact open_downward q m (hgreat q hq) U hm

private theorem basicOpen_le_iff_face {P : Type u} [CommMonoid P] (a c : P) :
    basicOpen c ≤ basicOpen a ↔ a ∈ principalFace c := by
  classical
  constructor
  · intro h
    obtain ⟨m, hm, hmc, _⟩ := principalFace_prime c
    have ha : a ∉ m.carrier := h hmc
    rw [hm] at ha
    exact not_not.mp ha
  · intro h q hq
    exact prime_avoids_face q c hq a h

private theorem localization_le_of_face {P : Type u} [CommMonoid P] (a c : P)
    (h : a ∈ principalFace c) :
    Algebra.faceLocalization P (Submonoid.powers a) ≤
      Algebra.faceLocalization P (Submonoid.powers c) := by
  obtain ⟨d, n, hd⟩ := h
  rintro x ⟨p, s, rfl⟩
  obtain ⟨m, hm⟩ := (Submonoid.mem_powers_iff s.val a).mp s.property
  refine ⟨p * d ^ m, ⟨c ^ (n * m), Submonoid.pow_mem _ (Submonoid.mem_powers c) _⟩, ?_⟩
  have he : Algebra.GrothendieckGroup.of a * Algebra.GrothendieckGroup.of d =
      Algebra.GrothendieckGroup.of c ^ n := by
    rw [← map_mul, hd, map_pow]
  rw [← hm]
  simp only [map_mul, map_pow]
  rw [pow_mul, ← he, mul_pow]
  simp [mul_assoc, mul_comm]

/-- Principal faces give greatest primes and minimal neighborhoods in basic opens;
every cover of such an open has the whole open as a member. Basic-open containment
is equivalent to membership in the principal face. Under this condition the
localization submonoids are nested, so `Submonoid.inclusion` is precisely the
restriction of the identity of the group completion. The last two clauses give
preservation of units and the representative formula on sharpening.
Source: ILO VIII, 3.1.1--3.1.4(i),(iii), printed p. 98
(blueprint: lem-trf-monoid-principal-open-face).

Proof (using the definitions in `def-trf-fine-fan-blowup`):
1. The witnesses `(1,0)` and `(1,1)` put `1,a` in the face. Multiplying two
   witness equations proves closure. From `(x*y)*d = a^n`, the witnesses `y*d`
   and `x*d` put both factors in the face.
2. Its complement is an ideal by this face condition, proper since it avoids `1`,
   and prime since the face is multiplicatively closed. It avoids `a`. If a prime
   avoiding `a` contained a divisor of a power of `a`, ideal absorption would put
   that power in the prime, a contradiction. Hence this is the greatest prime in `D(a)`.
3. A basic neighborhood `D(b)` of that prime contains every prime in `D(a)` by
   ideal containment. Every open neighborhood therefore contains `D(a)`. A cover
   has a member containing the greatest prime, and that member must be `D(a)`.
4. Divisors of `1` are exactly units; no proper ideal contains `1`, so `D(1)` is all
   of the spectrum.
5. Apply `D(c) ≤ D(a)` to the greatest prime of `D(c)` to get `a ∈ F_c`.
   Conversely `a*d = c^n` prevents a prime avoiding `c` from containing `a`.
   The second equivalence is the defining witness formula for the face.
6. If `a*d = c^n`, then `p*a^(-m) = (p*d^m)*c^(-(m*n))` in the group completion.
   Thus the localizations are nested; subtype inclusion is the identity on the
   ambient group and is independent of fraction representatives.
7. Applying this homomorphism to a unit and its inverse preserves their product `1`.
   Thus it descends to `Associates` via the recorded `sharpenMap`; a representative
   has the same ambient value on either side, giving the asserted class formula.
-/
theorem monoid_principalOpen_face (P : Type u) [CommMonoid P] (hP : IsFine P) :
    (∀ a : P,
      1 ∈ principalFace a ∧ a ∈ principalFace a ∧
      (∀ x y : P, x ∈ principalFace a → y ∈ principalFace a →
        x * y ∈ principalFace a) ∧
      (∀ x y : P, x * y ∈ principalFace a →
        x ∈ principalFace a ∧ y ∈ principalFace a) ∧
      (∃ m : MonoidPrime P,
        m.carrier = (principalFace a)ᶜ ∧ m ∈ basicOpen a ∧
        (∀ q : MonoidPrime P, q ∈ basicOpen a → q.carrier ⊆ m.carrier) ∧
        (∀ U : Opens (MonoidPrime P), m ∈ U → basicOpen a ≤ U)) ∧
      (∀ S : Set (Opens (MonoidPrime P)),
        (∀ U ∈ S, U ≤ basicOpen a) → sSup S = basicOpen a → basicOpen a ∈ S)) ∧
    principalFace (1 : P) = {p : P | IsUnit p} ∧
    basicOpen (1 : P) = ⊤ ∧
    (∀ a c : P,
      ((basicOpen c ≤ basicOpen a) ↔ a ∈ principalFace c) ∧
      ((a ∈ principalFace c) ↔ ∃ (d : P) (n : ℕ), a * d = c ^ n) ∧
      (basicOpen c ≤ basicOpen a →
        ∃ h : Algebra.faceLocalization P (Submonoid.powers a) ≤
            Algebra.faceLocalization P (Submonoid.powers c),
          (∀ q : Algebra.faceLocalization P (Submonoid.powers a),
            IsUnit q → IsUnit (Submonoid.inclusion h q)) ∧
          (∀ (q : Algebra.faceLocalization P (Submonoid.powers a))
              (r : Algebra.faceLocalization P (Submonoid.powers c)),
            r.val = q.val →
            sharpenMap (Submonoid.inclusion h) (Associates.mk q) = Associates.mk r))) := by
  classical
  rcases hP with ⟨_, _⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro a
    obtain ⟨m, hm, hma, hgreat, hnhds⟩ := principalFace_prime a
    refine ⟨principalFace_one a, principalFace_self a, principalFace_mul a,
      principalFace_factors a, ⟨m, hm, hma, hgreat, hnhds⟩, ?_⟩
    intro S hS hsup
    have hmS : m ∈ sSup S := hsup.symm ▸ hma
    obtain ⟨U, hUS, hmU⟩ := Opens.mem_sSup.mp hmS
    have hU : U = basicOpen a := le_antisymm (hS U hUS) (hnhds U hmU)
    exact hU ▸ hUS
  · ext p
    change (∃ d : P, ∃ n : ℕ, p * d = 1 ^ n) ↔ IsUnit p
    simp only [one_pow]
    constructor
    · rintro ⟨d, _, hd⟩
      exact isUnit_iff_exists_inv.mpr ⟨d, hd⟩
    · intro hp
      obtain ⟨d, hd⟩ := isUnit_iff_exists_inv.mp hp
      exact ⟨d, 0, hd⟩
  · apply top_unique
    intro q _
    exact prime_one_not_mem q
  · intro a c
    refine ⟨basicOpen_le_iff_face a c, Iff.rfl, ?_⟩
    intro hac
    let h := localization_le_of_face a c ((basicOpen_le_iff_face a c).mp hac)
    refine ⟨h, fun q hq ↦ hq.map (Submonoid.inclusion h), ?_⟩
    intro q r hr
    change Associates.mk (Submonoid.inclusion h q) = Associates.mk r
    exact congrArg Associates.mk (Subtype.ext hr.symm)

end AlgebraicGeometry.FineFan
