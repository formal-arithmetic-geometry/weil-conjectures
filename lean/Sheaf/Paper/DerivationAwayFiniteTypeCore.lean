module

public import Mathlib.RingTheory.Derivation.Basic
public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.RingTheory.FiniteType

@[expose] public section

universe u v
namespace RingTheory

/-- Restrict a localized derivation to a finite type algebra after multiplying by a power
of the localizing element. Source: Stacks Project, More on Algebra, Tag 07PE, final
statement; the agent proof clears denominators of derivative values directly.
(blueprint: lem-weil-pbc-derivation-away-finite-type-core)

Proof: write `ι : R' → R'_g` for the localization map, which is injective because `g`
is a nonzerodivisor. Choose finite algebra generators `s` using finite type. For each
`x`, localization surjectivity gives `n(x)` and `a(x)` with
`δ(ι(x)) * ι(g)^n(x) = ι(a(x))`. Let `N` be the maximum of `n(x)` over `s` (zero when
`s` is empty), and put `Δ = ι(g)^N • δ`. For each generator its value under `Δ` is the
image of `a(x) * g^(N-n(x))`. On a coefficient from `R`, the extension hypothesis
identifies its value with the image of `g^N * D(r)`. Additivity and Leibniz show by
algebra-adjoin induction that `Δ(ι(x))` lies in the image of `ι` for every `x` in `R'`.
Take the unique preimage as `D'(x)`. Applying the injective ring map `ι` proves
additivity, integer-linearity, vanishing at one, Leibniz, and the required values on `R`.
-/
theorem exists_derivation_of_finiteType_away_extension
    (R : Type u) (R' : Type v) [CommRing R] [CommRing R'] [Algebra R R']
    (hfinite : Algebra.FiniteType R R')
    (_hinj : Function.Injective (algebraMap R R'))
    (g : R) (hreg : algebraMap R R' g ∈ nonZeroDivisors R')
    (D : Derivation ℤ R R)
    (δ : Derivation ℤ (Localization.Away (algebraMap R R' g))
      (Localization.Away (algebraMap R R' g)))
    (hδ : ∀ r : R, δ (algebraMap R' (Localization.Away (algebraMap R R' g))
      (algebraMap R R' r)) =
      algebraMap R' (Localization.Away (algebraMap R R' g))
        (algebraMap R R' (D r))) :
    ∃ N : ℕ, ∃ D' : Derivation ℤ R' R',
      ∀ r : R, D' (algebraMap R R' r) = algebraMap R R' (g ^ N * D r) := by
  classical
  let L := Localization.Away (algebraMap R R' g)
  let ι : R' →+* L := algebraMap R' L
  have hι : Function.Injective ι :=
    IsLocalization.injective L (Submonoid.powers_le.mpr hreg)
  obtain ⟨s, hs⟩ := hfinite.out
  have hden : ∀ x : R', ∃ n : ℕ, ∃ a : R',
      δ (ι x) * ι (algebraMap R R' g) ^ n = ι a := by
    intro x
    exact IsLocalization.Away.surj (algebraMap R R' g) (δ (ι x))
  choose n a ha using hden
  let N := s.sup n
  let Δ : Derivation ℤ L L := ι (algebraMap R R' g) ^ N • δ
  have hbase (r : R) : Δ (ι (algebraMap R R' r)) =
      ι (algebraMap R R' (g ^ N * D r)) := by
    change ι (algebraMap R R' g) ^ N * δ (ι (algebraMap R R' r)) = _
    rw [hδ]
    simp only [map_mul, map_pow]
    rfl
  have hgen (x : R') (hx : x ∈ s) : ∃ y : R', ι y = Δ (ι x) := by
    refine ⟨a x * algebraMap R R' g ^ (N - n x), ?_⟩
    change ι (a x * algebraMap R R' g ^ (N - n x)) =
      ι (algebraMap R R' g) ^ N * δ (ι x)
    rw [map_mul, map_pow, ← ha x]
    have hn : n x ≤ N := Finset.le_sup hx
    rw [mul_assoc, ← pow_add, Nat.add_sub_of_le hn]
    exact mul_comm _ _
  have H : ∀ x : R', ∃ y : R', ι y = Δ (ι x) := by
    intro x
    have hx : x ∈ Algebra.adjoin R (s : Set R') := by rw [hs]; trivial
    induction hx using Algebra.adjoin_induction with
    | mem x hx => exact hgen x hx
    | algebraMap r => exact ⟨algebraMap R R' (g ^ N * D r), (hbase r).symm⟩
    | add x y _ _ hx hy =>
      obtain ⟨x', hx'⟩ := hx
      obtain ⟨y', hy'⟩ := hy
      exact ⟨x' + y', by rw [map_add, hx', hy', map_add, map_add]⟩
    | mul x y _ _ hx hy =>
      obtain ⟨x', hx'⟩ := hx
      obtain ⟨y', hy'⟩ := hy
      refine ⟨x * y' + y * x', ?_⟩
      simp only [map_add, map_mul, hx', hy', Δ.leibniz, smul_eq_mul]
  choose d hd using H
  let D' : Derivation ℤ R' R' :=
    { toFun := d
      map_add' := by
        intro x y
        apply hι
        simp only [map_add, hd]
      map_smul' := by
        intro z x
        apply hι
        simp only [map_zsmul, hd]
        rfl
      map_one_eq_zero' := by
        apply hι
        change ι (d 1) = ι 0
        rw [hd, map_one, Δ.map_one_eq_zero, map_zero]
      leibniz' := by
        intro x y
        apply hι
        change ι (d (x * y)) = ι (x * d y + y * d x)
        simp only [map_add, map_mul, hd, Δ.leibniz, smul_eq_mul] }
  refine ⟨N, D', ?_⟩
  intro r
  apply hι
  exact (hd (algebraMap R R' r)).trans (hbase r)

end RingTheory
