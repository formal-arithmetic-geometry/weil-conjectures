module

public import Mathlib.RingTheory.DividedPowers.Basic
import Sheaf.Combinatorics.ColourProfileCoefficients

/-!
# Checking divided-power axioms on ideal generators

Source: Stacks Project, `dpa.tex`, Tag 07GP (lemma-check-on-generators),
conditions (a), (b) and conclusion (blueprint: lem-sfb-pd-check-generators).

The maps are represented by their extension by zero outside the ideal, exactly
as in Mathlib's `DividedPowers`. The positive maps preserve the ideal and the
zeroth map is one on it. The iteration coefficient is `Nat.uniformBell n m`,
whose factorial formula is `Nat.uniformBell_eq_div`; no division in the ring
is used.
-/

@[expose] public section

set_option autoImplicit false

universe u

namespace DividedPowers

/-- The multiplication and iteration axioms of divided powers need only be
checked on ideal generators, provided identity, homogeneity and addition hold
everywhere on the ideal.

Source: Stacks Project, `dpa.tex`, Tag 07GP (lemma-check-on-generators),
conditions (a), (b) and conclusion (blueprint: lem-sfb-pd-check-generators).

Proof:
1. Let `P z` assert the multiplication and iteration identities for every pair
   of positive indices at `z`. Homogeneity with scalar zero gives `g k 0 = 0`
   for positive `k`, so `P 0`. If `P z`, homogeneity gives `P (c * z)`:
   multiplication acquires `c ^ (n + m)` and iteration acquires `c ^ (m * n)`.
   In the second application of homogeneity, `g m z` belongs to the ideal.
2. If `P x` and `P y`, expand `g n (x + y) * g m (x + y)` by addition.
   Apply the multiplication identities at `x` and `y`, including the automatic
   zero-index cases. For fixed `a + b = n + m`, the resulting coefficient is
   the sum of `choose a i * choose b j` over `i + j = n`. Counting an `n`-subset
   of a disjoint union proves it is `choose (n + m) n`. Regrouping and addition
   prove multiplication at `x + y`, without any linear independence assumption.
3. Write `g m (x + y)` as the sum of `t i = g i x * g (m - i) y`.
   Each `t i` is in the ideal: the first factor is in it for positive `i`,
   and `t 0 = g m y`. Inductively apply addition to obtain the expansion of
   `g n` of this sum over profiles `r` with sum `n`.
4. For positive `k` and `0 < i < m`, homogeneity and iteration at `x` give
   `g k (t i) = B(k,i) * (g (m-i) y)^k * g (k*i) x`.
   Repeated multiplication at `y` gives the coefficient
   `(k*i)! * (k*(m-i))! / (k! * (i!)^k * ((m-i)!)^k)`.
   For `i = 0` use iteration at `y`; for `i = m` use iteration at `x`.
   For `k = 0` the factor is one. No operation takes `g 0 x` as an ideal input.
5. Repeated multiplication at each of `x` and `y` collects the factors of a
   profile into `g a x * g b y`, with `a = sum (i * r i)` and
   `b = sum ((m-i) * r i)`. Cancellation of factorials in rational coefficient
   calculations gives precisely the profile coefficient of
   `lem-sfb-pd-colour-profile-coefficients` (`Nat.colourProfile_coefficients`).
   That lemma proves its integrality; no element of the ring is cancelled.
6. Regroup by `a + b = n*m`. The same coefficient lemma shows that the sum
   over profiles with red weight `a` is `B(n,m)`, independently of `a`.
   Addition now gives iteration at `x + y`. Thus `P` is closed under addition;
   the integer equalities map to every commutative ring, including torsion rings.
7. Every element of `Ideal.span S` is a finite sum of scalar multiples of
   generators. The assumed identities on `S`, steps 1 and 2--6 prove `P`
   everywhere in `I`, including the empty sum. The three assumed axioms and
   these two identities give the ordinary five axioms of
   `def-sfb-ordinary-divided-power-structure` (`DividedPowers`, Tag 07GL).
   Zero indices follow from `g_zero` and `g_one`; the extension by zero and
   positive preservation of the ideal give the remaining representation fields.
-/
theorem exists_of_axioms_on_generators {A : Type u} [CommRing A]
    (I : Ideal A) (S : Set A) (hS : I = Ideal.span S) (g : ℕ → A → A)
    (g_null : ∀ (n : ℕ) (x : A), x ∉ I → g n x = 0)
    (g_zero : ∀ (x : A), x ∈ I → g 0 x = 1)
    (g_mem : ∀ (n : ℕ), 0 < n → ∀ (x : A), x ∈ I → g n x ∈ I)
    (g_one : ∀ (x : A), x ∈ I → g 1 x = x)
    (g_mul : ∀ (n : ℕ), 0 < n → ∀ (a x : A), x ∈ I →
      g n (a * x) = a ^ n * g n x)
    (g_add : ∀ (n : ℕ), 0 < n → ∀ (x y : A), x ∈ I → y ∈ I →
      g n (x + y) = ∑ i ∈ Finset.range (n + 1), g i x * g (n - i) y)
    (g_mul_gens : ∀ (s : A), s ∈ S → ∀ (n m : ℕ), 0 < n → 0 < m →
      g n s * g m s = ((n + m).choose n : A) * g (n + m) s)
    (g_comp_gens : ∀ (s : A), s ∈ S → ∀ (n m : ℕ), 0 < n → 0 < m →
      g n (g m s) = (Nat.uniformBell n m : A) * g (n * m) s) :
    ∃ γ : DividedPowers I, γ.dpow = g := by
  sorry

end DividedPowers
