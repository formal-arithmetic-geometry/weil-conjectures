module

public import Mathlib.Algebra.MonoidAlgebra.Basic
public import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
# Joint detection by torsion quotients of a split torus

Source: Milne, Algebraic Groups (2017), Theorem 12.33, printed p.243, and the proof of
Theorem 12.36, printed pp.243–244 (blueprint: lem-sfb-torus-torsion-joint-injectivity).

The Laurent ring is Mathlib's `AddMonoidAlgebra B (Fin r → ℤ)`: its coefficients have finite
support, addition is coefficientwise, and multiplication adds exponent vectors. In rank zero,
`AddMonoidAlgebra.uniqueAlgEquiv B (Fin 0 → ℤ)` is the canonical identification with `B`.
-/

@[expose] public noncomputable section

universe u

namespace AddMonoidAlgebra

/-- The ideal `J_n = (t_1^n - 1, …, t_r^n - 1)` in the Laurent ring over `B`.
The exponent `Pi.single i (n : ℤ)` is `n` times the `i`th coordinate vector, so its monomial
is `t_i^n`. The span of the empty range in rank zero is the zero ideal.
Source: Milne, Algebraic Groups (2017), Theorem 12.33, printed p.243, and Theorem 12.36,
printed pp.243–244 (blueprint: lem-sfb-torus-torsion-joint-injectivity). -/
def torusTorsionIdeal (B : Type u) [CommRing B] (r n : ℕ) :
    Ideal (AddMonoidAlgebra B (Fin r → ℤ)) :=
  Ideal.span (Set.range fun i : Fin r ↦
    (AddMonoidAlgebra.single (Pi.single i (n : ℤ)) (1 : B) - 1))

/-- The torsion ideals have zero intersection, and the associated canonical quotient maps
jointly detect equality. In rank zero every torsion ideal is zero; the Laurent ring itself is
identified with `B` by `AddMonoidAlgebra.uniqueAlgEquiv B (Fin 0 → ℤ)`.

Source: Milne, Algebraic Groups (2017), Theorem 12.33, printed p.243, and the proof of
Theorem 12.36, printed pp.243–244 (blueprint: lem-sfb-torus-torsion-joint-injectivity).

Proof:
1. When `r = 0`, there is just one exponent vector. The canonical trivial-monoid algebra
   equivalence identifies the ring with `B`. There are no ideal generators, so every `J_n`
   and their intersection are zero.
2. For positive `n` and a residue vector `a` modulo `n`, sum the coefficients of a Laurent
   polynomial over its finite support at exponents reducing to `a`. These sums are `B`-linear:
   use the union of supports for addition, pad missing coefficients by zero, and distribute
   finite sums; scalar multiplication is coefficientwise.
3. Multiplication by `t_i^n` translates the support by `n` times the coordinate vector. This
   bijection preserves residues, so every residue sum kills `h * (t_i^n - 1)`. Distributing
   products in the ideal span expresses each ideal element as a finite sum of such multiples.
   Linearity therefore makes every residue sum vanish on `J_n`.
4. For a polynomial in every `J_n`, its empty support gives zero immediately. Otherwise let
   `M` bound the absolute values of all support coordinates, and choose `n = 2*M + 1`.
   Two support vectors with the same residue have coordinate differences divisible by `n`
   and of absolute value less than `n`; all those differences vanish. Each residue sum thus
   isolates one coefficient, which vanishes by step 3. Every coefficient is zero. Conversely,
   zero belongs to every ideal.
5. By the quotient construction of def-weil-pbc-algebra-hom-quotient, the kernel of the
   canonical quotient map is `J_n`. Equality of the images of `f` and `g` is equivalent to
   membership of `f-g` in `J_n`; step 4 gives `f=g`. Conversely, joint detection applied to
   `f` and zero gives the intersection assertion. This argument also applies in rank zero. -/
theorem torus_torsion_joint_injectivity (B : Type u) [CommRing B] (r : ℕ) :
    (⨅ (n : ℕ) (_ : 0 < n), torusTorsionIdeal B r n) = ⊥ ∧
      (∀ f g : AddMonoidAlgebra B (Fin r → ℤ),
        (∀ (n : ℕ) (_ : 0 < n),
          Ideal.Quotient.mkₐ B (torusTorsionIdeal B r n) f =
            Ideal.Quotient.mkₐ B (torusTorsionIdeal B r n) g) → f = g) ∧
      (∀ (n : ℕ) (_ : 0 < n), torusTorsionIdeal B 0 n = ⊥) := by
  sorry

end AddMonoidAlgebra
