module

public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Sheaf.RingTheory.DifferentialOrder

/-!
# Finite-order differential operators extend to prime localizations

Source: Stacks Project, Algebra, Tag 0G36, `lemma-invert-system-differential-operators`,
specialized to the ring as both modules and to the complement of a prime ideal
(blueprint: lem-trf-differential-operator-localization).
-/

@[expose] public section

universe u v

namespace LinearMap

/-- Every finite-order `R`-linear differential operator on `B` has a unique extension of
at most the same order to its ordinary prime localization.
Source: Stacks Project, Algebra, Tag 0G36
(blueprint: lem-trf-differential-operator-localization).

Proof: Put `S = B ∖ p` and `A = Bₚ`. Induct on the order bound, proving existence and
uniqueness together. At order zero, the operator is multiplication by `D 1`, so extend it
by multiplication by its image in `A`. Sums, negatives and composition with multiplication
preserve an order bound, by induction and
`lem-trf-differential-operator-composition-order`. At successor order, let `E_b` be the unique
extension of the lower-order commutator `L_b = [D,b]`. The identities for `L_(bc)` and the
symmetry of its scalar commutators pass to `E_b` by lower-order uniqueness; also `E_1 = 0`.
Define `E(b/s) = j(s)⁻¹ (j(D(b)) - E_s(b/s))`. The product identity for `E_(ts)` proves
invariance under refinement of a fraction. If two fractions agree, the localization
relation supplies a common refinement with equal numerators, even when `j` is not injective;
thus `E` is well-defined. Common denominators prove additivity and `R`-linearity; denominator
one proves extension of `D`. The commutator symmetry gives `[E,j(b)] = E_b`, while
`[E,j(s)⁻¹] = -j(s)⁻¹ [E,j(s)] j(s)⁻¹` has the required lower order. The elements whose
commutators have that bound form an `R`-subalgebra, using closure under sums, negatives and
composition with multiplication. They contain all `j(b)` and inverse denominators, hence
all fractions. This proves the order bound, as in Tag 0G35. Finally any other extension `F`
has `[F,j(s)] = E_s` by lower-order uniqueness. Evaluating on `b/s` forces the displayed
formula for `F`, proving uniqueness. -/
theorem existsUnique_differentialOperator_atPrime
    (R : Type u) (B : Type v) [CommRing R] [CommRing B] [Algebra R B]
    (p : Ideal B) [p.IsPrime] (r : ℕ) (D : B →ₗ[R] B)
    (hD : HasDifferentialOrderLE R B r D) :
    ∃! E : Localization.AtPrime p →ₗ[R] Localization.AtPrime p,
      HasDifferentialOrderLE R (Localization.AtPrime p) r E ∧
        ∀ b : B, E (algebraMap B (Localization.AtPrime p) b) =
          algebraMap B (Localization.AtPrime p) (D b) := by
  sorry

end LinearMap
