/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Q63
-/
module

public import WeilConjectures.RingTheory.GradedAlgebra.Standard
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.RingTheory.GradedAlgebra.Homogeneous.Submodule
public import Mathlib.LinearAlgebra.Quotient.Basic
public import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.RingTheory.Noetherian.Basic

/-!
# Nilpotent devissage and homogeneous power torsion

Source: Stacks Project, Algebra, Tag 00K1, proposition-graded-hilbert-polynomial,
first two middle paragraphs, with the graded finite-generation argument of Tag 00K0
and the Noetherian submodule assertion of Tag 00IK
(blueprint: lem-trf-graded-power-torsion-polynomial-devissage).
-/

@[expose] public section

set_option autoImplicit false

namespace GradedAlgebra.IsStandard

universe u v w

/-- Eventual polynomiality for modules killed by `x` extends to modules killed by a
power of `x`. In every finite graded module, the exact power-torsion subset is a finite
homogeneous submodule killed by a uniform positive power. Its intersection grading has
an eventual polynomial Hilbert function, and the image grading on the finite quotient
has injective multiplication by `x`.

Source: Stacks Project, Algebra, Tags 00K0, 00K1 and 00IK
(blueprint: lem-trf-graded-power-torsion-polynomial-devissage).

Proof plan, following the seven steps of the node:
1. Replace finite module generators by their homogeneous components. Finite degree-one
algebra generators from `def-pc-standard-graded-algebra` give finitely many monomials in
any fixed degree, so every homogeneous piece is finite-dimensional.
2. Induct on the positive nilpotence exponent. For exponent greater than one use
`A = xL` and `B = L/xL`. Images of generators give finite generation; homogeneous
components show that A and B have the induced gradings. A has a smaller exponent and
B is killed by x.
3. In each degree the inclusion and quotient form a short exact sequence. A basis of
A together with lifts of a basis of B gives dimension additivity. Add the two eventual
polynomials and take the maximum threshold. This includes the zero module.
4. The subset of elements killed by a positive power is closed under addition and
S-scaling. If a power kills a sum of homogeneous components, it kills each component,
because their shifted degrees are distinct. Thus this submodule T is homogeneous.
5. Apply `lem-weil-pbc-noetherian-submodule-finite` (`Submodule.FG.of_le`) to T inside
the finite module M over the Noetherian ring S.
6. Choose finite generators of T and take the maximum of 1 and their annihilating
exponents. The resulting power kills all of T, so the nilpotent assertion gives its
polynomial and threshold; an empty generating family permits exponent 1.
7. Images of generators make M/T finite. Homogeneity gives directness of the image
grading and scalar multiplication respects degrees. If x kills a quotient class, a
power of x kills its representative, so the class is zero. When x is zero, T=M.
-/
theorem power_torsion_polynomial_devissage
    {k : Type u} {S : Type v} [Field k] [CommRing S] [Algebra k S]
    (𝒜 : ℕ → Submodule k S) [GradedAlgebra 𝒜] [IsStandard 𝒜] [IsNoetherianRing S]
    (x : S) (hx : x ∈ 𝒜 1)
    (hbase : ∀ (L : Type w) [AddCommGroup L] [Module S L] [Module k L]
      [IsScalarTower k S L] (ℒ : ℕ → Submodule k L)
      [DirectSum.Decomposition ℒ] [SetLike.GradedSMul 𝒜 ℒ] [Module.Finite S L],
      (∀ l : L, x • l = 0) →
        ∃ P : Polynomial ℚ, ∃ d : ℕ, ∀ n : ℕ, d ≤ n →
          (Module.finrank k (ℒ n) : ℚ) = P.eval (n : ℚ)) :
    (∀ (L : Type w) [AddCommGroup L] [Module S L] [Module k L]
      [IsScalarTower k S L] (ℒ : ℕ → Submodule k L)
      [DirectSum.Decomposition ℒ] [SetLike.GradedSMul 𝒜 ℒ] [Module.Finite S L],
      (∃ r : ℕ, 1 ≤ r ∧ ∀ l : L, x ^ r • l = 0) →
        ∃ P : Polynomial ℚ, ∃ d : ℕ, ∀ n : ℕ, d ≤ n →
          (Module.finrank k (ℒ n) : ℚ) = P.eval (n : ℚ)) ∧
    (∀ (M : Type w) [AddCommGroup M] [Module S M] [Module k M]
      [IsScalarTower k S M] (ℳ : ℕ → Submodule k M)
      [DirectSum.Decomposition ℳ] [SetLike.GradedSMul 𝒜 ℳ] [Module.Finite S M],
      ∃ T : Submodule S M,
        (∀ m : M, m ∈ T ↔ ∃ r : ℕ, 1 ≤ r ∧ x ^ r • m = 0) ∧
        Module.Finite S T ∧ T.IsHomogeneous ℳ ∧
        DirectSum.IsInternal (fun n : ℕ => (ℳ n).comap (T.subtype.restrictScalars k)) ∧
        SetLike.GradedSMul 𝒜 (fun n : ℕ => (ℳ n).comap (T.subtype.restrictScalars k)) ∧
        (∃ r : ℕ, 1 ≤ r ∧ ∀ t : T, x ^ r • t = 0) ∧
        (∃ P : Polynomial ℚ, ∃ d : ℕ, ∀ n : ℕ, d ≤ n →
          (Module.finrank k ((ℳ n).comap (T.subtype.restrictScalars k)) : ℚ) =
            P.eval (n : ℚ)) ∧
        Module.Finite S (M ⧸ T) ∧
        DirectSum.IsInternal (fun n : ℕ => (ℳ n).map (T.mkQ.restrictScalars k)) ∧
        SetLike.GradedSMul 𝒜 (fun n : ℕ => (ℳ n).map (T.mkQ.restrictScalars k)) ∧
        Function.Injective (fun q : M ⧸ T => x • q)) := by
  sorry

end GradedAlgebra.IsStandard
