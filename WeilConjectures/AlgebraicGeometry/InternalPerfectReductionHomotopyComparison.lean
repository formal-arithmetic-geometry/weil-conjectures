/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.InternalPerfectReductionHomEquiv

/-! # Actual derived reductions and ordinary homotopy endomorphisms -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite
namespace AlgebraicGeometry.ProEtale

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

/-- The canonical levelwise derived-to-homotopy comparisons commute with successor
scalar extension. The levelwise bijections themselves are already constructed and proved.
No scalar Hom cohomology or locally constant functions enter this assertion.

Source: Stacks Tags 06YY and 064B; blueprint Compatible isomorphisms.
(blueprint: lem-pe-internal-perfect-reduction-homotopy-comparison).

Proof: use the derived counit comparison fixed in internalPerfectReductionOrdinaryIso.
The ordinary and derived balancing isomorphisms are mates of the same restriction
compositor, including the equality of the composite quotient map with the direct
quotient. Write gamma_n for the canonical model isomorphism, alpha_n for derived
balancing, a_n for ordinary balancing, and epsilon_psi for the counit of successor
extension. After the specified quotient factorizations, the square is
alpha_n followed by gamma_n = L(psi)(gamma_(n+1)) followed by epsilon_psi followed
by Qh(a_n). The ordinary quotient complex is K-flat, so epsilon_psi is invertible.
The formulas for the derived adjunction unit on the homotopy quotient
identify the two mate squares after applying the restriction adjunction's hom
bijection. Its injectivity proves the balancing square on these K-flat models.
Naturality of the derived counit then identifies extension of a representative
chain map with ordinary extension of that chain map. Conjugating by the balancing
isomorphisms gives equality after localization. The K-projective localization
bijection is injective, so this proves the displayed equality in the homotopy
category. Every homotopy class has a chain-map representative. The same identities
apply for zero complexes and empty schemes, without a nonzero-basis assumption. -/
theorem internalPerfectReduction_homotopyComparison
    (X : Scheme.{u}) (W : X.ProEt) (_hAffine : IsAffine W.left)
    (_hweak : (Scheme.ProEt.topology X).IsWeaklyContractible.{u + 1} W)
    (P : CochainComplex (ModuleCat.{u} (Padic.coefficientExtensionIntegers l E)) ℤ)
    (a b : ℤ) (_ha : P.IsStrictlyGE a) (_hb : P.IsStrictlyLE b)
    (_hfree : ∀ i : ℤ, Module.Finite (Padic.coefficientExtensionIntegers l E) (P.X i) ∧
      Module.Free (Padic.coefficientExtensionIntegers l E) (P.X i)) :
    ∀ (n : ℕ) (x : (internalReductionHomTower l E W.left
      (internalPerfectScalarModel l E W.left P)
      (internalPerfectScalarModel l E W.left P)).obj (op (n + 1))),
      internalPerfectReductionHomEquiv l E X W _hweak P a b _ha _hb _hfree n
        ((internalReductionHomTower l E W.left
          (internalPerfectScalarModel l E W.left P)
          (internalPerfectScalarModel l E W.left P)).map (homOfLE (Nat.le_succ n)).op x) =
      internalPerfectOrdinaryHomStep l E W.left P n
        (internalPerfectReductionHomEquiv l E X W _hweak P a b _ha _hb _hfree (n + 1) x) := by
  sorry

end AlgebraicGeometry.ProEtale
