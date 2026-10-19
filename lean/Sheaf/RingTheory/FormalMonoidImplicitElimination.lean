/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q12
-/
module

public import Mathlib.Algebra.MonoidAlgebra.Basic
public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.Topology.Algebra.Nonarchimedean.AdicTopology
public import Sheaf.AlgebraicGeometry.FineSaturatedLogBlowup
import Mathlib.RingTheory.AdicCompletion.LocalRing
import Mathlib.RingTheory.FiniteType
import WeilConjectures.RingTheory.AdicCompletionNoetherian
import WeilConjectures.RingTheory.CompleteLocalQuotient
import Sheaf.RingTheory.FormalMonoidAdicEvaluation

/-!
# Implicit elimination in completed sharp monoid algebras

Source: ILO, Travaux de Gabber, Exposé VI 2.3, printed p. 73, completed Kummer
chart formulas; agent-supplied implicit substitution retaining chart unit twists
(blueprint: lem-per-formal-monoid-implicit-elimination).
-/

@[expose] public section

universe u v w

namespace AddMonoidAlgebra

open Classical in
/-- Elimination of the relations `X^s = u(s) Y^(β s)` in the completed monoid ring.

Source: ILO VI 2.3, printed p. 73, completed Kummer chart formulas, with the
agent-supplied implicit substitution argument
(blueprint: lem-per-formal-monoid-implicit-elimination).

The three ideals `aS`, `aT`, `aH` are named by their defining equalities. The map
`ι` is the canonical continuous inclusion of the source completion: its value on
every coefficient-monomial term is specified, so density and separatedness
uniquely determine it. Likewise `e` is the coefficient-and-`Y` map, specified on
all such terms. The completion topologies are the inverse-limit topologies; the
topology on the quotient is the quotient topology. The final map `ε` is the
continuous augmentation killing every nonzero `T`-monomial. The last equality
expresses the identity on `D` after applying the inverse and this augmentation.

Proof plan (the ten steps of the DAG node):
1. Finite generation gives finite-type monoid algebras. Apply
   lem-weil-pbc-finite-type-algebra-noetherian,
   lem-weil-pbc-adic-completion-noetherian and
   lem-weil-pbc-adic-completion-mod-ideal to obtain Noetherian complete separated
   completions with residue field `D / n`.
2. A geometric series in the defining ideal inverts each element of nonzero
   residue. Thus the completions are nonzero complete Noetherian local rings.
3. For a monoid map `a` into the maximal ideal of `A = D[[T]]`, use
   lem-per-formal-monoid-adic-evaluation to define
   `F(a)(s) = E_a(u(s)) Y^(β s)`. Its congruence estimate gains one power of the
   maximal ideal because `β s` is nonzero for nonzero `s`.
4. Iterate from the augmentation monoid map. Successive differences lie in
   increasing ideal powers; completeness gives a limit monoid map `a`.
5. The evaluation congruence estimate and separatedness give the exact fixed
   point equations. Each nonzero source monomial is a multiple of `Y^(β s)`.
6. Evaluate on `S × T` at `(s,t) ↦ a(s) Y^t`. This gives a continuous map from
   `H` to `A`, killing the displayed relation ideal, which is therefore proper.
7. Use lem-weil-pbc-complete-local-quotient to make `H / I` complete local.
   Evaluate the target monoid in this quotient. Evaluation uniqueness shows
   that the composite `A → H / I → A` is the identity.
8. In `H / I`, compare the original source monomials with the substituted ones.
   They satisfy the same fixed point equations. The contraction improves their
   difference through every maximal-ideal power, so separatedness equates them.
9. Evaluation uniqueness on `S × T` then gives the other inverse identity, hence
   the continuous equivalence `e` with continuous inverse.
10. The fixed point formula puts inverse source monomials in the target monomial
    ideal. Evaluation at zero on nonzero target exponents gives `ε`; both maps
    fix coefficients, proving the final identity.
-/
theorem exists_formalMonoid_implicitElimination
    (D : Type u) [CommRing D] [IsNoetherianRing D] [IsLocalRing D]
    [IsAdicComplete (IsLocalRing.maximalIdeal D) D]
    (S : Type v) [AddCommMonoid S] (T : Type w) [AddCommMonoid T]
    (hS : AlgebraicGeometry.IsFineSaturatedMonoid (Multiplicative S))
    (hT : AlgebraicGeometry.IsFineSaturatedMonoid (Multiplicative T))
    (hsharpS : ∀ s : S, IsUnit (Multiplicative.ofAdd s) → s = 0)
    (hsharpT : ∀ t : T, IsUnit (Multiplicative.ofAdd t) → t = 0)
    (β : S →+ T) (hβ : ∀ s : S, β s = 0 → s = 0)
    (aS : Ideal (AddMonoidAlgebra D S))
    (haS : aS = Ideal.map (algebraMap D (AddMonoidAlgebra D S))
        (IsLocalRing.maximalIdeal D) ⊔
      Ideal.span {z | ∃ s : S, s ≠ 0 ∧ z = single s (1 : D)})
    (aT : Ideal (AddMonoidAlgebra D T))
    (haT : aT = Ideal.map (algebraMap D (AddMonoidAlgebra D T))
        (IsLocalRing.maximalIdeal D) ⊔
      Ideal.span {z | ∃ t : T, t ≠ 0 ∧ z = single t (1 : D)})
    (aH : Ideal (AddMonoidAlgebra D (S × T)))
    (haH : aH = Ideal.map (algebraMap D (AddMonoidAlgebra D (S × T)))
        (IsLocalRing.maximalIdeal D) ⊔
      Ideal.span {z | ∃ p : S × T, p ≠ 0 ∧ z = single p (1 : D)})
    (u : Multiplicative S →* (AdicCompletion aS (AddMonoidAlgebra D S))ˣ) :
    ∃ ι : AdicCompletion aS (AddMonoidAlgebra D S) →+*
        AdicCompletion aH (AddMonoidAlgebra D (S × T)),
      @Continuous _ _
        (⨅ n : ℕ, TopologicalSpace.induced (AdicCompletion.evalₐ aS n) ⊥)
        (⨅ n : ℕ, TopologicalSpace.induced (AdicCompletion.evalₐ aH n) ⊥) ι ∧
      (∀ (s : S) (d : D),
        ι (AdicCompletion.of aS (AddMonoidAlgebra D S) (single s d)) =
          AdicCompletion.of aH (AddMonoidAlgebra D (S × T)) (single (s, 0) d)) ∧
      ∃ I : Ideal (AdicCompletion aH (AddMonoidAlgebra D (S × T))),
        I = Ideal.span {z | ∃ s : S,
          z = AdicCompletion.of aH (AddMonoidAlgebra D (S × T)) (single (s, 0) 1) -
            ι (u (Multiplicative.ofAdd s) : AdicCompletion aS (AddMonoidAlgebra D S)) *
              AdicCompletion.of aH (AddMonoidAlgebra D (S × T)) (single (0, β s) 1)} ∧
        ∃ e : AdicCompletion aT (AddMonoidAlgebra D T) ≃+*
            (AdicCompletion aH (AddMonoidAlgebra D (S × T)) ⧸ I),
          (∀ (t : T) (d : D),
            e (AdicCompletion.of aT (AddMonoidAlgebra D T) (single t d)) =
              Ideal.Quotient.mk I
                (AdicCompletion.of aH (AddMonoidAlgebra D (S × T)) (single (0, t) d))) ∧
          @Continuous _ _
            (⨅ n : ℕ, TopologicalSpace.induced (AdicCompletion.evalₐ aT n) ⊥)
            (TopologicalSpace.coinduced (Ideal.Quotient.mk I)
              (⨅ n : ℕ, TopologicalSpace.induced (AdicCompletion.evalₐ aH n) ⊥)) e ∧
          @Continuous _ _
            (TopologicalSpace.coinduced (Ideal.Quotient.mk I)
              (⨅ n : ℕ, TopologicalSpace.induced (AdicCompletion.evalₐ aH n) ⊥))
            (⨅ n : ℕ, TopologicalSpace.induced (AdicCompletion.evalₐ aT n) ⊥) e.symm ∧
          (∀ s : S, s ≠ 0 →
            e.symm (Ideal.Quotient.mk I
              (AdicCompletion.of aH (AddMonoidAlgebra D (S × T)) (single (s, 0) 1))) ∈
                Ideal.span {z | ∃ t : T, t ≠ 0 ∧
                  z = AdicCompletion.of aT (AddMonoidAlgebra D T) (single t 1)}) ∧
          ∃ ε : AdicCompletion aT (AddMonoidAlgebra D T) →+* D,
            @Continuous _ _
              (⨅ n : ℕ, TopologicalSpace.induced (AdicCompletion.evalₐ aT n) ⊥)
              (IsLocalRing.maximalIdeal D).adicTopology ε ∧
            (∀ (t : T) (d : D),
              ε (AdicCompletion.of aT (AddMonoidAlgebra D T) (single t d)) =
                if t = 0 then d else 0) ∧
            ∀ d : D, ε (e.symm (Ideal.Quotient.mk I
              (algebraMap D (AdicCompletion aH (AddMonoidAlgebra D (S × T))) d))) = d := by
  sorry

end AddMonoidAlgebra
