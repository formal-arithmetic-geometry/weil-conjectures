/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.RingTheory.Localization.Algebra
import WeilConjectures.RingTheory.PopescuAuxiliaryAlgebraLocalizationsPart1
import WeilConjectures.RingTheory.PopescuAuxiliaryAlgebraLocalizationsPart2

/-!
# Localizations of the auxiliary algebra in height-zero delocalization

The auxiliary algebra `B` of the height-zero delocalization step becomes, after inverting `z` or
one of the `y_l`, a localization of an explicit polynomial algebra.

## Implementation details

The statement is written without `let`. The variable indices of
`S = MvPolynomial (Fin n ⊕ (Fin r ⊕ (Unit ⊕ (Fin r × Fin m)))) A` are, in order, `x`, `y`, `z`
and `t`; `B` is `S` modulo the span of the `f_j - ∑ y_i t_ij` and the `z y_i`, `C` is
`MvPolynomial (Fin n) A` modulo the span of the `f_j`, and the variable indices of
`T = MvPolynomial ((Fin r × Fin m) ⊕ Unit) C` are `t` and `z`. In
`Q_l = MvPolynomial (Fin n ⊕ (Fin r ⊕ ({i // i ≠ l} × Fin m))) A` the row of `t`
indexed by `l` is omitted.

In `B_z` the relations `z y_i = 0` give `y = 0`; in `B_{y_l}` one has `z = 0` and
`t (l, j) = y_l⁻¹ (f_j - ∑_{i ≠ l} y_i t (i, j))`. The maps come from the universal properties of
polynomial rings, quotients and localizations.

## References

* [Stacks, Tag 07FA]
-/

@[expose] public section

universe u

open MvPolynomial
open scoped BigOperators

namespace Algebra

/-- The two localizations of the auxiliary algebra `B` of height-zero delocalization: `B_z` is
the localization at `z` of `C[t, z]`, and for each `l`, `B_{y_l}` is the localization at `y_l` of
the polynomial ring `Q_l` in which the row of `t` indexed by `l` is omitted. -/
theorem popescu_auxiliaryAlgebra_localizations
    (A : Type u) [CommRing A] (n m r : ℕ) (hr : 1 ≤ r)
    (f : Fin m → MvPolynomial (Fin n) A) :
    (∃ phi : (MvPolynomial (Fin n ⊕ (Fin r ⊕ (Unit ⊕ (Fin r × Fin m)))) A ⧸
          (Ideal.span
            (Set.range (fun j : Fin m =>
                aeval (fun k : Fin n =>
                  (X (Sum.inl k) :
                    MvPolynomial (Fin n ⊕ (Fin r ⊕ (Unit ⊕ (Fin r × Fin m)))) A)) (f j) -
                  ∑ i : Fin r,
                    (X (Sum.inr (Sum.inl i)) :
                      MvPolynomial (Fin n ⊕ (Fin r ⊕ (Unit ⊕ (Fin r × Fin m)))) A) *
                    X (Sum.inr (Sum.inr (Sum.inr (i, j))))) ∪
              Set.range (fun i : Fin r =>
                (X (Sum.inr (Sum.inr (Sum.inl ()))) :
                  MvPolynomial (Fin n ⊕ (Fin r ⊕ (Unit ⊕ (Fin r × Fin m)))) A) *
                  X (Sum.inr (Sum.inl i)))))) →ₐ[A]
        Localization.Away (X (Sum.inr ()) :
          MvPolynomial ((Fin r × Fin m) ⊕ Unit)
            (MvPolynomial (Fin n) A ⧸ (Ideal.span (Set.range f)))),
      (∀ k : Fin n,
        phi (Ideal.Quotient.mkₐ A
          (Ideal.span
            (Set.range (fun j : Fin m =>
                aeval (fun k : Fin n =>
                  (X (Sum.inl k) :
                    MvPolynomial (Fin n ⊕ (Fin r ⊕ (Unit ⊕ (Fin r × Fin m)))) A)) (f j) -
                  ∑ i : Fin r,
                    (X (Sum.inr (Sum.inl i)) :
                      MvPolynomial (Fin n ⊕ (Fin r ⊕ (Unit ⊕ (Fin r × Fin m)))) A) *
                    X (Sum.inr (Sum.inr (Sum.inr (i, j))))) ∪
              Set.range (fun i : Fin r =>
                (X (Sum.inr (Sum.inr (Sum.inl ()))) :
                  MvPolynomial (Fin n ⊕ (Fin r ⊕ (Unit ⊕ (Fin r × Fin m)))) A) *
                  X (Sum.inr (Sum.inl i)))))
          (X (Sum.inl k) :
            MvPolynomial (Fin n ⊕ (Fin r ⊕ (Unit ⊕ (Fin r × Fin m)))) A)) =
          algebraMap (MvPolynomial ((Fin r × Fin m) ⊕ Unit)
              (MvPolynomial (Fin n) A ⧸ (Ideal.span (Set.range f)))) _
            (MvPolynomial.C (Ideal.Quotient.mkₐ A (Ideal.span (Set.range f)) (X k)))) ∧
      (∀ i : Fin r,
        phi (Ideal.Quotient.mkₐ A
          (Ideal.span
            (Set.range (fun j : Fin m =>
                aeval (fun k : Fin n =>
                  (X (Sum.inl k) :
                    MvPolynomial (Fin n ⊕ (Fin r ⊕ (Unit ⊕ (Fin r × Fin m)))) A)) (f j) -
                  ∑ i : Fin r,
                    (X (Sum.inr (Sum.inl i)) :
                      MvPolynomial (Fin n ⊕ (Fin r ⊕ (Unit ⊕ (Fin r × Fin m)))) A) *
                    X (Sum.inr (Sum.inr (Sum.inr (i, j))))) ∪
              Set.range (fun i : Fin r =>
                (X (Sum.inr (Sum.inr (Sum.inl ()))) :
                  MvPolynomial (Fin n ⊕ (Fin r ⊕ (Unit ⊕ (Fin r × Fin m)))) A) *
                  X (Sum.inr (Sum.inl i)))))
          (X (Sum.inr (Sum.inl i)) :
            MvPolynomial (Fin n ⊕ (Fin r ⊕ (Unit ⊕ (Fin r × Fin m)))) A)) = 0) ∧
      phi (Ideal.Quotient.mkₐ A
        (Ideal.span
          (Set.range (fun j : Fin m =>
              aeval (fun k : Fin n =>
                (X (Sum.inl k) :
                  MvPolynomial (Fin n ⊕ (Fin r ⊕ (Unit ⊕ (Fin r × Fin m)))) A)) (f j) -
                ∑ i : Fin r,
                  (X (Sum.inr (Sum.inl i)) :
                    MvPolynomial (Fin n ⊕ (Fin r ⊕ (Unit ⊕ (Fin r × Fin m)))) A) *
                  X (Sum.inr (Sum.inr (Sum.inr (i, j))))) ∪
            Set.range (fun i : Fin r =>
              (X (Sum.inr (Sum.inr (Sum.inl ()))) :
                MvPolynomial (Fin n ⊕ (Fin r ⊕ (Unit ⊕ (Fin r × Fin m)))) A) *
                X (Sum.inr (Sum.inl i)))))
        (X (Sum.inr (Sum.inr (Sum.inl ()))) :
          MvPolynomial (Fin n ⊕ (Fin r ⊕ (Unit ⊕ (Fin r × Fin m)))) A)) =
        algebraMap (MvPolynomial ((Fin r × Fin m) ⊕ Unit)
            (MvPolynomial (Fin n) A ⧸ (Ideal.span (Set.range f)))) _
          (X (Sum.inr ())) ∧
      (∀ ij : Fin r × Fin m,
        phi (Ideal.Quotient.mkₐ A
          (Ideal.span
            (Set.range (fun j : Fin m =>
                aeval (fun k : Fin n =>
                  (X (Sum.inl k) :
                    MvPolynomial (Fin n ⊕ (Fin r ⊕ (Unit ⊕ (Fin r × Fin m)))) A)) (f j) -
                  ∑ i : Fin r,
                    (X (Sum.inr (Sum.inl i)) :
                      MvPolynomial (Fin n ⊕ (Fin r ⊕ (Unit ⊕ (Fin r × Fin m)))) A) *
                    X (Sum.inr (Sum.inr (Sum.inr (i, j))))) ∪
              Set.range (fun i : Fin r =>
                (X (Sum.inr (Sum.inr (Sum.inl ()))) :
                  MvPolynomial (Fin n ⊕ (Fin r ⊕ (Unit ⊕ (Fin r × Fin m)))) A) *
                  X (Sum.inr (Sum.inl i)))))
          (X (Sum.inr (Sum.inr (Sum.inr ij))) :
            MvPolynomial (Fin n ⊕ (Fin r ⊕ (Unit ⊕ (Fin r × Fin m)))) A)) =
          algebraMap (MvPolynomial ((Fin r × Fin m) ⊕ Unit)
              (MvPolynomial (Fin n) A ⧸ (Ideal.span (Set.range f)))) _
            (X (Sum.inl ij))) ∧
      ∃ e : Localization.Away (Ideal.Quotient.mkₐ A
          (Ideal.span
            (Set.range (fun j : Fin m =>
                aeval (fun k : Fin n =>
                  (X (Sum.inl k) :
                    MvPolynomial (Fin n ⊕ (Fin r ⊕ (Unit ⊕ (Fin r × Fin m)))) A)) (f j) -
                  ∑ i : Fin r,
                    (X (Sum.inr (Sum.inl i)) :
                      MvPolynomial (Fin n ⊕ (Fin r ⊕ (Unit ⊕ (Fin r × Fin m)))) A) *
                    X (Sum.inr (Sum.inr (Sum.inr (i, j))))) ∪
              Set.range (fun i : Fin r =>
                (X (Sum.inr (Sum.inr (Sum.inl ()))) :
                  MvPolynomial (Fin n ⊕ (Fin r ⊕ (Unit ⊕ (Fin r × Fin m)))) A) *
                  X (Sum.inr (Sum.inl i)))))
          (X (Sum.inr (Sum.inr (Sum.inl ()))) :
            MvPolynomial (Fin n ⊕ (Fin r ⊕ (Unit ⊕ (Fin r × Fin m)))) A)) ≃ₐ[A]
          Localization.Away (X (Sum.inr ()) :
            MvPolynomial ((Fin r × Fin m) ⊕ Unit)
              (MvPolynomial (Fin n) A ⧸ (Ideal.span (Set.range f)))),
        ∀ b : MvPolynomial (Fin n ⊕ (Fin r ⊕ (Unit ⊕ (Fin r × Fin m)))) A ⧸
            (Ideal.span
              (Set.range (fun j : Fin m =>
                  aeval (fun k : Fin n =>
                    (X (Sum.inl k) :
                      MvPolynomial (Fin n ⊕ (Fin r ⊕ (Unit ⊕ (Fin r × Fin m)))) A)) (f j) -
                    ∑ i : Fin r,
                      (X (Sum.inr (Sum.inl i)) :
                        MvPolynomial (Fin n ⊕ (Fin r ⊕ (Unit ⊕ (Fin r × Fin m)))) A) *
                      X (Sum.inr (Sum.inr (Sum.inr (i, j))))) ∪
                Set.range (fun i : Fin r =>
                  (X (Sum.inr (Sum.inr (Sum.inl ()))) :
                    MvPolynomial (Fin n ⊕ (Fin r ⊕ (Unit ⊕ (Fin r × Fin m)))) A) *
                    X (Sum.inr (Sum.inl i))))),
          e (algebraMap _ _ b) = phi b) ∧
    (∀ l : Fin r,
      ∃ e : Localization.Away (X (Sum.inr (Sum.inl l)) :
            MvPolynomial (Fin n ⊕ (Fin r ⊕ ({i : Fin r // i ≠ l} × Fin m))) A) ≃ₐ[A]
          Localization.Away (Ideal.Quotient.mkₐ A
            (Ideal.span
              (Set.range (fun j : Fin m =>
                  aeval (fun k : Fin n =>
                    (X (Sum.inl k) :
                      MvPolynomial (Fin n ⊕ (Fin r ⊕ (Unit ⊕ (Fin r × Fin m)))) A)) (f j) -
                    ∑ i : Fin r,
                      (X (Sum.inr (Sum.inl i)) :
                        MvPolynomial (Fin n ⊕ (Fin r ⊕ (Unit ⊕ (Fin r × Fin m)))) A) *
                      X (Sum.inr (Sum.inr (Sum.inr (i, j))))) ∪
                Set.range (fun i : Fin r =>
                  (X (Sum.inr (Sum.inr (Sum.inl ()))) :
                    MvPolynomial (Fin n ⊕ (Fin r ⊕ (Unit ⊕ (Fin r × Fin m)))) A) *
                    X (Sum.inr (Sum.inl i)))))
            (X (Sum.inr (Sum.inl l)) :
              MvPolynomial (Fin n ⊕ (Fin r ⊕ (Unit ⊕ (Fin r × Fin m)))) A)),
        (∀ a : MvPolynomial (Fin n ⊕ (Fin r ⊕ ({i : Fin r // i ≠ l} × Fin m))) A,
          e (algebraMap _ _ a) = algebraMap _ _
            (aeval
              (Sum.elim
                (fun k : Fin n =>
                  Ideal.Quotient.mkₐ A
                  (Ideal.span
                    (Set.range (fun j : Fin m =>
                        aeval (fun k : Fin n =>
                          (X (Sum.inl k) :
                            MvPolynomial (Fin n ⊕ (Fin r ⊕ (Unit ⊕ (Fin r × Fin m)))) A)) (f j) -
                          ∑ i : Fin r,
                            (X (Sum.inr (Sum.inl i)) :
                              MvPolynomial (Fin n ⊕ (Fin r ⊕ (Unit ⊕ (Fin r × Fin m)))) A) *
                            X (Sum.inr (Sum.inr (Sum.inr (i, j))))) ∪
                      Set.range (fun i : Fin r =>
                        (X (Sum.inr (Sum.inr (Sum.inl ()))) :
                          MvPolynomial (Fin n ⊕ (Fin r ⊕ (Unit ⊕ (Fin r × Fin m)))) A) *
                          X (Sum.inr (Sum.inl i)))))
                  (X (Sum.inl k) :
                    MvPolynomial (Fin n ⊕ (Fin r ⊕ (Unit ⊕ (Fin r × Fin m)))) A))
                (Sum.elim
                  (fun i : Fin r =>
                    Ideal.Quotient.mkₐ A
                    (Ideal.span
                      (Set.range (fun j : Fin m =>
                          aeval (fun k : Fin n =>
                            (X (Sum.inl k) :
                              MvPolynomial (Fin n ⊕ (Fin r ⊕ (Unit ⊕ (Fin r × Fin m)))) A)) (f j) -
                            ∑ i : Fin r,
                              (X (Sum.inr (Sum.inl i)) :
                                MvPolynomial (Fin n ⊕ (Fin r ⊕ (Unit ⊕ (Fin r × Fin m)))) A) *
                              X (Sum.inr (Sum.inr (Sum.inr (i, j))))) ∪
                        Set.range (fun i : Fin r =>
                          (X (Sum.inr (Sum.inr (Sum.inl ()))) :
                            MvPolynomial (Fin n ⊕ (Fin r ⊕ (Unit ⊕ (Fin r × Fin m)))) A) *
                            X (Sum.inr (Sum.inl i)))))
                    (X (Sum.inr (Sum.inl i)) :
                      MvPolynomial (Fin n ⊕ (Fin r ⊕ (Unit ⊕ (Fin r × Fin m)))) A))
                  (fun ij : {i : Fin r // i ≠ l} × Fin m =>
                    Ideal.Quotient.mkₐ A
                    (Ideal.span
                      (Set.range (fun j : Fin m =>
                          aeval (fun k : Fin n =>
                            (X (Sum.inl k) :
                              MvPolynomial (Fin n ⊕ (Fin r ⊕ (Unit ⊕ (Fin r × Fin m)))) A)) (f j) -
                            ∑ i : Fin r,
                              (X (Sum.inr (Sum.inl i)) :
                                MvPolynomial (Fin n ⊕ (Fin r ⊕ (Unit ⊕ (Fin r × Fin m)))) A) *
                              X (Sum.inr (Sum.inr (Sum.inr (i, j))))) ∪
                        Set.range (fun i : Fin r =>
                          (X (Sum.inr (Sum.inr (Sum.inl ()))) :
                            MvPolynomial (Fin n ⊕ (Fin r ⊕ (Unit ⊕ (Fin r × Fin m)))) A) *
                            X (Sum.inr (Sum.inl i)))))
                    (X (Sum.inr (Sum.inr (Sum.inr (ij.1.val, ij.2)))) :
                      MvPolynomial (Fin n ⊕ (Fin r ⊕ (Unit ⊕ (Fin r × Fin m)))) A)))) a)) ∧
        e.symm (algebraMap _ _ (Ideal.Quotient.mkₐ A
          (Ideal.span
            (Set.range (fun j : Fin m =>
                aeval (fun k : Fin n =>
                  (X (Sum.inl k) :
                    MvPolynomial (Fin n ⊕ (Fin r ⊕ (Unit ⊕ (Fin r × Fin m)))) A)) (f j) -
                  ∑ i : Fin r,
                    (X (Sum.inr (Sum.inl i)) :
                      MvPolynomial (Fin n ⊕ (Fin r ⊕ (Unit ⊕ (Fin r × Fin m)))) A) *
                    X (Sum.inr (Sum.inr (Sum.inr (i, j))))) ∪
              Set.range (fun i : Fin r =>
                (X (Sum.inr (Sum.inr (Sum.inl ()))) :
                  MvPolynomial (Fin n ⊕ (Fin r ⊕ (Unit ⊕ (Fin r × Fin m)))) A) *
                  X (Sum.inr (Sum.inl i)))))
          (X (Sum.inr (Sum.inr (Sum.inl ()))) :
            MvPolynomial (Fin n ⊕ (Fin r ⊕ (Unit ⊕ (Fin r × Fin m)))) A))) = 0 ∧
        ∀ j : Fin m,
          e.symm (algebraMap _ _ (Ideal.Quotient.mkₐ A
              (Ideal.span
                (Set.range (fun j : Fin m =>
                    aeval (fun k : Fin n =>
                      (X (Sum.inl k) :
                        MvPolynomial (Fin n ⊕ (Fin r ⊕ (Unit ⊕ (Fin r × Fin m)))) A)) (f j) -
                      ∑ i : Fin r,
                        (X (Sum.inr (Sum.inl i)) :
                          MvPolynomial (Fin n ⊕ (Fin r ⊕ (Unit ⊕ (Fin r × Fin m)))) A) *
                        X (Sum.inr (Sum.inr (Sum.inr (i, j))))) ∪
                  Set.range (fun i : Fin r =>
                    (X (Sum.inr (Sum.inr (Sum.inl ()))) :
                      MvPolynomial (Fin n ⊕ (Fin r ⊕ (Unit ⊕ (Fin r × Fin m)))) A) *
                      X (Sum.inr (Sum.inl i)))))
              (X (Sum.inr (Sum.inr (Sum.inr (l, j)))) :
                MvPolynomial (Fin n ⊕ (Fin r ⊕ (Unit ⊕ (Fin r × Fin m)))) A))) =
            IsLocalization.Away.invSelf
                (S := Localization.Away (X (Sum.inr (Sum.inl l)) :
                  MvPolynomial (Fin n ⊕ (Fin r ⊕ ({i : Fin r // i ≠ l} × Fin m))) A))
                (X (Sum.inr (Sum.inl l)) :
                  MvPolynomial (Fin n ⊕ (Fin r ⊕ ({i : Fin r // i ≠ l} × Fin m))) A) *
              algebraMap
                (MvPolynomial (Fin n ⊕ (Fin r ⊕ ({i : Fin r // i ≠ l} × Fin m))) A) _
                (aeval (fun k : Fin n => (X (Sum.inl k) :
                    MvPolynomial (Fin n ⊕ (Fin r ⊕ ({i : Fin r // i ≠ l} × Fin m))) A)) (f j) -
                  ∑ i : {i : Fin r // i ≠ l},
                    (X (Sum.inr (Sum.inl i.val)) :
                      MvPolynomial (Fin n ⊕ (Fin r ⊕ ({i : Fin r // i ≠ l} × Fin m))) A) *
                      X (Sum.inr (Sum.inr (i, j))))) := by
  exact ⟨popescu_auxiliaryAlgebra_localizations_part1 A n m r hr f,
    popescu_auxiliaryAlgebra_localizations_part2 A n m r hr f⟩

end Algebra
