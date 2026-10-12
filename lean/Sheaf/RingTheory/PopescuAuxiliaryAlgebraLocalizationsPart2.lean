/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F1
-/
module

public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.RingTheory.Localization.Algebra

/-!
# Localizations of the auxiliary algebra in height-zero delocalization

Source: Stacks Project, Smoothing Ring Maps, proof of Lemma 16.9.4, Tag 07FA
(blueprint: lem-weil-pbc-popescu-height-zero-auxiliary-algebra-localizations).

The second conjunct asserts an A-algebra equivalence for every l : Fin r between
the localization away from y_l of Q_l and the localization B_{y_l}. The inverse sends
z to 0 and t_(l,j) to y_l⁻¹ (f_j − Σ_{i ≠ l} y_i t_(i,j)), with the stated formulas.
This is the second localization assertion in Stacks Project Tag 07FA; its proof uses
universal properties of polynomial rings, quotients, and localization and checks generators.

(blueprint: lem-weil-pbc-popescu-height-zero-auxiliary-algebra-localizations-part2).

Proof: construct the maps by the universal properties of multivariate polynomial rings,
ideal quotients, and localization away from one element; verify the displayed generator
formulas and use extensionality on polynomial generators and localization.
-/

@[expose] public section

universe u

open MvPolynomial
open scoped BigOperators

namespace Algebra


/-- This intermediate statement is the corresponding localization conjunct from Stacks
Project Tag 07FA.
The maps are constructed by the universal properties of multivariate polynomial rings, ideal
quotients, and localization away from one element; the displayed generator formulas and
extensionality on generators establish the assertion.
(blueprint: lem-weil-pbc-popescu-height-zero-auxiliary-algebra-localizations-part2). -/
theorem popescu_auxiliaryAlgebra_localizations_part2
    (A : Type u) [CommRing A] (n m r : ℕ) (hr : 1 ≤ r)
    (f : Fin m → MvPolynomial (Fin n) A) :
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
                      X (Sum.inr (Sum.inr (i, j)))))  := by
  sorry

end Algebra
