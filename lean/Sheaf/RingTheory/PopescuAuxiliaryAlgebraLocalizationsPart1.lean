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

The first conjunct asserts an A-algebra map from the auxiliary quotient B to the
localization of the polynomial ring over C, with prescribed images of x, y, z, and t.
It also asserts an algebra equivalence between B_z and that target restricting to the map.
This is the first localization assertion in Stacks Project Tag 07FA; its proof uses
universal properties of polynomial rings, quotients, and localization and checks generators.

(blueprint: lem-weil-pbc-popescu-height-zero-auxiliary-algebra-localizations-part1).

Proof: construct the maps by the universal properties of multivariate polynomial rings,
ideal quotients, and localization away from one element; verify the displayed generator
formulas and use extensionality on polynomial generators and localization.
the maps by universal properties of polynomial rings, quotients, and localization and checks
the generators.
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
(blueprint: lem-weil-pbc-popescu-height-zero-auxiliary-algebra-localizations-part1). -/
theorem popescu_auxiliaryAlgebra_localizations_part1
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
          e (algebraMap _ _ b) = phi b)  := by
  sorry

end Algebra
