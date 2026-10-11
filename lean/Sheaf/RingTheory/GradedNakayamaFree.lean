/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group M1
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.CategoryTheory.Monoidal.Tor
public import Mathlib.Algebra.DirectSum.Decomposition
public import Mathlib.LinearAlgebra.Quotient.Basic
public import Sheaf.RingTheory.MinimalPresentationTor
public import Mathlib.LinearAlgebra.Basis.Defs
public import Mathlib.RingTheory.MvPolynomial.Homogeneous

/-!
# Graded Nakayama freeness criterion

Source: blueprint `lem-sc-p1-graded-resolution`, proof, graded Nakayama criterion applied to
`K_2` (blueprint: lem-sc-p1-graded-nakayama-free).
-/

@[expose] public section

universe u

open CategoryTheory

namespace MvPolynomial

/-- A finitely generated graded module over `k[x₀,x₁]` whose first Tor with the residue
field vanishes has a finite homogeneous basis.

Source: blueprint `lem-sc-p1-graded-resolution`, proof, graded Nakayama criterion applied to
`K_2`.

Proof: choose homogeneous lifts of a basis modulo the irrelevant ideal and form the minimal
finite graded free presentation. The minimal-presentation Tor calculation identifies the first
Tor with the kernel modulo the irrelevant ideal. Its vanishing and finite graded generation of
the kernel imply that the kernel is zero by graded Nakayama, so the presentation is an
isomorphism. The source basis then gives the asserted finite homogeneous basis.
(blueprint: lem-sc-p1-graded-nakayama-free) -/
theorem graded_nakayama_free (k : Type u) [Field k]
    (N : Type u) [AddCommGroup N] [Module (MvPolynomial (Fin 2) k) N]
    (ℳ : ℤ → AddSubgroup N) (hℳ : DirectSum.IsInternal ℳ)
    (hsmul : ∀ (n : ℕ) (j : ℤ) (f : MvPolynomial (Fin 2) k) (x : N),
      f ∈ homogeneousSubmodule (Fin 2) k n → x ∈ ℳ j →
        f • x ∈ ℳ ((n : ℤ) + j))
    (hN : ∃ s : Set N, s.Finite ∧
      (∀ x ∈ s, SetLike.IsHomogeneousElem ℳ x) ∧
      Submodule.span (MvPolynomial (Fin 2) k) s = ⊤)
    (hTor : Subsingleton (((Tor' (ModuleCat.{u} (MvPolynomial (Fin 2) k)) 1).obj
      (ModuleCat.of (MvPolynomial (Fin 2) k) N)).obj
      ((ModuleCat.restrictScalars
        (MvPolynomial.constantCoeff : MvPolynomial (Fin 2) k →+* k)).obj
        (ModuleCat.of k k)))) :
    ∃ (r : ℕ) (b : Module.Basis (Fin r) (MvPolynomial (Fin 2) k) N)
      (d : Fin r → ℤ), ∀ i : Fin r, b i ∈ ℳ (d i) := by
  sorry

end MvPolynomial
