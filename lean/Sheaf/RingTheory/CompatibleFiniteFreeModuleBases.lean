/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group B4
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Free
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.RingTheory.Ideal.Maps

import Sheaf.RingTheory.NilpotentFiniteFreeBasisLift
import Mathlib.LinearAlgebra.FreeModule.Finite.Basic

/-! # Compatible finite coordinates for a module tower

Source: Stacks Project, More on Algebra, Tag 0CQF.
-/

@[expose] public section

set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u v

open CategoryTheory Module

namespace ModuleCat

/-- Choose one finite coordinate size and compatible coordinates throughout the tower.
Source: Stacks Project, Tag 0CQF, compatible-basis induction
(blueprint: lem-weil-pbc-compatible-finite-free-module-bases).

Proof: Choose a finite basis at level zero and reindex it by Fin r. At each successor
apply the single-step nilpotent finite-basis lift to the prescribed coordinates of the
previous level. Dependent recursion retains these choices, and its successor equation
is exactly the desired transition compatibility. No ring limit or complex is involved. -/
theorem exists_compatible_finiteFree_module_coordinates
    (R : ℕ → Type u) [∀ n, CommRing (R n)]
    (φ : ∀ n, R (n + 1) →+* R n)
    (hsurj : ∀ n, Function.Surjective (φ n))
    (hnil : ∀ n, IsNilpotent (RingHom.ker (φ n)))
    (N : ∀ n, ModuleCat.{max u v} (R n))
    (uₙ : ∀ n, N (n + 1) ⟶ (restrictScalars (φ n)).obj (N n))
    (θₙ : ∀ n, (extendScalars (φ n)).obj (N (n + 1)) ≅ N n)
    (hterms : ∀ n, Module.Free (R n) (N n) ∧ Module.Finite (R n) (N n))
    (hsurju : ∀ n, Function.Surjective (uₙ n))
    (hθₙ : ∀ n, (extendRestrictScalarsAdj (φ n)).homEquiv
      (N (n + 1)) (N n) (θₙ n).hom = uₙ n) :
    ∃ (r : ℕ) (e : ∀ n, N n ≃ₗ[R n] (Fin r → R n)),
      ∀ n (x : N (n + 1)) j, e n (uₙ n x) j = φ n (e (n + 1) x j) := by
  classical
  have (n : ℕ) : Module.Free (R n) (N n) := (hterms n).1
  have (n : ℕ) : Module.Finite (R n) (N n) := (hterms n).2
  let I := Module.Free.ChooseBasisIndex (R 0) (N 0)
  let r := Fintype.card I
  let b₀ : Basis (Fin r) (R 0) (N 0) :=
    (Module.Free.chooseBasis (R 0) (N 0)).reindex (Fintype.equivFin I)
  have step (n : ℕ) (e : N n ≃ₗ[R n] (Fin r → R n)) :=
    exists_nilpotent_finiteFree_basis_lift (φ n) (hsurj n) (hnil n)
      (N (n + 1)) (N n) (uₙ n) (θₙ n) (hsurju n) (hθₙ n) r e
  let e : ∀ n, N n ≃ₗ[R n] (Fin r → R n) :=
    Nat.rec b₀.equivFun (fun n e ↦ (step n e).choose)
  exact ⟨r, e, fun n ↦ (step n (e n)).choose_spec⟩

end ModuleCat
