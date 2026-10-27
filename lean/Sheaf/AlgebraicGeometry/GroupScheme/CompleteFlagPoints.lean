/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q32
-/
module

public import Sheaf.AlgebraicGeometry.LinearGroupSchemes
public import WeilConjectures.AlgebraicGeometry.GroupScheme.Defs
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.LinearAlgebra.Projection
public import Mathlib.RingTheory.Spectrum.Prime.FreeLocus

/-! # Complete flags on algebra-valued points

Source: Milne, Algebraic Groups (2017), Propositions 7.29--7.30, pp.146--147,
and Theorem 17.9, p.354 (blueprint: def-sfb-complete-flag-points).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry.CompleteFlagPoints

/-- A family of submodules, before imposing the flag conditions.
Source: Milne, 7.29 (blueprint: def-sfb-complete-flag-points). -/
abbrev Levels (n : ℕ) (A : Type u) [CommRing A] :=
  Fin (n + 1) → Submodule A (LinearGroupSchemes.Index.{u} n → A)

/-- Complete flags have endpoints zero and the full module, nested terms, and locally
split finite locally free submodules of the prescribed ranks. Over an affine scheme,
a subbundle of a finite free module is a direct summand; its quotient is finite projective.
The stalk ranks allow nonfree projective submodules and disconnected test algebras.
Source: Milne, 7.29--7.30 (blueprint: def-sfb-complete-flag-points). -/
def IsComplete {n : ℕ} {A : Type u} [CommRing A] (L : Levels n A) : Prop :=
  L 0 = ⊥ ∧ L (Fin.last n) = ⊤ ∧ Monotone L ∧
    ∀ i : Fin (n + 1), (∃ Q : Submodule A (LinearGroupSchemes.Index.{u} n → A), IsCompl (L i) Q) ∧
      Module.Finite A (L i) ∧
      ∀ p : PrimeSpectrum A, Module.rankAtStalk (L i) p = i.val

/-- Complete flags of subbundles in the free rank-n module, including the zero ring.
Source: Milne, 7.29--7.30 (blueprint: def-sfb-complete-flag-points). -/
def Points (n : ℕ) (A : Type u) [CommRing A] := {L : Levels n A // IsComplete L}

/-- Scalar extension sends a submodule to the span of its coordinatewise image.
This is the image of the tensor extension inside the base-changed ambient free module.
Source: Milne, 7.29 (blueprint: def-sfb-complete-flag-points). -/
def extend {n : ℕ} {A B : Type u} [CommRing A] [CommRing B]
    (f : A →+* B) (L : Levels n A) : Levels n B :=
  fun i ↦ Submodule.span B
    ((fun v : LinearGroupSchemes.Index.{u} n → A ↦ fun j ↦ f (v j)) '' (L i : Set _))

/-- An invertible matrix preserves each term of a flag. Equality of submodules records
preservation, including infinitesimal points, rather than only rational-point invariance.
Source: Milne, 17.9 (blueprint: def-sfb-complete-flag-points). -/
def Preserves {n : ℕ} {A : Type u} [CommRing A]
    (g : Matrix.GeneralLinearGroup (LinearGroupSchemes.Index.{u} n) A) (L : Levels n A) : Prop :=
  ∀ i : Fin (n + 1), (L i).map (Matrix.toLin' g.val) = L i

/-- The inclusion is precisely the scheme-theoretic flag stabilizer: on every algebra,
its image consists exactly of elements preserving the scalar-extended flag.
Source: Milne, 17.9 (blueprint: def-sfb-complete-flag-points). -/
def IsStabilizer {k : Type u} [Field k] {n : ℕ}
    {G K : Over (Spec (.of k))} (i : K ⟶ G)
    (r : G ⟶ GeneralLinearGroup (LinearGroupSchemes.Index.{u} n) k) (L : Points n k) : Prop :=
  ∀ (A : Type u) [CommRing A] [Algebra k A]
    (g : (Spec (.of A)).asOver (Spec (.of k)) ⟶ G),
    (∃ h : (Spec (.of A)).asOver (Spec (.of k)) ⟶ K, h ≫ i = g) ↔
      Preserves (GeneralLinearGroup.homMulEquiv (LinearGroupSchemes.Index.{u} n) k A (g ≫ r))
        (extend (algebraMap k A) L.val)

end AlgebraicGeometry.CompleteFlagPoints
