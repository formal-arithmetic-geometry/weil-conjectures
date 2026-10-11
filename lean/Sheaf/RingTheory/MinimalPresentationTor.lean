/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group M1
-/
module

public import Sheaf.RingTheory.MinimalGradedPresentation
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.CategoryTheory.Monoidal.Tor
public import Mathlib.LinearAlgebra.Quotient.Basic

/-!
# Tor one of a minimal finite graded free presentation

Source: stage-1 minimal-presentation refinement of the graded free resolution argument in
blueprint `lem-sc-p1-graded-resolution`, proof;
Stacks Project, Algebra, Tag 00M0 and Section 00LY
(blueprint: lem-sc-p1-minimal-presentation-tor).
-/

@[expose] public section

universe v

open CategoryTheory

namespace MvPolynomial

/-- Tor one is naturally isomorphic to the kernel modulo the irrelevant ideal for a minimal
finite graded free presentation. The equivalences are oriented from the kernel quotient to
Tor. Naturality is stated on quotient generators for every commuting square of graded
presentations, with `c` its induced kernel map. The zero-module consequence is included explicitly.

Source: stage-1 minimal-presentation refinement of the graded free resolution argument in
blueprint `lem-sc-p1-graded-resolution`, proof;
Stacks Project, Algebra, Tag 00M0 and Section 00LY.

Proof: (1) The presentation gives the short exact sequence `0 → K → F → N → 0`.
Apply `lem-weil-pbc-tor-long-exact-first-variable` with second variable `k`.
(2) Freeness gives `Tor₁(F,k) = 0` by `lem-sc-p1-tor-free-vanishing`.
By `lem-weil-pbc-tensor-over-quotient-ring`, and the tensor symmetry, identify
`M ⊗ k` with `M/S₊M` for `M = K,F,N`. These identifications commute with linear maps.
Minimality says `F ⊗ k → N ⊗ k` is an isomorphism. Exactness therefore makes
`K ⊗ k → F ⊗ k` zero and identifies `Tor₁(N,k)` with `K/S₊K`.
The connecting morphism and quotient identifications are natural in commuting squares.
(3) An isomorphism carries a zero module to a zero module.
(blueprint: lem-sc-p1-minimal-presentation-tor) -/
theorem exists_minimalPresentationTor_equiv (k : Type v) [Field k] :
    let S := MvPolynomial (Fin 2) k
    let I : Ideal S := Ideal.span (Set.range (X : Fin 2 → S))
    let residue : ModuleCat.{v} S :=
      (ModuleCat.restrictScalars (constantCoeff : S →+* k)).obj (ModuleCat.of k k)
    let T := Tor' (ModuleCat.{v} S) 1
    ∃ e : ∀ P : MinimalGradedPresentation k,
        (LinearMap.ker P.q ⧸ (I • (⊤ : Submodule S (LinearMap.ker P.q)))) ≃ₗ[S]
          ((T.obj P.N).obj residue),
      (∀ P : MinimalGradedPresentation k,
        Subsingleton ((T.obj P.N).obj residue) →
          Subsingleton (LinearMap.ker P.q ⧸ (I • (⊤ : Submodule S (LinearMap.ker P.q))))) ∧
      (∀ (P Q : MinimalGradedPresentation k) (a : P.F →ₗ[S] Q.F)
          (b : P.N →ₗ[S] Q.N) (c : LinearMap.ker P.q →ₗ[S] LinearMap.ker Q.q),
        (∀ (j : ℤ) (x : P.F), x ∈ P.fGrading j → a x ∈ Q.fGrading j) →
        (∀ (j : ℤ) (x : P.N), x ∈ P.nGrading j → b x ∈ Q.nGrading j) →
        Q.q.comp a = b.comp P.q →
        (∀ x : LinearMap.ker P.q, (c x : Q.F) = a (x : P.F)) →
        ∀ x : LinearMap.ker P.q,
          ((T.map (ModuleCat.ofHom b)).app residue).hom
              (e P ((I • (⊤ : Submodule S (LinearMap.ker P.q))).mkQ x)) =
            e Q ((I • (⊤ : Submodule S (LinearMap.ker Q.q))).mkQ (c x))) := by
  sorry

end MvPolynomial
