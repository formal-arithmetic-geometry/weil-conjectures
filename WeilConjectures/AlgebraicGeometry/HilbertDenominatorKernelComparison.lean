/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.MeromorphicDenominatorIdeal
public import Mathlib.RingTheory.Lasker
public import Mathlib.AlgebraicGeometry.Noetherian
public import WeilConjectures.AlgebraicGeometry.Coherent


/-! # Kernel comparison for regular denominator multiplication

Source: Stacks Project, Divisors, Tag 02P2, affine calculation.
-/

@[expose] public section
universe u
open scoped AlgebraicGeometry.Scheme.Modules
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
namespace AlgebraicGeometry.Scheme.Modules

/-- The two maps from I tensor F have the same kernel.
Source: Stacks Project, Divisors, Tag 02P2, proof of the affine assertion
(blueprint: lem-sc-hilbert-denominator-kernel-comparison).

Proof: Trivialize L on an affine neighbourhood and write the regular meromorphic
section as a/b with a and b nonzerodivisors. Coherence makes the section module M
finite; full support and the absence of embedded associated primes imply that
all its associated primes are minimal primes of the ring. Hence a and b act
injectively on M. The denominator-module calculation gives f:IM to M with
b f(z)=a z, and f is injective. Under the affine tensor-section comparison the
first map is multiplication into M and the second is f after this multiplication.
Thus either composite with a kernel inclusion is zero: one by factorization,
the other by injectivity of f. Equalities of sheaf morphisms may be tested on an
affine basis, so these local equalities are the two global identities below.
Neither an Euler identity, coherence of a cokernel, nor a dimension bound is
part of this assertion. The zero tensor module and empty affine charts cause
no exception to the kernel calculation.
-/
theorem hilbert_denominator_kernel_comparison {X : Scheme.{u}} [IsLocallyNoetherian X]
    (F : X.Modules)
    (hFcoh : AlgebraicGeometry.RingedSpace.IsCoherent X.toRingedSpace F)
    (hFsupport : ∀ x : X, ¬ Subsingleton ((presheaf F).stalk x))
    (hFnoEmbedded : ∀ (U : X.Opens) (_ : IsAffineOpen U)
      (p : Ideal (Γ(X, U))),
      p ∈ associatedPrimes (Γ(X, U)) (Γ(F, U)) →
        Minimal (fun q : Ideal (Γ(X, U)) =>
          q ∈ associatedPrimes (Γ(X, U)) (Γ(F, U))) p)
    (L : X.Modules) [L.IsInvertible]
    (s : unit X ⟶ meromorphicModule X L)
    (hs : Mono (meromorphicSectionMap X L s)) :
    kernel.ι ((pullback.fst s (toMeromorphicModule X L)) ▷ F ≫ (λ_ F).hom) ≫
        ((pullback.snd s (toMeromorphicModule X L)) ▷ F ≫ (β_ L F).hom) = 0 ∧
      kernel.ι ((pullback.snd s (toMeromorphicModule X L)) ▷ F ≫ (β_ L F).hom) ≫
        ((pullback.fst s (toMeromorphicModule X L)) ▷ F ≫ (λ_ F).hom) = 0 := by
  sorry

end AlgebraicGeometry.Scheme.Modules
