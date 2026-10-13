/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F1
-/
module

public import Sheaf.RingTheory.PthRootResidueDifferentials
public import Mathlib.RingTheory.Extension.Cotangent.Basic

/-! # The snake sequence of absolute residue conormal rows

Source: Stacks Project, More on Algebra, Tag 07E5, the big conormal diagram.
-/

@[expose] public section

universe u v

open scoped TensorProduct

namespace Algebra

/-- The absolute residue comparison fits into the conormal snake sequence for any
local homomorphism of local algebras over the positive prime field.

Source: Stacks Project, More on Algebra, Tag 07E5, proof of (2) ⇒ (4), big diagram;
Algebra, Tags 00S1 and 0322 for the conormal rows and prime-field homology vanishing.
(blueprint: lem-weil-pbc-residue-conormal-snake-sequence).

Proof: Write K and L for the residue fields. The Jacobi-Zariski sequence for
F_p -> A -> K, prime-field H1 vanishing, and the identification H1(K/A) = m/m²
produce a short exact conormal row. Tensor it with L over K; field extensions
are flat, and tensor cancellation identifies its middle term with L tensor_A
Omega[A/F_p]. The analogous row for B has middle term L tensor_B Omega[B/F_p].
The local homomorphism induces the conormal map alpha and the field differential
comparison gamma. Naturality of the conormal connecting maps gives the first
commuting square; compatibility of differential maps with residue maps gives the
second. On generators these identities send 1 tensor df to 1 tensor d(f) and
then to d(residue(f)), respectively. Apply the module snake lemma to these two
short exact rows. Jacobi-Zariski for F_p -> K -> L identifies ker gamma with
H1(L/K), because H1(L/F_p) vanishes, and identifies coker gamma with Omega[L/K].
Transport the snake maps through these two linear equivalences. This gives the
five displayed maps, their four exactness assertions, and the endpoint injection
and surjection. No finiteness or regularity is needed for this exact sequence. -/
theorem residue_conormal_snake_sequence
    (p : ℕ) [Fact p.Prime] (A : Type u) (B : Type v)
    [CommRing A] [CommRing B] [Algebra (ZMod p) A] [Algebra A B]
    [Algebra (ZMod p) B] [IsScalarTower (ZMod p) A B]
    [IsLocalRing A] [IsLocalRing B] [IsLocalHom (algebraMap A B)] :
    let K := IsLocalRing.ResidueField A
    let L := IsLocalRing.ResidueField B
    let β := residueDifferentialComparison p A B
    ∃ (α : (L ⊗[K] IsLocalRing.CotangentSpace A) →ₗ[L] IsLocalRing.CotangentSpace B)
      (f₀ : α.ker →ₗ[L] β.ker)
      (f₁ : β.ker →ₗ[L] H1Cotangent K L)
      (f₂ : H1Cotangent K L →ₗ[L] (IsLocalRing.CotangentSpace B ⧸ α.range))
      (f₃ : (IsLocalRing.CotangentSpace B ⧸ α.range) →ₗ[L]
        ((L ⊗[B] KaehlerDifferential (ZMod p) B) ⧸ β.range))
      (f₄ : ((L ⊗[B] KaehlerDifferential (ZMod p) B) ⧸ β.range) →ₗ[L]
        KaehlerDifferential K L),
      Function.Injective f₀ ∧ Function.Exact f₀ f₁ ∧ Function.Exact f₁ f₂ ∧
        Function.Exact f₂ f₃ ∧ Function.Exact f₃ f₄ ∧ Function.Surjective f₄ := by
  sorry

end Algebra
