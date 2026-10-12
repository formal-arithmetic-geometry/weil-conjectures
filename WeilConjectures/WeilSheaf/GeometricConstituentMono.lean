/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.WeilSheaf.GeometricConstituent

/-!
# Geometric constituents of an irreducible Weil sheaf are subsheaves

Let `X̄` be irreducible and `F` an irreducible lisse Weil sheaf on `X`. Every irreducible lisse
subquotient `A` of the underlying sheaf `F̄` on `X̄` is isomorphic to a lisse subsheaf of `F̄`:
`F̄` is a quotient of a finite sum `S_0 ⊕ ⋯ ⊕ S_N` of Frobenius translates of an irreducible
subsheaf `S_0 ⊆ F̄`, each of which is a subsheaf of `F̄`, and a nonzero morphism from some `S_k`
to `A` is an isomorphism by irreducibility. This is the semisimplicity half of the
sheaf-theoretic Clifford theorem, as in
`AlgebraicGeometry.WeilSheaf.IsIrreducibleLisse.exists_iso_biproduct_unit`.
-/

@[expose] public section

universe u

open CategoryTheory Limits

attribute [local instance] Abelian.hasFiniteBiproducts

namespace AlgebraicGeometry.WeilSheaf

open ProEtale

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime]
  {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))] [Fact (ringChar k₀ ≠ l)]
  [IrreducibleSpace (X ↘ Spec (CommRingCat.of k₀)).geometricFiber]

/-- **Geometric constituents are subsheaves** (semisimplicity half of the sheaf-theoretic
Clifford theorem). Let `X̄` be irreducible and `F` an irreducible lisse Weil sheaf on `X`. If a
lisse subsheaf `B` of the underlying sheaf `F̄` surjects onto an irreducible lisse sheaf `A`,
then `A` embeds into `F̄`. -/
theorem IsIrreducibleLisse.exists_mono_of_isIrreducibleAdicLocalSystem {F : WeilSheaf k₀ l X}
    (hF : F.IsIrreducibleLisse)
    {A B : AdicSheaf l (X ↘ Spec (CommRingCat.of k₀)).geometricFiber}
    (hA : IsIrreducibleAdicLocalSystem A) (hB : IsAdicLisseSheaf B)
    (i : B ⟶ F.obj.carrier) [Mono i] (p : B ⟶ A) [Epi p] :
    ∃ m : A ⟶ F.obj.carrier, Mono m := by
  sorry

end AlgebraicGeometry.WeilSheaf
