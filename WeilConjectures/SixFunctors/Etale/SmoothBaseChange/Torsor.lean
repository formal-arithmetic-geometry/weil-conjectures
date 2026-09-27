/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import Mathlib
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Sheaf

/-!
# Torsors and étale `H^1`

Let `Y` be a scheme and `M` a finite abelian group. An `M`-torsor on the small étale site of
`Y` is the same thing as a finite étale surjective `Y`-scheme `P` carrying a simply
transitive action of `M` over `Y`; that is the form in which the notion is recorded here, as
`AlgebraicGeometry.Scheme.EtaleTorsor`. Simple transitivity is the statement that the
canonical morphism `∐_{m ∈ M} P ⟶ P ×_Y P` sending the `m`-th summand by `(m • -, id)` is an
isomorphism, which is available because `M` is finite, hence `Small.{u}`.

The proposition of the blueprint subsection `sk-prop-input-torsors` is that the isomorphism
classes of `M`-torsors on `Y` are in canonical bijection with `H^1(Y_ét, M)`, the first
sheaf cohomology of the constant sheaf with value `M`. Rather than forming the quotient of
`EtaleTorsor M Y` by the isomorphism relation, the statement below asserts the existence of
a surjection `EtaleTorsor M Y → H^1(Y_ét, M)` whose fibres are exactly the isomorphism
classes; this carries the same content and avoids a setoid.

Two refinements of Stacks `02NE` recorded in the sketch are left to the prose: the
naturality of the bijection in the pair `(Y, M)`, and the criterion, for `Y` connected and
`M = ℤ/dℤ`, that the torsor attached to a class be connected — a Galois cover with group
`ℤ/dℤ`, which is the input of `sk-prop-input-spreading` — exactly when the corresponding
homomorphism out of the étale fundamental group is surjective.

## Main definitions

- `AlgebraicGeometry.Scheme.EtaleTorsor`: an `M`-torsor over a scheme `Y`.
- `AlgebraicGeometry.Scheme.EtaleTorsor.IsIsomorphic`: the isomorphism relation on torsors.

## Main statements

- `AlgebraicGeometry.Scheme.EtaleTorsor.exists_surjective_sheafH`: the bijection between
  isomorphism classes of `M`-torsors on `Y` and `H^1(Y_ét, M)`.

## References

- Stacks Project, Tag `02NE`, <https://stacks.math.columbia.edu/tag/02NE>
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

variable (M : Type (u + 1)) [AddCommGroup M] [Finite M]

/-- An `M`-torsor over a scheme `Y`: a finite étale surjective `Y`-scheme with a simply
transitive action of the finite abelian group `M`.

Simple transitivity is expressed by the isomorphism `M × P ≅ P ×_Y P`, in the form that the
morphism `∐_{m ∈ M} P ⟶ P ×_Y P` whose `m`-th component is `(m • -, id)` is an isomorphism.
The coproduct exists because `M` is finite, hence small. -/
structure Scheme.EtaleTorsor (Y : Scheme.{u}) where
  /-- the total space of the torsor -/
  P : Scheme.{u}
  /-- the structure morphism to the base -/
  π : P ⟶ Y
  [isFinite : IsFinite π]
  [etale : Etale π]
  /-- the action of `M` on `P` over `Y` -/
  smul : M → (P ⟶ P)
  /-- the action is by morphisms over `Y` -/
  smul_π (m : M) : smul m ≫ π = π
  /-- the zero of `M` acts as the identity -/
  smul_zero : smul 0 = 𝟙 P
  /-- the action is additive -/
  smul_add (m n : M) : smul (m + n) = smul m ≫ smul n
  /-- the action is simply transitive: `∐_{m ∈ M} P ≅ P ×_Y P` -/
  isIso_sigmaDesc : IsIso (Sigma.desc
    fun m : M ↦ pullback.lift (f := π) (g := π) (smul m) (𝟙 P) (by simp [smul_π]))
  /-- the structure morphism is surjective -/
  surjective : Function.Surjective π.base

namespace Scheme.EtaleTorsor

variable {M} {Y : Scheme.{u}}

/-- Two `M`-torsors over `Y` are isomorphic when their total spaces are isomorphic over `Y`
by an isomorphism commuting with the `M`-actions. -/
def IsIsomorphic (t₁ t₂ : EtaleTorsor M Y) : Prop :=
  ∃ φ : t₁.P ≅ t₂.P, φ.hom ≫ t₂.π = t₁.π ∧
    ∀ m : M, t₁.smul m ≫ φ.hom = φ.hom ≫ t₂.smul m

variable (M Y) in
/-- Blueprint `sk-prop-input-torsors`: Torsors and étale H^1

For a scheme `Y` and a finite abelian group `M` there is a canonical bijection between the
isomorphism classes of `M`-torsors on the small étale site of `Y` and the first sheaf
cohomology group `H^1(Y_ét, M)` of the constant sheaf with value `M`. It is rendered here
as a surjection `EtaleTorsor M Y → H^1(Y_ét, M)` two torsors having the same image exactly
when they are isomorphic, which is the bijection without the quotient.

An `M`-torsor is, by `AlgebraicGeometry.Scheme.EtaleTorsor`, the same thing as a finite
étale surjective `Y`-scheme with a simply transitive `M`-action; the naturality of the
bijection in `(Y, M)` and the connectedness criterion of the sketch are not part of this
statement. This is [Stacks 02NE]. -/
@[stacks 02NE]
theorem exists_surjective_sheafH :
    ∃ c : EtaleTorsor M Y → Sheaf.H
      ((constantSheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
        (AddCommGrpCat.of M)) 1,
      Function.Surjective c ∧ ∀ t₁ t₂ : EtaleTorsor M Y, c t₁ = c t₂ ↔ t₁.IsIsomorphic t₂ :=
  sorry

end Scheme.EtaleTorsor

end AlgebraicGeometry
