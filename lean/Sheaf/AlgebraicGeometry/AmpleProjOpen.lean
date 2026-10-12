/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group C1
-/
module

public import Sheaf.AlgebraicGeometry.Ample
public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Scheme
public import Mathlib.AlgebraicGeometry.OpenImmersion
import Sheaf.AlgebraicGeometry.AmpleFiniteAffineCover
import Sheaf.AlgebraicGeometry.AmpleProjLocalChart

/-!
# An ample invertible module gives an open immersion into Proj

Source: Stacks Project, Properties, Proposition 01Q3, implication (1) => (2),
and Lemma 01Q1 (blueprint: lem-sc-ample-proj-open).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- A scheme with an ample invertible module is an open subscheme of the Proj of a
nonnegatively graded commutative ring.
Source: Stacks Project, Properties, Proposition 01Q3, implication (1) => (2),
and Lemma 01Q1 (blueprint: lem-sc-ample-proj-open).

Proof: form the section ring `S = ⨁ n ≥ 0, Γ(X, L^{⊗ n})`. By
`lem-sc-ample-finite-affine-cover`, finitely many positive-degree homogeneous sections
have affine nonvanishing loci covering `X`. The cover hypothesis of
`lem-sc-ample-proj-local-chart` supplies the canonical morphism `f : X ⟶ Proj(S)`.
For each chosen section `s`, that node identifies the inverse image of `D₊(s)` with
`X_s` and the map `X_s ⟶ D₊(s)` with an isomorphism. The image is consequently the
union of these standard open charts. These local isomorphisms agree on overlaps,
as restrictions of the single morphism `f`; they glue to an isomorphism from `X`
to that open subscheme. Hence `f` is an open immersion. -/
theorem exists_isOpenImmersion_proj_of_isAmple (X : Scheme.{u}) (L : X.Modules)
    [L.IsInvertible] (hL : Scheme.Modules.IsAmple X L) :
    ∃ (S : Type u) (_ : CommRing S) (𝒮 : ℕ → AddSubgroup S) (_ : GradedRing 𝒮)
      (f : X ⟶ Proj 𝒮), IsOpenImmersion f := by
  sorry

end AlgebraicGeometry
