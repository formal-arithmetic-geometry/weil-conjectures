/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N1
-/
module

public import Sheaf.ConstructibleSheaf.TorsorAssociatedModule

/-!
# Surjectivity of diagonal evaluation of torsor sections

Source: Stacks Project, Tags 0DV5 (3), 0DV6, 0A3R, 04TR and 04TS.
(blueprint: lem-weil-pbc-torsor-equivariant-module-diagonal-evaluation)
-/

@[expose] public section

set_option autoImplicit false
universe u
open CategoryTheory Limits Opposite
namespace AlgebraicGeometry.Scheme.GaloisCover

/-- Every module value occurs as the value of an equivariant section at a
specified point on the diagonal of the torsor's double overlap.
Source: Stacks Project, etale-cohomology.tex Tag 0DV5 (3), Tags 0DV6 and 0A3R.
(blueprint: lem-weil-pbc-torsor-equivariant-module-diagonal-evaluation)

Proof: Compose the torsor isomorphism with interchange of the two factors.
This identifies c.P times_V c.P with the disjoint union, indexed by the group,
of copies of c.P, whose g-th component is (identity, g times identity). Given a
value n, prescribe on this component the constant value rho(g)n. These
functions are locally constant on the disjoint union; transport them across the
isomorphism to the double overlap. The second factor action by h carries
component g to component hg. The representation identity rho(hg)n =
rho(h)(rho(g)n) proves equivariance. On the identity component, which is the
diagonal, the value is rho(1)n = n. Thus the section has the requested value at
the diagonal point. No connectedness or nonzero module hypothesis is needed,
and the construction works for the trivial group. -/
theorem equivariantSections_diagonalEvaluation_surjective
    {V : Scheme.{u}} (ℓ : ℕ) {P : Type u} [Group P] [Finite P]
    (c : Scheme.GaloisCover (ULift.{u + 1} P) V)
    (N : Rep.{u + 1} (ZMod ℓ) P) (x : c.P) :
    letI := c.etale
    Function.Surjective (fun s : c.equivariantSections ℓ N (Etale.mk c.π) ↦
      s.val ((pullback.lift (f := c.π) (g := c.π) (𝟙 c.P) (𝟙 c.P) rfl) x)) := by sorry

end AlgebraicGeometry.Scheme.GaloisCover
