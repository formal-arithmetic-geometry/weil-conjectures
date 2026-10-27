/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q30
-/
module

public import Sheaf.AlgebraicGeometry.SplitSolvableTorsorDefinitions
public import Sheaf.AlgebraicGeometry.UpperTriangularGroupScheme

/-! # A split solvable group embeds into the upper triangular group

Source: Milne, Algebraic Groups (2017), Proposition 16.52, printed p.343,
and Proposition 16.2(a) implies (c), printed pp.324--325.
(blueprint: lem-sfb-split-solvable-triangular-embedding)
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- A smooth connected affine split solvable group of finite type over any field
has a faithful upper triangular representation, as a closed immersion into B_n.
Source: Milne, Proposition 16.52, p.343, and Proposition 16.2, pp.324--325
(blueprint: lem-sfb-split-solvable-triangular-embedding).

Proof plan:
1. Apply lem-sfb-affine-group-faithful-linear-representation to obtain a
   closed immersion rho into GL_n with n positive and injective maps on all
   algebra-valued points.
2. By lem-sfb-complete-linear-flag-scheme, the complete flag scheme is
   proper of finite type, carries the GL_n action, and has the coordinate
   flag as a k-point. Restrict the action along rho. Apply
   lem-sfb-split-solvable-rational-fixed-point to obtain a k-rational flag
   preserved by H on every test algebra.
3. Choose a basis adapted to this flag. Conjugation by its basis matrix
   makes rho upper triangular over every algebra, including nonreduced ones.
4. Evaluate the below-diagonal vanishing on the universal point of H.
   The coordinate map therefore kills the defining ideal of B_n and
   factors through its quotient. The factor is a group homomorphism since
   its composite with the monomorphism B_n into GL_n is one. Its maps on
   all algebra-valued points are injective. B_n is affine of finite type,
   so lem-sfb-geometric-unipotence-faithful-closed-immersion makes the
   factor a closed immersion. The construction includes H = 1 and n = 1. -/
theorem split_solvable_triangular_embedding {k : Type u} [Field k]
    (H : Grp (Over (Spec (.of k))))
    (hsm : Smooth H.X.hom) (hc : ConnectedSpace H.X.left)
    (haff : IsAffine H.X.left) (hft : LocallyOfFiniteType H.X.hom)
    (hqc : QuasiCompact H.X.hom) (hsplit : IsSplitSolvable H) :
    ∃ n : ℕ, 0 < n ∧
      ∃ b : H.X ⟶ UpperTriangularGroup.scheme k n,
        IsMonHom b ∧ IsClosedImmersion b.left := by
  sorry

end AlgebraicGeometry
