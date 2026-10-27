/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q151
-/
module

public import WeilConjectures.AlgebraicGeometry.GroupScheme.GeneralLinear.Lie
public import WeilConjectures.AlgebraicGeometry.GroupScheme.Defs
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-! # Geometric semisimplicity of a group-scheme tangent element

Source: Milne, Algebraic Groups (2017), Proposition 17.74 and Example 17.75, p.377;
faithful detection in the statement of lem-sfb-algebraic-lie-additive-jordan
(blueprint: def-sfb-semisimple-lie-element).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry.GrpObj

/-- The differential of some faithful closed linear representation is diagonalizable over K.
When K is an algebraic closure this is geometric semisimplicity of the tangent element.
The same formula also makes sense over an arbitrary extension field K.
Source: Milne, Algebraic Groups (2017), 17.74--17.75, p.377, with faithful detection as in
lem-sfb-algebraic-lie-additive-jordan (blueprint: def-sfb-semisimple-lie-element). -/
def HasDiagonalizableFaithfulLieImage {k : Type u} [Field k]
    (K : Type u) [Field K] [Algebra k K]
    (G : Grp (Over (Spec (.of k)))) (X : Lie G.X) : Prop :=
  ∃ n : ℕ, 0 < n ∧
    ∃ r : G ⟶ Grp.mk (GeneralLinearGroup (ULift.{u} (Fin n)) k),
      IsClosedSubgroupScheme r.hom.hom ∧
      ∃ (P : Matrix.GeneralLinearGroup (ULift.{u} (Fin n)) K)
        (d : ULift.{u} (Fin n) → K),
        (P⁻¹).val *
            (GeneralLinearGroup.RationalHom.differential r.hom.hom X).map (algebraMap k K) *
            P.val = Matrix.diagonal d

end AlgebraicGeometry.GrpObj
