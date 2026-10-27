/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q91
-/
module

public import Sheaf.AlgebraicGeometry.LinearGroupSchemes
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType

/-! # Faithful detection of semisimple points

Source: Milne, Algebraic Groups (2017), Theorem 9.18, printed p.170,
and Section 9.19, printed p.171
(blueprint: lem-sfb-rational-representation-semisimple-point).

The representations are morphisms of group schemes, and faithfulness is tested
on every commutative k-algebra. Diagonalizability means conjugacy to a diagonal matrix.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- A point diagonalizable in one faithful rational representation is diagonalizable
in every rational representation. The field may have any characteristic, and the affine
finite-type group scheme need not be smooth or connected.
Source: Milne, Algebraic Groups (2017), Theorem 9.18, p.170 and Section 9.19, p.171
(blueprint: lem-sfb-rational-representation-semisimple-point).

Proof plan:
1. For every finite-dimensional rational representation V, take the semisimple part
   of its action on g, using lem-sfb-multiplicative-jordan-linear-compatibility.
   Equivariant maps intertwine the original actions, so they intertwine the semisimple
   parts. The tensor clause makes this family tensor-compatible. On the trivial
   representation, uniqueness applied to I = I * I makes the semisimple part I.
   The zero representation is allowed throughout.
2. Apply lem-sfb-tannaka-rational-point-reconstruction to this invertible, natural,
   tensor-compatible family to obtain h in J(k). In particular, i(h) and r(h) are
   the semisimple parts of i(g) and r(g), respectively.
3. The diagonalizable matrix i(g) has decomposition i(g) = i(g) * I. Its unipotent
   factor satisfies (I - I)^1 = 0, so uniqueness gives i(h) = i(g). Faithfulness
   evaluated at the algebra k implies h = g.
4. Substitute h = g into r(h) = r(g)_s. The semisimple part is diagonalizable,
   which gives the required conjugating matrix for r(g). -/
theorem rationalRepresentation_diagonalizable_of_faithful
    {k : Type u} [Field k] [IsAlgClosed k]
    (J : Over (Spec (.of k))) [GrpObj J] [IsAffine J.left]
    [LocallyOfFiniteType J.hom] [QuasiCompact J.hom]
    (m d : ℕ) (_hm : 1 ≤ m) (_hd : 1 ≤ d)
    (i : J ⟶ GeneralLinearGroup (LinearGroupSchemes.Index.{u} m) k) [IsMonHom i]
    (r : J ⟶ GeneralLinearGroup (LinearGroupSchemes.Index.{u} d) k) [IsMonHom r]
    (hi : ∀ (A : Type u) [CommRing A] [Algebra k A],
      Function.Injective (fun x : (Spec (.of A)).asOver (Spec (.of k)) ⟶ J ↦
        GeneralLinearGroup.homMulEquiv (LinearGroupSchemes.Index.{u} m) k A (x ≫ i)))
    (g : (Spec (.of k)).asOver (Spec (.of k)) ⟶ J)
    (hg : ∃ (P : GL (LinearGroupSchemes.Index.{u} m) k)
      (a : LinearGroupSchemes.Index.{u} m → k),
      (↑P⁻¹ : Matrix _ _ k) *
        (GeneralLinearGroup.homMulEquiv (LinearGroupSchemes.Index.{u} m) k k (g ≫ i) :
          Matrix _ _ k) * (↑P : Matrix _ _ k) = Matrix.diagonal a) :
    ∃ (P : GL (LinearGroupSchemes.Index.{u} d) k)
      (a : LinearGroupSchemes.Index.{u} d → k),
      (↑P⁻¹ : Matrix _ _ k) *
        (GeneralLinearGroup.homMulEquiv (LinearGroupSchemes.Index.{u} d) k k (g ≫ r) :
          Matrix _ _ k) * (↑P : Matrix _ _ k) = Matrix.diagonal a := by
  sorry

end AlgebraicGeometry
