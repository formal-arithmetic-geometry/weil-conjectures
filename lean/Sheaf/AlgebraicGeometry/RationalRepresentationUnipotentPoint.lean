module

public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.CategoryTheory.Monoidal.Grp
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Sheaf.AlgebraicGeometry.LinearGroupSchemes

/-!
# Rational representations preserve unipotence of a point

Source: Milne, Algebraic Groups (2017), 9.19, printed p.171, and Theorem 9.18,
printed p.170 (blueprint: lem-sfb-rational-representation-unipotent-point).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- A point unipotent in one faithful rational representation is unipotent in every
rational representation. Faithfulness is injectivity on all algebra-valued points;
the group scheme need not be smooth, connected, or itself unipotent.

Source: Milne, Algebraic Groups (2017), 9.19, printed p.171, and Theorem 9.18,
printed p.170 (blueprint: lem-sfb-rational-representation-unipotent-point).

Proof plan:
1. For every finite-dimensional rational representation V, take the unipotent part of
   its action at g. The intertwiner and tensor clauses of
   lem-sfb-multiplicative-jordan-linear-compatibility make these parts natural and
   compatible with tensor products. Uniqueness applied to I = I * I gives the unit
   condition, also allowing the zero representation.
2. Apply lem-sfb-tannaka-rational-point-reconstruction to this family to obtain a point h
   whose action in every representation is the unipotent part of the action of g.
3. The hypothesis says i(g) is already unipotent. Uniqueness of the linear Jordan
   decomposition gives i(h) = i(g). Faithfulness at R = K then implies h = g.
4. Thus r(g) equals its unipotent part, whose difference from the identity has a
   positive power equal to zero. This supplies the required exponent M.
-/
theorem rationalRepresentation_unipotent_point {K : Type u} [Field K] [IsAlgClosed K]
    (G : Over (Spec (.of K))) [GrpObj G] [IsAffine G.left]
    [LocallyOfFiniteType G.hom] [QuasiCompact G.hom]
    (m d : ℕ) (hm : 0 < m) (hd : 0 < d)
    (i : G ⟶ GeneralLinearGroup (LinearGroupSchemes.Index.{u} m) K) [IsMonHom i]
    (r : G ⟶ GeneralLinearGroup (LinearGroupSchemes.Index.{u} d) K) [IsMonHom r]
    (hi : ∀ (R : Type u) [CommRing R] [Algebra K R],
      Function.Injective (fun x : (Spec (.of R)).asOver (Spec (.of K)) ⟶ G ↦ x ≫ i))
    (g : (Spec (.of K)).asOver (Spec (.of K)) ⟶ G)
    (hg : ∃ N : ℕ, 0 < N ∧
      ((GeneralLinearGroup.homMulEquiv (LinearGroupSchemes.Index.{u} m) K K
        (g ≫ i)).val - 1) ^ N = 0) :
    ∃ M : ℕ, 0 < M ∧
      ((GeneralLinearGroup.homMulEquiv (LinearGroupSchemes.Index.{u} d) K K
        (g ≫ r)).val - 1) ^ M = 0 := by
  sorry

end AlgebraicGeometry
