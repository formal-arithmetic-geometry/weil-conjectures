/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q85
-/
module

public import Sheaf.AlgebraicGeometry.SolvableGroupStructure
public import Sheaf.AlgebraicGeometry.LinearGroupSchemes
public import WeilConjectures.AlgebraicGeometry.GroupScheme.Defs
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

import Sheaf.AlgebraicGeometry.GroupScheme.AffineNormalQuotientGeometry
import Sheaf.AlgebraicGeometry.RationalRepresentationComoduleDictionary

/-! # Extensions of arbitrary unipotent affine group schemes

Source: Milne, Algebraic Groups (2017), Corollary 14.7 and Theorem 14.5,
printed pp.281--282, with Proposition 6.45, printed p.135
(blueprint: lem-sfb-unipotent-extension-arbitrary).

A closed group immersion into GL_n satisfying the unitriangular equations on every
commutative algebra is exactly a closed group immersion into its closed subgroup U_n.
This formulation retains nonreduced test algebras and does not require smoothness.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- Extensions of arbitrary unipotent affine group schemes of finite type are unipotent.
The quotient is the recorded fppf quotient with its specified scheme-theoretic kernel.
The two hypotheses and conclusion express closed unitriangular embeddings over k.

Source: Milne, Algebraic Groups (2017), Corollary 14.7 and Theorem 14.5,
printed pp.281--282, with Proposition 6.45, printed p.135
(blueprint: lem-sfb-unipotent-extension-arbitrary).

Proof plan, following all seven steps of the node:
1. Apply lem-sfb-affine-normal-quotient-geometry to N in E. Its quotient represents
   the same fppf sheaf as Q, so the unique representing isomorphism respects the maps
   from E. Consequently the given q is faithfully flat on coordinate rings and has
   scheme-theoretic kernel N, without any smoothness or connectedness assumption.
2. Let V be a nonzero finite-dimensional rational E-representation. Restrict to N
   and choose a basis. The closed unitriangular embedding and
   lem-sfb-unitriangular-subgroup-rational-fixed-vector give a nonzero N-fixed v over
   every algebra. By lem-sfb-rational-representation-comodule-dictionary its restricted
   coaction is v mapped to v tensor 1.
3. Apply lem-sfb-central-kernel-cyclic-representation-descent with H = E, G = Q,
   K = N and v. The smallest E-subcomodule W containing v is nonzero and finite-dimensional.
   N acts trivially on W, and the E-action descends to a rational Q-action whose pullback
   is the original action. The cited statement requires no centrality of N.
4. Choose a basis of W and apply lem-sfb-unitriangular-subgroup-rational-fixed-vector
   to Q and its given embedding. A nonzero Q-fixed w is also E-fixed over every algebra
   by the pullback identity. Its image in V is still nonzero.
5. Induct on dim V to construct a full rational flag with trivial successive quotients.
   In dimension zero use the empty flag. Otherwise take the fixed line kw. The projected
   coaction kills kw and descends to V/kw, with counit and coassociativity inherited from V.
   Apply induction, lift the flag along V to V/kw and prepend the fixed line. These
   constructions commute with scalar extension since vector-space exact sequences split.
   Use lem-sfb-rational-representation-comodule-dictionary for the action/coaction dictionary.
6. Apply lem-sfb-normal-subgroup-representation-kernel to E and its trivial closed normal
   subgroup, defined by the augmentation ideal. Obtain a representation of positive size
   with trivial scheme-theoretic kernel. Equal images of x and y imply that y inverse
   times x is in the kernel, so it is injective on all algebra points. Then
   lem-sfb-geometric-unipotence-faithful-closed-immersion makes it a closed immersion.
7. Choose a basis adapted to its flag from step 5. Flag preservation gives zero entries
   below the diagonal and trivial quotient actions give diagonal entries one over every
   algebra. Evaluate at the universal point to obtain regular-function identities.
   The resulting closed immersion into GL_d factors through U_d. The coordinate-ring
   surjection still surjects after this factorization, so it is closed into U_d as well,
   by def-weil-closed-immersion. This is precisely the conclusion.
-/
theorem unipotent_extension_arbitrary
    {k : Type u} [Field k]
    (N E Q : Grp (Over (Spec (.of k))))
    [IsAffine N.X.left] [LocallyOfFiniteType N.X.hom] [QuasiCompact N.X.hom]
    [IsAffine E.X.left] [LocallyOfFiniteType E.X.hom] [QuasiCompact E.X.hom]
    [IsAffine Q.X.left] [LocallyOfFiniteType Q.X.hom] [QuasiCompact Q.X.hom]
    (i : N ⟶ E) (q : E ⟶ Q)
    [IsClosedSubgroupScheme i.hom.hom] [IsNormalSubgroupScheme i.hom.hom]
    (hq : SolvableGroupStructure.IsFppfQuotient i.hom.hom q)
    (hN : ∃ (n : ℕ), 0 < n ∧
        ∃ r : N.X ⟶ GeneralLinearGroup (ULift.{u} (Fin n)) k,
          IsClosedSubgroupScheme r ∧
          ∀ (R : Type u) [CommRing R] [Algebra k R]
            (x : (Spec (.of R)).asOver (Spec (.of k)) ⟶ N.X),
            (∀ a : Fin n,
              (GeneralLinearGroup.homMulEquiv (ULift.{u} (Fin n)) k R (x ≫ r)).val
                ⟨a⟩ ⟨a⟩ = 1) ∧
            (∀ a b : Fin n, b < a →
              (GeneralLinearGroup.homMulEquiv (ULift.{u} (Fin n)) k R (x ≫ r)).val
                ⟨a⟩ ⟨b⟩ = 0))
    (hQ : ∃ (n : ℕ), 0 < n ∧
        ∃ r : Q.X ⟶ GeneralLinearGroup (ULift.{u} (Fin n)) k,
          IsClosedSubgroupScheme r ∧
          ∀ (R : Type u) [CommRing R] [Algebra k R]
            (x : (Spec (.of R)).asOver (Spec (.of k)) ⟶ Q.X),
            (∀ a : Fin n,
              (GeneralLinearGroup.homMulEquiv (ULift.{u} (Fin n)) k R (x ≫ r)).val
                ⟨a⟩ ⟨a⟩ = 1) ∧
            (∀ a b : Fin n, b < a →
              (GeneralLinearGroup.homMulEquiv (ULift.{u} (Fin n)) k R (x ≫ r)).val
                ⟨a⟩ ⟨b⟩ = 0)) :
    ∃ (n : ℕ), 0 < n ∧
      ∃ r : E.X ⟶ GeneralLinearGroup (ULift.{u} (Fin n)) k,
        IsClosedSubgroupScheme r ∧
        ∀ (R : Type u) [CommRing R] [Algebra k R]
          (x : (Spec (.of R)).asOver (Spec (.of k)) ⟶ E.X),
          (∀ a : Fin n,
            (GeneralLinearGroup.homMulEquiv (ULift.{u} (Fin n)) k R (x ≫ r)).val
              ⟨a⟩ ⟨a⟩ = 1) ∧
          (∀ a b : Fin n, b < a →
            (GeneralLinearGroup.homMulEquiv (ULift.{u} (Fin n)) k R (x ≫ r)).val
              ⟨a⟩ ⟨b⟩ = 0) := by
  sorry

end AlgebraicGeometry
