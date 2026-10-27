/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q116
-/
module

public import Sheaf.AlgebraicGeometry.ToriMultiplicativeType
public import Sheaf.AlgebraicGeometry.LinearGroupSchemes
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth

/-!
# Torus-free smooth connected affine groups over arbitrary fields

Source: Milne, Algebraic Groups (2017), Proposition 17.81, printed pp.378--379,
and Theorem 14.5, printed pp.281--282
(blueprint: lem-sfb-torus-free-implies-unipotent-arbitrary-field).

A closed embedding into the unitriangular group is expressed as a closed embedding
into GL_n whose matrices, over every test algebra, have diagonal entries one and
entries below the diagonal zero. These equations define the closed subgroup U_n,
so the displayed embedding factors as a closed embedding into U_n.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- A smooth connected affine group of finite type with only trivial base-field torus
subgroups admits a closed unitriangular embedding, over any field.
Source: Milne, Algebraic Groups (2017), Proposition 17.81, pp.378--379, and
Theorem 14.5, pp.281--282
(blueprint: lem-sfb-torus-free-implies-unipotent-arbitrary-field).

Proof:
1. For infinite k, use strong induction on dim H. The infinitesimal-isogeny reduction
`lem-sfb-infinitesimal-isogeny-lie-reduction` gives H -> G' of the same dimension.
Its torus-lifting clause makes G' torus-free. If G' is unipotent, reflect unipotence
along this isogeny by `lem-sfb-infinitesimal-isogeny-unipotence-reflection`.
2. In the nilpotent case, `lem-sfb-nilpotent-central-torus-quotient` gives a central
torus T' with unipotent quotient. Torus-freeness forces T' trivial, and its
trivial-kernel clause identifies G' with the unipotent quotient.
3. Otherwise `lem-sfb-infinite-field-semisimple-centralizer-reduction` gives a smooth
connected closed subgroup K, the identity component of a semisimple centralizer,
of strictly smaller dimension which is not unipotent. Every torus of K is a torus
of G', hence trivial. Induction contradicts nonunipotence of K. In dimension zero
this case would give a group of negative dimension, so the base case is included.
4. For finite k, `lem-sfb-finite-field-geometric-maximal-torus` gives a k-torus T
whose algebraic-closure extension is maximal. T is trivial by hypothesis, so every
torus over the algebraic closure is trivial. Apply `lem-sfb-no-torus-unipotent`
over the algebraic closure to obtain a faithful closed representation with
unipotent matrices on all geometric points.
5. Choose a closed faithful representation over k using
`lem-sfb-affine-group-faithful-linear-representation`. After scalar extension,
`lem-sfb-rational-representation-unipotent-point` transfers unipotence from the
preceding faithful representation to this one. Finally
`lem-sfb-geometric-unipotence-unitriangular-embedding` gives a closed embedding
into U_n over k for some n >= 1. This completes both field cases. -/
theorem exists_unitriangular_embedding_of_torusFree {k : Type u} [Field k]
    (H : Grp (Over (Spec (.of k)))) [IsAffine H.X.left]
    [LocallyOfFiniteType H.X.hom] [QuasiCompact H.X.hom]
    [Smooth H.X.hom] [ConnectedSpace H.X.left]
    (htorus : ∀ (T : Grp (Over (Spec (.of k)))) (i : T ⟶ H),
      IsClosedSubgroupScheme i.hom.hom → MultiplicativeType.IsTorus T →
        Nonempty (T ≅ Grp.trivial (Over (Spec (.of k))))) :
    ∃ n : ℕ, 0 < n ∧
      ∃ r : H.X ⟶ GeneralLinearGroup (ULift.{u} (Fin n)) k,
        IsClosedSubgroupScheme r ∧
        ∀ (R : Type u) [CommRing R] [Algebra k R]
          (x : (Spec (.of R)).asOver (Spec (.of k)) ⟶ H.X),
          (∀ i : Fin n,
            (GeneralLinearGroup.homMulEquiv (ULift.{u} (Fin n)) k R (x ≫ r)).val
              ⟨i⟩ ⟨i⟩ = 1) ∧
          (∀ i j : Fin n, j < i →
            (GeneralLinearGroup.homMulEquiv (ULift.{u} (Fin n)) k R (x ≫ r)).val
              ⟨i⟩ ⟨j⟩ = 0) := by
  sorry

end AlgebraicGeometry
