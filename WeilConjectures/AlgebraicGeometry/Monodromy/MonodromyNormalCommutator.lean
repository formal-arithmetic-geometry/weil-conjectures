/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.LinearAlgebraicGroup.Monodromy
public import WeilConjectures.AlgebraicGeometry.GroupScheme.GeneralLinear.Representation
public import WeilConjectures.RingTheory.HopfAlgebra.GeneralLinearGroup.Regular

import WeilConjectures.RingTheory.HopfAlgebra.GeneralLinearGroup.Stabilizer
import WeilConjectures.RingTheory.HopfAlgebra.GeneralLinearGroup.ExteriorPower

/-! # Monodromy groups and their commutators

Source: latest blueprint, part-weights-riemann-hypothesis/sec-determinant-weights/
sec-a-central-element-of-positive-degree/sk-lem-walg-normal-commutator/_section.md
(blueprint: sk-lem-walg-normal-commutator).

The reduced closed monodromy subgroup schemes, their inclusion, all-algebra
normality and commutators, and the derived subgroup containment are the existing
`RepresentedDegreeDatum` declarations in `Monodromy`. These statements render
the Complement for arbitrary closed subgroup schemes and
rational actions: density, invariant subspaces and quotients, and finite direct
sums, tensor products, exterior powers and determinants.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe v

open CategoryTheory
open AlgebraicGeometry.GeneralLinearGroup Matrix.GeneralLinearGroup
open scoped Matrix Pointwise commutatorElement MonObj

namespace AlgebraicGeometry.Monodromy

/-- Density preserves invariant subspaces for any rational action of a closed
linear algebraic group, with no relation between the ambient and action dimensions.
The density hypothesis says exactly that the subgroup has all of `G(k)` as its
Zariski closure in the ambient general linear group.
Source: latest blueprint, part-weights-riemann-hypothesis/sec-determinant-weights/
sec-a-central-element-of-positive-degree/sk-lem-walg-normal-commutator/_section.md,
Complement, first sentence (blueprint: sk-lem-walg-normal-commutator).

Proof: the stabilizer equations for the action are regular functions on `G`.
If they vanish on the dense subgroup, they vanish on its closure. The converse
is restriction. This is the closed-stabilizer argument of
`mulVec_mem_of_mem_zeroLocus_vanishingIdeal`, pulled back along the rational action.
-/
theorem rational_action_dense_invariance
    {n m : Type v} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]
    {k : Type v} [Field k] (I : Ideal (CoordinateRing n k)) [I.IsHopfIdeal k]
    (r : RationalHom (subgroupScheme I) m) [IsMonHom r]
    (Γ : Subgroup (zeroLocus I k))
    (hdense : zeroLocus
      (vanishingIdeal ((Γ.map (zeroLocus I k).subtype : Subgroup (GL n k)) : Set (GL n k))) k =
        zeroLocus I k)
    (U : Submodule k (m → k)) :
    (∀ g ∈ Γ, U ≤ U.comap (r.representation (zeroLocusMulEquiv I k g))) ↔
      ∀ g : AlgebraicGeometry.points (subgroupScheme I) k,
        U ≤ U.comap (r.representation g) := by
  sorry

/-- Invariant subspaces and quotients of a rational action carry the induced
rational actions. Invariance means stability after scalar extension under
`G(R)` for every coefficient algebra R, as asserted by `hU_all`. The R-span
of the coordinatewise image of U is exactly the image of `R ⊗[k] U` in `R^n`.
The redundant field-point witness `hU` types the standard induced representations;
it follows from `hU_all` at R = k, since `span k U = U`.
An equivalence of representations identifies the induced action as well as its
underlying vector space.
Source: latest blueprint, part-weights-riemann-hypothesis/sec-determinant-weights/
sec-a-central-element-of-positive-degree/sk-lem-walg-normal-commutator/_section.md,
Complement, second sentence (blueprint: sk-lem-walg-normal-commutator).

Proof: choose a basis adapted to U. Apply `hU_all` at the universal points:
the lower off-diagonal block vanishes as regular functions, not merely on k-points.
The diagonal blocks give the restriction and quotient. Their entries are
regular functions; applying `hU_all` to inverse points gives their inverses. Thus they
define homomorphisms to the respective general linear groups. The inclusion
and quotient map identify their point actions with the standard induced actions.
-/
theorem rational_invariant_subspace_quotient
    {k : Type v} [Field k] {G : Over (Spec (.of k))} [GrpObj G]
    {n : Type v} [Fintype n] [DecidableEq n]
    (r : RationalHom G n) [IsMonHom r] (U : Submodule k (n → k))
    (hU : ∀ g : AlgebraicGeometry.points G k, U ≤ U.comap (r.representation g))
    (hU_all : ∀ (R : Type v) [CommRing R] [Algebra k R]
      (g : AlgebraicGeometry.points G R),
      Submodule.span R ((Pi.algebraMap n k R) '' (U : Set (n → k))) ≤
        (Submodule.span R ((Pi.algebraMap n k R) '' (U : Set (n → k)))).comap
          (Matrix.toLin' (r.points R g : Matrix n n R))) :
    (∃ (a : Type v) (_ : Fintype a) (_ : DecidableEq a)
      (q : RationalHom G a) (_ : IsMonHom q),
      Nonempty ((r.representation.subrepresentation U hU).Equiv q.representation)) ∧
    (∃ (a : Type v) (_ : Fintype a) (_ : DecidableEq a)
      (q : RationalHom G a) (_ : IsMonHom q),
      Nonempty ((r.representation.quotient U hU).Equiv q.representation)) := by
  sorry

/-- Finite direct sums of rational actions are rational, including the empty sum.
Source: latest blueprint, part-weights-riemann-hypothesis/sec-determinant-weights/
sec-a-central-element-of-positive-degree/sk-lem-walg-normal-commutator/_section.md,
Complement, second sentence (blueprint: sk-lem-walg-normal-commutator).

Proof: in the concatenated bases take the block diagonal action. Each block has
regular entries and inverse entries, so the result is a homomorphism of group
schemes. The concatenated-basis equivalence identifies its point action with
`Representation.directSum`.
-/
theorem rational_finite_direct_sum
    {k : Type v} [Field k] {G : Over (Spec (.of k))} [GrpObj G]
    {Jdx : Type v} [Finite Jdx] (n : Jdx → Type v)
    [∀ i, Fintype (n i)] [∀ i, DecidableEq (n i)]
    (r : ∀ i, RationalHom G (n i)) [∀ i, IsMonHom (r i)] :
    ∃ (a : Type v) (_ : Fintype a) (_ : DecidableEq a)
      (q : RationalHom G a) (_ : IsMonHom q),
      Nonempty ((Representation.directSum (fun i ↦ (r i).representation)).Equiv
        q.representation) := by
  sorry

/-- Tensor products, all exterior powers and determinant characters of rational
actions are rational. The determinant equality and tensor/exterior equivalences
specify the actual induced actions.
Source: latest blueprint, part-weights-riemann-hypothesis/sec-determinant-weights/
sec-a-central-element-of-positive-degree/sk-lem-walg-normal-commutator/_section.md,
Complement, second sentence (blueprint: sk-lem-walg-normal-commutator).

Proof: use the Kronecker product for tensor products, the minors for exterior
powers, and the determinant for the determinant line. Each is polynomial in the
entries, and its inverse is obtained by the same operation on inverse matrices;
composition with the input rational homomorphisms is therefore rational.
`exists_algHom_comp_eq_evalAlgHom_exteriorPower` and
`exists_algHom_comp_eq_evalAlgHom_detGL` give the exterior and determinant
coordinate maps. The standard tensor and exterior bases identify the point actions.
-/
theorem rational_tensor_exterior_determinant
    {k : Type v} [Field k] {G : Over (Spec (.of k))} [GrpObj G]
    {n m : Type v} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]
    (r : RationalHom G n) [IsMonHom r] (s : RationalHom G m) [IsMonHom s] :
    (∃ (a : Type v) (_ : Fintype a) (_ : DecidableEq a)
      (q : RationalHom G a) (_ : IsMonHom q),
      Nonempty ((r.representation.tprod s.representation).Equiv q.representation)) ∧
    (∀ j : ℕ, ∃ (a : Type v) (_ : Fintype a) (_ : DecidableEq a)
      (q : RationalHom G a) (_ : IsMonHom q),
      Nonempty ((r.representation.exteriorPower j).Equiv q.representation)) ∧
    (∃ (q : RationalHom G PUnit.{v + 1}) (_ : IsMonHom q),
      ∀ (R : Type v) [CommRing R] [Algebra k R] (g : AlgebraicGeometry.points G R)
        (i j : PUnit.{v + 1}),
        (q.points R g : Matrix PUnit.{v + 1} PUnit.{v + 1} R) i j =
          (r.points R g : Matrix n n R).det) := by
  sorry

end AlgebraicGeometry.Monodromy
