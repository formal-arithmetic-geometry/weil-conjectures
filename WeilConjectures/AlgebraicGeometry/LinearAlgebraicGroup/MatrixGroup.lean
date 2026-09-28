/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.RingTheory.Nullstellensatz
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.Topology.Constructible
public import Mathlib.Topology.KrullDimension
public import Mathlib.Topology.NoetherianSpace
public import Mathlib.GroupTheory.Index

/-!
# Matrix algebraic groups and the Zariski topology

An *affine variety* over a field `k` is the zero locus of a family of polynomials, and a *matrix
algebraic group* is a Zariski-closed subgroup of the general linear group `GL n k`.  This file
sets up the small amount of point-set affine geometry the monodromy arguments need: the Zariski
topology on affine space `σ → k`, on the space of `n × n` matrices and on `GL n k`, regular maps,
the Zariski closure of a subgroup and the identity component, together with the basic
propositions about them.

The topology is stated on affine space `σ → k` for an arbitrary index type, with the space of
matrices `Matrix n n k` the case `σ = n × n`, because products of affine spaces are affine spaces
and the arguments of this block use products.  Its closed sets are the zero loci
`MvPolynomial.zeroLocus` of ideals, so the Nullstellensatz of
`Mathlib.RingTheory.Nullstellensatz` applies to them; in particular the *vanishing principle* —
a polynomial vanishing at every `k`-point of a closed set lies in the radical of its ideal — is
`MvPolynomial.vanishingIdeal_zeroLocus_eq_radical` and is not restated here.

The topologies are *scoped* instances in the `Zariski` namespace, since these function spaces
carry a product topology whenever `k` does, and the two must not be confused.

## Main declarations

* `MvPolynomial.zariskiTopology`, `Matrix.zariskiTopology`,
  `Matrix.GeneralLinearGroup.zariskiTopology`: the Zariski topology on affine space, on the space
  of matrices and on `GL n k`.
* `Matrix.IsRegularOn`, `Matrix.IsRegularHom`: regular functions and regular homomorphisms.
* `Subgroup.zariskiClosure`, `Subgroup.identityComponent`, `Subgroup.centerOf`: the Zariski
  closure `H̄` of a subgroup, the identity component `G°` and the centre `Z(G)`.
* `MvPolynomial.instNoetherianSpace`,
  `MvPolynomial.exists_isOpen_inter_subset_of_isConstructible`,
  `MvPolynomial.topologicalKrullDim_lt_of_ssubset`: the affine-geometric facts quoted from the
  library.
* `Subgroup.isClosed_identityComponent`, `Subgroup.identityComponent_le`,
  `Subgroup.isIrreducible_identityComponent`, `Subgroup.finiteIndex_identityComponent_subgroupOf`,
  `Subgroup.connectedComponentIn_eq_image_identityComponent`: the structure of `G°`.
* `Matrix.isClosed_range_of_isRegularHom`, `Subgroup.eq_of_topologicalKrullDim_eq`: closedness of
  images of regular homomorphisms and the dimension criterion.

## Blueprint

`MvPolynomial.zariskiTopology`, `Matrix.zariskiTopology`,
`Matrix.GeneralLinearGroup.zariskiTopology`, `Matrix.IsRegularOn`, `Matrix.IsRegularHom`,
`Subgroup.identityComponent` and `Subgroup.centerOf` implement `sk-d-geometry`;
`MvPolynomial.instNoetherianSpace`, `MvPolynomial.exists_isOpen_inter_subset_of_isConstructible`
and `MvPolynomial.topologicalKrullDim_lt_of_ssubset` implement `sk-i-geometry`;
`Matrix.GeneralLinearGroup.continuous_mul_left`,
`Matrix.GeneralLinearGroup.continuous_mul_right`, `Matrix.GeneralLinearGroup.continuous_inv` and
`Subgroup.zariskiClosure` implement part of `sk-i-restriction`; the lemmas about
`Subgroup.identityComponent`, `Matrix.isClosed_range_of_isRegularHom` and
`Subgroup.eq_of_topologicalKrullDim_eq` implement `sk-p-geometry`.
-/

@[expose] public section

open scoped Matrix
open TopologicalSpace Topology

/-- The Zariski topology on affine space `σ → k`: the basic open sets are the nonvanishing loci
of polynomial functions of the coordinates, so the closed sets are the zero loci
`MvPolynomial.zeroLocus` of families of polynomials.
(blueprint: `sk-d-geometry`) -/
@[instance_reducible]
def MvPolynomial.zariskiTopology (σ k : Type*) [CommSemiring k] : TopologicalSpace (σ → k) :=
  .generateFrom {U | ∃ f : MvPolynomial σ k, U = {x | MvPolynomial.eval x f ≠ 0}}

/-- The Zariski topology on the space of `n × n` matrices over `k`, induced from the Zariski
topology of the affine space `(n × n) → k` of which it is a relabelling.
(blueprint: `sk-d-geometry`) -/
@[instance_reducible]
def Matrix.zariskiTopology (n k : Type*) [CommSemiring k] : TopologicalSpace (Matrix n n k) :=
  .induced (fun (M : Matrix n n k) (p : n × n) ↦ M p.1 p.2) (MvPolynomial.zariskiTopology _ k)

/-- The Zariski topology on `GL n k`, the subspace topology from the space of matrices; `GL n k`
is an open affine subvariety of that space.
(blueprint: `sk-d-geometry`) -/
@[instance_reducible]
def Matrix.GeneralLinearGroup.zariskiTopology (n k : Type*) [Fintype n] [DecidableEq n]
    [CommRing k] : TopologicalSpace (GL n k) :=
  .induced Units.val (Matrix.zariskiTopology n k)

-- The `Zariski` scope carries the Zariski topologies of affine space, of the space of matrices
-- and of `GL n k`.
namespace Zariski

attribute [scoped instance] MvPolynomial.zariskiTopology Matrix.zariskiTopology
  Matrix.GeneralLinearGroup.zariskiTopology

end Zariski

open scoped Zariski

namespace Matrix

variable {n m : Type*} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]
variable {k : Type*} [Field k]

/-- The coordinates of an element of `GL n k`: the entries of the matrix together with the entries
of its inverse.  These generate the algebra of regular functions on `GL n k`. -/
def glCoords (g : GL n k) : (n × n) ⊕ (n × n) → k :=
  Sum.elim (fun p ↦ (g : Matrix n n k) p.1 p.2) (fun p ↦ ((g⁻¹ : GL n k) : Matrix n n k) p.1 p.2)

/-- A function on a set of invertible matrices is *regular* if it agrees there with a polynomial
in the entries of the matrix and of its inverse.
(blueprint: `sk-d-geometry`) -/
def IsRegularOn (s : Set (GL n k)) (f : GL n k → k) : Prop :=
  ∃ F : MvPolynomial ((n × n) ⊕ (n × n)) k, ∀ g ∈ s, f g = MvPolynomial.eval (glCoords g) F

/-- A homomorphism of matrix groups is *regular* if every matrix entry of its value is a regular
function of its argument.  A *rational representation* of `G` is a regular homomorphism
`G →* GL m k`.
(blueprint: `sk-d-geometry`) -/
def IsRegularHom {G : Subgroup (GL n k)} (ρ : G →* GL m k) : Prop :=
  ∀ p : m × m, ∃ F : MvPolynomial ((n × n) ⊕ (n × n)) k,
    ∀ g : G, (ρ g : Matrix m m k) p.1 p.2 = MvPolynomial.eval (glCoords (g : GL n k)) F

namespace GeneralLinearGroup

/-- Left translation by a fixed element of `GL n k` is Zariski-continuous: its coordinates are
polynomials in the coordinates of the argument.
(blueprint: `sk-i-restriction`) -/
theorem continuous_mul_left (g : GL n k) : Continuous fun x : GL n k ↦ g * x := by
  sorry

/-- Right translation by a fixed element of `GL n k` is Zariski-continuous.
(blueprint: `sk-i-restriction`) -/
theorem continuous_mul_right (g : GL n k) : Continuous fun x : GL n k ↦ x * g := by
  sorry

/-- Inversion is Zariski-continuous on `GL n k`: it exchanges the two halves of the coordinate
system `Matrix.glCoords`.
(blueprint: `sk-i-restriction`) -/
theorem continuous_inv : Continuous (Inv.inv : GL n k → GL n k) := by
  sorry

end GeneralLinearGroup

end Matrix

namespace Subgroup

open Matrix Matrix.GeneralLinearGroup

variable {n : Type*} [Fintype n] [DecidableEq n] {k : Type*} [Field k]
variable (G : Subgroup (GL n k))

/-- The Zariski closure of a subgroup of `GL n k` is closed under multiplication.
(blueprint: `sk-i-restriction`) -/
theorem mul_mem_closure_coe {x y : GL n k} (hx : x ∈ _root_.closure (G : Set (GL n k)))
    (hy : y ∈ _root_.closure (G : Set (GL n k))) :
    x * y ∈ _root_.closure (G : Set (GL n k)) := by
  have key : ∀ a ∈ G, ∀ z ∈ _root_.closure (G : Set (GL n k)),
      a * z ∈ _root_.closure (G : Set (GL n k)) := by
    intro a ha z hz
    refine _root_.closure_mono ?_
      (image_closure_subset_closure_image (continuous_mul_left a) ⟨z, hz, rfl⟩)
    rintro _ ⟨w, hw, rfl⟩
    exact G.mul_mem ha hw
  have hclosed : IsClosed {z : GL n k | z * y ∈ _root_.closure (G : Set (GL n k))} :=
    isClosed_closure.preimage (continuous_mul_right y)
  exact hclosed.closure_subset_iff.2 (fun a ha ↦ key a ha y hy) hx

/-- The Zariski closure of a subgroup of `GL n k` is closed under inversion.
(blueprint: `sk-i-restriction`) -/
theorem inv_mem_closure_coe {x : GL n k} (hx : x ∈ _root_.closure (G : Set (GL n k))) :
    x⁻¹ ∈ _root_.closure (G : Set (GL n k)) := by
  refine _root_.closure_mono ?_
    (image_closure_subset_closure_image Matrix.GeneralLinearGroup.continuous_inv ⟨x, hx, rfl⟩)
  rintro _ ⟨w, hw, rfl⟩
  exact G.inv_mem hw

/-- The Zariski closure of a subgroup of `GL n k`, again a subgroup.
(blueprint: `sk-i-restriction`) -/
def zariskiClosure : Subgroup (GL n k) where
  carrier := _root_.closure (G : Set (GL n k))
  mul_mem' := G.mul_mem_closure_coe
  one_mem' := _root_.subset_closure G.one_mem
  inv_mem' := G.inv_mem_closure_coe

@[simp]
theorem coe_zariskiClosure :
    (G.zariskiClosure : Set (GL n k)) = _root_.closure (G : Set (GL n k)) :=
  rfl

/-- The identity component of a subgroup of `GL n k` is closed under multiplication.
(blueprint: `sk-p-geometry`) -/
theorem mul_mem_connectedComponentIn_one {x y : GL n k}
    (hx : x ∈ connectedComponentIn (G : Set (GL n k)) 1)
    (hy : y ∈ connectedComponentIn (G : Set (GL n k)) 1) :
    x * y ∈ connectedComponentIn (G : Set (GL n k)) 1 := by
  have hsub := connectedComponentIn_subset (G : Set (GL n k)) 1
  have himage : (fun z ↦ x * z) '' connectedComponentIn (G : Set (GL n k)) 1 ⊆
      connectedComponentIn (G : Set (GL n k)) x := by
    refine (isPreconnected_connectedComponentIn.image _
      (continuous_mul_left x).continuousOn).subset_connectedComponentIn
      ⟨1, mem_connectedComponentIn G.one_mem, mul_one x⟩ ?_
    rintro _ ⟨z, hz, rfl⟩
    exact G.mul_mem (hsub hx) (hsub hz)
  rw [← connectedComponentIn_eq hx] at himage
  exact himage ⟨y, hy, rfl⟩

/-- The identity component of a subgroup of `GL n k` is closed under inversion.
(blueprint: `sk-p-geometry`) -/
theorem inv_mem_connectedComponentIn_one {x : GL n k}
    (hx : x ∈ connectedComponentIn (G : Set (GL n k)) 1) :
    x⁻¹ ∈ connectedComponentIn (G : Set (GL n k)) 1 := by
  have hsub := connectedComponentIn_subset (G : Set (GL n k)) 1
  refine (isPreconnected_connectedComponentIn.image _
    Matrix.GeneralLinearGroup.continuous_inv.continuousOn).subset_connectedComponentIn
    ⟨1, mem_connectedComponentIn G.one_mem, inv_one⟩ ?_ ⟨x, hx, rfl⟩
  rintro _ ⟨z, hz, rfl⟩
  exact G.inv_mem (hsub hz)

/-- The identity component `G°` of a subgroup of `GL n k`: the connected component of `1` in `G`.

The Zariski topology on `GL n k` is not a group topology — multiplication is separately, but not
jointly, continuous — so Mathlib's `Subgroup.connectedComponentOfOne`, which assumes
`IsTopologicalGroup`, does not apply; the two group-closure properties are the lemmas above.
(blueprint: `sk-d-geometry`) -/
def identityComponent : Subgroup (GL n k) where
  carrier := connectedComponentIn (G : Set (GL n k)) 1
  mul_mem' := G.mul_mem_connectedComponentIn_one
  one_mem' := mem_connectedComponentIn G.one_mem
  inv_mem' := G.inv_mem_connectedComponentIn_one

@[simp]
theorem coe_identityComponent :
    (G.identityComponent : Set (GL n k)) = connectedComponentIn (G : Set (GL n k)) 1 :=
  rfl

/-- The identity component of a subgroup is contained in it. -/
theorem identityComponent_le : G.identityComponent ≤ G :=
  fun _ hx ↦ connectedComponentIn_subset (G : Set (GL n k)) 1 hx

/-- The centre of a matrix algebraic group `G ≤ GL n k`, viewed as a subgroup of `GL n k`: the
elements of `G` commuting with every element of `G`.  It is the image in `GL n k` of
`Subgroup.center ↥G`, and differs from `Subgroup.center (GL n k) ⊓ G`, which asks for commutation
with every invertible matrix.
(blueprint: `sk-d-geometry`) -/
def centerOf : Subgroup (GL n k) :=
  G ⊓ Subgroup.centralizer (G : Set (GL n k))

@[simp]
theorem mem_centerOf {x : GL n k} : x ∈ G.centerOf ↔ x ∈ G ∧ ∀ g ∈ G, g * x = x * g := by
  simp [centerOf, Subgroup.mem_centralizer_iff]

end Subgroup

namespace MvPolynomial

variable {σ : Type*} [Finite σ] {k : Type*} [Field k]

/-- In the Zariski topology affine space over a field is a Noetherian space, so every closed set
has finitely many irreducible components.  This is the Hilbert basis theorem, and needs no
hypothesis on the field beyond being a field.
(blueprint: `sk-i-geometry`) -/
instance instNoetherianSpace : NoetherianSpace (σ → k) := by
  sorry

variable [IsAlgClosed k]

/-- A constructible set dense in an irreducible closed set of affine space contains a nonempty
open piece of it.
(blueprint: `sk-i-geometry`) -/
theorem exists_isOpen_inter_subset_of_isConstructible {s t : Set (σ → k)}
    (hs : IsConstructible s) (ht : IsClosed t) (hirr : IsIrreducible t) (hst : closure s = t) :
    ∃ u : Set (σ → k), IsOpen u ∧ (u ∩ t).Nonempty ∧ u ∩ t ⊆ s := by
  sorry

/-- A proper closed subset of an irreducible closed set of affine space has strictly smaller
dimension.
(blueprint: `sk-i-geometry`) -/
theorem topologicalKrullDim_lt_of_ssubset {s t : Set (σ → k)} (hs : IsClosed s)
    (hirr : IsIrreducible s) (ht : IsClosed t) (hts : t ⊂ s) :
    topologicalKrullDim t < topologicalKrullDim s := by
  sorry

end MvPolynomial

namespace Subgroup

variable {n : Type*} [Fintype n] [DecidableEq n] {k : Type*} [Field k] [IsAlgClosed k]
variable (G : Subgroup (GL n k))

/-- The identity component of a matrix algebraic group is closed.
(blueprint: `sk-p-geometry`) -/
theorem isClosed_identityComponent (hG : IsClosed (G : Set (GL n k))) :
    IsClosed (G.identityComponent : Set (GL n k)) := by
  sorry

/-- The identity component of a matrix algebraic group is a normal subgroup of it: conjugation is
a homeomorphism of `G` fixing `1`, so it preserves the connected component of `1`.
(blueprint: `sk-p-geometry`) -/
instance identityComponent_subgroupOf_normal : (G.identityComponent.subgroupOf G).Normal := by
  sorry

/-- The identity component of a matrix algebraic group is irreducible.
(blueprint: `sk-p-geometry`) -/
theorem isIrreducible_identityComponent (hG : IsClosed (G : Set (GL n k))) :
    IsIrreducible (G.identityComponent : Set (GL n k)) := by
  sorry

/-- The identity component of a matrix algebraic group has finite index in it.
(blueprint: `sk-p-geometry`) -/
theorem finiteIndex_identityComponent_subgroupOf (hG : IsClosed (G : Set (GL n k))) :
    (G.identityComponent.subgroupOf G).FiniteIndex := by
  sorry

/-- The connected components of a matrix algebraic group are exactly the cosets of its identity
component; there are finitely many of them by
`Subgroup.finiteIndex_identityComponent_subgroupOf`.
(blueprint: `sk-p-geometry`) -/
theorem connectedComponentIn_eq_image_identityComponent (hG : IsClosed (G : Set (GL n k)))
    {g : GL n k} (hg : g ∈ G) :
    connectedComponentIn (G : Set (GL n k)) g =
      (fun x ↦ g * x) '' (G.identityComponent : Set (GL n k)) := by
  sorry

/-- A closed subgroup of the same dimension as a connected matrix algebraic group is the whole
group.
(blueprint: `sk-p-geometry`) -/
theorem eq_of_topologicalKrullDim_eq {J : Subgroup (GL n k)} (hJG : J ≤ G)
    (hJ : IsClosed (J : Set (GL n k))) (hGirr : IsIrreducible (G : Set (GL n k)))
    (hdim : topologicalKrullDim (J : Set (GL n k)) =
      topologicalKrullDim (G : Set (GL n k))) :
    J = G := by
  sorry

end Subgroup

namespace Matrix

variable {n m : Type*} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]
variable {k : Type*} [Field k] [IsAlgClosed k]

/-- The image of a rational representation of a matrix algebraic group is a closed subgroup.
(blueprint: `sk-p-geometry`) -/
theorem isClosed_range_of_isRegularHom {G : Subgroup (GL n k)}
    (hG : IsClosed (G : Set (GL n k))) (ρ : G →* GL m k) (hρ : IsRegularHom ρ) :
    IsClosed (ρ.range : Set (GL m k)) := by
  sorry

end Matrix
