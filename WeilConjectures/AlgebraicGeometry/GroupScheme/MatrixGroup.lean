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
topology on the space of `n × n` matrices and on `GL n k`, regular maps, the Zariski closure of a
subgroup and the identity component, together with the two basic propositions about them.

The topologies are *scoped* instances in the `Matrix.Zariski` namespace, since the space of
matrices carries a product topology whenever `k` does, and the two must not be confused.

## Main declarations

* `Matrix.zariskiTopology`, `Matrix.GeneralLinearGroup.zariskiTopology`: the Zariski topology on
  the space of matrices and the induced topology on `GL n k`.
* `Matrix.IsRegularOn`, `Matrix.IsRegularHom`: regular functions and regular homomorphisms.
* `Subgroup.zariskiClosure`, `Subgroup.identityComponent`, `Subgroup.centerOf`: the Zariski
  closure `H̄` of a subgroup, the identity component `G°` and the centre `Z(G)`.
* `Matrix.zariski_noetherian_constructible_dim`: the affine-geometric facts quoted from the
  library.
* `Matrix.identityComponent_spec_and_isClosed_range_and_eq_of_krullDim_eq`: the structure of `G°`,
  closedness of images of regular homomorphisms, and the dimension criterion.
-/

@[expose] public section

open scoped Matrix
open TopologicalSpace Topology

namespace Matrix

variable {n m : Type*} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]
variable {k : Type*} [Field k]

/-- Blueprint `sk-d-geometry`: Affine geometry and matrix groups.  The Zariski topology on the
space of `n × n` matrices over `k`: the basic open sets are the nonvanishing loci of polynomial
functions of the matrix entries, so the closed sets are the zero loci of families of polynomials. -/
@[instance_reducible]
def zariskiTopology (n k : Type*) [Field k] : TopologicalSpace (Matrix n n k) :=
  .generateFrom {U | ∃ f : MvPolynomial (n × n) k,
    U = {M | MvPolynomial.eval (fun p ↦ M p.1 p.2) f ≠ 0}}

/-- Blueprint `sk-d-geometry`: Affine geometry and matrix groups.  The Zariski topology on
`GL n k`, the subspace topology from the space of matrices; `GL n k` is an open affine subvariety
of that space. -/
@[instance_reducible]
def GeneralLinearGroup.zariskiTopology (n k : Type*) [Fintype n] [DecidableEq n] [Field k] :
    TopologicalSpace (GL n k) :=
  .induced Units.val (Matrix.zariskiTopology n k)

namespace Zariski

attribute [scoped instance] Matrix.zariskiTopology Matrix.GeneralLinearGroup.zariskiTopology

end Zariski

open scoped Zariski

/-- The coordinates of an element of `GL n k`: the entries of the matrix together with the entries
of its inverse.  These generate the algebra of regular functions on `GL n k`. -/
def glCoords (g : GL n k) : (n × n) ⊕ (n × n) → k :=
  Sum.elim (fun p ↦ (g : Matrix n n k) p.1 p.2) (fun p ↦ ((g⁻¹ : GL n k) : Matrix n n k) p.1 p.2)

/-- Blueprint `sk-d-geometry`: Affine geometry and matrix groups.  A function on a set of
invertible matrices is *regular* if it agrees there with a polynomial in the entries of the matrix
and of its inverse. -/
def IsRegularOn (s : Set (GL n k)) (f : GL n k → k) : Prop :=
  ∃ F : MvPolynomial ((n × n) ⊕ (n × n)) k, ∀ g ∈ s, f g = MvPolynomial.eval (glCoords g) F

/-- Blueprint `sk-d-geometry`: Affine geometry and matrix groups.  A homomorphism of matrix groups
is *regular* if every matrix entry of its value is a regular function of its argument.  A
*rational representation* of `G` is a regular homomorphism `G →* GL m k`. -/
def IsRegularHom {G : Subgroup (GL n k)} (ρ : G →* GL m k) : Prop :=
  ∀ p : m × m, ∃ F : MvPolynomial ((n × n) ⊕ (n × n)) k,
    ∀ g : G, (ρ g : Matrix m m k) p.1 p.2 = MvPolynomial.eval (glCoords (g : GL n k)) F

end Matrix

open scoped Matrix.Zariski

namespace Subgroup

variable {n : Type*} [Fintype n] [DecidableEq n] {k : Type*} [Field k]

/-- Blueprint `sk-i-restriction`: Normal restriction and passage to closure.  The Zariski closure
of a subgroup of `GL n k` is again a subgroup; that the closure is closed under multiplication and
inversion is part of the proposition of that subsection. -/
def zariskiClosure (G : Subgroup (GL n k)) : Subgroup (GL n k) where
  carrier := closure (G : Set (GL n k))
  mul_mem' := by sorry
  one_mem' := subset_closure G.one_mem
  inv_mem' := by sorry

/-- Blueprint `sk-d-geometry`: Affine geometry and matrix groups.  The identity component `G°` of
a subgroup of `GL n k`: the connected component of `1` in `G`.  That it is a subgroup is part of
the proposition `sk-p-geometry`. -/
def identityComponent (G : Subgroup (GL n k)) : Subgroup (GL n k) where
  carrier := Subtype.val '' connectedComponent (1 : G)
  mul_mem' := by sorry
  one_mem' := ⟨1, mem_connectedComponent, rfl⟩
  inv_mem' := by sorry

/-- Blueprint `sk-d-geometry`: Affine geometry and matrix groups.  The centre of a matrix
algebraic group `G ≤ GL n k`, viewed as a subgroup of `GL n k`: the elements of `G` commuting with
every element of `G`. -/
abbrev centerOf (G : Subgroup (GL n k)) : Subgroup (GL n k) :=
  G ⊓ Subgroup.centralizer (G : Set (GL n k))

end Subgroup

namespace Matrix

open scoped Matrix.Zariski

variable {n m : Type*} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]
variable {k : Type*} [Field k] [IsAlgClosed k]

/-- Blueprint `sk-i-geometry`: Basic affine geometry.  In the Zariski topology the space of
matrices over an algebraically closed field is a Noetherian space, so every closed set has
finitely many irreducible components; a constructible set dense in an irreducible closed set
contains a nonempty open piece of it; and a proper closed subset of an irreducible closed set has
strictly smaller dimension. -/
theorem zariski_noetherian_constructible_dim (n : Type*) :
    NoetherianSpace (Matrix n n k) ∧
      (∀ s t : Set (Matrix n n k), IsConstructible s → IsClosed t → IsIrreducible t →
        closure s = t → ∃ u : Set (Matrix n n k), IsOpen u ∧ (u ∩ t).Nonempty ∧ u ∩ t ⊆ s) ∧
      (∀ s t : Set (Matrix n n k), IsClosed s → IsIrreducible s → IsClosed t → t ⊂ s →
        topologicalKrullDim t < topologicalKrullDim s) := by
  sorry

/-- Blueprint `sk-p-geometry`: Algebraic-group geometry.  For a matrix algebraic group `G`: the
identity component `G°` is a closed normal irreducible subgroup of finite index, so its cosets are
the finitely many connected components of `G`; the image of a regular homomorphism is a closed
subgroup; and a closed subgroup of a connected `G` of the same dimension is all of `G`. -/
theorem identityComponent_spec_and_isClosed_range_and_eq_of_krullDim_eq
    (G : Subgroup (GL n k)) (hG : IsClosed (G : Set (GL n k))) :
    (IsClosed (G.identityComponent : Set (GL n k)) ∧ G.identityComponent ≤ G ∧
        (∀ g ∈ G, ∀ x ∈ G.identityComponent, g * x * g⁻¹ ∈ G.identityComponent) ∧
        IsPreirreducible (G.identityComponent : Set (GL n k)) ∧
        (G.identityComponent.subgroupOf G).index ≠ 0) ∧
      (∀ ρ : G →* GL m k, IsRegularHom ρ → IsClosed (Set.range fun g : G ↦ ρ g)) ∧
      (∀ J : Subgroup (GL n k), J ≤ G → IsClosed (J : Set (GL n k)) →
        IsPreirreducible (G : Set (GL n k)) →
        topologicalKrullDim (J : Set (GL n k)) = topologicalKrullDim (G : Set (GL n k)) →
          J = G) := by
  sorry

end Matrix
