/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF worker K3
-/
module

public import Sheaf.CategoryTheory.DiscreteContinuousRepToCommGrp

/-!
# Reconstruction of a representation from an internal group object

Source: Stacks Project, Tag 04JQ, proof of lemma-equivalence-abelian-sheaves-point.
-/

@[expose] public section

universe u w
open CategoryTheory
namespace Rep

/-- Source: Stacks Project, Tag 04JQ, proof of lemma-equivalence-abelian-sheaves-point.
(blueprint: lem-exc-discrete-continuous-rep-to-commgrp-ess-surj)

Proof: The forgetful functor from discrete continuous actions to types preserves
finite products: the terminal carrier is a singleton and binary products carry the
diagonal action, which is continuous in the discrete topology because stabilizers
are intersections of two open stabilizers. Thus transport the internal unit, product
and inverse along the unique Cartesian comparison maps. The internal group diagrams
become the commutative group identities on the carrier. Use additive notation and its
canonical integer module structure. Equivariance of the operations makes every action
map additive, hence integer-linear. Continuity and discreteness give open stabilizers,
so this is a discrete continuous representation. Its represented group law on every
set of equivariant functions is pointwise addition, by the product comparison and
Yoneda. Consequently the reverse functor recovers the original internal group object
up to the identity carrier isomorphism. This establishes essential surjectivity.
The construction works for the zero group, arbitrary carrier universes, and
non-Hausdorff topological groups. -/
theorem discreteContinuousRepToCommGrp_essSurj
    (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CartesianMonoidalCategory (DiscreteContAction (Type w) G)]
    [BraidedCategory (DiscreteContAction (Type w) G)] :
    (discreteContinuousRepToCommGrp (G := G)).EssSurj := by sorry

end Rep
