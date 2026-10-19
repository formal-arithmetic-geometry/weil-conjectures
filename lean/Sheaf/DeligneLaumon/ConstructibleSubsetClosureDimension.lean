/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q146
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.AlgebraicGeometry.Over
public import Mathlib.Topology.Constructible
public import Mathlib.Topology.Defs.Induced
public import Mathlib.Topology.KrullDimension
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.Topology.Irreducible
import Mathlib.Topology.NoetherianSpace
import WeilConjectures.AlgebraicGeometry.DimensionLocallyAlgebraic
import WeilConjectures.AlgebraicGeometry.ReducedInducedClosedSubscheme

/-! # Dimension of a constructible subset and its closure over a field

Source: Stacks Project, Tag 00OT, lemma-dimension-at-a-point-finite-type-over-field,
proof of (1)=(2), together with Tag 0A21 (3)
(blueprint: lem-per-constructible-subset-closure-dimension).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory Topology
namespace AlgebraicGeometry

/--
For a constructible subset of a finite-type scheme over a field, its subspace
Krull dimension equals that of its Zariski closure.

Source: Stacks Project, Tag 00OT, lemma-dimension-at-a-point-finite-type-over-field,
proof of (1)=(2), together with Tag 0A21 (3)
(blueprint: lem-per-constructible-subset-closure-dimension).

Proof, following the seven steps of the node:
1. If `S` is empty its closure is empty and both dimensions are bottom
   (`def-kun-topological-krull-dimension`). Otherwise, constructibility gives finitely
   many nonempty locally closed pieces `L_a = U_a ∩ F_a`
   (`def-weil-constructible-subset`). Put `Z_a = closure L_a`. Since `F_a` is closed,
   `L_a = U_a ∩ Z_a`, and finiteness gives `closure S = ⋃ a, Z_a`.
2. A field is Noetherian, and its spectrum is Noetherian. Finite type makes `T`
   Noetherian (`lem-weil-pbc-finite-type-over-noetherian`). Each closed `Z_a` is
   covered by finitely many distinct irreducible components `C_ab`, closed in `T`
   (`lem-sc-noetherian-closed-subset-finite-components`).
3. A component is not contained in the union of the others: irreducibility would put
   it in one of them, contrary to maximality (`def-weil-irreducible-components`).
   Removing the other components therefore gives a nonempty open of `Z_a` lying in
   `C_ab`. Density of `L_a` meets this open, so `V_ab = U_a ∩ C_ab` is a nonempty
   open of `C_ab` contained in `S`. All topologies are induced subspace topologies
   (`def-kun-subspace-topology`).
4. Give `C_ab` its reduced induced closed subscheme structure
   (`lem-weil-pbc-reduced-induced-closed-subscheme`). Its closed immersion identifies
   its underlying space with `C_ab` (`def-weil-closed-immersion`). It is irreducible;
   its affine charts are quotients of the finite-type affine charts of `T`, so it is
   locally of finite type over `k` (`def-weil-finite-type-morphism`).
5. Apply `lem-sc-dimension-locally-algebraic` to this irreducible scheme and its
   nonempty open `V_ab`: `dim C_ab = dim V_ab` (Stacks Tag 0A21 (3)).
6. Closing every term of a chain of irreducible closed subsets of a subspace in its
   ambient space preserves irreducibility and strict inclusions: intersecting the
   closures back with the subspace recovers each term. Thus subspace dimension is
   monotone (`def-kun-topological-krull-dimension`, `def-kun-subspace-topology`).
   This gives `dim S ≤ dim (closure S)` and `dim C_ab = dim V_ab ≤ dim S`.
7. Every irreducible closed subset of `closure S` lies in one member of its finite
   closed cover by the `C_ab` (`def-weil-irreducible-components`). In particular the
   largest term of each finite chain lies in one component; the whole chain remains
   closed and irreducible there. Hence its length is at most `dim C_ab ≤ dim S`.
   Taking the supremum of the chain lengths gives the reverse inequality.
-/
theorem topologicalKrullDim_constructible_eq_closure
    {k : Type u} [Field k] {T : Scheme.{u}}
    [T.Over (Spec (.of k))]
    [LocallyOfFiniteType (T ↘ Spec (.of k))]
    [QuasiCompact (T ↘ Spec (.of k))]
    (S : Set T) (hS : Topology.IsConstructible S) :
    topologicalKrullDim S = topologicalKrullDim (closure S : Set T) := by
  sorry

end AlgebraicGeometry
