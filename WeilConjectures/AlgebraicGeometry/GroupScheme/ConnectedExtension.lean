/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.GroupScheme.Defs
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Mathlib.Topology.Connected.Basic
import Mathlib.RingTheory.RingHom.FaithfullyFlat

/-! # Connectedness of extensions of affine algebraic groups

Source: Milne, Algebraic Groups (2017), Proposition 5.59(a), printed p.114;
Proposition 5.45 and Section 5(j) supply faithful-flat exactness.
(blueprint: lem-sfb-connected-group-extension)
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- An affine algebraic group with connected kernel and connected faithfully flat quotient
is connected. The kernel is scheme-theoretic; it need not be reduced or smooth.

Source: Milne, Algebraic Groups (2017), Proposition 5.59(a), printed p.114, with
Proposition 5.45 and Section 5(j); its application in Lemma 16.39, printed p.338.
(blueprint: lem-sfb-connected-group-extension)

Proof:
1. Apply `lem-sfb-finite-constant-component-quotient` to obtain a surjective homomorphism
   `c : G ⟶ P_k` to a finite constant group scheme whose fibres are the connected components.
2. On the connected kernel, the inverse images of the constant summands form a finite
   clopen partition. Only the identity summand is nonempty, since the map preserves the
   identity. Factoring through this open summand shows scheme-theoretically that the
   restriction of `c` to the kernel is the identity section followed by its structure map,
   including on nonreduced test algebras (`def-weil-connected-scheme`,
   `def-weil-open-immersion`).
3. Under the affine-spectrum correspondence (`def-weil-affine-spectrum`), flatness and
   surjectivity of `p` make its coordinate-ring map faithfully flat, by
   `lem-weil-pbc-flat-ring-map-iff-flat-affine` and
   `lem-weil-pbc-flat-surjective-spectrum-faithfully-flat`. Apply
   `lem-sfb-faithfully-flat-group-quotient-universal` to factor `c` through `Q`.
4. The same clopen-partition argument on connected `Q` makes this factorization trivial.
   Surjectivity of `c` forces `P` to be the trivial group. Its only fibre, all of `G`,
   is a connected component by step 1. The identity section ensures nonemptiness, so
   `G` is connected (`def-weil-connected-scheme`, `def-weil-open-immersion`). -/
theorem connectedSpace_of_connected_kernel {k : Type u} [Field k] [IsAlgClosed k]
    (G Q : Over (Spec (.of k))) [GrpObj G] [GrpObj Q]
    [IsAffine G.left] [IsAffine Q.left]
    [LocallyOfFiniteType G.hom] [QuasiCompact G.hom]
    [LocallyOfFiniteType Q.hom] [QuasiCompact Q.hom]
    (p : G ⟶ Q) [IsMonHom p] [Flat p.left] [Surjective p.left]
    [ConnectedSpace (GrpObj.ker p).left] [ConnectedSpace Q.left] :
    ConnectedSpace G.left := by
  sorry

end AlgebraicGeometry
