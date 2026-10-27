module

public import Sheaf.AlgebraicGeometry.ReductiveTorusCentralizerTerminology
public import Sheaf.AlgebraicGeometry.ToriMultiplicativeType
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.Topology.Connected.Basic

import WeilConjectures.Mathlib.AlgebraicGeometry.Geometrically.Connected
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import WeilConjectures.Mathlib.AlgebraicGeometry.Scheme
import Sheaf.AlgebraicGeometry.GroupScheme.AffineNormalQuotientGeometry

/-! # Maximal tori and extension of the ground field

Source: Milne, Algebraic Groups (2017), Theorem 17.82, printed p.379
(blueprint: lem-sfb-maximal-torus-field-extension).

Maximality is unchanged by any field extension for a closed torus in a smooth
connected affine group of finite type. Scalar extension is the recorded pullback
functor on group schemes; maximality uses the existing closed-subgroup predicate.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- A closed torus is maximal exactly when its scalar extension is maximal.
There is no reductivity, splitting, perfectness or characteristic hypothesis,
and the trivial torus is included.

Source: Milne, Algebraic Groups (2017), Theorem 17.82, printed p.379
(blueprint: lem-sfb-maximal-torus-field-extension).

Proof plan, following the six steps of the DAG node:
1. A torus is smooth and geometrically connected: over a splitting algebraic
   closure its coordinate ring is a Laurent polynomial domain, whose only
   idempotents are 0 and 1. Use lem-pc-scheme-connected-iff-idempotents and
   lem-sfb-geometrically-reduced-group-smooth. The identity point and
   lem-sbc-connected-rational-point-geometrically-connected make G geometrically
   connected. Smoothness is stable under base change (lem-pc-proper-base-change,
   clause 2); affine finite type and the torus splitting persist by tensoring.
2. By lem-sfb-torus-centralizer-smooth-connected, C = C_G(T) is smooth,
   geometrically connected and affine finite type. T is central in C, so
   lem-sfb-affine-normal-quotient-geometry gives Q = C/T and its quotient map q.
   Every torus containing T centralizes it, so maximality in G equals that in C.
3. If T is maximal, the inverse image P of a torus R in Q is smooth and connected
   by lem-sfb-affine-normal-quotient-geometry. It is a central extension of R by T,
   hence a torus by lem-sfb-central-extension-of-tori. Maximality gives P = T,
   so R is trivial by the quotient identification.
4. Apply lem-sfb-torus-free-implies-unipotent-arbitrary-field to Q. The previous
   step concerns all ground-field tori, so this also applies over finite or
   imperfect fields and shows that Q is unipotent.
5. Conversely, if Q is unipotent, a torus S in C containing T maps trivially to Q:
   over an algebraic closure, use lem-sfb-diagonalizable-group-geometric-criteria
   to identify S with D(Z^r), and lem-sfb-diagonalizable-to-unipotent-trivial
   to kill the map. Descend equality of coordinate maps by injectivity of scalar
   extension of vector spaces. The scheme-theoretic kernel of q is T, so S = T.
   Thus T is maximal exactly when Q is unipotent.
6. The centralizer commutes with field extension: the functor-of-points tests
   agree because any algebra over an L-algebra inherits an L-structure.
   Quotients commute with extension by lem-sfb-affine-normal-quotient-geometry.
   Unipotence is invariant under extension by
   lem-sfb-unipotent-to-multiplicative-trivial. Apply the criterion from steps
   2--5 to both fields, using step 1 for all base-changed hypotheses.
-/
theorem maximal_torus_iff_baseChange {k : Type u} [Field k]
    (T G : Grp (Over (Spec (.of k))))
    [Smooth G.X.hom] [ConnectedSpace G.X.left] [IsAffine G.X.left]
    [LocallyOfFiniteType G.X.hom] [QuasiCompact G.X.hom]
    (i : T ⟶ G) [IsClosedSubgroupScheme i.hom.hom]
    (hT : MultiplicativeType.IsTorus T) (L : Type u) [Field L] [Algebra k L] :
    ReductiveTorusCentralizer.IsMaximalTorus i ↔
      ReductiveTorusCentralizer.IsMaximalTorus
        ((MultiplicativeType.baseChange (K := L)).map i) := by
  sorry

end AlgebraicGeometry
