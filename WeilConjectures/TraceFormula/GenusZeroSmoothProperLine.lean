/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Curve
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.FieldTheory.IsAlgClosed.Basic
import WeilConjectures.AlgebraicGeometry.SmoothConnectedCurveLocalRings
import WeilConjectures.AlgebraicGeometry.ClosedPointField
import WeilConjectures.AlgebraicGeometry.DivisorModuleSupplement
import WeilConjectures.AlgebraicGeometry.DivisorModuleLocal
import WeilConjectures.AlgebraicGeometry.Curve.RiemannRoch
import WeilConjectures.AlgebraicGeometry.PointTangentSeparationClosedImmersion
import WeilConjectures.AlgebraicGeometry.ProjectiveSpaceStandardCharts
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

/-!
# Genus-zero smooth proper curves over an algebraically closed field

Source: literature/stacks-project/curves.tex, Tag 0C6U, proposition-projective-line,
with the degree-one linear system of Tag 0C6T
(blueprint: lem-trf-genus-zero-smooth-proper-line).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- A smooth proper connected genus-zero curve over an algebraically closed field is the
projective line. Source: Stacks Project, curves.tex, Tag 0C6U, proposition-projective-line,
specialized to an algebraically closed field; also Tag 0C6T, lemma-genus-zero-positive-degree
(blueprint: lem-trf-genus-zero-smooth-proper-line).

Proof:
1. The smooth connected curve local-rings theorem gives an integral curve, a nonclosed
   generic point, and a closed point P. The closed-point residue-field theorem makes the
   residue field finite over k. Algebraic closedness makes this extension trivial, so P,
   and similarly every closed point, is rational.
2. The divisor module L = O(P) is invertible by the local-module theorem and has degree
   one by the divisor degree formula. For arbitrary closed Q and R, possibly equal,
   the bundles O(P), O(P-Q), and O(P-Q-R) have degrees 1, 0, and -1. Riemann--Roch in
   degree at least 2g-1 = -1 gives their section dimensions 2, 1, and 0.
3. The local divisor-module descriptions identify the last two section spaces with
   sections vanishing at Q and at Q+R. When Q = R, the latter condition is vanishing
   to order two. The dimension drops imply generation, point separation, and tangent
   separation: a nonzero section vanishing once has coefficient in (t) but not (t^2),
   where the DVR uniformizer spans the cotangent space.
4. The point-and-tangent separation criterion gives a closed immersion over k into
   projective space on a basis of the two-dimensional full section space, namely the
   specified base-change ProjectiveSpace on two homogeneous coordinates.
5. Its two standard charts are Spec k[t] and Spec k[s], with s = t inverse on the
   overlap. Their common generic point is the unique nonclosed point of the target.
   The generic point of C must map there, since otherwise its singleton preimage
   would be closed. Thus the closed image contains a dense point and is surjective.
6. On either polynomial chart the closed immersion is defined by an ideal I.
   Surjectivity puts the zero prime in V(I), whence I = 0. The chart restrictions are
   isomorphisms; their inverses agree on the overlap and glue to an inverse over k.
-/
theorem genus_zero_smooth_proper_line
    (k : Type u) [Field k] [IsAlgClosed k]
    (C : Scheme.{u}) [C.Over (Spec (.of k))]
    [IsConnectedCurve (C ↘ Spec (.of k))]
    [Smooth (C ↘ Spec (.of k))] [IsProper (C ↘ Spec (.of k))]
    (h : (C ↘ Spec (.of k)).genus = 0) :
    Nonempty ((Over.mk (C ↘ Spec (.of k)) : Over (Spec (.of k))) ≅
      Over.mk (ProjectiveSpace (ULift.{u} (Fin 2)) (Spec (.of k)) ↘
        Spec (.of k))) := by
  sorry

end AlgebraicGeometry
