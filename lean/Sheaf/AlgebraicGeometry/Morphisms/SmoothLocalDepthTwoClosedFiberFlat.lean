/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group G2
-/
module

public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Fiber
public import Sheaf.RingTheory.Depth

/-!
# Formal flatness at a closed boundary point of the closed fibre

Source: Stacks Project, Tag 0EYB, closed-point formal-completion calculation.
(blueprint: lem-sbc-smooth-local-depth-two-closed-fiber-flat)
-/

@[expose] public section

universe u
open CategoryTheory
namespace AlgebraicGeometry.Scheme

/-- Formal completion gives flatness at source points over a closed boundary point.

Source: Stacks Project, Tag 0EYB, from the choice of a closed point through the
completion argument; Tags 0EY6(2),(a),(b), 07NE, 057G, 05D5, 00MB, and 0EYA.
(blueprint: lem-sbc-smooth-local-depth-two-closed-fiber-flat)

Proof: The fibre is locally of finite type over the residue field. Closedness
of x therefore makes its residue extension finite. Realize that extension
by a finite flat local extension A to A' (07NE), and use the smooth etale
slice (057G) to obtain, after a further flat local base change, a section
through x. The new local base is Noetherian and has depth at least two by
the flat local depth formula (0337). Choose a smooth affine chart through
the section point and complete in the section ideal. Tag 05D5 identifies
the result with A'[[x_1,...,x_d]], and 00MB makes the completion map flat.
The inverse image of U contains every point away from the closed base
point. If d is zero, the section point is generic in its closed fibre;
fibrewise density then puts it in U, contradicting hout. If d is positive,
the prime m(A') times the power-series ring maps to a generic point of the
closed fibre and thus belongs to the inverse image of U. Tag 0EYA extends
the finite etale restriction to a finite etale cover of the completion.
Smoothness and 0337 give depth at least two on the target boundary. The
boundary depth of E identifies the supplied p with the unique depth-two
finite extension (0EY6(2)); that identification commutes with the two flat
base changes and completion (0EY6(a),(b)). Thus the completed p is flat.
Completion localized at the section point is faithfully flat, since the
section ideal is contained in its maximal ideal. Descent of flatness gives
flatness of every local ring map over x, including the specified z.
The finite flat local extensions used above are faithfully flat, so the
same descent gives the assertion before those base changes. Empty E has
no z; no global flat locus argument is used in this local statement. -/
theorem flat_stalk_of_smooth_local_depth_two_closed_fiber
    (A : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    {L : Scheme.{u}} (q : L ⟶ Spec (.of A)) [Smooth q]
    (U : L.Opens)
    (haway : ∀ y : L, q y ≠ IsLocalRing.closedPoint A → y ∈ U)
    (hclosed : Dense (↑((q.fiberι (IsLocalRing.closedPoint A)) ⁻¹ᵁ U) :
      Set (q.fiber (IsLocalRing.closedPoint A))))
    (hdepth : (2 : ℕ∞) ≤ IsLocalRing.depth (R := A) A)
    {E : Scheme.{u}} (p : E ⟶ L) [IsFinite p] [Etale (p ∣_ U)]
    (hboundary : ∀ z : E, p z ∉ U →
      (2 : ℕ∞) ≤ IsLocalRing.depth (R := E.presheaf.stalk z) (E.presheaf.stalk z))
    (x : q.fiber (IsLocalRing.closedPoint A)) (hx : IsClosed ({x} : Set _))
    (hout : q.fiberι (IsLocalRing.closedPoint A) x ∉ U)
    (z : E) (hz : p z = q.fiberι (IsLocalRing.closedPoint A) x) :
    (p.stalkMap z).hom.Flat := by sorry

end AlgebraicGeometry.Scheme
