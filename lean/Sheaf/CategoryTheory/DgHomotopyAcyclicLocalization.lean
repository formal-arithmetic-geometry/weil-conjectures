/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The SHEAF contributors
-/
module

public import Sheaf.CategoryTheory.DgAlgebraHomotopyStructure

/-!
# Triangulation and the acyclic cone class of dg modules

Source: Stacks Project, dga.tex, Tags 09KH, 09KJ and 09KW
(blueprint: lem-sfb-dg-homotopy-acyclic-localization).
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

namespace CategoryTheory.DgAlgebra

/-- The three assertions for the specified dg homotopy triangulation: TR4,
strictly full triangulated acyclic objects, and equality of their cone class with
maps inducing isomorphisms on all cohomology groups. `trW` quantifies over the
actual distinguished triangles with the given first arrow.
Source: Stacks, dga.tex, Tags 09KJ and 09KW
(blueprint: lem-sfb-dg-homotopy-acyclic-localization). -/
def HomotopyStructure.AcyclicLocalization (A : Algebra.{u}) [HomotopyStructure A] : Prop :=
  IsTriangulated (HomotopyCategory A) ∧
    (homotopyAcyclic A).IsClosedUnderIsomorphisms ∧
    (homotopyAcyclic A).IsTriangulated ∧
    (homotopyAcyclic A).trW =
      (fun _ _ f ↦ ∀ n : ℤ, IsIso ((HomotopyStructure.cohomology n).map f))

/-- The homotopy category of arbitrary right dg modules has its standard cone
triangulation, its acyclic objects form a strictly full triangulated subcategory,
and the acyclic cone class is exactly the cohomology-isomorphism class.
Source: Stacks, dga.tex, Tags 09KH, 09KJ and 09KW
(blueprint: lem-sfb-dg-homotopy-acyclic-localization).

Proof plan, following the nine steps of the node:
1. Homotopies add and compose with dg maps, so the quotient is additive.
   The zero module and finite sums descend. Shifts multiply differentials and
   homotopies by the appropriate sign. Cones satisfy d squared equals zero and
   the dg Leibniz rule. The identity cone contracts by (y,x) maps to (0,y).
   Every quotient arrow has a representative, giving TR1.
2. Apply lem-sfb-dg-cone-rotation to obtain both rotations of standard cones,
   including their negative projection signs; triangle isomorphisms rotate. This is TR2.
3. For a square commuting up to h, use the cone map (y,x) maps to (by+hx,ax).
   Its chain equation is bf-f'a=dh+hd. Conjugating by triangle isomorphisms gives TR3.
4. For composable f,g, lem-sfb-dg-composite-cone-contraction supplies the
   distinguished triangle C(f),C(gf),C(g), with maps (gy,x), (z,fx), (-y,0).
   Direct substitution verifies all four octahedral squares and the last arrow.
5. TR3 and lem-sf-triangle-morphism-iso identify arbitrary prescribed cone
   triangles with the standard ones. Conjugate the three cone maps; their
   equations persist and the fourth triangle stays distinguished. This is TR4.
6. Homotopic maps have equal cohomology maps, since their difference on a cycle
   is a boundary. Cohomology descends as a functor. The sign on a shifted
   differential leaves kernels and images unchanged, giving H^n(M[k])=H^(n+k)(M).
7. A cycle (y,x) in C(f) satisfies dx=0 and dy=-fx. Bijectivity on cohomology
   gives x=dt and y+ft=fz+dw with dz=0; then (y,x)=d(w,z-t).
   Conversely acyclicity applied to (y,0) proves surjectivity, and applied to
   (-y,x) when fx=dy proves injectivity. Thus C(f) is acyclic iff f is a quasi-iso.
8. Zero is acyclic. Step 6 gives shift and isomorphism closure. In a cone triangle
   with acyclic source and cone, step 7 forces the target cohomology to vanish.
   Transport along triangle isomorphisms gives the triangulated-subcategory axiom.
9. A cohomology isomorphism has an acyclic standard cone by step 7. Conversely
   a distinguished triangle with acyclic third object is isomorphic to a standard
   cone triangle; steps 6 and 7 show its first arrow is a cohomology isomorphism.
No commutativity, boundedness or finiteness enters any step. -/
theorem homotopy_acyclic_localization (A : Algebra.{u}) :
    ∃ s : HomotopyStructure A, @HomotopyStructure.AcyclicLocalization A s := by
  sorry

end CategoryTheory.DgAlgebra
