/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The SHEAF contributors
-/
module

public import Sheaf.CategoryTheory.DgAlgebraHomotopyStructure

/-!
# The canonical functor from the DG homotopy quotient to the derived category

Source: Stacks Project, dga.tex, Tags 09KW and 09KX, localization of the homotopy category
(blueprint: def-sfb-dg-homotopy-derived-functor).
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

namespace CategoryTheory.DgAlgebra

/-- The quasi-isomorphism localization identifies right A-linear homotopic maps.
This is the well-definedness assertion needed to descend Q to the homotopy quotient.
Source: Stacks Project, dga.tex, Tags 09KW and 09KX
(blueprint: def-sfb-dg-homotopy-derived-functor).

Proof: for f-g=dh+hd, take the cylinder with degree-n elements (y,z,x) in
M^n + M^n + M^(n+1), differential (dy+x,dz-x,-dx), and componentwise right action.
Its inclusions i0(m)=(m,0,0), i1(m)=(0,m,0) and projection p(y,z,x)=y+z
are right DG maps. The kernel of p is the contractible cone of the identity,
so p is a quasi-isomorphism. The map H(y,z,x)=f(y)+g(z)+h(x) is right linear;
the homotopy equation says precisely that it commutes with the differentials.
Since p i0=p i1=id, inversion of Q(p) gives Q(i0)=Q(i1). Composing with Q(H)
gives Q(f)=Q(g). This argument includes the zero module and unbounded complexes. -/
theorem Q_map_eq_of_homotopy (A : Algebra.{u}) (M N : RightModule A)
    (f g : M ⟶ N) (h : homotopyRel A f g) : (Q A).map f = (Q A).map g := by
  sorry

/-- Descend the existing localization functor along the actual homotopy quotient.
On objects this is Q(M), and on a class represented by f it is Q(f), by the
construction of `CategoryTheory.Quotient.lift`. Its data are specified by Q;
only the preceding well-definedness proof is postponed.
Source: Stacks Project, dga.tex, definition-unbounded-derived-category, Tag 09KX
(blueprint: def-sfb-dg-homotopy-derived-functor). -/
def homotopyDerivedFunctor (A : Algebra.{u}) : HomotopyCategory A ⥤ Derived A :=
  CategoryTheory.Quotient.lift (homotopyRel A) (Q A) (Q_map_eq_of_homotopy A)

end CategoryTheory.DgAlgebra
