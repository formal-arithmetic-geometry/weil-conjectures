/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The SHEAF contributors
-/
module

public import Sheaf.CategoryTheory.DgHomotopicallyProjective
public import Sheaf.CategoryTheory.DgHomotopyDerivedFunctor
import Sheaf.CategoryTheory.DgHomotopyAcyclicLocalization
import Mathlib.CategoryTheory.Triangulated.Orthogonal

/-!
# Derived morphisms from a homotopically projective right DG module

Source: Stacks Project, dga.tex, Tag 09KY, lemma-hom-derived, part (1) and its proof
(blueprint: lem-sfb-dg-homotopically-projective-hom-derived).
-/

@[expose] public section

set_option autoImplicit false

universe u

namespace CategoryTheory.DgAlgebra

/-- The canonical map from homotopy classes to derived morphisms is bijective
for a homotopically projective source over any associative unital DG algebra.
There are no boundedness, freeness or countability hypotheses.
Source: Stacks Project, dga.tex, Tag 09KY, lemma-hom-derived, part (1), using
only Hom-complex vanishing from its proof
(blueprint: lem-sfb-dg-homotopically-projective-hom-derived).

Proof plan:
1. Apply lem-sfb-dg-homotopy-acyclic-localization to obtain the standard
triangulation on the actual homotopy quotient. Its acyclic objects form a
strictly full triangulated subcategory, and its cone class is exactly the
quasi-isomorphisms. The specified functor to Derived A is localization at this
class: it is the descent of Q along the homotopy quotient, and both universal
properties identify functors out of it with functors inverting quasi-isomorphisms.
2. For every acyclic E, homotopical projectivity says every closed right-linear
cochain P to E in degree zero is a boundary. Such a boundary is a right-linear
null homotopy, so every morphism from P to E in the quotient vanishes. This is
left orthogonality to the acyclic objects. All shifts of an acyclic object are
acyclic, so the same vanishing holds for the shifts used in the source proof.
3. Apply lem-sfb-left-orthogonal-localization-hom, namely
ObjectProperty.leftOrthogonal.map_bijective_of_isTriangulated, to this object,
subcategory and localization functor. Its map is precisely the function below.
All constructions and the vanishing apply also to P=0, N=0 and the zero algebra. -/
theorem homotopicallyProjective_hom_derived_bijective
    (A : Algebra.{u}) (P N : RightModule A) (hP : IsHomotopicallyProjective A P) :
    Function.Bijective
      ((homotopyDerivedFunctor A).map :
        ((homotopyQuotient A).obj P ⟶ (homotopyQuotient A).obj N) →
          ((homotopyDerivedFunctor A).obj ((homotopyQuotient A).obj P) ⟶
            (homotopyDerivedFunctor A).obj ((homotopyQuotient A).obj N))) := by
  sorry

end CategoryTheory.DgAlgebra
