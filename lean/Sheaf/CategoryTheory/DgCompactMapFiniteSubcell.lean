module

public import Sheaf.CategoryTheory.DgFiniteSemiFreeFiltration
public import WeilConjectures.CategoryTheory.CompactObject

import Mathlib.CategoryTheory.Triangulated.Pretriangulated

/-!
# Finite-cell support of a compact-source map

Source: Stacks Project, dga.tex, Tag 09R2, lemma-factor-through-nicer
(blueprint: lem-sfb-dg-compact-map-finite-subcell).

A dg submodule is represented by its degreewise injective dg inclusion. The layer
condition is equality of the image of the intersection with the specified coordinate
subsum, not just an abstract isomorphism with some finite free dg module.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped BigOperators

namespace CategoryTheory.DgAlgebra

/-- Every derived map from a compact object into a finite semi-free filtration factors
through a submodule using finitely many of its specified cells in every layer.
The equivalence describes the image of (F_i intersect U)/(F_(i-1) intersect U) in the
specified layer, degree by degree. The finite sum on its right is the coordinate
subsum of shifts, so it also identifies those successive quotients with finite sums.
Source: Stacks, dga.tex, Tag 09R2, lemma-factor-through-nicer
(blueprint: lem-sfb-dg-compact-map-finite-subcell).

Proof: descend from the top layer to the zero initial term. Initially take U=T and
the given map. Lift the finitely many generators selected in higher layers to U.
Subtract their multiples successively from the top down: this gives a unique graded
expansion of U as F_m plus those free generators. Their differentials have a part in
F_m and parts in the lower selected higher layers. Choose the finite union K of the
supports of their F_m parts in the specified layer F_m/F_(m-1). Take its inverse
image H_K in F_m, and add the selected higher generators. The differential formulas
show that the resulting V_K is a dg submodule; its higher coordinate layers remain
unchanged and its layer m is exactly K. The quotient U/V_K is the complementary sum
of free shifts in layer m. Homogeneous lifts of its free generators give a graded
splitting, without asserting a dg splitting. Compactness (def-pc-compact-object)
factors E to this quotient through a finite subsum. Enlarge K by this finite support
so that the composite to the new complementary quotient vanishes. The graded-split
short exact sequence gives the actual inclusion/quotient distinguished triangle
(lem-sfb-dg-derived-admissible-triangles). Exactness of Hom into that triangle
(lem-weil-pbc-hom-into-triangle-exact, clause ii) lifts the current map to V_K.
This completes the descending step. At the zero initial term all layer selections
are finite, and composition of the inclusions gives the asserted factorization.
Empty selections, zero layers and the zero target are allowed throughout. -/
theorem exists_finite_subcell_factorization (A : Algebra.{u}) [DerivedStructure A]
    (E : Derived A) (hE : IsCompactObject.{u} E) (n : ℕ) (T : RightModule A)
    (F : FiniteSemiFreeFiltration A T n) (f : E ⟶ (Q A).obj T) :
    ∃ (U : RightModule A) (ι : U ⟶ T),
      (∀ p : ℤ, Function.Injective (((underlying A).map ι).f p)) ∧
      ∃ (S : ∀ i : Fin (n + 1), Finset (F.index i)) (g : E ⟶ (Q A).obj U),
        f = g ≫ (Q A).map ι ∧
        ∀ (i : Fin (n + 1)) (p : ℤ) (z : ((underlying A).obj (F.layer i)).X p),
          (∃ (x : ((underlying A).obj (F.term i.succ)).X p)
            (y : ((underlying A).obj U).X p),
            (((underlying A).map (F.inclusion i.succ)).f p) x =
              (((underlying A).map ι).f p) y ∧
            (((underlying A).map (F.projection i)).f p) x = z) ↔
          ∃ a : ∀ j : F.index i, ((underlying A).obj (F.summand i j)).X p,
            z = ∑ j ∈ S i, (((underlying A).map (F.coprojection i j)).f p) (a j) := by
  sorry

end CategoryTheory.DgAlgebra
