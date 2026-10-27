module

public import Sheaf.CategoryTheory.DgFiniteCellModule
public import WeilConjectures.CategoryTheory.CompactObject

import Mathlib.CategoryTheory.Triangulated.Pretriangulated

/-! # Compact dg modules are retracts of finite-cell modules

Source: Stacks Project, dga.tex, Tag 09R3, proposition-compact, (1) implies (2),
and Tag 0FQ0 for conversion between left and right modules
(blueprint: lem-sfb-dg-compact-finite-cell-retract).
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.SheafDg

/-- Every compact object of the derived category of left dg modules over an
arbitrary unital associative dg Z-algebra is a retract of a finite-cell module.
The preadditive and coproduct instances expose the additive category with small
coproducts used in the compactness definition. No constraint on the grading or
multiplication of A is imposed beyond its dg algebra structure.
Source: Stacks, dga.tex, Tag 09R3, implication (1) to (2), and Tag 0FQ0
(blueprint: lem-sfb-dg-compact-finite-cell-retract).

Proof:
1. Convert left C-modules to right modules over the graded opposite algebra:
a*b=(-1)^(|a||b|)ba and x*a=(-1)^(|x||a|)ax. These inverse sign conversions
preserve the complexes, homotopies, localization words, sums and shifted regular
modules. Hence they preserve compactness, filtrations and retractions.
2. By lem-sfb-dg-property-p-resolution represent the compact object E by a
property-(P) resolution R. Its exhaustive filtration gives a telescope triangle
B --(1-s)--> B --> E --> B[1], where B is the sum of its stages and s is the
forward transition shift, by lem-sfb-dg-sequential-colimit-triangle and
lem-sfb-dg-derived-admissible-triangles.
3. Compactness expresses the connecting map as a finite sum of components.
Its composite with (1-s)[1] is zero by lem-weil-pbc-hom-into-triangle-exact.
Projection to stage 0 makes that component zero; projection to each subsequent
stage identifies its component with the transition of the preceding one.
Induction annihilates every component, so the connecting map is zero.
4. Hom exactness in lem-weil-pbc-hom-into-triangle-exact splits B --> E.
Compactness makes a section have finite support. Choose one stage F_N R above
that support and sum the transition composites to factor the identity through
F_N R. This stage has finitely many layers, possibly with infinitely many cells.
5. Lem-sfb-dg-compact-map-finite-subcell factors the map E --> F_N R through a
dg submodule P whose induced filtration has finite sums of shifted regular
modules as quotients. Compose P --> F_N R --> E for the retraction. Its composite
with E --> P is the identity. Apply the inverse sign conversion from step 1.
Empty layers and the zero module are included in this construction. -/
theorem compact_exists_finiteCell_retract
    (A : Algebra (pointIntegers.{u}))
    [Preadditive (Derived A)] [HasCoproducts.{u} (Derived A)]
    (M : Derived A) (hM : IsCompactObject.{u} M) :
    ∃ P : LeftModule A, HasFiniteCellFiltration A P ∧
      ∃ (i : M ⟶ (moduleQ A).obj P) (p : (moduleQ A).obj P ⟶ M), i ≫ p = 𝟙 M := by
  sorry

end CategoryTheory.SheafDg
