/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group M3
-/
module

public import Sheaf.Topology.RingedSpaceModuleCohomology
public import Mathlib.Algebra.Homology.HomotopyCategory
public import Mathlib.Algebra.Homology.Single

/-! # Evaluation at one on homotopy classes of structure-sheaf maps

Source: Stacks Project, Tag 09M1, proof, first paragraph.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

/-- Evaluation at one identifies homotopy classes of maps from the structure sheaf
in degree zero with maps from the global sections ring in degree zero.
Source: Stacks Project, Tag 09M1, proof, first paragraph, and Tag 0B6A.
(blueprint: lem-pc-structure-sheaf-homotopy-global-sections).
Proof: For a complex J, a chain map from O_X[0] is an O_X-linear morphism
O_X to J^0 whose composite with d^0 is zero. Evaluate at one on the total open.
The inverse takes a global cycle z to the morphism whose value on an open U at
r is r times the restriction of z to U. Naturality and linearity give inverse
additive maps. The identical cycle z determines the A-linear chain map from
A[0] to the termwise global-sections complex. A homotopy between two maps on
either side is a degree minus one section t with d(t) equal to the difference
of the degree zero cycles. Thus evaluation and its inverse identify the
homotopy relations, and descend to inverse additive maps on the quotient.
Postcomposition with a chain map sends z to its degree zero image, so commutes
with evaluation. Every morphism in the homotopy category has a chain-map
representative; changing it by a homotopy changes none of these classes. This
proves naturality for all homotopy-category morphisms. The construction uses
only global cycles and boundaries, with no injectivity or boundedness assumption;
it applies to the empty scheme and the zero ring as well. -/
theorem structureSheaf_homotopy_globalSections (X : RingedSpace.{u}) :
    let C := SheafOfModules.{u} (moduleRings X)
    let A := (moduleRings X).obj.obj (op ⊤)
    let P := (HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj
      ((CochainComplex.singleFunctor C 0).obj
        (SheafOfModules.unit (moduleRings X)))
    let Q := (HomotopyCategory.quotient (ModuleCat.{u} A) (ComplexShape.up ℤ)).obj
      ((CochainComplex.singleFunctor (ModuleCat.{u} A) 0).obj (ModuleCat.of A A))
    let G := (RingedSpace.globalSectionsFunctor X).mapHomotopyCategory
      (ComplexShape.up ℤ)
    ∃ e : ∀ J : HomotopyCategory C (ComplexShape.up ℤ),
      (P ⟶ J) ≃+ (Q ⟶ G.obj J),
      ∀ (J J' : HomotopyCategory C (ComplexShape.up ℤ)) (f : J ⟶ J') (g : P ⟶ J),
        e J' (g ≫ f) = e J g ≫ G.map f := by sorry

end AlgebraicGeometry
