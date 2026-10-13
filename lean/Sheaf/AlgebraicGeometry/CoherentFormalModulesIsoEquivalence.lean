/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group P4
-/
module

public import Sheaf.AlgebraicGeometry.CoherentFormalModule

/-! # Transport of coherent formal modules along a scheme isomorphism

Source: Stacks Project, Section 0EHN, and the affine identification in Lemma 087W.
(blueprint: lem-weil-pbc-coherent-formal-modules-iso-equivalence).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- A scheme isomorphism transports the category of coherent formal modules.
Source: Stacks Project, Section 0EHN (definition of coherent formal modules), and
Lemma 087W (identification with an affine presentation).
(blueprint: lem-weil-pbc-coherent-formal-modules-iso-equivalence).

Proof: Pull back each module and each transition along the inverse of e. Pullback
along an isomorphism is an equivalence of module categories, with inverse pullback
along e. It carries coherent modules to coherent modules. The ideal comap carries
powers and multiplication maps to their pullbacks. As an equivalence it preserves
images and cokernels, so it carries ideal products and their quotient projections
to the corresponding products and projections for I.comap e.inv. Thus all three
formal object conditions transport, including the equation identifying the
transition with the quotient projection followed by an isomorphism. Apply this
termwise to objects and natural transformations. Pullback along e supplies the
inverse functor; the pullback composition and identity isomorphisms supply the
unit and counit, restricted to the full subcategories. The two transported ideals
are identified by comap composition and e.hom_inv_id. This argument also applies
to the zero ideal, the unit ideal, and the empty scheme. -/
theorem coherentFormalModules_iso_equivalence {X Y : Scheme.{u}}
    [IsNoetherian X] [IsNoetherian Y] (I : X.IdealSheafData) (e : X ≅ Y) :
    Nonempty (CoherentFormalModule X I ≌ CoherentFormalModule Y (I.comap e.inv)) := by
  sorry

end AlgebraicGeometry
