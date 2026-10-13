/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group V4
-/
module

public import Sheaf.AlgebraicGeometry.Coherent

/-! # Relations of a coherent sheaf on an iterated open slice

Source: Stacks Project, Modules, Definition 01BV, condition (2).
(blueprint: lem-weil-pbc-coherent-iterated-slice-relations).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace AlgebraicGeometry.RingedSpace

/-- Finite families of sections of a coherent module have finite type relations
also after passing to an iterated open slice.
Source: Stacks Project, Modules, Definition 01BV, condition (2).
(blueprint: lem-weil-pbc-coherent-iterated-slice-relations).

Proof: Write V as an open W of X with W contained in U. The category of opens
below V in the slice below U is equivalent to the category of opens below W
in X: forget the factorization through U, and conversely insert the unique
inclusion into U. These inverse functors preserve covers and all section rings.
They therefore identify the iterated restriction of G with G.over W. Reindex
I by ULift (Fin n), where n is its finite cardinality. The resulting finite free
map into G.over W has finite type kernel by hG's relation clause. The site
identification carries its kernel back to kernel f, since kernels are computed
sectionwise. It carries finite local generators back as well, since the rings,
restrictions, and covers agree. This also covers I empty and W empty. -/
theorem coherent_iterated_slice_relations (X : RingedSpace.{u})
    (U : Opens X) (G : SheafOfModules.{u} (moduleRings X))
    (hG : IsCoherent X G) (V : Over U) (I : Type u) [Finite I]
    (f : SheafOfModules.free (R := ((moduleRings X).over U).over V) I ⟶
      (G.over U).over V) : (kernel f).IsFiniteType := by sorry

end AlgebraicGeometry.RingedSpace
