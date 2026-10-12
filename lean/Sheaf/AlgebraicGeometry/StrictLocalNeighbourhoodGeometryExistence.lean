/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group G2
-/
module

public import Sheaf.AlgebraicGeometry.StrictLocalNeighbourhoodGeometry
import Sheaf.AlgebraicGeometry.FibreProductNeighbourhoodLimit
import Mathlib.AlgebraicGeometry.Morphisms.Affine

/-! # Existence of the canonical strict-local neighbourhood geometry

Source: Stacks Project, Tag 03Q9, first proof paragraph.
-/

@[expose] public section

universe v

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry

namespace AlgebraicGeometry.Etale

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The pullback of the strict henselization is the limit of the small affine
neighbourhood pullbacks, with qcqs stages and affine transition morphisms.
This supplies only geometry, with no derived sheaves, cocones or mates.
Source: Stacks, Tag 03Q9, first proof paragraph
(blueprint: lem-weil-pbc-strict-local-neighbourhood-geometry).

Proof: use strictHenselization_properties to obtain the cofiltered small category and
its limiting cone. Identify the spectra of global sections with the affine
neighbourhoods, compatibly with the chosen legs. The equation characterizing
strictHenselizationStructuralMap makes this a cone in Over S. Fibre products commute
with this connected limit, giving a limit cone with vertex X ×_S S_(s), after the
canonical symmetry from V ×_S X. Its first component is the original limit leg and
its second is the projection to X, which prove the two displayed leg equations.
Each stage maps by a base change of f to an affine neighbourhood. Quasi-compactness
and quasi-separatedness of f therefore make the stage qcqs. A map between the affine
neighbourhoods is affine; its base change is the stage transition and is also affine.
No qcqs assumption on X or S themselves is needed. -/
theorem nonempty_strictLocalNeighbourhoodGeometry {X S : Scheme.{v}}
    (f : X ⟶ S) [QuasiCompact f] [QuasiSeparated f]
    {Ω : Type v} [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ S) :
    Nonempty (StrictLocalNeighbourhoodGeometry f s) := by sorry

end AlgebraicGeometry.Etale
