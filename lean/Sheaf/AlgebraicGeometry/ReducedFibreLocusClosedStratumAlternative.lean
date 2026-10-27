/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q52
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.AlgebraicGeometry.Pullbacks
public import WeilConjectures.Mathlib.AlgebraicGeometry.ResidueField
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import Mathlib.Topology.Sober
import Sheaf.AlgebraicGeometry.GenericConstancyGeometricReducedness
import Sheaf.AlgebraicGeometry.GeometricallyReducedAlgebraicClosureTest
import Sheaf.TraceFormula.GeometricReducedFibreLocusBaseChange

/-!
# The reduced geometric-fibre locus on an irreducible closed stratum

Source: Stacks Project, More on Morphisms, Tag 0579, second proof paragraph,
with Tags 0576, 0577 and 0578
(blueprint: lem-trf-reduced-fibre-locus-closed-stratum-alternative).
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- Every irreducible closed subset of the base has a nonempty relatively open subset
on which either every geometric fibre is reduced or every geometric fibre is nonreduced.
The geometric points use the canonical algebraic closures of the residue fields.

Source: Stacks Project, More on Morphisms, Tag 0579, second proof paragraph,
with Tags 0576, 0577 and 0578
(blueprint: lem-trf-reduced-fibre-locus-closed-stratum-alternative).

Proof:
1. Give `Z` a closed subscheme structure `i : T ⟶ Y` using
   lem-weil-pbc-closed-subset-closed-subscheme. By def-weil-closed-immersion its
   underlying space is homeomorphic to `Z`. Thus `T` is irreducible and nonempty;
   lem-sc-scheme-sober supplies its generic point. No reduced structure is needed.
2. Form `h : X ×[Y] T ⟶ T`. Clause (3) of
   lem-weil-pbc-qcqs-morphism-permanence makes `h` quasi-compact and locally of
   finite presentation. No finite presentation of `i` or quasi-separatedness of `f`
   is used.
3. Apply lem-trf-generic-constancy-geometric-reducedness to `h`. On a nonempty open
   `W` of `T`, geometric reducedness of each fibre agrees with that of the generic
   fibre. Excluded middle gives the two alternatives on `W`.
4. Apply lem-trf-geometric-reducedness-algebraic-closure-test to each fibre over
   its residue field. By def-weil-geometric-fibre, its algebraic-closure base change
   is the geometric fibre. Thus either all geometric fibres on `W` are reduced or
   none are; the test includes empty fibres.
5. By lem-trf-geometric-reduced-fibre-locus-base-change, the reduced geometric-fibre
   locus for `h` is the inverse image of that for `f`. Transport `W` along the
   homeomorphism `T ≃ Z` supplied by def-weil-closed-immersion to obtain `V`.
   Its nonemptiness and openness, and either alternative, are preserved. When `Y`
   is empty there is no irreducible closed subset, so the assertion is vacuous. -/
theorem exists_nonempty_open_reduced_geometricFiber_closed_stratum_alternative
    {X Y : Scheme.{u}} (f : X ⟶ Y) [QuasiCompact f] [LocallyOfFinitePresentation f]
    (Z : Set Y) (hZclosed : IsClosed Z) (hZirreducible : IsIrreducible Z) :
    ∃ V : TopologicalSpace.Opens Z, (V : Set Z).Nonempty ∧
      ((∀ z : Z, z ∈ V →
          IsReduced (pullback f (Y.fromSpecAlgebraicClosureResidueField z.val))) ∨
        (∀ z : Z, z ∈ V →
          ¬ IsReduced (pullback f (Y.fromSpecAlgebraicClosureResidueField z.val)))) := by
  sorry

end AlgebraicGeometry
