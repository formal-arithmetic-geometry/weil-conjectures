/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NL
-/
module

public import Mathlib.AlgebraicGeometry.Geometrically.Integral
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.Topology.Sober
import Sheaf.AlgebraicGeometry.GenericGeometricallyReducedPreparation
import Sheaf.TraceFormula.GeometricReducedFibreLocusBaseChange
import Sheaf.AlgebraicGeometry.GeometricallyReducedAlgebraicClosureTest
import Sheaf.AlgebraicGeometry.ReductionGenericFibre
import Sheaf.AlgebraicGeometry.NonreducedFibreOpen

/-!
# Non-geometrically reduced fibres near the generic fibre

Source: Stacks Project, More on Morphisms, Tag 0577,
`lemma-not-geometrically-reduced-in-neighbourhood`.
(blueprint: lem-trf-generic-fibre-not-geometrically-reduced-open)
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- If the generic fibre of a finite type morphism to an irreducible scheme is not
geometrically reduced, then every fibre over some nonempty open subset is not
geometrically reduced. Each fibre has its canonical structure map to the spectrum
of the residue field. No flatness, reducedness of the base, Noetherianity, or
nonemptiness of the fibres is assumed.

Source: Stacks Project, More on Morphisms, Tag 0577,
`lemma-not-geometrically-reduced-in-neighbourhood`.
(blueprint: lem-trf-generic-fibre-not-geometrically-reduced-open)

Proof:
1. By lem-pur-generic-geometrically-reduced-preparation, shrink to a nonempty open
   `U` and take a finite universal homeomorphism `q : T → U` with `T` integral affine,
   such that the reduction `R` of `P = X ×[Y] T` has geometrically reduced generic fibre.
   The projection `h : P → T` is finite type by base change of local finite type and
   quasi-compactness. The generic point `ξ` of `T` maps to `η`: a homeomorphism preserves
   generic points, the nonempty open `U` is dense in `Y`, and schemes are sober.
2. Apply lem-trf-geometric-reduced-fibre-locus-base-change to `T → U → Y`, and use
   lem-trf-geometric-reducedness-algebraic-closure-test on both fibres. Since the generic
   fibre at `η` is not geometrically reduced, neither is the generic fibre of `h` at `ξ`.
3. By lem-pur-reduction-generic-fibre, the generic fibre of `R` is the reduction of
   the generic fibre of `P`. If the latter were reduced, its reduction map would be
   an isomorphism, since on affine charts the nilradical would be zero. It would then
   be geometrically reduced by step 1, contradicting step 2. Thus `P_ξ` is not reduced.
4. By lem-trf-nonreduced-fibre-open applied to the finite type morphism `h` over the
   irreducible scheme `T`, there is a nonempty open `W` where every fibre of `h`
   is nonreduced.
5. The image `q(W)` is nonempty and open in `U`, hence in `Y`, because `q` is a
   homeomorphism. For `y = q(t)` with `t ∈ W`, the fibre `P_t` is canonically the base
   change of `X_y` from `κ(y)` to `κ(t)`, by the fibre-product universal property.
   If `X_y` were geometrically reduced, this base change would be reduced, contrary
   to step 4. Hence this image is the required open subset. -/
theorem exists_nonempty_open_not_geometricallyReduced_fiber_of_generic
    {X Y : Scheme.{u}} (f : X ⟶ Y) [LocallyOfFiniteType f] [QuasiCompact f]
    [IrreducibleSpace Y] (η : Y) (hη : IsGenericPoint η Set.univ)
    (hred : ¬ GeometricallyReduced (f.fiberToSpecResidueField η)) :
    ∃ V : Y.Opens, (V : Set Y).Nonempty ∧
      ∀ y : Y, y ∈ V → ¬ GeometricallyReduced (f.fiberToSpecResidueField y) := by
  sorry

end AlgebraicGeometry
