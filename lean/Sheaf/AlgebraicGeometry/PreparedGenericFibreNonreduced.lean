/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q09
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.Topology.Irreducible
public import Mathlib.Topology.Sober
public import Mathlib.CategoryTheory.MorphismProperty.Limits
public import Mathlib.AlgebraicGeometry.Morphisms.Constructors
public import Mathlib.Topology.Homeomorph.Defs
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.AlgebraicGeometry.Geometrically.Integral
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
import Sheaf.AlgebraicGeometry.ReductionGenericFibre
import Sheaf.TraceFormula.GeometricReducedFibreLocusBaseChange
import Sheaf.AlgebraicGeometry.GeometricallyReducedAlgebraicClosureTest

/-!
# Detecting a nonreduced prepared generic fibre

Source: Stacks Project, More on Morphisms, Tag 0577,
`lemma-not-geometrically-reduced-in-neighbourhood`, proof at the prepared generic fibre.
(blueprint: lem-trf-prepared-generic-fibre-nonreduced)
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- The pullback to the prepared integral base has nonreduced generic fibre if its
reduction has geometrically reduced generic fibre and the original generic fibre is
not geometrically reduced.

Source: Stacks Project, More on Morphisms, Tag 0577,
`lemma-not-geometrically-reduced-in-neighbourhood`, proof at the prepared generic fibre.
(blueprint: lem-trf-prepared-generic-fibre-nonreduced)

Proof plan:
1. Put g = q followed by the inclusion of U into Y. The universal homeomorphism q
   is a homeomorphism, so q(xi) is generic in U. Every nonempty open of irreducible Y
   meets the nonempty open U, hence contains g(xi). Thus g(xi) is generic in Y,
   and sobriety of schemes gives g(xi) = eta. This uses
   def-weil-universal-homeomorphism, def-sc-generic-point,
   def-weil-irreducible-components and lem-sc-scheme-sober.
2. Suppose P_xi is reduced. Since T is integral, xi is the generic point of its sole
   irreducible component. By lem-pur-reduction-generic-fibre (Stacks 054Z), R_xi is
   canonically the reduction of P_xi, compatibly with the maps to Spec kappa(xi).
   Reduction of a reduced scheme is itself, so R_xi and P_xi are isomorphic over
   kappa(xi). The hypothesis therefore makes P_xi geometrically reduced. This uses
   def-pc-integral-scheme, def-weil-pbc-scheme-reduction, def-pc-reduced-scheme and
   def-pc-geometrically-irreducible as well as the reduction comparison.
3. Choose algebraic closures of kappa(xi) and kappa(eta). The geometric fibre of P
   at xi is reduced. Apply lem-trf-geometric-reduced-fibre-locus-base-change to f
   and g, and use g(xi) = eta, to deduce that the geometric fibre of X at eta is
   reduced. By lem-trf-geometric-reducedness-algebraic-closure-test, X_eta is
   geometrically reduced, contradicting the hypothesis. This also uses
   def-weil-geometric-fibre. Therefore P_xi is not reduced. -/
theorem prepared_generic_fibre_nonreduced
    {X Y : Scheme.{u}} (f : X ⟶ Y) [LocallyOfFiniteType f] [QuasiCompact f]
    [IrreducibleSpace Y] (η : Y) (hη : IsGenericPoint η Set.univ)
    (U : Y.Opens) (hU : (U : Set Y).Nonempty)
    (T : Scheme.{u}) [IsIntegral T] (ξ : T) (hξ : IsGenericPoint ξ Set.univ)
    (q : T ⟶ U.toScheme) (hq : (topologically IsHomeomorph).universally q)
    (hX : ¬ GeometricallyReduced (f.fiberToSpecResidueField η))
    (hR : GeometricallyReduced
      (((pullback f (q ≫ U.ι)).nilradical.subschemeι ≫
        pullback.snd f (q ≫ U.ι)).fiberToSpecResidueField ξ)) :
    ¬ IsReduced ((pullback.snd f (q ≫ U.ι)).fiber ξ) := by
  sorry

end AlgebraicGeometry
