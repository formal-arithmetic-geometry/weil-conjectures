/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.PolarizedSchemeEtaleDescentData

/-! # The underlying scheme of polarized descent

Source: Stacks Project, Spaces, Tags 02WW and 02WV; Spaces Descent, Tags 04W8 and 0D3C
(blueprint: lem-trf-polarized-scheme-charts).
-/

@[expose] public section

set_option autoImplicit false

universe u v

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- The scheme part of polarized effectivity, with every prescribed transition retained.
No global ordinary module or module comparison is asserted here.

Source: Stacks Project, Spaces, Tags 02WW and 02WV; Spaces Descent, Tags 04W8 and 0D3C
(blueprint: lem-trf-polarized-scheme-charts).

Proof:
1. Choose, for each point of S, a member of the covering and a point above it.
   This gives a subfamily indexed in the scheme universe, still covering S. Restrict
   theta, lambda, the diagonal identities and the test-scheme cocycles to it.
2. Form the coproduct of its X charts and overlaps. Apply
   SchemeDescentCocycle.etale_relation: an overlap with equal base coordinates factors
   through the diagonal by pullback uniqueness, and the supplied four-map cocycle
   gives its three-map cocycle by constructing the fourth map with the pullback lift.
   The quotient sheaf of this small etale relation is an algebraic space by
   AlgebraicSpace.etale_relation_quotient, with the prescribed kernel pair.
3. Apply scheme_descent_quotient_chart_isomorphism to recover the subfamily charts.
   For an arbitrary original index, base change to that U_i. Its overlaps with the
   subfamily cover U_i, and theta identifies the local quotient charts with the
   base changes of X_i. The cocycle makes these identifications agree; representable
   sheaf gluing makes them a unique isomorphism. Thus all original indices are retained.
4. Descend lambda on the small atlas by exists_lineModule_of_etale_descent. The
   identity and cocycle are exactly the given ones after the canonical tensor
   comparisons. Its ordinary restriction on each chart is the given L_i.
5. The given ampleness over inverse images of affine base opens verifies
   representable_and_ample_of_etale_cover. The identity scheme test represents the
   algebraic space by Y over S. Transport its chart identifications to obtain e.
   Their kernel-pair identification gives the displayed theta equation. This argument
   also covers empty S and empty covers: their quotient and Y are empty. -/
theorem exists_polarizedSchemeCharts
    {S : Scheme.{u}} {I : Type v} {U : I → Scheme.{u}}
    {uMap : ∀ i, U i ⟶ S} {X : I → Scheme.{u}} {f : ∀ i, X i ⟶ U i}
    {L : ∀ i, (X i).Modules} {hL : ∀ i, Scheme.Modules.IsInvertible (L i)}
    (D : PolarizedSchemeEtaleDescentDatum S I U uMap X f L hL)
    : ∃ (Y : Scheme.{u}) (g : Y ⟶ S) (e : ∀ i, pullback g (uMap i) ≅ X i),
      (∀ i, (e i).hom ≫ f i = pullback.snd g (uMap i)) ∧
        ∀ i j,
          polarizedOverlapX U uMap X f i j ≫ (e i).inv ≫ pullback.fst g (uMap i) =
            (D.theta i j).hom ≫ polarizedOverlapX U uMap X f j i ≫
              (e j).inv ≫ pullback.fst g (uMap j) := by sorry

end AlgebraicGeometry
