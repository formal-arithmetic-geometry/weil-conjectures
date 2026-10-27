/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NC
-/
module

public import Sheaf.AlgebraicGeometry.AlgebraicSpacePointClasses
public import WeilConjectures.Mathlib.Topology.KrullDimension

/-!
# Dimension from local dimensions in étale scheme charts

Source: Stacks Project, spaces-properties.tex, definition-dimension-at-point and
definition-dimension (blueprint: def-sfb-algebraic-space-etale-dimension).

Taking the supremum over all charts makes the construction explicit without choosing one.
For algebraic spaces every point has a chart, and the chart values agree by étale descent
of local topological dimension. These formulas also define values for arbitrary presheaves.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry.AlgebraicSpace

/-- Local dimension computed by étale scheme charts above the specified point class.
For an algebraic space this supremum is the common value in every such chart.
Scheme local dimension is the infimum of the dimensions of its open neighbourhoods.
Source: Stacks, spaces-properties.tex, definition-dimension-at-point
(blueprint: def-sfb-algebraic-space-etale-dimension). -/
def etaleLocalDimension {S : Scheme.{u}} (F : (Over S)ᵒᵖ ⥤ Type u)
    (x : Point F) : WithBot ℕ∞ :=
  ⨆ (T : Over S) (a : yoneda.obj T ⟶ F) (_ : IsEtale a)
    (t : T.left) (_ : schemePointMap a t = x), topologicalKrullDimAt t

/-- The dimension is the supremum of the local dimensions over all point classes.
In particular the empty space has dimension bottom. No atlas is chosen.
Source: Stacks, spaces-properties.tex, definition-dimension
(blueprint: def-sfb-algebraic-space-etale-dimension). -/
def etaleDimension {S : Scheme.{u}} (F : (Over S)ᵒᵖ ⥤ Type u) : WithBot ℕ∞ :=
  ⨆ x : Point F, etaleLocalDimension F x

end AlgebraicGeometry.AlgebraicSpace
