/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.AlgebraicSpace
public import WeilConjectures.AlgebraicGeometry.AlgebraicSpaceAbelianStalk
public import Mathlib.CategoryTheory.Filtered.Basic
public import Mathlib.CategoryTheory.Limits.HasLimits
public import Mathlib.FieldTheory.IsAlgClosed.Basic
import WeilConjectures.AlgebraicGeometry.EtaleFibreDiscreteSeparablePoints
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import WeilConjectures.AlgebraicGeometry.AlgebraicSpaceRepresentableEtaleSchemeTests
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback

/-! # Cofiltered pointed étale scheme neighbourhoods of an algebraic-space point

Source: Stacks Project, Properties of Spaces, Tag 04JW (lemma-cofinal-etale),
restricted to scheme neighbourhoods, and the paragraph following Tag 04JY
(definition-stalk) (blueprint: lem-sfb-space-pointed-etale-neighbourhoods-cofiltered).

The existing `AlgebraicSpace.PointedEtale` is the actual category of pointed scheme
charts, with objects in `Type (u + 1)` and morphisms in `Type u`.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory Opposite

namespace AlgebraicGeometry.AlgebraicSpace

/-- Pointed étale scheme neighbourhoods of a geometric point form a small cofiltered
category in the containing universe; their opposite is filtered.
Source: Stacks Project, Properties of Spaces, Tag 04JW and the paragraph after Tag 04JY
(blueprint: lem-sfb-space-pointed-etale-neighbourhoods-cofiltered).

Proof:
1. The chosen bounded site has its objects in `Type (u + 1)` and hom sets in `Type u`.
   Lifts of the point are scheme homomorphisms over `S`, and pointing conditions are
   equations. The structured-arrow construction is therefore small in `u + 1`, by
   `def-weil-size-convention`. If a site representative is needed, transport the lift
   by the inverse representative isomorphism and conjugate the incident maps.
2. Choose a surjective étale scheme atlas of `X`, using `def-trf-algebraic-space`.
   Its pullback to `Spec Ω` is a nonempty étale scheme over `Ω`. By
   `lem-weil-pbc-etale-fibre-discrete-separable-points`, it has a component `Spec L`
   for a finite separable extension of `Ω`. Every element of `L` belongs to `Ω`:
   its annihilating polynomial splits into linear factors by
   `def-weil-algebraic-closure`, and one factor vanishes in the field `L`.
   Thus that component gives a section of the atlas fibre and a pointed chart.
3. Two pointed charts admit their fibre product over `X`, represented by a scheme
   and étale over `X` by `lem-trf-space-representable-etale-scheme-tests`.
   Their two lifts give the lift to this fibre product and its two pointed projections.
4. For parallel pointed maps `h₁, h₂ : V → U`, the map `(h₁,h₂) : V → U ×_X U`
   is étale by the comparison-map clause of
   `lem-trf-space-representable-etale-scheme-tests`. Pull it back along the diagonal
   `U → U ×_X U` using `def-pc-fibre-product`. The resulting scheme `W` is étale
   over `U` and hence over `X`. The pair of the prescribed lifts of `V` and `U`
   gives a lift to `W`, and `W → V` equalizes `h₁,h₂` by the pullback equation.
   No separatedness or closedness of the diagonal is required.
5. These are precisely nonemptiness, common incoming cones and incoming equalizers,
   the axioms of `IsCofiltered`. Reversing arrows gives `IsFiltered` as in
   `def-weil-pbc-category-colimit`. -/
theorem pointedEtale_small_cofiltered {S : Scheme.{u}} (X : AlgebraicSpace S)
    (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ S)
    (x : yoneda.obj (Over.mk s) ⟶ X.obj.obj) :
    Small.{u + 1} (X.PointedEtale x) ∧ IsCofiltered (X.PointedEtale x) ∧
      IsFiltered (X.PointedEtale x)ᵒᵖ := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
