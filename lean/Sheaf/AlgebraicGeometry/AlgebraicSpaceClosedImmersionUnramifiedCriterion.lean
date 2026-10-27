/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q03
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Sheaf.AlgebraicGeometry.AlgebraicSpace
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers
public import Sheaf.AlgebraicGeometry.AlgebraicSpacePointTopology
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceMorphismProperties
public import Sheaf.AlgebraicGeometry.UnramifiedMorphism
import Sheaf.AlgebraicGeometry.AlgebraicSpacePointClasses
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyInjective

/-! # Closed immersions among universally closed morphisms of algebraic spaces

Source: Stacks Project, More on Morphisms of Spaces, Tag 05W8, equivalence of (1) and (3)
with universal closedness fixed
(blueprint: lem-sfb-space-closed-immersion-unramified-criterion).

Closed immersion uses the existing representable scheme-test predicate. Unramifiedness
uses the existing scheme predicate on every compatible pair of etale scheme charts.
Universal injectivity is written on the existing point classes of every sheaf base change.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.AlgebraicSpace

/-- A universally closed map of algebraic spaces is a closed immersion exactly when it is
unramified on etale scheme charts and injective on points after every space base change.
Source: Stacks Project, Tag 05W8, (1) iff (3), using Tags 05W6 and 04XV
(blueprint: lem-sfb-space-closed-immersion-unramified-criterion).

Proof: (1) For a closed immersion, every scheme base change is a closed immersion.
Universal closedness passes to these scheme tests by
[def-sfb-space-morphism-properties]. Apply the scheme criterion
[lem-sfb-universally-closed-unramified-radicial-criterion] to see that all these maps are
unramified and universally injective.
(2) Pull back a surjective etale scheme atlas of the target. Representability makes its
pullback a scheme, and [lem-trf-space-fibre-products-etale-covers] makes the source chart
surjective etale. The scheme map is unramified by (1), so
[lem-sfb-unramified-etale-compatible-charts] yields the chart test for the original map.
(3) For any algebraic-space base change, two point classes with the same target point
admit common-field representatives with equal target components, by
[def-a1-algebraic-space-point-classes]. Their source components are points over the identity
of Spec K in the scheme fibre over that K-point of the target. Scheme universal injectivity
from (1), and its field-valued criterion [def-weil-radicial-morphism], make them equal.
The sheaf fibre-product identity of [lem-trf-space-fibre-products-etale-covers] then makes
their point classes equal. This proves universal injectivity for algebraic-space tests.
(4) Conversely, unramifiedness and universal injectivity imply representability by
[lem-sfb-space-unramified-radicial-representable]. Every scheme base change is unramified
by [lem-sfb-space-unramified-permanence]; identity charts and
[lem-sfb-unramified-etale-compatible-charts] identify this with scheme unramifiedness.
Its further scheme base changes are universally closed and injective by the hypotheses
on all algebraic-space base changes. Apply
[lem-sfb-universally-closed-unramified-radicial-criterion] to each scheme test. Each is a
closed immersion, which is exactly the representable closed-immersion predicate. -/
theorem isClosedImmersion_iff_unramified_universallyInjective
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} (g : X ⟶ Y)
    (hg : MapIsUniversallyClosed g) :
    IsRepresentableWith (fun _ _ p ↦ IsClosedImmersion p.left) g.hom.hom ↔
      MapIsLocally (@IsUnramified) g ∧
        ∀ (Y' : AlgebraicSpace S) (h : Y' ⟶ Y),
          Function.Injective (mapPoint (pullback.snd g.hom h.hom).hom) := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
