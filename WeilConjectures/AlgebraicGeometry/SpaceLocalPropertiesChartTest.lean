/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SpaceEtalePresentationPropertyCriterion
public import WeilConjectures.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import WeilConjectures.AlgebraicGeometry.SchemeEtaleSourceTargetProperties
import WeilConjectures.AlgebraicGeometry.AlgebraicSpaceRepresentableEtaleSchemeTests

/-! # Local properties detected on étale scheme charts

Source: Stacks Project, Morphisms of Spaces, Tags 03MJ, 03MM, 0410 and 040Y
(blueprint: lem-sfb-space-local-properties-chart-test).

The map from the source chart to the target scheme is the canonical map obtained by
composing with the second fibre-product projection and applying Yoneda's inverse.
The scheme comparison uses the same universal presentation test as `MapIsLocally`.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.AlgebraicSpace

/-- Flatness, local finite presentation and local finite type are detected by every
surjective étale scheme chart of the pullback to a surjective étale target scheme chart.
Identity target charts are allowed when the target is a scheme.

Source: Stacks Project, Morphisms of Spaces, Tag 03MJ and Tags 03MM, 0410, 040Y,
conditions (7) and (8) (blueprint: lem-sfb-space-local-properties-chart-test).

Proof: (1) For each of the three choices of P, apply
[lem-sfb-scheme-etale-source-target-properties] to obtain étale source-and-target locality.
Isomorphism invariance follows from the affine or stalk definitions
[def-weil-flat-morphism, def-sbc-locally-finite-presentation,
def-weil-finite-type-morphism].
(2) The pullback X ×_Y V is an algebraic space by
[lem-trf-space-fibre-products-etale-covers]. Its projection to X is the base change
of b, hence representable surjective étale. Compose this projection with q to obtain
a surjective étale source chart a, using
[lem-trf-space-representable-etale-scheme-tests]. The second projection gives the
canonical scheme map h:U → V, and the pullback identity gives a ≫ f = h ≫ b.
(3) The universal presentation condition implies P(h). Conversely P(h) supplies one
presentation with surjective source chart, so the equivalence in
[lem-sfb-space-etale-presentation-property-criterion] gives `MapIsLocally P f`.
(4) Both charts were arbitrary. In particular the identity chart of a scheme target
is representable surjective étale by [lem-trf-space-representable-etale-scheme-tests].
The same argument therefore covers that case, with no compactness or separation input. -/
theorem local_properties_chart_test {S : Scheme.{u}}
    (P : MorphismProperty Scheme.{u})
    (hP : P = @Flat ∨ P = @LocallyOfFinitePresentation ∨ P = @LocallyOfFiniteType)
    {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    (V : Over S) (b : yoneda.obj V ⟶ Y.obj.obj)
    (hb : IsEtale b) (hbs : IsSurjective b)
    (U : Over S) (q : yoneda.obj U ⟶ Limits.pullback f.hom.hom b)
    (hq : IsEtale q) (hqs : IsSurjective q) :
    MapIsLocally P f ↔
      P (yoneda.preimage (q ≫ Limits.pullback.snd f.hom.hom b)).left := by
  sorry

/-- On scheme morphisms, the universal étale chart extension agrees with the original
scheme property, for each of the three indicated properties.

Source: Stacks Project, Morphisms of Spaces, Tag 03MJ, representable-source-and-target
comparison; Tags 03MM, 0410, 040Y
(blueprint: lem-sfb-space-local-properties-chart-test).

Proof: (1) The indicated scheme property is étale local on source-and-target by
[lem-sfb-scheme-etale-source-target-properties] and invariant under isomorphism by
[def-weil-flat-morphism, def-sbc-locally-finite-presentation,
def-weil-finite-type-morphism].
(2) Apply the scheme-comparison clause of
[lem-sfb-space-etale-presentation-property-criterion] to the Yoneda image of f.
The universal presentation condition is exactly `MapIsLocally` expanded on schemes.
Identity charts recover P(f), and locality gives P on every compatible chart diagram.
This also works for empty schemes and imposes no quasi-compactness or separation. -/
theorem local_properties_chart_test_iff_scheme {S : Scheme.{u}}
    (P : MorphismProperty Scheme.{u})
    (hP : P = @Flat ∨ P = @LocallyOfFinitePresentation ∨ P = @LocallyOfFiniteType)
    {X Y : Over S} (f : X ⟶ Y) :
    (∀ D : EtalePresentation (yoneda.map f), P D.h.left) ↔ P f.left := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
