/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q61
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Sheaf.AlgebraicGeometry.AlgebraicSpace
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceMorphismProperties
import Sheaf.AlgebraicGeometry.SpaceLocalPropertiesChartTest

/-! # The diagonal of an algebraic-space morphism is locally of finite type

Source: Stacks Project, Morphisms of Spaces, Tag 03HK (lemma-properties-diagonal),
parts (1) and (2) (blueprint: lem-sfb-space-diagonal-locally-finite-type).

The base is Spec ℤ in the chosen scheme universe. Representability is tested on all
schemes, and local finite type uses the existing universal étale chart predicate.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.AlgebraicSpace

/-- Every morphism of algebraic spaces over Spec ℤ has a representable diagonal that is
locally of finite type on étale scheme charts. No finiteness or separation is assumed.

Source: Stacks Project, Morphisms of Spaces, Tag 03HK, parts (1) and (2), with
Spaces, Tag 025V (blueprint: lem-sfb-space-diagonal-locally-finite-type).

Proof: (1) Apply [lem-sfb-space-diagonal-scheme-tests] with base Spec ℤ. For every
scheme T mapping to W = U ×_V U it supplies a representing scheme D_T for U ×_W T,
whose projection to T is locally of finite type. The existence of these representing
schemes is exactly `IsRepresentable` from [def-trf-algebraic-space].
(2) The sheaf W is an algebraic space by [lem-trf-space-fibre-products-etale-covers].
Choose a surjective étale scheme atlas T → W using [def-trf-algebraic-space]. The
scheme D_T of step (1) is a source chart for the diagonal after this target base change;
use its identity as the surjective étale chart of the pullback. Apply
[lem-sfb-space-local-properties-chart-test] with P = locally of finite type. Its scheme
map is precisely D_T → T, already locally of finite type by step (1), so it gives
`MapIsLocally (@LocallyOfFiniteType)` for the diagonal. The same identity-chart argument
allows empty D_T and T; it requires no finiteness or separation hypothesis. -/
theorem diagonal_representable_and_locallyOfFiniteType
    {U V : AlgebraicSpace (Spec (CommRingCat.of (ULift.{u} ℤ)))} (g : U ⟶ V) :
    IsRepresentable (Limits.pullback.diagonal g.hom.hom) ∧
      MapIsLocally (@LocallyOfFiniteType)
        (Y := ⟨Limits.pullback g.hom g.hom, (fibreProduct_isAlgebraicSpace U U V g g).1⟩)
        (ObjectProperty.homMk (Limits.pullback.diagonal g.hom)) := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
