/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import WeilConjectures.AlgebraicGeometry.StrictHenselizationStructuralMap
public import WeilConjectures.AlgebraicGeometry.StrictHenselizationExtension
public import Sheaf.AlgebraicGeometry.StrictHenselizationClosedLift
import Sheaf.AlgebraicGeometry.AffineStrictLocalRingComparison
import WeilConjectures.AlgebraicGeometry.StrictHenselizationExtension
import Sheaf.Paper.StrictHenselizationFunctoriality
import WeilConjectures.RingTheory.MapIntoHenselianColimit
import WeilConjectures.RingTheory.PointedEtaleFiltered
import Sheaf.RingTheory.StrictHenselizationPresentationIn
import WeilConjectures.RingTheory.StrictlyHenselianQuotient
import WeilConjectures.AlgebraicGeometry.EtaleLocalRingTriples
import WeilConjectures.AlgebraicGeometry.StrictHenselization

/-!
# Strict localization along a closed immersion

Source: Stacks Project, Tag 05WS
(blueprint: lem-trf-closed-immersion-strict-localization-cartesian).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry

namespace AlgebraicGeometry.Scheme

/-- The strict localization of a closed subscheme is the base change of the ambient
strict localization. Source: Stacks Project, Tag 05WS
(blueprint: lem-trf-closed-immersion-strict-localization-cartesian).

Proof: Choose an affine neighbourhood of the image of the geometric point and write the
closed immersion there as a quotient by an ideal. The affine strict-local comparison
identifies the two strict local rings with the corresponding algebraic strict
henselizations. The quotient of the ambient strict henselization by the extended ideal
is the strict henselization of the quotient ring, by the henselian mapping and
uniqueness statements. The induced isomorphism of affine spectra is the required
isomorphism of the fibre product. This uses
`lem-exc-affine-strict-local-ring-comparison`,
`lem-weil-pbc-etale-local-ring-triples`,
`lem-weil-pbc-strictly-henselian-quotient`,
`lem-sc-pointed-etale-filtered`, and
`lem-weil-pbc-map-into-henselian-colimit`.
-/
theorem isIso_strictHenselizationClosedImmersionCartesian
    {Z W : Scheme.{u}} (i : Z ⟶ W) [IsClosedImmersion i]
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (a : Spec (.of Ω) ⟶ Z) :
    IsIso (pullback.lift (f := i)
      (g := strictHenselizationStructuralMap (a ≫ i))
      (strictHenselizationStructuralMap a)
      (strictHenselizationMap i a)
      (by exact (strictHenselizationMap_over i a).symm)) := by
  sorry

end AlgebraicGeometry.Scheme
