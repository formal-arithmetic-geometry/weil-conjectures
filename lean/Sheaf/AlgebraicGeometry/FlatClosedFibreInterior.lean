/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation

/-! # Empty fibre interior for a flat closed family

Source: Stacks Project, Tag 054X, the argument after generic flatness.
(blueprint: lem-sbc-flat-closed-fibre-interior)
-/

@[expose] public section

universe u
open CategoryTheory Topology
namespace AlgebraicGeometry

/-- Once a family and its closed subfamily are flat and locally finitely presented
on a base open, empty interior in the generic fibre persists on that open.

Source: Stacks Project, Tag 054X, proof after the application of generic flatness;
Tags 03HV and 054U.
Proof: work over U, an integral scheme with generic point eta. If the closed
subfamily has nonempty interior in the fibre at t, this interior contains a
point xi generic in a component of the ambient fibre. In the closed subfamily
it is also generic in a fibre component. Flatness of the closed subfamily
lifts the generalization eta of t to a generalization xi' of xi over eta,
by Tag 03HV. The dimensions at xi of the closed and ambient fibres agree,
since a neighbourhood of xi in the ambient fibre is contained in the closed
subfamily. Tag 054U, applied to the two flat locally finitely presented maps,
identifies each of these dimensions with its value at xi' in the corresponding
generic fibre. A component of the closed generic fibre through xi' therefore
has dimension equal to the ambient local fibre dimension there. Since the
ambient generic fibre is of finite type over a field, a proper closed subset
of every irreducible component has strictly smaller dimension. Thus some
ambient component is contained in the closed generic fibre, contradicting
its empty interior. This proves the assertion. Empty fibres have empty
interior and require no choice of xi. The open U may equal the whole base;
the assertion uses no reducedness of the source or of the closed subfamily.

(blueprint: lem-sbc-flat-closed-fibre-interior) -/
theorem interior_fibre_closed_eq_empty_of_flat_restrict
    {Z X T : Scheme.{u}} [IsIntegral T]
    (f : X ⟶ T) [LocallyOfFiniteType f] [QuasiCompact f]
    (i : Z ⟶ X) [IsClosedImmersion i]
    (η : T) (hη : IsGenericPoint η Set.univ)
    (U : T.Opens) (hηU : η ∈ U)
    [Flat (f ∣_ U)] [LocallyOfFinitePresentation (f ∣_ U)]
    [Flat ((i ≫ f) ∣_ U)] [LocallyOfFinitePresentation ((i ≫ f) ∣_ U)]
    (hgeneric : interior ((f.fiberι η) ⁻¹' Set.range i) = ∅) :
    ∀ t ∈ U, interior ((f.fiberι t) ⁻¹' Set.range i) = ∅ := by sorry

end AlgebraicGeometry
