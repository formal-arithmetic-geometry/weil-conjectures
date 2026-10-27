module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.Algebra.Field.Defs

import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.AlgebraicGeometry.OpenImmersion
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyInjective
import Sheaf.AlgebraicGeometry.ProEtaleFiniteLocalSystemsType

/-! # Monomorphisms into coproducts of field spectra

Source: Stacks Project, Schemes, Tag 03DP, `lemma-mono-towards-spec-field`,
final arbitrary-disjoint-union assertion
(blueprint: lem-sfb-monomorphism-into-field-coproduct).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- A monomorphism into a disjoint union of field spectra identifies its source with the
coproduct of a subset of those same field spectra, compatibly with the component inclusions.
The index set and the selected subset may be empty or infinite.

Source: Stacks Project, Schemes, Tag 03DP, `lemma-mono-towards-spec-field`, final assertion
(blueprint: lem-sfb-monomorphism-into-field-coproduct).

Proof: The coprojections have pairwise disjoint clopen images covering the target
(`lem-weil-pbc-scheme-coproduct-family`). Pull these opens back to the source. The induced
map from each piece to its field spectrum exists by
`lem-weil-pbc-morphism-factors-through-open-subscheme` and is monic by cancellation with
the given monomorphism and `lem-weil-pbc-open-immersion-monomorphism`.
By the field-point criterion in `def-weil-radicial-morphism`, each such map is universally
injective. Thus its source has at most one point. A nonempty piece is affine by
`lem-weil-pbc-affine-opens-basis`, since an affine neighbourhood of its point is the whole
piece. The corresponding ring map from the field is epic: contravariance and faithfulness
of Spec turn cancellation for scheme morphisms into cancellation for ring maps
(`def-weil-affine-spectrum`). By `lem-sfb-field-ring-epimorphism-trivial-or-iso`, its target
ring is zero or the map is an isomorphism. Nonemptiness excludes the zero ring, whose
spectrum has no prime ideals. Therefore every nonempty piece maps isomorphically to its
field spectrum. Select exactly the indices of these nonempty pieces. Their inclusions
present the source as a coproduct by `det-pe-finite-local-systems-type-coproduct`.
Use these isomorphisms and the two coproduct universal properties to construct inverse
maps between the source and the selected field coproduct. Their composites are identities
on every component; their compatibility with the original map is likewise checked on
coprojections. This argument also covers both empty index sets and infinite families. -/
theorem monomorphism_into_field_coproduct
    (I : Type u) (k : I → Type u) [∀ i : I, Field (k i)]
    (T : Scheme.{u}) (m : T ⟶ ∐ (fun i : I ↦ Spec (CommRingCat.of (k i)))) [Mono m] :
    ∃ (J : Set I) (e : T ≅ ∐ (fun j : J ↦ Spec (CommRingCat.of (k j.val)))),
      e.hom ≫ Sigma.desc (fun j : J ↦
        Sigma.ι (fun i : I ↦ Spec (CommRingCat.of (k i))) j.val) = m := by
  sorry

end AlgebraicGeometry
