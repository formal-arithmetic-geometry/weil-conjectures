module

public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
import Sheaf.AlgebraicGeometry.SeparatedOpenInduction

@[expose] public section

universe u

open TopologicalSpace

namespace AlgebraicGeometry

/-- The intersection property needed for quasi-compact open induction.

The overlap of a quasi-compact open with an affine open is separated and quasi-compact;
applying separated quasi-compact open induction proves `P` on the overlap. Source:
literature/stacks-project/coherent.tex, Cohomology of Schemes, Lemma 08DR (blueprint:
lem-sc-invert-s-cohomology-induction), second paragraph.
(blueprint: property-intersection-qc-affine)

Proof: The intersection is quasi-compact by quasi-separatedness and finite affine cover criteria,
and separated as an open subscheme of affine V; apply separated_quasiCompact_open_induction. -/
theorem property_intersection_of_quasiCompact_affine
    (X : Scheme.{u}) [CompactSpace X] [QuasiSeparatedSpace X] (P : X.Opens → Prop)
    (h_affine : ∀ U : X.Opens, IsAffineOpen U → P U)
    (h_union : ∀ (U V : X.Opens), IsCompact (U : Set X) → IsAffineOpen V →
      P U → P V → P (U ⊓ V) → P (U ⊔ V))
    (U V : X.Opens) (hU : IsCompact (U : Set X)) (hV : IsAffineOpen V) :
    P (U ⊓ V) := by
  sorry

end AlgebraicGeometry
