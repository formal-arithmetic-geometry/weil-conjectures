module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Properties

import Mathlib.AlgebraicGeometry.StructureSheaf
import Mathlib.AlgebraicGeometry.FunctionField
import Mathlib.Topology.Irreducible

/-!
# Integrality from a pairwise intersecting affine domain cover

Source: Stacks Project, Tags 01OL, 01OM and 01ON, `properties.tex`,
lemmas `characterize-reduced`, `characterize-irreducible` and `characterize-integral`
(blueprint: lem-per-integral-affine-cover-criterion).
-/

@[expose] public section

universe u v

open CategoryTheory

namespace AlgebraicGeometry

/-- A scheme covered by spectra of integral domains with pairwise nonempty intersections
is integral. No separatedness or finiteness hypothesis is needed.

Source: Stacks Project, Tags 01OL, 01OM and 01ON
(blueprint: lem-per-integral-affine-cover-criterion).

Proof: By `lem-weil-pbc-spec-domain-stalks-function-field` (2), each `Spec (A i)` is
integral. Transport this across `e i` to the open subscheme `(V i).toScheme`.
The equivalence in `def-pc-integral-scheme` makes each member nonempty, reduced and
irreducible. Apply `lem-trf-reduced-scheme-open-cover` to deduce reducedness of `Y`.
Choose an index `i₀`; its nonempty open also witnesses nonemptiness of `Y`.
For irreducibility as in `def-weil-irreducible-components`, suppose `Y = Z₁ ∪ Z₂`
with both subsets closed. Irreducibility puts `V i₀` in one of them, say `Z₁`.
For every `j`, the nonempty open `V i₀ ∩ V j` of `V j` is contained in `Z₁`.
If `V j` were not contained in `Z₁`, its complement of `Z₁` would be a disjoint
nonempty open in `V j`. The two proper closed complements would cover `V j`,
contradicting irreducibility. Thus every `V j` lies in `Z₁`; the covering gives
`Y = Z₁`. Finally reducedness and irreducibility imply integrality by
`def-pc-integral-scheme`. No intersection is assumed affine. -/
theorem isIntegral_of_pairwise_intersecting_affine_cover
    (Y : Scheme.{u}) (I : Type v) [Nonempty I]
    (V : I → Y.Opens) (A : I → CommRingCat.{u})
    (e : ∀ i : I, (V i).toScheme ≅ Spec (A i))
    (hcover : iSup V = ⊤) (hDomain : ∀ i : I, IsDomain (A i))
    (hinter : ∀ i j : I, ((V i : Set Y) ∩ (V j : Set Y)).Nonempty) :
    IsIntegral Y := by
  sorry

end AlgebraicGeometry
