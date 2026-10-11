import Sheaf.Topology.LocallyConstantMapsPresheaf
import Mathlib.Topology.Sheaves.Sheaf

/-!
# Maps out of the sheaf of locally constant maps on a space

Source: Stacks Project, Sites, Example Tag 0H7J and Sheaves, Example Tag 0081,
Definition Tag 006W (blueprint: lem-weil-pbc-constant-sheaf-open-maps-sections).
-/

set_option autoImplicit false

universe u v

open CategoryTheory Opposite TopologicalSpace

namespace TopCat

/-- Morphisms out of the sheaf of locally constant maps to `T` into a sheaf of sets `G`
correspond bijectively to maps `T → G(X)`, via `φ ↦ (t ↦ φ_X(const_t))`. Morphisms of
sheaves are the morphisms of the underlying presheaves (full subcategory). Naturality in
`G` holds by definition of composition and is not restated.
Source: Stacks Project, Sites, Example Tag 0H7J; Sheaves, Example Tag 0081, Definition
Tag 006W. Proof: the fibres of a locally constant map form an open partition and
`G(∅)` is a point; injectivity by separatedness, surjectivity by gluing `ψ(t)` over the
fibres.
(blueprint: lem-weil-pbc-constant-sheaf-open-maps-sections) -/
theorem locallyConstantMapsPresheaf_hom_bijective (X : TopCat.{u}) (T : Type v)
    (G : TopCat.Sheaf (Type (max u v)) X) :
    Function.Bijective
      (fun (φ : locallyConstantMapsPresheaf X T ⟶ G.obj) (t : T) =>
        φ.app (op ⊤) (LocallyConstant.const _ t)) := by
  sorry

end TopCat
