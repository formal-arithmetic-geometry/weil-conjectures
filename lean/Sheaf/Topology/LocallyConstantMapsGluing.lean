module

public import Sheaf.Topology.LocallyConstantMapsPresheaf
public import Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing

@[expose] public section
set_option autoImplicit false
universe w z
open CategoryTheory Opposite TopologicalSpace
namespace TopCat

/-- Compatible locally constant maps on an open cover admit a locally constant gluing.
The proof defines the glued function pointwise and checks local constancy on a member of
 the cover containing each point.
(blueprint: lem-weil-pbc-locally-constant-maps-gluing-exists) -/
theorem locallyConstantMaps_gluing_exists (X : TopCat.{w}) (R : Type z) :
    ∀ {ι : Type w} (U : ι → Opens X)
      (sf : ∀ i, ToType ((locallyConstantMapsPresheaf X R).obj (op (U i)))),
      Presheaf.IsCompatible (locallyConstantMapsPresheaf X R) U sf →
      ∃ s : ToType ((locallyConstantMapsPresheaf X R).obj (op (iSup U))),
        Presheaf.IsGluing (locallyConstantMapsPresheaf X R) U sf s := by
  sorry

end TopCat
