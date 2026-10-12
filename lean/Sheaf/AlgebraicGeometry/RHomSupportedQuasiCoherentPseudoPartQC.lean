module

public import Sheaf.Algebra.Homology.DerivedInternalHom
public import Sheaf.AlgebraicGeometry.PseudoCoherentComplex
import Mathlib.Algebra.Homology.DerivedCategory.TStructure

@[expose] public section

universe u w

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

namespace AlgebraicGeometry

/-- The quasi-coherence component of the pseudo-coherent internal-Hom lemma.

Source: Stacks Project, Tag 0A6H, clause (1).
The proof is the affine-local finite-free calculation, followed by local gluing of
quasi-coherent cohomology; it is split from the local lower-bound component so that
the two independent conclusions can be proved separately.
(blueprint: new-lem-sc-rhom-supported-qcoherent-pseudo-part-qc). -/
theorem rhom_supported_quasiCoherent_pseudo_part_qc
    (X : Scheme.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [∀ U : X.Opens, HasDerivedCategory.{w}
      (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))]
    (K L : schemeDerivedCategory X)
    (hL : schemeDerivedQCohProperty X L)
    (hK : Scheme.IsPseudoCoherent X K) (hGE : ∃ a : ℤ, L.IsGE a) :
    schemeDerivedQCohProperty X
      ((derivedInternalHom (Opens.grothendieckTopology X.toRingedSpace)
        X.toRingedSpace.sheaf).obj (op K, L)) := by
  sorry

end AlgebraicGeometry
