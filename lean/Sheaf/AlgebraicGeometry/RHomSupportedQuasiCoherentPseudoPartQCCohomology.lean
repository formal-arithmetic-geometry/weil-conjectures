module

public import Sheaf.AlgebraicGeometry.PseudoCoherentComplex
public import Sheaf.Algebra.Homology.DerivedInternalHom
import Mathlib.Algebra.Homology.DerivedCategory.TStructure

@[expose] public section

universe u w

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

namespace AlgebraicGeometry

/-- The degreewise quasi-coherence calculation for RHom from a pseudo-coherent complex.

Source: Stacks Project, Tag 0A6H, clause (1), affine-local finite-free calculation.
The proof computes the Hom complex on an affine neighbourhood, identifies its cohomology
with a quasi-coherent module, and transports this identification across the restriction.
(blueprint: new-lem-sc-rhom-supported-qcoherent-pseudo-part-qc-cohomology). -/
theorem rhom_supported_quasiCoherent_pseudo_part_qc_cohomology
    (X : Scheme.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [∀ U : X.Opens, HasDerivedCategory.{w}
      (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))]
    (K L : schemeDerivedCategory X)
    (hL : schemeDerivedQCohProperty X L)
    (hK : Scheme.IsPseudoCoherent X K) (hGE : ∃ a : ℤ, L.IsGE a)
    (n : ℤ) :
    ((DerivedCategory.homologyFunctor
      (SheafOfModules.{u} (moduleRings X.toRingedSpace)) n).obj
      ((derivedInternalHom (Opens.grothendieckTopology X.toRingedSpace)
        X.toRingedSpace.sheaf).obj (op K, L))).IsQuasicoherent := by
  sorry

end AlgebraicGeometry
