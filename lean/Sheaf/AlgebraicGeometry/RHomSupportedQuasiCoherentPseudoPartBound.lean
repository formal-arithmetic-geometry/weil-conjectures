module

public import Sheaf.Algebra.Homology.DerivedInternalHom
public import Sheaf.AlgebraicGeometry.PseudoCoherentComplex
import Mathlib.Algebra.Homology.DerivedCategory.TStructure

@[expose] public section

universe u w

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

namespace AlgebraicGeometry

/-- The local lower-bound component of the pseudo-coherent internal-Hom lemma.

Source: Stacks Project, Tag 0A6H, clause (1).
On an affine neighbourhood carrying a bounded-above finite-free model of the source,
the affine Hom-complex estimate gives a lower bound; exact restriction transports it
to the stated neighbourhood. This is split from quasi-coherence to isolate the
cohomological estimate.
(blueprint: new-lem-sc-rhom-supported-qcoherent-pseudo-part-bound). -/
theorem rhom_supported_quasiCoherent_pseudo_part_bound
    (X : Scheme.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [∀ U : X.Opens, HasDerivedCategory.{w}
      (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))]
    (K L : schemeDerivedCategory X)
    (hL : schemeDerivedQCohProperty X L)
    (hK : Scheme.IsPseudoCoherent X K) (hGE : ∃ a : ℤ, L.IsGE a) :
    ∀ x : X, ∃ U : X.Opens, x ∈ U ∧ ∃ a : ℤ, ∀ n : ℤ, n < a →
      IsZero ((SheafOfModules.overFunctor (moduleRings X.toRingedSpace) U).obj
        ((DerivedCategory.homologyFunctor
          (SheafOfModules.{u} (moduleRings X.toRingedSpace)) n).obj
            ((derivedInternalHom (Opens.grothendieckTopology X.toRingedSpace)
              X.toRingedSpace.sheaf).obj (op K, L)))) := by
  sorry

end AlgebraicGeometry
