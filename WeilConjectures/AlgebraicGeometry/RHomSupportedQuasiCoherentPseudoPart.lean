/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.PseudoCoherentComplex
public import WeilConjectures.Algebra.Homology.DerivedInternalHom
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
import WeilConjectures.AlgebraicGeometry.RHomSupportedQuasiCoherentPseudoPartQC
import WeilConjectures.AlgebraicGeometry.RHomSupportedQuasiCoherentPseudoPartBound

/-! # PseudoPart of derived internal Hom

## References

* [Stacks Project, Tag 0A6H](https://stacks.math.columbia.edu/tag/0A6H)
-/

@[expose] public section

universe u w

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

namespace AlgebraicGeometry

/-- Pseudo-coherent internal Hom is quasi-coherent and locally bounded below. -/
theorem rhom_supported_quasiCoherent_pseudo_part
    (X : Scheme.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [∀ U : X.Opens, HasDerivedCategory.{w}
      (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))]
    (K L : schemeDerivedCategory X)
    (hL : schemeDerivedQCohProperty X L)
    (hK : Scheme.IsPseudoCoherent X K) (hGE : ∃ a : ℤ, L.IsGE a) :
    schemeDerivedQCohProperty X
        ((derivedInternalHom (Opens.grothendieckTopology X.toRingedSpace)
          X.toRingedSpace.sheaf).obj (op K, L)) ∧
      ∀ x : X, ∃ U : X.Opens, x ∈ U ∧ ∃ a : ℤ, ∀ n : ℤ, n < a →
        IsZero ((SheafOfModules.overFunctor.{u} (moduleRings X.toRingedSpace) U).obj
          ((DerivedCategory.homologyFunctor
            (SheafOfModules.{u} (moduleRings X.toRingedSpace)) n).obj
              ((derivedInternalHom (Opens.grothendieckTopology X.toRingedSpace)
                X.toRingedSpace.sheaf).obj (op K, L)))) := by
  exact ⟨rhom_supported_quasiCoherent_pseudo_part_qc X K L hL hK hGE,
    rhom_supported_quasiCoherent_pseudo_part_bound X K L hL hK hGE⟩

end AlgebraicGeometry
