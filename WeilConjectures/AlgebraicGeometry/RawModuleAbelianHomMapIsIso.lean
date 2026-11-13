/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.RawModuleAbelianHomMap
import WeilConjectures.AlgebraicGeometry.RawModuleAbelianHomMapInjective
import WeilConjectures.AlgebraicGeometry.RawModuleAbelianHomMapSurjective

/-! # Invertibility of the fixed raw scalar comparison

## References

* [Stacks Project, Tag 03FD](https://stacks.math.columbia.edu/tag/03FD)
-/

@[expose] public section

universe u
open CategoryTheory Limits Opposite
open scoped CategoryTheory.Functor AlgebraicGeometry.Etale
namespace AlgebraicGeometry.Etale

/-- Forgetting the raw class induces an additive bijection. -/
theorem isIso_rawModuleAbelianHomMap
    (Λ : Type (u + 1)) [CommRing Λ] {W S : Scheme.{u}} (k : W ⟶ S)
    (G : Sheaf W.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (q : ℕ)
    (U : S.Etale) (A : Over W) :
    IsIso (rawModuleAbelianHomMap Λ k G q U A) := by
  apply (ConcreteCategory.isIso_iff_bijective _).2
  exact ⟨rawModuleAbelianHomMap_injective Λ k G q U A,
    rawModuleAbelianHomMap_surjective Λ k G q U A⟩

end AlgebraicGeometry.Etale
