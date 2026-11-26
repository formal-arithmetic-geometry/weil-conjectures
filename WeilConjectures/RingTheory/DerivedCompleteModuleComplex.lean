/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Homology.DerivedCategory.Linear
public import Mathlib.RingTheory.Ideal.Defs
public import WeilConjectures.CategoryTheory.Triangulated.DerivedLimit

/-!
# Derived completeness of module complexes

This file defines derived completeness of objects of `D(A)` and of `A`-modules with respect to
an ideal, using the derived limit `T(K, f)` of multiplication-by-`f` towers.

## Implementation details

The definition quantifies over product structures, so the Roos-triangle condition can be
expressed without choosing a product or imposing an additional product hypothesis.

## References

* [Stacks, Tag 091N]
* [Stacks, Tag 091S]
-/

@[expose] public section

universe u v w

open CategoryTheory CategoryTheory.Limits

namespace DerivedCategory

/-- An object of `D(A)` is derived complete for `I` when every derived limit of the
constant tower with transition multiplication by `f` is zero, for every `f ∈ I`. -/
noncomputable def IsDerivedComplete {A : Type u} [CommRing A]
    [HasDerivedCategory.{w} (ModuleCat.{v} A)] (I : Ideal A)
    (K : DerivedCategory (ModuleCat.{v} A)) : Prop :=
  ∀ (f : A), f ∈ I → ∀ [HasProduct (fun _ : ℕ ↦ K)]
    (T : DerivedCategory (ModuleCat.{v} A)),
      IsDerivedLimit (K := fun _ : ℕ ↦ K) (fun _ ↦ f • 𝟙 K) T → IsZero T

end DerivedCategory

namespace ModuleCat

/-- A module is derived complete for `I` if its complex concentrated in degree zero is
derived complete. -/
noncomputable def IsDerivedComplete {A : Type u} [CommRing A]
    [HasDerivedCategory.{w} (ModuleCat.{v} A)] (I : Ideal A) (M : ModuleCat.{v} A) : Prop :=
  DerivedCategory.IsDerivedComplete I ((DerivedCategory.singleFunctor (ModuleCat.{v} A) 0).obj M)

end ModuleCat
