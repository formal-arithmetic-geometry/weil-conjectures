/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group R2
-/
module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat

/-!
# K-flat base change over commutative rings

Source: Stacks Project, More on Algebra, Tag 06Y1.
(blueprint: lem-pc-kflat-extension-of-scalars)
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory

namespace CochainComplex

/-- Extension of scalars preserves K-flatness without requiring the ring map to be flat.
Source: Stacks Project, More on Algebra, Tag 06Y1.
(blueprint: lem-pc-kflat-extension-of-scalars)

Proof: let `L` be an acyclic complex of `B`-modules. Restriction of scalars along `ρ`
is exact: kernels and images have the same underlying additive groups. Thus the
restricted `L` is acyclic over `A`. On pure tensors the maps
`l ⊗ (b ⊗ k) ↦ (b • l) ⊗ k` and `l ⊗ k ↦ l ⊗ (1 ⊗ k)` give inverse
isomorphisms between tensoring `L` over `B` with the extended `K` and tensoring
restricted `L` over `A` with `K`. They commute with each differential. Applying them
to every summand of total degree `n` gives inverse chain maps, including the sign
on the second differential. K-flatness of `K` makes the latter total complex
acyclic. The isomorphism and exactness of restriction of scalars give acyclicity
of the former total complex. This also covers zero rings and unbounded complexes:
there is no flatness hypothesis and each total degree uses a direct sum. -/
theorem acyclic_mapBifunctor_extendScalars_of_kFlat
    {A B : Type u} [CommRing A] [CommRing B] (ρ : A →+* B)
    (K : CochainComplex (ModuleCat.{u} A) ℤ)
    (hK : ∀ F : CochainComplex (ModuleCat.{u} A) ℤ, F.Acyclic →
      (mapBifunctor F K (curriedTensor _)).Acyclic)
    (L : CochainComplex (ModuleCat.{u} B) ℤ) (hL : L.Acyclic) :
    (mapBifunctor L
      (((ModuleCat.extendScalars ρ).mapHomologicalComplex (.up ℤ)).obj K)
      (curriedTensor _)).Acyclic := by sorry

end CochainComplex
