/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group G1
-/
module

public import Sheaf.Algebra.Homology.KFlat
public import Mathlib.Geometry.RingedSpace.SheafedSpace

/-!
# Tensor products of K-flat complexes

Source: Stacks Project, Cohomology, Lemma 079R
(blueprint: lem-pc-kflat-tensor-product).
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory TopologicalSpace AlgebraicGeometry

namespace CochainComplex

section

variable {X : SheafedSpace CommRingCat.{u}}

noncomputable local instance : MonoidalCategory
    (SheafOfModules.{u} ((sheafCompose (Opens.grothendieckTopology (X : Type u))
      (forget₂ CommRingCat.{u} RingCat.{u})).obj X.sheaf)) :=
  SheafOfModules.monoidalCategory X.sheaf

/-- (blueprint: lem-pc-kflat-tensor-product) Stacks Project, Cohomology, Lemma 079R.
Let `(X, O_X)` be a ringed space. The total tensor product `Tot(K ⊗_{O_X} L)` of two K-flat
complexes of `O_X`-modules is K-flat.

Proof: For any acyclic complex `M`, K-flatness of `K` makes `Tot(M ⊗ K)` acyclic.
K-flatness of `L` then makes `Tot(Tot(M ⊗ K) ⊗ L)` acyclic. The canonical associativity
isomorphism of total tensor complexes identifies this with `Tot(M ⊗ Tot(K ⊗ L))`, including
the Koszul signs. Hence `Tot(K ⊗ L)` is K-flat. -/
theorem IsKFlat.mapBifunctor
    (K L : CochainComplex
      (SheafOfModules.{u} ((sheafCompose (Opens.grothendieckTopology (X : Type u))
        (forget₂ CommRingCat.{u} RingCat.{u})).obj X.sheaf)) ℤ)
    (hK : K.IsKFlat) (hL : L.IsKFlat) :
    (mapBifunctor K L (curriedTensor _)).IsKFlat := by
  sorry

end

end CochainComplex
