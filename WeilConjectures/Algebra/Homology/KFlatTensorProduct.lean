/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Algebra.Homology.KFlat
public import Mathlib.Geometry.RingedSpace.SheafedSpace
public import Mathlib.CategoryTheory.Monoidal.Closed.Braided
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorClosed
import Mathlib.Algebra.Homology.Monoidal
public import Mathlib.AlgebraicGeometry.AffineScheme

/-!
# Tensor products of K-flat complexes

## References

* Stacks Project, Cohomology, Lemma 079R
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory TopologicalSpace AlgebraicGeometry

namespace CochainComplex

section

variable {X : SheafedSpace CommRingCat.{u}}

noncomputable local instance instMonoidalCategoryModulesOfKFlatTensorProduct : MonoidalCategory
    (SheafOfModules.{u} ((sheafCompose (Opens.grothendieckTopology (X : Type u))
      (forget₂ CommRingCat.{u} RingCat.{u})).obj X.sheaf)) :=
  SheafOfModules.monoidalCategory X.sheaf

/-- Let `(X, O_X)` be a ringed space. The total tensor product `Tot(K ⊗_{O_X} L)` of two K-flat
complexes of `O_X`-modules is K-flat. -/
theorem IsKFlatTensor.mapBifunctor
    (K L : CochainComplex
      (SheafOfModules.{u} ((sheafCompose (Opens.grothendieckTopology (X : Type u))
        (forget₂ CommRingCat.{u} RingCat.{u})).obj X.sheaf)) ℤ)
    (hK : K.IsKFlatTensor) (hL : L.IsKFlatTensor) :
    (mapBifunctor K L (curriedTensor _)).IsKFlatTensor := by
  let := SheafOfModules.symmetricCategory X.sheaf
  let := (SheafOfModules.tensorClosed X.sheaf).1.some
  let := (SheafOfModules.tensorClosed X.sheaf).2.1.some
  intro M hM i
  exact (hL _ (hK M hM) i).of_iso (HomologicalComplex.associator M K L)

end

end CochainComplex
