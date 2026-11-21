/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Flat
public import WeilConjectures.Algebra.Homology.KFlat
import WeilConjectures.Mathlib.Algebra.Homology.TotalComplex
import WeilConjectures.Algebra.Homology.BoundedAboveFlatTensorAcyclicDegree

/-!
# Tensoring bounded-above acyclic complexes with bounded-above flat complexes

## References

* Stacks Project, Cohomology on Sites, Lemma 21.17.8 (Tag 06YQ) (bounded-above case)
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory Limits

namespace CochainComplex

variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}] [HasWeakSheafify J AddCommGrpCat.{u}]
  {R : Sheaf J CommRingCat.{u}}

/-- If `A` is bounded above and acyclic, and `P` is bounded above with flat terms,
then their total tensor complex is acyclic. The tensor is the sheaf tensor product
in `SheafOfModules.monoidalCategory R`. -/
theorem acyclic_mapBifunctor_of_boundedAbove_flat_sheaf
    (A P : CochainComplex
      (SheafOfModules.{u}
        ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R)) ℤ)
    (hAbounded : ∃ a : ℤ, ∀ i : ℤ, a < i → IsZero (A.X i))
    (hPbounded : ∃ b : ℤ, ∀ i : ℤ, b < i → IsZero (P.X i))
    (hPflat : ∀ i : ℤ, SheafOfModules.IsFlat (P.X i)) :
    A.Acyclic →
      (letI := SheafOfModules.monoidalCategory R
       mapBifunctor A P (curriedTensor _)).Acyclic := by
  intro hA n
  exact isZero_homology_mapBifunctor_of_boundedAbove_flat_sheaf A P hAbounded hPbounded
    hPflat hA n

end CochainComplex
