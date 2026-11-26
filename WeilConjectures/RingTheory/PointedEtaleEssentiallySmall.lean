/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.RingTheory.IsStrictHenselization
public import Mathlib.CategoryTheory.EssentiallySmall

import Mathlib.Algebra.Category.CommAlgCat.FiniteType
import Mathlib.CategoryTheory.Comma.StructuredArrow.Small

/-!
# Essential smallness of pointed etale algebras

The category of étale `R`-algebras pointed into a fixed `K` is essentially small.

## Implementation details

The category embeds fully faithfully into the costructured arrow category of `FGAlgCat R` over
`CommAlgCat.of R K`, which is essentially small by Mathlib.

## References

* [Stacks, Tag 04GW]
-/

@[expose] public section
universe u
open CategoryTheory
namespace Algebra

/-- The category of étale `R`-algebras pointed into a fixed `K` is essentially small. -/
theorem pointedEtale_essentiallySmall
    (R K : Type u) [CommRing R] [IsLocalRing R] [Field K]
    [Algebra (IsLocalRing.ResidueField R) K]
    [IsSepClosure (IsLocalRing.ResidueField R) K] [Algebra R K]
    [IsScalarTower R (IsLocalRing.ResidueField R) K] :
    let P : ObjectProperty (Over (CommAlgCat.of R K)) := fun X ↦ Etale R X.left
    EssentiallySmall.{u} P.FullSubcategory := by
  let P : ObjectProperty (Over (CommAlgCat.of R K)) := fun X ↦ Etale R X.left
  let Q : ObjectProperty (CommAlgCat R) := fun A ↦ FiniteType R A
  let F : P.FullSubcategory ⥤ CostructuredArrow Q.ι (CommAlgCat.of R K) :=
    { obj := fun A ↦
        CostructuredArrow.mk (Y := (⟨A.obj.left, by
          have : Etale R A.obj.left := A.property
          infer_instance⟩ : Q.FullSubcategory)) A.obj.hom
      map := fun f ↦ CostructuredArrow.homMk (ObjectProperty.homMk f.hom.left)
        (Over.w f.hom) }
  have hF : F.FullyFaithful :=
    { preimage := fun f ↦ ObjectProperty.homMk
        (Over.homMk f.left.hom (CostructuredArrow.w f)) }
  have : F.Full := hF.full
  have : F.Faithful := hF.faithful
  exact essentiallySmall_of_fully_faithful F
end Algebra
