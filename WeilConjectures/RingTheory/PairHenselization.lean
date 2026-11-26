/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import Mathlib.CategoryTheory.EssentiallySmall
public import Mathlib.CategoryTheory.Filtered.Basic
public import WeilConjectures.Mathlib.RingTheory.Henselian
import WeilConjectures.RingTheory.PairHenselizationEssentiallySmall
import WeilConjectures.RingTheory.PairHenselizationFiltered
import WeilConjectures.RingTheory.PairHenselizationColimit

/-!
# Henselization of a pair

The henselization of a pair `(B, J)` is the colimit of the étale `B`-algebras which are trivial
modulo `J`.

## Implementation details

The full subcategory of `Under (CommRingCat.of B)` has precisely the prescribed objects; its
morphisms are all `B`-algebra maps. It is essentially small by finite presentation and filtered:
tensor products give common successors, and the tensor-product coequalizer
`(C' ⊗[C] C') ⊗[C' ⊗[B] C'] C'` equalizes parallel maps. The colimit is henselian: an étale
algebra with a section modulo the ideal descends to a stage, and splitting the section by a
lifted idempotent gives a localization which is an object of the diagram.

## References

* [Stacks, Tag 0A02]
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace RingTheory

/-- The henselization of a pair `(B, J)` exists as the colimit of the étale `B`-algebras `C` with
`B / J ≅ C / J C`. The diagram is the full subcategory of `Under (CommRingCat.of B)` on these
objects, and the cocone is taken in that under category. -/
theorem pair_henselization (B : Type u) [CommRing B] (J : Ideal B) :
    EssentiallySmall.{u} (ObjectProperty.FullSubcategory
      (fun C : Under (CommRingCat.of B) ↦
        AlgebraicGeometry.Etale (AlgebraicGeometry.Spec.map C.hom) ∧
          Function.Bijective (Ideal.quotientMap (J.map C.hom.hom) C.hom.hom
            (Ideal.le_comap_map)))) ∧
    IsFiltered (ObjectProperty.FullSubcategory
      (fun C : Under (CommRingCat.of B) ↦
        AlgebraicGeometry.Etale (AlgebraicGeometry.Spec.map C.hom) ∧
          Function.Bijective (Ideal.quotientMap (J.map C.hom.hom) C.hom.hom
            (Ideal.le_comap_map)))) ∧
    ∃ c : Cocone (ObjectProperty.ι
      (fun C : Under (CommRingCat.of B) ↦
        AlgebraicGeometry.Etale (AlgebraicGeometry.Spec.map C.hom) ∧
          Function.Bijective (Ideal.quotientMap (J.map C.hom.hom) C.hom.hom
            (Ideal.le_comap_map)))),
      Nonempty (IsColimit c) ∧
        HenselianRing c.pt.right (J.map c.pt.hom.hom) ∧
        Function.Bijective (Ideal.quotientMap (J.map c.pt.hom.hom) c.pt.hom.hom
          (Ideal.le_comap_map)) := by
  exact ⟨pair_henselization_essentiallySmall B J,
    pair_henselization_filtered B J, pair_henselization_colimit B J⟩

end RingTheory
