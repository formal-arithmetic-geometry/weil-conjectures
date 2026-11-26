/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.RingTheory.IsStrictHenselization
public import WeilConjectures.RingTheory.SurjectiveQuotientBaseChange
import Mathlib.RingTheory.RingHom.Etale

/-! # The pointed extension-of-scalars functor

Extension of scalars along `A → B` as a functor between categories of pointed étale algebras.

## Implementation details

The functor is a construction, with no choice of lifted étale algebras; its underlying algebra
diagram is extension of scalars.

## References

* [Stacks, Tag 05WS]
* [Stacks, Tag 00U2]
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits
namespace Algebra

/-- Étaleness is preserved by the pushout defining extension of scalars. -/
theorem quotientBaseChange_etale {A B : Type u} [CommRing A] [CommRing B]
    (π : A →+* B) (S : CommAlgCat.{u} A) (hS : Etale A S) :
    Etale B ((quotientBaseChange π).obj S) := by
  have : (RingHom.toMorphismProperty RingHom.Etale).IsStableUnderCobaseChange :=
    (RingHom.isStableUnderCobaseChange_toMorphismProperty_iff (P := RingHom.Etale)).mpr
      RingHom.Etale.isStableUnderBaseChange
  have h := MorphismProperty.of_isPushout (P := RingHom.toMorphismProperty RingHom.Etale)
    (IsPushout.of_hasPushout
      (CommRingCat.ofHom (algebraMap A S)) (CommRingCat.ofHom π)).flip
    ((RingHom.etale_algebraMap).mpr hS)
  exact (RingHom.etale_algebraMap).mp h

/-- The pointed base-change functor from pointed étale `A`-algebras to pointed étale
`B`-algebras: extend scalars and postcompose the base-changed point with the comparison to `L`. -/
noncomputable def pointedEtaleBaseChange {A K B L : Type u}
    [CommRing A] [CommRing K] [Algebra A K]
    [CommRing B] [CommRing L] [Algebra B L]
    (π : A →+* B) (c : (quotientBaseChange π).obj (CommAlgCat.of A K) ⟶
      CommAlgCat.of B L) :
    ObjectProperty.FullSubcategory (fun X : Over (CommAlgCat.of A K) ↦ Etale A X.left) ⥤
      ObjectProperty.FullSubcategory (fun X : Over (CommAlgCat.of B L) ↦ Etale B X.left) :=
  ObjectProperty.lift _
    ((ObjectProperty.ι (fun X : Over (CommAlgCat.of A K) ↦ Etale A X.left)) ⋙
      Over.post (quotientBaseChange π) ⋙ Over.map c)
    (fun S ↦ quotientBaseChange_etale π S.obj.left S.property)

/-- The underlying algebra diagram of pointed base change is extension of scalars. -/
noncomputable def pointedEtaleBaseChange_forgetIso {A K B L : Type u}
    [CommRing A] [CommRing K] [Algebra A K]
    [CommRing B] [CommRing L] [Algebra B L]
    (π : A →+* B) (c : (quotientBaseChange π).obj (CommAlgCat.of A K) ⟶
      CommAlgCat.of B L) :
    ((ObjectProperty.ι (fun X : Over (CommAlgCat.of A K) ↦ Etale A X.left)) ⋙
      Over.forget (CommAlgCat.of A K)) ⋙ quotientBaseChange π ≅
    pointedEtaleBaseChange π c ⋙
      ((ObjectProperty.ι (fun X : Over (CommAlgCat.of B L) ↦ Etale B X.left)) ⋙
        Over.forget (CommAlgCat.of B L)) := Iso.refl _

end Algebra
