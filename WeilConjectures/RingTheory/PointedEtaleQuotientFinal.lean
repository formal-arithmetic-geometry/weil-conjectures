/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.RingTheory.IsStrictHenselization
public import WeilConjectures.RingTheory.SurjectiveQuotientBaseChange
public import Mathlib.CategoryTheory.Limits.Final
import WeilConjectures.RingTheory.PointedEtaleQuotientPoint
import WeilConjectures.RingTheory.PointedEtaleQuotientCommaNonempty
import WeilConjectures.RingTheory.PointedEtaleQuotientCommaRefinement

/-! # Finality of pointed etale base change

Base change of pointed étale algebras along a surjective local homomorphism is a final functor.

## Implementation details

Every comma category `(T ↓ F)` is nonempty by the coefficient-lift theorem, and any two of its
objects have a common successor, obtained from filteredness of source and target and the relative
étale lifting lemma. The connected-comma criterion then gives finality. No strict henselization
or colimit hypothesis is used. This is the pointed-algebra argument used in
`IsStrictHenselization.surjective_quotient`.

## References

* [Stacks, Tag 05WS]
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits
namespace Algebra

/-- Base change of pointed étale algebras along a surjective local map is final. -/
theorem pointedEtaleQuotient_final
    (A K B L : Type u) [CommRing A] [IsLocalRing A] [Field K]
    [Algebra (IsLocalRing.ResidueField A) K] [IsSepClosure (IsLocalRing.ResidueField A) K]
    [Algebra A K] [IsScalarTower A (IsLocalRing.ResidueField A) K]
    [CommRing B] [IsLocalRing B] [Field L]
    [Algebra (IsLocalRing.ResidueField B) L]
    [IsSepClosure (IsLocalRing.ResidueField B) L]
    [Algebra B L] [IsScalarTower B (IsLocalRing.ResidueField B) L]
    (π : A →+* B) (hπ : Function.Surjective π) :
    let P : ObjectProperty (Over (CommAlgCat.of A K)) := fun X ↦ Etale A X.left
    let Q : ObjectProperty (Over (CommAlgCat.of B L)) := fun X ↦ Etale B X.left
    ∃ F : P.FullSubcategory ⥤ Q.FullSubcategory, F.Final ∧
      Nonempty ((P.ι ⋙ Over.forget (CommAlgCat.of A K)) ⋙ quotientBaseChange π ≅
        F ⋙ (Q.ι ⋙ Over.forget (CommAlgCat.of B L))) := by
  classical
  obtain ⟨c⟩ := pointedEtaleQuotient_point_iso A K B L π hπ
  let F := pointedEtaleBaseChange π c.hom
  refine ⟨F, ?_, ⟨pointedEtaleBaseChange_forgetIso π c.hom⟩⟩
  refine ⟨fun T ↦ ?_⟩
  have : Nonempty (StructuredArrow T F) :=
    pointedEtaleQuotient_comma_nonempty A K B L π hπ c T
  apply zigzag_isConnected
  intro X Y
  obtain ⟨Z, ⟨f⟩, ⟨g⟩⟩ :=
    pointedEtaleQuotient_comma_refinement A K B L π hπ c T X Y
  exact (Relation.ReflTransGen.single (show Zag X Z from Or.inl ⟨f⟩)).trans
    (Relation.ReflTransGen.single (show Zag Z Y from Or.inr ⟨g⟩))

end Algebra
