/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Adjunction.OfBijectiveCounit
public import WeilConjectures.CategoryTheory.Endofunctor.IsoAlgebra

/-!
# Free algebras and transport of algebras

Let `F : C ⥤ C` and `G : D ⥤ D` be autoequivalences, `L : C ⥤ D` a functor and
`e : L ⋙ G ≅ F ⋙ L`, transporting algebras along `L` (`IsoAlgebra.mapOfNatIso e`). The free algebra
`∐ₙ Gⁿ (L S)` maps to the transport `L (∐ₙ Fⁿ S)` of the free algebra on `S`
(`CategoryTheory.Adjunction.freeComparison` for the free–forgetful adjunctions and
`IsoAlgebra.mapOfNatIsoCompForgetIso e`); on the summand `n` it is the iterated exchange
isomorphism `Gⁿ (L S) ≅ L (Fⁿ S)` followed by `L` of the inclusion of `Fⁿ S`. Hence it is an
isomorphism as soon as `L` preserves the coproduct `∐ₙ Fⁿ S`
(`CategoryTheory.Endofunctor.IsoAlgebra.isIso_freeComparison_mapOfNatIso`).
-/

@[expose] public section

open CategoryTheory Limits

namespace CategoryTheory.Endofunctor.IsoAlgebra

variable {C D : Type*} [Category C] [Category D] {F : C ⥤ C} [F.IsEquivalence] {G : D ⥤ D}
  [G.IsEquivalence] [HasColimitsOfShape (Discrete ℤ) C] [HasColimitsOfShape (Discrete ℤ) D]
  {L : C ⥤ D} (e : L ⋙ G ≅ F ⋙ L)

/-- **Free algebras commute with transport along a functor preserving their coproducts.** If `L`
preserves the coproduct `∐ₙ Fⁿ S`, the comparison `∐ₙ Gⁿ (L S) ⟶ L (∐ₙ Fⁿ S)` of the free
algebras is an isomorphism. -/
theorem isIso_freeComparison_mapOfNatIso (S : C)
    [PreservesColimit (Discrete.functor (Free.obj F S)) L] :
    IsIso (Adjunction.freeComparison (Free.adjunction F) (Free.adjunction G) (mapOfNatIso e) L
      (mapOfNatIsoCompForgetIso e) S) :=
  sorry

end CategoryTheory.Endofunctor.IsoAlgebra
