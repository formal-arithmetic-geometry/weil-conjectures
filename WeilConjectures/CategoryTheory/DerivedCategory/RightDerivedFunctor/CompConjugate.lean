/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Adjunction

/-!
# The composition isomorphism of right derived functors is a conjugate

Let `adj₁ : L₁ ⊣ F`, `adj₂ : L₂ ⊣ G` and `adj : L ⊣ H` be adjunctions of additive functors
between abelian categories with exact left adjoints, and let `e : F ⋙ G ≅ H` be the conjugate
of an isomorphism `eL : L ≅ L₂ ⋙ L₁`. Then the composition isomorphism
`RF ⋙ RG ≅ RH` (`CategoryTheory.Functor.rightDerivedFunctorCompIso'`) is the conjugate of the
isomorphism `D(L) ≅ D(L₂) ⋙ D(L₁)` induced by `eL`, under the derived adjunctions
(`CategoryTheory.Adjunction.rightDerivedFunctorCompIso'_hom_eq_conjugateEquiv`).
-/

@[expose] public section

universe v u₁ u₂ u₃

open CategoryTheory Limits Abelian

namespace CategoryTheory.Adjunction

attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits

variable {C : Type u₁} {D : Type u₂} {E : Type u₃} [Category.{v} C] [Category.{v} D] [Category.{v} E]
  [Abelian C] [Abelian D] [Abelian E]
  [HasDerivedCategory C] [HasDerivedCategory D] [HasDerivedCategory E]
  [HasKInjectiveResolutions C] [HasKInjectiveResolutions D]
  {F : C ⥤ D} {G : D ⥤ E} {H : C ⥤ E} [F.Additive] [G.Additive] [H.Additive]
  [F.PreservesKInjectiveComplexes]
  {L₁ : D ⥤ C} {L₂ : E ⥤ D} {L : E ⥤ C} [L₁.Additive] [L₂.Additive] [L.Additive]
  [PreservesFiniteLimits L₁] [PreservesFiniteColimits L₁]
  [PreservesFiniteLimits L₂] [PreservesFiniteColimits L₂]
  [PreservesFiniteLimits L] [PreservesFiniteColimits L]
  (adj₁ : L₁ ⊣ F) (adj₂ : L₂ ⊣ G) (adj : L ⊣ H)

/-- The composition isomorphism `RF ⋙ RG ≅ RH` attached to the conjugate `e` of
`eL : L ≅ L₂ ⋙ L₁` is the conjugate of `D(L) ≅ D(L₂) ⋙ D(L₁)`. -/
lemma rightDerivedFunctorCompIso'_hom_eq_conjugateEquiv (e : F ⋙ G ≅ H) (eL : L ≅ L₂ ⋙ L₁)
    (he : e.hom = conjugateEquiv (adj₂.comp adj₁) adj eL.hom) :
    (Functor.rightDerivedFunctorCompIso' F G e).hom =
      conjugateEquiv (adj₂.mapDerivedCategoryRightDerivedAdjunction.comp
          adj₁.mapDerivedCategoryRightDerivedAdjunction)
        adj.mapDerivedCategoryRightDerivedAdjunction
        (Functor.mapDerivedCategoryNatIso eL ≪≫ Functor.mapDerivedCategoryCompIso _ _).hom := by
  apply (F.rightDerivedFunctor ⋙ G.rightDerivedFunctor).rightDerived_ext
    (Functor.rightDerivedFunctorCompUnit F G) (HomotopyCategory.quasiIso C (.up ℤ))
  ext X
  have hL : (Functor.rightDerivedFunctorCompUnit F G).app X ≫
      (Functor.rightDerivedFunctorCompIso' F G e).hom.app (DerivedCategory.Qh.obj X) =
        (Functor.rightDerivedFunctorUnit (F ⋙ G)).app X ≫
          (Functor.rightDerivedFunctorNatTrans e.hom).app (DerivedCategory.Qh.obj X) := by
    simp [Functor.rightDerivedFunctorCompIso', Functor.rightDerivedFunctorCompIso,
      Functor.rightDerivedFunctorNatIso]
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app]
  rw [hL]
  simp [Functor.rightDerivedFunctorNatTrans, conjugateEquiv_apply_app]
  sorry

end CategoryTheory.Adjunction
