/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusAdjunction
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusBaseChange

/-!
# The derived base change of a mate is the derived mate

Let `L ⊣ R` and `L' ⊣ R'` be adjunctions with exact left adjoints, let `G` and `G'` be exact
functors and `σ : G ⋙ L' ⟶ L ⋙ G'` a square. Its mate `R ⋙ G ⟶ G' ⋙ R'` induces a base change
morphism `R⁺ ⋙ G⁺ ⟶ G'⁺ ⋙ R'⁺` of bounded below right derived functors
(`CategoryTheory.Functor.rightDerivedFunctorPlusBaseChange`). On the other hand, a square `θ` of
the induced functors on the bounded below derived categories which is computed by `σ` on
complexes has a mate with respect to the bounded below derived adjunctions
`CategoryTheory.Adjunction.derivedPlus`. This file shows that the two agree
(`CategoryTheory.Adjunction.rightDerivedFunctorPlusBaseChange_mateEquiv`), and records the
resulting compatibility of the derived base change morphism with the derived counits
(`CategoryTheory.Adjunction.rightDerivedFunctorPlusBaseChange_mateEquiv_counit`).

This is the abstract form of the statement that the comparison `ν^* Rf_* ⟶ Rf_* ν^*` of the
pro-étale comparison functor `ν^*` with direct images is the mate of the comparison
`f^* ν^* ≅ ν^* f^*` of `ν^*` with inverse images, used to identify the transported étale exchange
map with the pro-étale one.
-/

@[expose] public section

open CategoryTheory Category Limits

namespace CategoryTheory.Adjunction

variable {C₁ C₂ C₃ C₄ : Type*} [Category* C₁] [Category* C₂] [Category* C₃] [Category* C₄]
  [Abelian C₁] [Abelian C₂] [Abelian C₃] [Abelian C₄]
  [HasDerivedCategory C₁] [HasDerivedCategory C₂] [HasDerivedCategory C₃]
  [HasDerivedCategory C₄] [EnoughInjectives C₁] [EnoughInjectives C₃]
  {L : C₂ ⥤ C₁} {R : C₁ ⥤ C₂} {L' : C₄ ⥤ C₃} {R' : C₃ ⥤ C₄}
  {G : C₂ ⥤ C₄} {G' : C₁ ⥤ C₃}
  [L.Additive] [R.Additive] [L'.Additive] [R'.Additive] [G.Additive] [G'.Additive]
  [PreservesFiniteLimits L] [PreservesFiniteColimits L]
  [PreservesFiniteLimits L'] [PreservesFiniteColimits L']
  [PreservesFiniteLimits G] [PreservesFiniteColimits G]
  [PreservesFiniteLimits G'] [PreservesFiniteColimits G']

/-- **The derived base change of a mate is the derived mate.** With the notation of the module
docstring, if `θ` is computed by `σ` on complexes, then the base change morphism
`R⁺ ⋙ G⁺ ⟶ G'⁺ ⋙ R'⁺` of the mate of `σ` is the mate of `θ` with respect to the bounded below
derived adjunctions. -/
theorem rightDerivedFunctorPlusBaseChange_mateEquiv (adj : L ⊣ R) (adj' : L' ⊣ R')
    (σ : TwoSquare G L L' G')
    (θ : TwoSquare G.mapDerivedCategoryPlus L.mapDerivedCategoryPlus L'.mapDerivedCategoryPlus
      G'.mapDerivedCategoryPlus)
    (hθ : ∀ N : HomotopyCategory.Plus C₂,
      θ.natTrans.app (DerivedCategory.Plus.Qh.obj N) ≫
          G'.mapDerivedCategoryPlus.map (L.mapDerivedCategoryPlusFactorsh.hom.app N) ≫
          G'.mapDerivedCategoryPlusFactorsh.hom.app (L.mapHomotopyCategoryPlus.obj N) =
        L'.mapDerivedCategoryPlus.map (G.mapDerivedCategoryPlusFactorsh.hom.app N) ≫
          L'.mapDerivedCategoryPlusFactorsh.hom.app (G.mapHomotopyCategoryPlus.obj N) ≫
          DerivedCategory.Plus.Qh.map ((NatTrans.mapHomotopyCategoryPlus σ.natTrans).app N)) :
    Functor.rightDerivedFunctorPlusBaseChange (mateEquiv adj adj' σ).natTrans =
      (mateEquiv adj.derivedPlus adj'.derivedPlus θ).natTrans := by
  refine Functor.rightDerived_ext _ (Functor.whiskerRight R.rightDerivedFunctorPlusUnit
      G.mapDerivedCategoryPlus ≫ (Functor.associator _ _ _).hom)
    (HomotopyCategory.Plus.quasiIso C₁) _ _ _ ?_
  rw [Functor.rightDerivedFunctorPlusBaseChange_fac]
  refine NatTrans.ext (funext fun K ↦ ?_)
  have h := derivedPlus_mateEquiv_app_fac adj adj' σ θ hθ K
  simp only [Functor.rightDerivedFunctorPlusBaseChangeAux, NatTrans.comp_app,
    Functor.whiskerLeft_app, Functor.whiskerRight_app, Functor.associator_hom_app,
    Functor.associator_inv_app, Functor.mapHomotopyCategoryPlusCompIso_refl_hom_app,
    Functor.mapHomotopyCategoryPlusCompIso_refl_inv_app, Functor.map_id, id_comp, comp_id,
    assoc]
  simpa using h.symm

/-- **The derived base change of a mate is compatible with the derived counits**: with the
notation and hypotheses of `CategoryTheory.Adjunction.rightDerivedFunctorPlusBaseChange_mateEquiv`,
for `K` in `D⁺(C₁)` the composite `L'⁺ G⁺ R⁺ K ⟶ L'⁺ R'⁺ G'⁺ K ⟶ G'⁺ K` of the base change
morphism and the counit of `L'⁺ ⊣ R'⁺` is `θ` followed by `G'⁺` of the counit of `L⁺ ⊣ R⁺`. -/
@[reassoc]
theorem rightDerivedFunctorPlusBaseChange_mateEquiv_counit (adj : L ⊣ R) (adj' : L' ⊣ R')
    (σ : TwoSquare G L L' G')
    (θ : TwoSquare G.mapDerivedCategoryPlus L.mapDerivedCategoryPlus L'.mapDerivedCategoryPlus
      G'.mapDerivedCategoryPlus)
    (hθ : ∀ N : HomotopyCategory.Plus C₂,
      θ.natTrans.app (DerivedCategory.Plus.Qh.obj N) ≫
          G'.mapDerivedCategoryPlus.map (L.mapDerivedCategoryPlusFactorsh.hom.app N) ≫
          G'.mapDerivedCategoryPlusFactorsh.hom.app (L.mapHomotopyCategoryPlus.obj N) =
        L'.mapDerivedCategoryPlus.map (G.mapDerivedCategoryPlusFactorsh.hom.app N) ≫
          L'.mapDerivedCategoryPlusFactorsh.hom.app (G.mapHomotopyCategoryPlus.obj N) ≫
          DerivedCategory.Plus.Qh.map ((NatTrans.mapHomotopyCategoryPlus σ.natTrans).app N))
    (K : DerivedCategory.Plus C₁) :
    L'.mapDerivedCategoryPlus.map
        ((Functor.rightDerivedFunctorPlusBaseChange (mateEquiv adj adj' σ).natTrans).app K) ≫
      adj'.derivedPlus.counit.app (G'.mapDerivedCategoryPlus.obj K) =
    θ.natTrans.app (R.rightDerivedFunctorPlus.obj K) ≫
      G'.mapDerivedCategoryPlus.map (adj.derivedPlus.counit.app K) := by
  rw [rightDerivedFunctorPlusBaseChange_mateEquiv adj adj' σ θ hθ]
  exact mateEquiv_counit _ _ _ K

end CategoryTheory.Adjunction
