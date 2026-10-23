/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.Adic.LowerStar
public import WeilConjectures.SixFunctors.ProEtale.Adic.LisseInternalHom

/-!
# Étale base change and clopen decomposition for direct images of `ℓ`-adic sheaves

* For an étale `j : U ⟶ Y`, the restriction of `Rf_* F` to `U` is computed on `X ×_Y U`
  (`AlgebraicGeometry.ProEtale.mapDerivedCategoryUpperStarRightDerivedFunctorLowerStarIsoOfEtale`),
  generalising the open base change
  `AlgebraicGeometry.ProEtale.mapDerivedCategoryUpperStarRightDerivedFunctorLowerStarIso`.
* If `X` has finitely many connected components, `Hⁿ(Rf_* F)` is lisse as soon as the
  corresponding sheaves for the restrictions of `f` to the connected components are
  (`AlgebraicGeometry.ProEtale.isAdicLisseSheaf_homology_rightDerivedFunctor_lowerStar_of_connectedComponents`).
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry.ProEtale

variable {l : ℕ} [Fact l.Prime] {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- **Étale base change for `Rf_*`**: the restriction of `Rf_* F` along an étale `j : U ⟶ Y` is
computed on `X ×_Y U`. -/
noncomputable def mapDerivedCategoryUpperStarRightDerivedFunctorLowerStarIsoOfEtale
    {U : Scheme.{u}} (j : U ⟶ Y) [Etale j] (F : AdicSheaf l X) :
    (j)^*ᵃ[l].mapDerivedCategory.obj ((f)_*ᵃ[l].rightDerivedFunctor.obj
        ((DerivedCategory.singleFunctor _ 0).obj F)) ≅
      (pullback.snd f j)_*ᵃ[l].rightDerivedFunctor.obj
        ((DerivedCategory.singleFunctor _ 0).obj ((pullback.fst f j)^*ᵃ[l].obj F)) :=
  sorry

/-- **Lisse direct images can be checked on connected components.** -/
theorem isAdicLisseSheaf_homology_rightDerivedFunctor_lowerStar_of_connectedComponents
    [IsLocallyNoetherian X] [CompactSpace X] (F : AdicSheaf l X) (n : ℤ)
    (h : ∀ (Z : Scheme.{u}) (ι : Z ⟶ X) [IsOpenImmersion ι] [IsClosedImmersion ι]
      [ConnectedSpace Z], IsAdicLisseSheaf ((DerivedCategory.homologyFunctor _ n).obj
        ((ι ≫ f)_*ᵃ[l].rightDerivedFunctor.obj
          ((DerivedCategory.singleFunctor _ 0).obj ((ι)^*ᵃ[l].obj F))))) :
    IsAdicLisseSheaf ((DerivedCategory.homologyFunctor _ n).obj
      ((f)_*ᵃ[l].rightDerivedFunctor.obj ((DerivedCategory.singleFunctor _ 0).obj F))) :=
  sorry

end AlgebraicGeometry.ProEtale
