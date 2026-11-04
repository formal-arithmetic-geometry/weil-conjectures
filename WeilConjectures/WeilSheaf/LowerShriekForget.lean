/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Adjunction.FreeComparisonComp
public import WeilConjectures.CategoryTheory.DerivedCategory.FreeComparisonMapDerivedCategory
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.IsoAlgebraFreeComparison
public import WeilConjectures.CategoryTheory.Endofunctor.IsoAlgebraDerivedAdjunction
public import WeilConjectures.WeilSheaf.LowerShriek

/-!
# The direct image with compact support of Weil complexes after forgetting the Weil structure

Let `f : X ⟶ Y` be a morphism of `k₀`-schemes with a compactification `X ⟶[i] Z ⟶[g] Y` over `k₀`.
The direct image with compact support `Rf_! = Rḡ_* ∘ D(ī_!)` of pro-étale Weil sheaves
(`AlgebraicGeometry.ProEtaleWeilSheaf.rightDerivedLowerShriek`) is computed, after forgetting the
Weil structures, by the direct image with compact support `Rf̄_! = Rḡ_* ∘ D(ī_!)` of `ℓ`-adic
sheaves on the geometric fibres (`AlgebraicGeometry.ProEtaleWeilSheaf.geometricRightDerivedLowerShriek`):
`For ∘ Rf_! ≅ Rf̄_! ∘ For` (`AlgebraicGeometry.ProEtaleWeilSheaf.rightDerivedLowerShriekCompForgetIso`).

The morphisms of Weil complexes are computed from the underlying morphisms through free Weil
objects (`CategoryTheory.Endofunctor.IsoAlgebra.bijective_map_comp_of_bijective_forget`), so the
maps `g ↦ Rf_! g ≫ ε` out of `Hom(K, P)` are bijective as soon as `Rf_!` commutes with the free
Weil objects on the shifts of `For K` and the underlying maps `f ↦ Rf̄_! f ≫ For ε` are bijective
(`AlgebraicGeometry.WeilComplex.bijective_map_comp_derivedLowerShriek`).
-/

@[expose] public section

universe u

open CategoryTheory Limits Endofunctor

namespace AlgebraicGeometry

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]
variable {X Y : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]
  [Y.Over (Spec (CommRingCat.of k₀))]

attribute [local instance] Compactification.over

open ProEtale

section Compactification

variable (k₀ l)

/-- The direct image with compact support `Rf̄_! = Rḡ_* ∘ D(ī_!)` of `ℓ`-adic pro-étale sheaves on
the geometric fibres, attached to a compactification `X ⟶[i] Z ⟶[g] Y` over `k₀`: the base changes
`ī` and `ḡ` of `i` and `g` to `k̄` form a compactification of the base change `f̄` of `f`. -/
noncomputable def ProEtaleWeilSheaf.geometricRightDerivedLowerShriek (f : X ⟶ Y)
    [f.IsOver (Spec (CommRingCat.of k₀))] (c : Compactification f) :
    DerivedCategory (ProEtale.AdicSheaf l (X ↘ Spec (CommRingCat.of k₀)).geometricFiber) ⥤
      DerivedCategory (ProEtale.AdicSheaf l (Y ↘ Spec (CommRingCat.of k₀)).geometricFiber) :=
  (Scheme.Hom.geometricFiberMap c.i (comp_over c.i _))_!ᵃ[l].mapDerivedCategory ⋙
    (Scheme.Hom.geometricFiberMap c.g (comp_over c.g _))_*ᵃ[l].rightDerivedFunctor

/-- **Forgetting the Weil structure commutes with the direct image with compact support**:
`For ∘ Rf_! ≅ Rf̄_! ∘ For`, the pasting of `For ∘ D(ī_!) ≅ D(ī_!) ∘ For` and
`For ∘ Rḡ_* ≅ Rḡ_* ∘ For`. -/
noncomputable def ProEtaleWeilSheaf.rightDerivedLowerShriekCompForgetIso (f : X ⟶ Y)
    [f.IsOver (Spec (CommRingCat.of k₀))] (c : Compactification f) :
    ProEtaleWeilSheaf.rightDerivedLowerShriek k₀ l f c ⋙
        (IsoAlgebra.forget (WeilSheaf.frobeniusPullback k₀ l Y)).mapDerivedCategory ≅
      (IsoAlgebra.forget (WeilSheaf.frobeniusPullback k₀ l X)).mapDerivedCategory ⋙
        ProEtaleWeilSheaf.geometricRightDerivedLowerShriek k₀ l f c := by
  have := IsGrothendieckAbelian.hasColimitsOfShape_discrete.{u + 2, u + 1, u + 1}
    (ProEtale.AdicSheaf l (c.Z ↘ Spec (CommRingCat.of k₀)).geometricFiber) ℤ
  have := IsGrothendieckAbelian.hasExactColimitsOfShape_discrete.{u + 2, u + 1, u + 1}
    (ProEtale.AdicSheaf l (c.Z ↘ Spec (CommRingCat.of k₀)).geometricFiber) ℤ
  have := IsGrothendieckAbelian.hasColimitsOfShape_discrete.{u + 2, u + 1, u + 1}
    (ProEtale.AdicSheaf l (X ↘ Spec (CommRingCat.of k₀)).geometricFiber) ℤ
  have := IsGrothendieckAbelian.hasExactColimitsOfShape_discrete.{u + 2, u + 1, u + 1}
    (ProEtale.AdicSheaf l (X ↘ Spec (CommRingCat.of k₀)).geometricFiber) ℤ
  exact Adjunction.compForgetIso
    (Functor.mapDerivedCategoryCompForgetIso (IsoAlgebra.mapOfNatIsoCompForgetIso _))
    (IsoAlgebra.rightDerivedFunctorMapOfNatIsoCompForgetIso _ _)

end Compactification

end AlgebraicGeometry
