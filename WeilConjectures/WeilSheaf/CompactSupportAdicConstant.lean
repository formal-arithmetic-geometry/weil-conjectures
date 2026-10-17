/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.WeilSheaf.Cohomology
public import WeilConjectures.WeilSheaf.Constant
public import WeilConjectures.WeilSheaf.LowerStar
public import WeilConjectures.Mathlib.CategoryTheory.Sites.GlobalSections
import WeilConjectures.WeilSheaf.CohomologyProEtale
import WeilConjectures.WeilSheaf.LowerShriek
import WeilConjectures.WeilSheaf.CohomologyNonneg

/-!
# Compactly supported cohomology of the constant Weil sheaf

## Main statements

- `AlgebraicGeometry.ProEtaleWeilSheaf.nonempty_lowerStarCohomologyIso`: for a pro-étale Weil sheaf `G` on
  a `k₀`-scheme `Y` and `φ : Y ⟶ Spec k₀`, the global sections of the `r`-th cohomology sheaf of
  `Rφ_* G` are the pro-étale cohomology `Rʳ Γ(Ȳ_proét, G)` of the underlying sheaf.
- `AlgebraicGeometry.WeilSheaf.subsingleton_compactlySupportedCohomology_congr`: the vanishing of
  `H_c^r(X ⊗ k̄, F)` only depends on the underlying `ℓ`-adic sheaf of `F`.
-/

@[expose] public section

universe u

open CategoryTheory Limits Endofunctor

open scoped AlgebraicGeometry.ProEtale

namespace AlgebraicGeometry

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]

namespace ProEtaleWeilSheaf

variable {Y : Scheme.{u}} [Y.Over (Spec (CommRingCat.of k₀))]
  (φ : Y ⟶ Spec (CommRingCat.of k₀)) [φ.IsOver (Spec (CommRingCat.of k₀))] [QuasiCompact φ]
  [QuasiSeparated φ] [LocallyOfFiniteType φ]

/-- **Cohomology of the direct image to `Spec k₀` is pro-étale cohomology.** For a pro-étale Weil
sheaf `G` on `Y` and `φ : Y ⟶ Spec k₀`, the global sections over `Spec k̄` of the `r`-th
cohomology sheaf of `Rφ_* G` are the pro-étale cohomology `Rʳ Γ(Ȳ_proét, G)` of the underlying
sheaf of `ℚ̄_ℓ`-modules: forgetting the Weil structure and the module structure commutes with
`Rφ̄_*`, `Γ(Spec k̄, -)` is exact and `Γ(Spec k̄, φ̄_* -) = Γ(Ȳ, -)`. -/
theorem nonempty_lowerStarCohomologyIso (G : ProEtaleWeilSheaf k₀ l Y) (r : ℕ) :
    Nonempty (
    (IsoAlgebra.forget _ ⋙ ProEtale.AdicSheaf.forget _ ⋙ Sheaf.Γ _ (WeilCoefficients.{u} l)).obj
        ((_root_.DerivedCategory.homologyFunctor _ (r : ℤ)).obj
          ((ProEtaleWeilSheaf.lowerStar k₀ l φ).rightDerivedFunctor.obj
            ((_root_.DerivedCategory.singleFunctor _ 0).obj G))) ≅
      ((Sheaf.Γ (Scheme.ProEt.topology (Y ↘ Spec (CommRingCat.of k₀)).geometricFiber)
        (WeilCoefficients.{u} l)).rightDerived r).obj ((ProEtale.AdicSheaf.forget _).obj
          G.carrier)) := by
  set φ' := Scheme.Hom.geometricFiberMap φ (comp_over φ (Spec (CommRingCat.of k₀)))
  have := IsGrothendieckAbelian.hasColimitsOfShape_discrete.{u + 2, u + 1, u + 1}
    (ProEtale.AdicSheaf l (Y ↘ Spec (CommRingCat.of k₀)).geometricFiber) ℤ
  have := IsGrothendieckAbelian.hasExactColimitsOfShape_discrete.{u + 2, u + 1, u + 1}
    (ProEtale.AdicSheaf l (Y ↘ Spec (CommRingCat.of k₀)).geometricFiber) ℤ
  -- forget the Weil structure: `For (Rφ_* G) ≅ Rφ̄_* (For G)`
  let e₁ : (IsoAlgebra.forget _).mapDerivedCategory.obj
      ((ProEtaleWeilSheaf.lowerStar k₀ l φ).rightDerivedFunctor.obj
        ((_root_.DerivedCategory.singleFunctor _ 0).obj G)) ≅
      (φ')_*ᵃ[l].rightDerivedFunctor.obj
        ((_root_.DerivedCategory.singleFunctor _ 0).obj G.carrier) :=
    (IsoAlgebra.rightDerivedFunctorMapOfNatIsoCompForgetIso _ _).app _ ≪≫
      Functor.mapIso _ (((IsoAlgebra.forget _).mapDerivedCategorySingleFunctor 0).app G)
  -- forget the `ℚ̄_ℓ,Ȳ`-module structure
  let e₂ : (ProEtale.AdicSheaf.forget _).mapDerivedCategory.obj
      ((φ')_*ᵃ[l].rightDerivedFunctor.obj
        ((_root_.DerivedCategory.singleFunctor _ 0).obj G.carrier)) ≅
      ((φ')_*[WeilCoefficients.{u} l]).rightDerivedFunctor.obj
        ((_root_.DerivedCategory.singleFunctor _ 0).obj
          ((ProEtale.AdicSheaf.forget _).obj G.carrier)) :=
    ((ProEtale.mapDerivedCategoryForgetCompRightDerivedLowerStarIso l φ').app _).symm ≪≫
      Functor.mapIso _
        (((ProEtale.AdicSheaf.forget _).mapDerivedCategorySingleFunctor 0).app G.carrier)
  -- the underlying sheaf of `𝓗ʳ(Rφ_* G)` is `Rʳφ̄_* G`
  let e₃ : (ProEtale.AdicSheaf.forget _).obj ((IsoAlgebra.forget _).obj
      ((_root_.DerivedCategory.homologyFunctor _ (r : ℤ)).obj
        ((ProEtaleWeilSheaf.lowerStar k₀ l φ).rightDerivedFunctor.obj
          ((_root_.DerivedCategory.singleFunctor _ 0).obj G)))) ≅
      (((φ')_*[WeilCoefficients.{u} l]).rightDerived r).obj
        ((ProEtale.AdicSheaf.forget _).obj G.carrier) :=
    (ProEtale.AdicSheaf.forget _).mapIso
        ((((IsoAlgebra.forget _).mapDerivedCategoryHomologyFunctorIso (r : ℤ)).app _) ≪≫
          (_root_.DerivedCategory.homologyFunctor _ (r : ℤ)).mapIso e₁) ≪≫
      (((ProEtale.AdicSheaf.forget _).mapDerivedCategoryHomologyFunctorIso (r : ℤ)).app _) ≪≫
      (_root_.DerivedCategory.homologyFunctor _ (r : ℤ)).mapIso e₂ ≪≫
      ((φ')_*[WeilCoefficients.{u} l]).homologyRightDerivedFunctorObjSingleFunctorIso _ r
  -- `Γ(Spec k̄, -)` is exact and `Γ(Spec k̄, φ̄_* -) = Γ(Ȳ, -)`
  exact ⟨(Sheaf.Γ _ (WeilCoefficients.{u} l)).mapIso e₃ ≪≫
    (Functor.rightDerivedCompObjIso _ _ r _).symm ≪≫
    Functor.rightDerivedObjIsoOfIso (ProEtale.globalSectionsLowerStarIso _ φ') r _⟩

end ProEtaleWeilSheaf

namespace WeilSheaf

variable {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]
  [IsSeparated (X ↘ Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))]

attribute [local instance] Compactification.over in
/-- **The vanishing of compactly supported cohomology only depends on the underlying sheaf.** If
the underlying `ℓ`-adic sheaves of two Weil sheaves `F` and `G` on `X` are isomorphic, then
`H_c^r(X ⊗ k̄, G) = 0` implies `H_c^r(X ⊗ k̄, F) = 0`: for the chosen compactification
`X ⟶[i] Z ⟶[g] Spec k₀`, `H_c^r(X ⊗ k̄, F)` is the pro-étale cohomology
`Rʳ Γ(Z̄_proét, ī_! F)`, which only depends on the underlying sheaf of `F`. -/
theorem subsingleton_compactlySupportedCohomology_of_iso {F G : WeilSheaf k₀ l X}
    (e : F.obj.carrier ≅ G.obj.carrier) (r : ℤ)
    (hG : Subsingleton (G.compactlySupportedCohomology r).carrier) :
    Subsingleton (F.compactlySupportedCohomology r).carrier := by
  obtain hr | hr := lt_or_ge r 0
  · exact subsingleton_compactlySupportedCohomology_of_neg F hr
  obtain ⟨n, rfl⟩ : ∃ n : ℕ, r = n := ⟨r.toNat, by lia⟩
  let c := HasCompactification.compactification (X ↘ Spec (CommRingCat.of k₀))
    (hf := hasCompactification_of_over (k₀ := k₀) _)
  let Φ : ProEtale.AdicSheaf l (X ↘ Spec (CommRingCat.of k₀)).geometricFiber ⥤
      WeilCoefficients.{u} l :=
    ProEtale.adicOpenImmersionLowerShriek l
        (Scheme.Hom.geometricFiberMap c.i (comp_over c.i (Spec (CommRingCat.of k₀)))) ⋙
      ProEtale.AdicSheaf.forget _ ⋙
        (Sheaf.Γ (Scheme.ProEt.topology (c.Z ↘ Spec (CommRingCat.of k₀)).geometricFiber)
          (WeilCoefficients.{u} l)).rightDerived n
  have key (H : WeilSheaf k₀ l X) : Nonempty
      ((IsoAlgebra.forget _ ⋙ ProEtale.AdicSheaf.forget _ ⋙
        Sheaf.Γ _ (WeilCoefficients.{u} l)).obj
          ((_root_.DerivedCategory.homologyFunctor _ (n : ℤ)).obj
            ((ProEtaleWeilSheaf.lowerStar k₀ l c.g).rightDerivedFunctor.obj
              ((ProEtaleWeilSheaf.extensionByZero k₀ l c.i).mapDerivedCategory.obj
                ((_root_.DerivedCategory.singleFunctor _ 0).obj H.obj)))) ≅
        Φ.obj H.obj.carrier) := by
    obtain ⟨e₁⟩ := ProEtaleWeilSheaf.nonempty_lowerStarCohomologyIso c.g
      ((ProEtaleWeilSheaf.extensionByZero k₀ l c.i).obj H.obj) n
    exact ⟨(IsoAlgebra.forget _ ⋙ ProEtale.AdicSheaf.forget _ ⋙
        Sheaf.Γ _ (WeilCoefficients.{u} l)).mapIso
          ((_root_.DerivedCategory.homologyFunctor _ (n : ℤ)).mapIso
            ((ProEtaleWeilSheaf.lowerStar k₀ l c.g).rightDerivedFunctor.mapIso
              (((ProEtaleWeilSheaf.extensionByZero k₀ l c.i).mapDerivedCategorySingleFunctor
                0).app H.obj))) ≪≫ e₁ ≪≫
      ((Sheaf.Γ _ (WeilCoefficients.{u} l)).rightDerived n).mapIso
        ((ProEtale.AdicSheaf.forget _).mapIso
          ((IsoAlgebra.mapOfNatIsoCompForgetIso
            (ProEtale.adicOpenImmersionLowerShriekGeometricFiberMapCompFrobeniusIso l c.i
              (comp_over c.i _))).app H.obj))⟩
  obtain ⟨eF⟩ := key F
  obtain ⟨eG⟩ := key G
  have hz : IsZero ((IsoAlgebra.forget _ ⋙ ProEtale.AdicSheaf.forget _ ⋙
      Sheaf.Γ _ (WeilCoefficients.{u} l)).obj
        ((_root_.DerivedCategory.homologyFunctor _ (n : ℤ)).obj
          ((ProEtaleWeilSheaf.lowerStar k₀ l c.g).rightDerivedFunctor.obj
            ((ProEtaleWeilSheaf.extensionByZero k₀ l c.i).mapDerivedCategory.obj
              ((_root_.DerivedCategory.singleFunctor _ 0).obj G.obj))))) :=
    @ModuleCat.isZero_of_subsingleton _ _ _ hG
  exact ModuleCat.subsingleton_of_isZero ((WeilCoefficients.toModuleCat l).map_isZero
    (hz.of_iso (eF ≪≫ Φ.mapIso e ≪≫ eG.symm)))

end WeilSheaf

end AlgebraicGeometry
