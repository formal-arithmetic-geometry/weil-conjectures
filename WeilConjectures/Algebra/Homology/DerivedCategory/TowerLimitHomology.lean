/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Algebra.Homology.DerivedCategory.TowerLimitRange
public import WeilConjectures.Algebra.Homology.DerivedCategory.TowerLimitReplete

/-!
# Cohomology of a derived limit under the Mittag-Leffler condition

Let `C` be an abelian category with exact countable products in which sequential limits of
epimorphisms project epimorphically onto the first term (`CategoryTheory.EpiπAppZeroOfEpi`), for
instance abelian sheaves on the pro-étale site
(`AlgebraicGeometry.Scheme.ProEt.epi_π_app_zero_of_epi_ab`). For a homotopy limit cone `c` over a
tower `F` in `D(C)` whose cohomology tower `H^{i-1}(Fₙ)` has epimorphic transitions,
`Hⁱ(R lim F) = lim Hⁱ(Fₙ)`
(`DerivedCategory.isLimitHomologyFunctorMapConeOfIsHomotopyLimit`): this is the sheaf-level
Milnor sequence `0 ⟶ lim¹ H^{i-1}(Fₙ) ⟶ Hⁱ(R lim F) ⟶ lim Hⁱ(Fₙ) ⟶ 0` in the case where the
`lim¹` term vanishes (`CategoryTheory.Limits.epi_one_sub_of_epiπAppZeroOfEpi`).
-/

@[expose] public section

open CategoryTheory Limits Opposite Pretriangulated

namespace DerivedCategory

variable {C : Type*} [Category* C] [Abelian C] [HasDerivedCategory C]
  [Abelian.HasKInjectiveResolutions C] [HasLimitsOfShape (Discrete ℕ) C]
  [HasExactLimitsOfShape (Discrete ℕ) C] [HasLimitsOfShape ℕᵒᵖ C]
  {F : ℕᵒᵖ ⥤ DerivedCategory C} {c : Cone F}

/-- **Cohomology of a derived limit under the Mittag-Leffler condition.** In an abelian category
with exact countable products in which sequential limits of epimorphisms project
epimorphically onto the first term (e.g. sheaves on a replete topos), let `c` be a homotopy
limit cone over a tower `F` in `D(C)` such that the transitions of the tower `H^{i-1}(Fₙ)` are
epimorphisms. Then `Hⁱ(R lim F) = lim Hⁱ(Fₙ)`: in the Milnor triangle, `1 - t` is surjective on
`∏ H^{i-1}(Fₙ)`, so `Hⁱ(R lim F) ⟶ ∏ Hⁱ(Fₙ)` is the kernel of `1 - t`, which is `lim Hⁱ(Fₙ)`. -/
noncomputable def isLimitHomologyFunctorMapConeOfIsHomotopyLimit (hC : EpiπAppZeroOfEpi C)
    (hc : IsHomotopyLimit c) (i : ℤ)
    (hepi : ∀ n : ℕ, Epi ((homologyFunctor C (i - 1)).map (F.map (homOfLE n.le_succ).op))) :
    IsLimit ((homologyFunctor C i).mapCone c) := by
  let K (n : ℕ) := F.obj (op n)
  let P : Fan K := Fan.mk (∏ᶜ K) (Pi.π K)
  have hP : IsLimit P := productIsProduct K
  have hδ := hc.exists_distTriang hP
  let δ := hδ.choose
  have hT := hδ.choose_spec
  let T := Triangle.mk (Fan.IsLimit.lift hP fun n ↦ c.π.app (op n)) (𝟙 _ - towerShift hP) δ
  -- the tower of cohomology objects in degree `j`, with its product fan
  have hQ (j : ℤ) := isLimitFanMkObjOfIsLimit (homologyFunctor C j) K P.proj hP
  have ht (j : ℤ) (n : ℕ) : (homologyFunctor C j).map (towerShift hP) ≫
      (homologyFunctor C j).map (P.proj n) = (homologyFunctor C j).map (P.proj (n + 1)) ≫
        (F ⋙ homologyFunctor C j).map (homOfLE n.le_succ).op := by
    rw [← Functor.map_comp, towerShift, Fan.IsLimit.fac, Functor.comp_map, Functor.map_comp]
  -- `1 - t` is an epimorphism in degree `i - 1`
  have h₁ : Epi ((homologyFunctor C (i - 1)).map T.mor₂) := by
    have e : (homologyFunctor C (i - 1)).map T.mor₂ =
        𝟙 _ - (homologyFunctor C (i - 1)).map (towerShift hP) := by
      change (homologyFunctor C (i - 1)).map (𝟙 P.pt - towerShift hP) = _
      rw [Functor.map_sub, CategoryTheory.Functor.map_id]
    rw [e]
    exact CategoryTheory.Limits.epi_one_sub_of_epiπAppZeroOfEpi hC
      (F := F ⋙ homologyFunctor C (i - 1))
        (hQ (i - 1)) _ (ht (i - 1)) hepi
  -- hence `Hⁱ(R lim F) ⟶ Hⁱ(∏ Fₙ)` is a monomorphism, a kernel of `1 - t`
  have h₂ : Mono ((homologyFunctor C i).map T.mor₁) :=
    (HomologySequence.mono_homologyMap_mor₁_iff T hT (i - 1) i (by lia)).2
      ((HomologySequence.epi_homologyMap_mor₂_iff T hT (i - 1) i (by lia)).1 h₁)
  have hK := (HomologySequence.exact₂ T hT i).fIsKernel
  have e₂ : (homologyFunctor C i).map T.mor₂ =
      𝟙 _ - (homologyFunctor C i).map (towerShift hP) := by
    change (homologyFunctor C i).map (𝟙 P.pt - towerShift hP) = _
    rw [Functor.map_sub, CategoryTheory.Functor.map_id]
  have hfac (n : ℕ) : (homologyFunctor C i).map T.mor₁ ≫ (homologyFunctor C i).map (P.proj n) =
      (homologyFunctor C i).map (c.π.app (op n)) := by
    rw [← Functor.map_comp]
    exact congrArg _ (Fan.IsLimit.fac hP _ n)
  have hw (s : Cone (F ⋙ homologyFunctor C i)) :
      Fan.IsLimit.lift (hQ i) (fun n ↦ s.π.app (op n)) ≫ (homologyFunctor C i).map T.mor₂ = 0 := by
    rw [e₂]
    exact Fan.IsLimit.lift_π_comp_one_sub_eq_zero (hQ i) _ (ht i) s
  have hl (s : Cone (F ⋙ homologyFunctor C i)) :=
    KernelFork.IsLimit.lift' hK (Fan.IsLimit.lift (hQ i) fun n ↦ s.π.app (op n)) (hw s)
  exact
    { lift s := (hl s).1
      fac s j := by
        obtain ⟨n⟩ := j
        change (hl s).1 ≫ (homologyFunctor C i).map (c.π.app (op n)) = _
        rw [← hfac, ← Category.assoc]
        exact (congrArg (· ≫ (homologyFunctor C i).map (P.proj n)) (hl s).2).trans
          (Fan.IsLimit.fac (hQ i) _ n)
      uniq s m hm := by
        rw [← cancel_mono ((homologyFunctor C i).map T.mor₁)]
        refine (Fan.IsLimit.hom_ext (hQ i) _ _ fun n ↦ ?_).trans (hl s).2.symm
        rw [Category.assoc]
        change m ≫ (homologyFunctor C i).map T.mor₁ ≫ (homologyFunctor C i).map (P.proj n) = _
        rw [hfac, Fan.IsLimit.fac]
        exact hm (op n) }

end DerivedCategory
