/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.Derived.DerivedTensorKoszulSymmetry
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Monoidal

/-! # Canonical condensed derived pullback tensor constraints

Source: literature/blueprint/latest/blueprint/sec-proetale-coefficients/
sk-prop-sf-open-closed-triangle/def-weil-derived-pullback-tensor-hom.md, direct
condensed-coefficient derived pullback and K-flat relative tensor paragraphs
(blueprint: lem-pur-derived-pullback-tensor-constraints).

## Main statements

* `AlgebraicGeometry.ProEtale.CondensedRing.derivedPullbackTensorConstraints`: the
  associativity, left and right unit, and Koszul-symmetry equations of the canonical
  comparisons `μ = leftDerivedUpperStarTensorIso` and `e = leftDerivedUpperStarUnitIso`
  of the derived pullback `Lf^*` of condensed module objects.
-/

@[expose] public noncomputable section
set_option autoImplicit false

universe u

open CategoryTheory MonoidalCategory
open scoped CategoryTheory.Obj
open scoped CategoryTheory.Functor
open CategoryTheory.Limits
open AlgebraicGeometry
open AlgebraicGeometry.ProEtale
open AlgebraicGeometry.ProEtale.CondensedRing

namespace AlgebraicGeometry.ProEtale.CondensedRing

/-- The canonical tensor, unit, and symmetry coherence equations for derived pullback:
for `F = Lf^*`, `μ_{K,N} : F(K ⊗ N) ≅ FK ⊗ FN` and `e : F 𝟙 ≅ 𝟙`,
`μ_{K⊗N,M} ≫ (μ_{K,N} ▷ FM) ≫ α = F(α) ≫ μ_{K,N⊗M} ≫ (FK ◁ μ_{N,M})`,
`μ_{𝟙,K} ≫ (e ▷ FK) ≫ λ = F(λ)`, `μ_{K,𝟙} ≫ (FK ◁ e) ≫ ρ = F(ρ)` and
`μ_{K,N} ≫ σ = F(σ) ≫ μ_{N,K}`, with `σ` the localized Koszul symmetry.

Source: literature/blueprint/latest/blueprint/sec-proetale-coefficients/
sk-prop-sf-open-closed-triangle/def-weil-derived-pullback-tensor-hom.md, direct
condensed-coefficient derived pullback and K-flat relative tensor paragraphs.

Proof (node steps):
1. For `T = X, Y`, det-prop-sfb-module-category clause 4 makes the `Λ_T`-module objects a
   closed symmetric monoidal Grothendieck abelian category with unit `Λ_T` and functorial
   flat resolutions; def-sfb-derived-tensor-modules and lem-sfb-derived-monoidal give the
   K-flat derived tensor with unit `Λ_T[0]` and associator/unitors from signed total
   complexes, and def-pur-localized-derived-tensor-braiding its localized Koszul symmetry.
2. lem-sfb-derived-pullback-strong-monoidal (`monoidal_leftDerivedUpperStar`) gives `μ`
   and `e`, natural, with tensorator `μ⁻¹` and unit `e⁻¹`; its associativity and two
   unitality axioms, rewritten with these inverses, are the first three equations. No
   boundedness or constructibility is assumed.
3. The symmetry equation is lem-sf-condensed-derived-pullback-braiding with `M = K`,
   `N = L`: its `δ_f` is the same `μ` and its `σ` the localized Koszul braiding of Step 1.
(blueprint: lem-pur-derived-pullback-tensor-constraints) -/
theorem derivedPullbackTensorConstraints
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X Y : Scheme.{u}} (f : X ⟶ Y)
    (K N M : DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y))) :
    (((leftDerivedUpperStarTensorIso Λ f).app
        (MonoidalCategoryStruct.tensorObj K N)).app M).hom ≫
        MonoidalCategoryStruct.whiskerRight
          (((leftDerivedUpperStarTensorIso Λ f).app K).app N).hom
          (L((f)^*⟦Λ⟧).obj M) ≫
        (MonoidalCategoryStruct.associator
          (L((f)^*⟦Λ⟧).obj K) (L((f)^*⟦Λ⟧).obj N) (L((f)^*⟦Λ⟧).obj M)).hom =
      (L((f)^*⟦Λ⟧).map
          (MonoidalCategoryStruct.associator K N M).hom) ≫
        (((leftDerivedUpperStarTensorIso Λ f).app K).app
          (MonoidalCategoryStruct.tensorObj N M)).hom ≫
        MonoidalCategoryStruct.whiskerLeft
          (L((f)^*⟦Λ⟧).obj K)
          (((leftDerivedUpperStarTensorIso Λ f).app N).app M).hom ∧
    (((leftDerivedUpperStarTensorIso Λ f).app
          (MonoidalCategoryStruct.tensorUnit _)).app K).hom ≫
      MonoidalCategoryStruct.whiskerRight
          (leftDerivedUpperStarUnitIso Λ f).hom
          (L((f)^*⟦Λ⟧).obj K) ≫
      (MonoidalCategoryStruct.leftUnitor (L((f)^*⟦Λ⟧).obj K)).hom =
      L((f)^*⟦Λ⟧).map (MonoidalCategoryStruct.leftUnitor K).hom ∧
    (((leftDerivedUpperStarTensorIso Λ f).app K).app
          (MonoidalCategoryStruct.tensorUnit _)).hom ≫
      MonoidalCategoryStruct.whiskerLeft
          (L((f)^*⟦Λ⟧).obj K)
          (leftDerivedUpperStarUnitIso Λ f).hom ≫
      (MonoidalCategoryStruct.rightUnitor (L((f)^*⟦Λ⟧).obj K)).hom =
      L((f)^*⟦Λ⟧).map (MonoidalCategoryStruct.rightUnitor K).hom ∧
    (((leftDerivedUpperStarTensorIso Λ f).app K).app N).hom ≫
      (CategoryTheory.derivedTensorKoszulSymmetry _
        (L((f)^*⟦Λ⟧).obj K) (L((f)^*⟦Λ⟧).obj N)).hom =
      L((f)^*⟦Λ⟧).map
          (CategoryTheory.derivedTensorKoszulSymmetry _ K N).hom ≫
        (((leftDerivedUpperStarTensorIso Λ f).app N).app K).hom := by
  sorry

end AlgebraicGeometry.ProEtale.CondensedRing
