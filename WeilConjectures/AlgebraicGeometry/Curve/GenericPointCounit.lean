/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Curve.GenericComparison
public import WeilConjectures.SixFunctors.Etale.LowerShriek.Comparison

/-!
# Pushforward along the generic point

Let `X` be an integral quasi-separated scheme with generic point `η : Spec k(X) ⟶ X`. For an
abelian étale sheaf `M` on `Spec k(X)`, the unit `η_* M ⟶ η_* η^* η_* M` is an isomorphism: by
continuity of sections at the limit `Spec k(X) = lim_U Spec Γ(X, U)`
(`AlgebraicGeometry.Etale.unitComparison_app_isColimit_of_isLimit`), the sections of
`η_* η^* G` over an affine étale `X`-scheme are the colimit of the sections of the
`j_{U*} j_U^* G`, and for `G = η_* M` all the units `G ⟶ j_{U*} j_U^* G` are isomorphisms since
`η` factors through the open immersion `j_U`.

## Main statements

- `AlgebraicGeometry.Etale.isIso_of_bijective_app_of_isAffine`: a morphism of étale sheaves
  bijective on the sections over affine étale schemes is an isomorphism.
- `AlgebraicGeometry.Scheme.isIso_unit_app_lowerStar_fromSpecFunctionField`: the unit
  `η_* M ⟶ η_* η^* η_* M` is an isomorphism.
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry

open Etale

/-- A morphism of abelian étale sheaves which is bijective on the sections over every étale
scheme with affine underlying scheme is an isomorphism. -/
lemma Etale.isIso_of_bijective_app_of_isAffine {X : Scheme.{u}}
    {F G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}} (φ : F ⟶ G)
    (h : ∀ W : X.Etale, IsAffine W.left → Function.Bijective (φ.hom.app (op W))) : IsIso φ := by
  have : PreservesLimitsOfSize.{u, u + 1} (CategoryTheory.forget AddCommGrpCat.{u + 1}) :=
    preservesLimitsOfSize_shrink.{u + 1, u + 1, u, u + 1} _
  have : X.smallEtaleTopology.HasSheafCompose (CategoryTheory.forget AddCommGrpCat.{u + 1}) :=
    inferInstance
  refine (Sheaf.isLocallyBijective_iff_isIso φ).1 ⟨⟨fun {V} x y hxy ↦ ?_⟩, ⟨fun {V} s ↦ ?_⟩⟩
  · refine Etale.mem_smallEtaleTopology_of_forall_isAffine _ fun W g hW ↦ (h W hW).1 ?_
    change φ.hom.app _ (F.obj.map g.op x) = φ.hom.app _ (F.obj.map g.op y)
    rw [NatTrans.naturality_apply, NatTrans.naturality_apply]
    exact congrArg _ hxy
  · refine Etale.mem_smallEtaleTopology_of_forall_isAffine _ fun W g hW ↦ ?_
    obtain ⟨t, ht⟩ := (h W hW).2 (G.obj.map g.op s)
    exact ⟨t, ht⟩

namespace Scheme

variable (X : Scheme.{u}) [IsIntegral X]

/-- For a nonempty affine open `U` of an integral scheme `X`, the unit `G ⟶ j_* j^* G` of the open
immersion `j : Spec Γ(X, U) ⟶ X` is an isomorphism on pushforwards `G = η_* M` from the generic
point, since `η` factors through `j`. -/
lemma isIso_affineOpenUnit_lowerStar (U : X.NonemptyAffineOpens)
    (M : Sheaf (Spec X.functionField).smallEtaleTopology AddCommGrpCat.{u + 1}) :
    IsIso (X.affineOpenUnit U ((X.fromSpecFunctionField)_*[AddCommGrpCat.{u + 1}].obj M)) := by
  let j := X.affineOpensDiagramι.app U
  let π := X.functionFieldCone.π.app U
  let adj := upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} j
  let Z := (π)_*[AddCommGrpCat.{u + 1}].obj M
  let e : (X.fromSpecFunctionField)_*[AddCommGrpCat.{u + 1}].obj M ≅
      (j)_*[AddCommGrpCat.{u + 1}].obj Z :=
    ((lowerStarComp AddCommGrpCat.{u + 1} π j X.fromSpecFunctionField
      (X.fromSpecFunctionField_eq_functionFieldCone_comp U)).app M).symm
  have : IsOpenImmersion j := U.2.1.isOpenImmersion_fromSpec
  have hZ : IsIso (adj.unit.app ((j)_*[AddCommGrpCat.{u + 1}].obj Z)) := by
    have h := adj.right_triangle_components Z
    have : IsIso ((j)_*[AddCommGrpCat.{u + 1}].map (adj.counit.app Z)) := inferInstance
    exact IsIso.of_isIso_comp_right _ ((j)_*[AddCommGrpCat.{u + 1}].map (adj.counit.app Z))
  have hn := adj.unit.naturality e.hom
  have : IsIso (adj.unit.app _ ≫ ((j)^*[AddCommGrpCat.{u + 1}] ⋙
      (j)_*[AddCommGrpCat.{u + 1}]).map e.hom) := by
    rw [← hn]
    change IsIso (e.hom ≫ _)
    infer_instance
  exact IsIso.of_isIso_comp_right (adj.unit.app _)
    (((j)^*[AddCommGrpCat.{u + 1}] ⋙ (j)_*[AddCommGrpCat.{u + 1}]).map e.hom)

lemma bijective_app_of_isIso {Y : Scheme.{u}} {F G : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}}
    (φ : F ⟶ G) [IsIso φ] (W : Y.Etale) : Function.Bijective (φ.hom.app (op W)) := by
  have : IsIso ((sheafToPresheaf _ _).map φ) := inferInstance
  have : IsIso (((sheafToPresheaf _ _).map φ).app (op W)) := inferInstance
  exact (ConcreteCategory.isIso_iff_bijective _).1 this

variable [QuasiSeparatedSpace X]

/-- **The unit at a pushforward from the generic point is an isomorphism.** For an integral
quasi-separated scheme `X` with generic point `η : Spec k(X) ⟶ X` and an abelian étale sheaf `M`
on `Spec k(X)`, the unit `η_* M ⟶ η_* η^* η_* M` is an isomorphism: on the sections over an affine
étale `X`-scheme it is the colimit of the units of the nonempty affine opens
(`AlgebraicGeometry.Etale.unitComparison_app_isColimit_of_isLimit`), which are isomorphisms
(`AlgebraicGeometry.Scheme.isIso_affineOpenUnit_lowerStar`). -/
theorem isIso_unit_app_lowerStar_fromSpecFunctionField
    (M : Sheaf (Spec X.functionField).smallEtaleTopology AddCommGrpCat.{u + 1}) :
    IsIso ((upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} X.fromSpecFunctionField).unit.app
      ((X.fromSpecFunctionField)_*[AddCommGrpCat.{u + 1}].obj M)) := by
  set G := (X.fromSpecFunctionField)_*[AddCommGrpCat.{u + 1}].obj M
  let ε := (upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} X.fromSpecFunctionField).unit.app G
  let D := X.affineOpensDiagram
  let ι := X.affineOpensDiagramι
  let c := X.functionFieldCone
  have hc : IsLimit c := X.isLimitFunctionFieldCone
  have hP := X.fromSpecFunctionField_eq_functionFieldCone_comp
  let τ (U : X.NonemptyAffineOpens) := unitComparison (c.π.app U) (ι.app U)
    X.fromSpecFunctionField (hP U) G
  have hτ (U : X.NonemptyAffineOpens) : X.affineOpenUnit U G ≫ τ U = ε :=
    unit_app_comp_unitComparison _ _ _ _ G
  refine Etale.isIso_of_bijective_app_of_isAffine ε fun W hW ↦ ⟨?_, fun t ↦ ?_⟩
  · rw [injective_iff_map_eq_zero]
    intro g hg
    let U₀ : X.NonemptyAffineOpens := Classical.arbitrary _
    have h₀ : (τ U₀).hom.app (op W) ((X.affineOpenUnit U₀ G).hom.app (op W) g) = 0 := by
      rw [← hτ U₀] at hg
      exact hg
    obtain ⟨U, f', hU⟩ := exists_unitComparison_app_eq_zero_of_isLimit D ι c
      X.fromSpecFunctionField hP hc G W U₀ _ h₀
    have hgU : (X.affineOpenUnit U G).hom.app (op W) g = 0 := by
      rw [← X.affineOpenUnit_comp_transition f' G]
      exact hU
    have := isIso_affineOpenUnit_lowerStar X U M
    exact (bijective_app_of_isIso _ W).1 (hgU.trans (map_zero _).symm)
  · obtain ⟨U, s, hs⟩ := unitComparison_app_surjective_of_isLimit D ι c
      X.fromSpecFunctionField hP hc G W t
    have := isIso_affineOpenUnit_lowerStar X U M
    obtain ⟨g, rfl⟩ := (bijective_app_of_isIso (X.affineOpenUnit U G) W).2 s
    refine ⟨g, ?_⟩
    rw [← hs, ← hτ U]
    rfl

end Scheme

end AlgebraicGeometry
