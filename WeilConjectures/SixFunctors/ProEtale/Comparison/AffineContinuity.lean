/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Sites.LimitSystem.DerivedContinuity
public import WeilConjectures.SixFunctors.ProEtale.Comparison.SiteComparison
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.GlobalSections

/-!
# Pro-étale cohomology of a pro-étale affine

Let `U = lim Uᵢ` be a cofiltered limit of quasi-compact quasi-separated schemes `Uᵢ` over `X`
with affine transition maps (for instance a pro-étale affine over `X`), and let `K` be a bounded
below complex of abelian étale sheaves on `X`. Then the canonical maps

`colimᵢ Hⁿ((Uᵢ)_ét, K|_{Uᵢ}) ⟶ Hⁿ(U_ét, K|_U) ⟶ Hⁿ(U_proét, (ν_X^* K)|_U)`

are bijective (`AlgebraicGeometry.ProEtale.proEtaleHyperH_affine_continuity`): the first by
continuity of étale cohomology (`AlgebraicGeometry.Etale.isHyperHContinuousAt_of_isLimit`), the
second because `D(ν^*)` is fully faithful on bounded below complexes and commutes with the
restriction to `U`.
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale

open Etale

/-- The comparison pullback `ν^*` sends constant étale sheaves of abelian groups to constant
pro-étale sheaves: `constantSheaf ⋙ ν^*` and `constantSheaf` are both left adjoint to the
global sections. -/
noncomputable def comparisonUpperStarConstantSheafIsoAddCommGrpCat (X : Scheme.{u}) :
    constantSheaf X.smallEtaleTopology AddCommGrpCat.{u + 1} ⋙ ν^*(X)[AddCommGrpCat.{u + 1}] ≅
      constantSheaf (Scheme.ProEt.topology X) AddCommGrpCat.{u + 1} :=
  (((constantSheafAdj X.smallEtaleTopology AddCommGrpCat.{u + 1}
      (Scheme.Etale.isTerminalMkId X)).comp
      (comparisonAdjunction AddCommGrpCat.{u + 1} X)).ofNatIsoRight
    ((Scheme.toProEt X).sheafPushforwardContinuousCompSheafSectionsObjIso AddCommGrpCat.{u + 1}
      X.smallEtaleTopology (Scheme.ProEt.topology X)
        (Opposite.op (Scheme.Etale.mk (𝟙 X))))).leftAdjointUniq
    (constantSheafAdj (Scheme.ProEt.topology X) AddCommGrpCat.{u + 1}
      (Scheme.ProEt.isTerminalMkId X))

/-- The constant pro-étale sheaf `ℤ`. -/
noncomputable abbrev proUnitSheaf (U : Scheme.{u}) :
    Sheaf (Scheme.ProEt.topology U) AddCommGrpCat.{u + 1} :=
  (constantSheaf (Scheme.ProEt.topology U) AddCommGrpCat.{u + 1}).obj
    (AddCommGrpCat.of (ULift.{u + 1} ℤ))

/-- The pro-étale hypercohomology `Hⁿ(U_proét, L) = Hom(ℤ, L[n])`. -/
abbrev proHyperH {U : Scheme.{u}}
    (L : DerivedCategory (Sheaf (Scheme.ProEt.topology U) AddCommGrpCat.{u + 1})) (n : ℤ) :
    Type (u + 1) :=
  ShiftedHom ((DerivedCategory.singleFunctor _ 0).obj (proUnitSheaf U)) L n

/-- The comparison `ν^* ℤ_U ≅ ℤ_U` in the derived category. -/
noncomputable def comparisonUnitSheafIso (U : Scheme.{u}) :
    (DerivedCategory.singleFunctor _ 0).obj (proUnitSheaf U) ≅
      D(ν^*(U)[AddCommGrpCat.{u + 1}]).obj
        ((DerivedCategory.singleFunctor _ 0).obj (unitSheaf U)) :=
  (DerivedCategory.singleFunctor _ 0).mapIso
      ((comparisonUpperStarConstantSheafIsoAddCommGrpCat U).symm.app _) ≪≫
    ((ν^*(U)[AddCommGrpCat.{u + 1}].mapDerivedCategorySingleFunctor 0).app _).symm

/-- The comparison pullbacks commute with restriction along `g : Y ⟶ X`, on derived
categories: `g^* ν_X^* ≅ ν_Y^* g^*`. -/
noncomputable def mapDerivedCategoryComparisonUpperStarRestrictIso {Y X : Scheme.{u}}
    (g : Y ⟶ X) :
    D(ν^*(X)[AddCommGrpCat.{u + 1}]) ⋙ D(ProEtale.upperStar AddCommGrpCat.{u + 1} g) ≅
      D(Etale.upperStar AddCommGrpCat.{u + 1} g) ⋙ D(ν^*(Y)[AddCommGrpCat.{u + 1}]) :=
  (Functor.mapDerivedCategoryCompIso _ _).symm ≪≫
    Functor.mapDerivedCategoryNatIso (comparisonUpperStarCompUpperStarIso _ g) ≪≫
    Functor.mapDerivedCategoryCompIso _ _

/-- The comparison map `Hⁿ(U_ét, K|_U) ⟶ Hⁿ(U_proét, (ν_X^* K)|_U)` for a morphism
`u : U ⟶ X` and a complex `K` of abelian étale sheaves on `X`. -/
noncomputable def hyperHComparison {U X : Scheme.{u}} (u : U ⟶ X)
    (K : DerivedCategory (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})) (n : ℤ) :
    hyperH (D(Etale.upperStar AddCommGrpCat.{u + 1} u).obj K) n →
      proHyperH (D(ProEtale.upperStar AddCommGrpCat.{u + 1} u).obj
        (D(ν^*(X)[AddCommGrpCat.{u + 1}]).obj K)) n :=
  fun x ↦ (ShiftedHom.mk₀ 0 rfl (comparisonUnitSheafIso U).hom).comp
    ((x.map D(ν^*(U)[AddCommGrpCat.{u + 1}])).comp
      (ShiftedHom.mk₀ 0 rfl ((mapDerivedCategoryComparisonUpperStarRestrictIso u).inv.app K))
      (zero_add n)) (add_zero n)

private lemma bijective_shiftedHom_comp_mk₀ {C : Type*} [Category C] [HasShift C ℤ]
    {X Y Z : C} (e : Y ≅ Z) (n : ℤ) :
    Function.Bijective (fun x : ShiftedHom X Y n ↦
      x.comp (ShiftedHom.mk₀ 0 rfl e.hom) (zero_add n)) :=
  (shiftedHomPostcompEquiv e n).bijective

private lemma bijective_mk₀_comp {C : Type*} [Category C] [HasShift C ℤ]
    {X Y Z : C} (e : X ≅ Y) (n : ℤ) :
    Function.Bijective (fun x : ShiftedHom Y Z n ↦
      (ShiftedHom.mk₀ 0 rfl e.hom).comp x (add_zero n)) := by
  refine ⟨fun x y h ↦ ?_, fun x ↦ ⟨(ShiftedHom.mk₀ 0 rfl e.inv).comp x (add_zero n), ?_⟩⟩
  · have := congrArg (fun z ↦ (ShiftedHom.mk₀ 0 rfl e.inv).comp z (add_zero n)) h
    simpa [ShiftedHom.mk₀_comp] using this
  · simp [ShiftedHom.mk₀_comp]

/-- `D(ν^*)` is bijective on morphisms between bounded below complexes. -/
lemma bijective_comparisonUpperStar_mapDerivedCategory_map_of_isGE {U : Scheme.{u}}
    (P M : DerivedCategory (Sheaf U.smallEtaleTopology AddCommGrpCat.{u + 1})) (a b : ℤ)
    [P.IsGE b] [M.IsGE a] :
    Function.Bijective (fun g : P ⟶ M ↦
      (comparisonUpperStar AddCommGrpCat.{u + 1} U).mapDerivedCategory.map g) := by
  let P' : DerivedCategory.Plus (Sheaf U.smallEtaleTopology AddCommGrpCat.{u + 1}) :=
    ⟨P, b, inferInstance⟩
  let M' : DerivedCategory.Plus (Sheaf U.smallEtaleTopology AddCommGrpCat.{u + 1}) :=
    ⟨M, a, inferInstance⟩
  let e₁ := Equiv.ofBijective _ ((ObjectProperty.fullyFaithfulι _).map_bijective P' M')
  have h₂ := (fullyFaithfulComparisonUpperStarMapDerivedCategoryPlus
    AddCommGrpCat.{u + 1} U).map_bijective P' M'
  have h₃ := (ObjectProperty.fullyFaithfulι _).map_bijective
    ((comparisonUpperStar AddCommGrpCat.{u + 1} U).mapDerivedCategoryPlus.obj P')
    ((comparisonUpperStar AddCommGrpCat.{u + 1} U).mapDerivedCategoryPlus.obj M')
  have key : (fun g : P ⟶ M ↦
      (comparisonUpperStar AddCommGrpCat.{u + 1} U).mapDerivedCategory.map g) =
      (fun x ↦ DerivedCategory.Plus.ι.map
        ((comparisonUpperStar AddCommGrpCat.{u + 1} U).mapDerivedCategoryPlus.map x)) ∘
        e₁.symm := by
    funext g
    conv_lhs => rw [← e₁.apply_symm_apply g]
    rfl
  rw [key]
  exact (h₃.comp h₂).comp e₁.symm.bijective

/-- `Hⁿ(U_ét, L) ⟶ Hⁿ(U_proét, ν^* L)` is bijective for bounded below `L`. -/
lemma bijective_shiftedHom_map_comparisonUpperStar {U : Scheme.{u}}
    (P L : DerivedCategory (Sheaf U.smallEtaleTopology AddCommGrpCat.{u + 1})) (a b n : ℤ)
    [P.IsGE b] [L.IsGE a] :
    Function.Bijective (fun x : ShiftedHom P L n ↦
      x.map (comparisonUpperStar AddCommGrpCat.{u + 1} U).mapDerivedCategory) := by
  have : (L⟦n⟧).IsGE (a - n) := DerivedCategory.TStructure.t.isGE_shift L a n (a - n) (by omega)
  have h := bijective_comparisonUpperStar_mapDerivedCategory_map_of_isGE P (L⟦n⟧) (a - n) b
  have e (x : ShiftedHom P L n) :
      x.map (comparisonUpperStar AddCommGrpCat.{u + 1} U).mapDerivedCategory =
        (comparisonUpperStar AddCommGrpCat.{u + 1} U).mapDerivedCategory.map x ≫
          ((comparisonUpperStar AddCommGrpCat.{u + 1} U).mapDerivedCategory.commShiftIso n).hom.app
            L := rfl
  refine ⟨fun x y hxy ↦ h.1 ?_, fun z ↦ ?_⟩
  · simp only at hxy
    rw [e, e] at hxy
    exact (cancel_mono _).1 hxy
  · obtain ⟨g, hg⟩ := h.2 (z ≫
      ((comparisonUpperStar AddCommGrpCat.{u + 1} U).mapDerivedCategory.commShiftIso n).inv.app L)
    refine ⟨g, ?_⟩
    simp only at hg ⊢
    rw [e, hg, Category.assoc, Iso.inv_hom_id_app]
    exact Category.comp_id _

/-- Blueprint `det-sf-comparison-affine-continuity`: Pro-étale cohomology of a pro-étale affine.

Let `(Dᵢ)` be a cofiltered system of quasi-compact quasi-separated schemes over `X` with affine
transition maps (for instance affine schemes étale over `X`), with limit `U = c.pt`, and let `K`
be a bounded below complex of abelian étale sheaves on `X`. Then
1. `Hⁿ(U_ét, K|_U)` is the colimit of the `Hⁿ((Dᵢ)_ét, K|_{Dᵢ})` along the restriction maps
  (`AlgebraicGeometry.Etale.IsHyperHContinuousAt`), and
2. the comparison map `Hⁿ(U_ét, K|_U) ⟶ Hⁿ(U_proét, (ν_X^* K)|_U)` is bijective. -/
theorem proEtaleHyperH_affine_continuity {X : Scheme.{u}} {I : Type u} [SmallCategory I]
    [IsCofiltered I] (D : I ⥤ Over X) [∀ i, CompactSpace (D.obj i).left]
    [∀ i, QuasiSeparatedSpace (D.obj i).left] [∀ {i j} (g : i ⟶ j), IsAffineHom (D.map g).left]
    (c : Cone D) (hc : IsLimit ((Over.forget X).mapCone c))
    (K : DerivedCategory (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})) (a : ℤ) [K.IsGE a]
    (n : ℤ) :
    IsHyperHContinuousAt D c K n ∧ Function.Bijective (hyperHComparison c.pt.hom K n) := by
  refine ⟨isHyperHContinuousAt_of_isLimit D c hc K a n, ?_⟩
  have : (D(Etale.upperStar AddCommGrpCat.{u + 1} c.pt.hom).obj K).IsGE a :=
    Functor.isGE_mapDerivedCategory_obj _ K a
  exact (bijective_mk₀_comp (comparisonUnitSheafIso c.pt.left) n).comp
    ((bijective_shiftedHom_comp_mk₀
      ((mapDerivedCategoryComparisonUpperStarRestrictIso c.pt.hom).app K).symm n).comp
    (bijective_shiftedHom_map_comparisonUpperStar _ _ a 0 n))

end AlgebraicGeometry.ProEtale
