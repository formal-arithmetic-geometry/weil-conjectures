/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Endofunctor.IsoAlgebraLeftAdjoint
public import WeilConjectures.WeilSheaf.Localization

/-!
# The open–closed triangle of pro-étale Weil sheaves

Let `j : U ⟶ X` be an open immersion of `k₀`-schemes and `i : Z ⟶ X` a closed immersion whose
range is the complement of that of `j`. This file constructs the open–closed triangle
`j_! j^* M ⟶ M ⟶ Ri_* i^* M ⟶ (j_! j^* M)[1]` on the derived category of pro-étale Weil sheaves
on `X`, the Weil form of blueprint `sk-prop-sf-open-closed-triangle`.

The left adjoint `j_!` of the pullback `j^*` of pro-étale Weil sheaves
(`AlgebraicGeometry.ProEtaleWeilSheaf.upperStarLeftAdjoint`) is the extension by zero `j̄_!` of the
underlying sheaves on the geometric fibers, with the Weil structure for which the adjunction
`j̄_! ⊣ j̄^*` lifts (`CategoryTheory.Endofunctor.IsoAlgebra.leftMateIso`).

## Main declarations

- `AlgebraicGeometry.ProEtaleWeilSheaf.upperStarLeftAdjointAdjunction`: `j_! ⊣ j^*` on
  pro-étale Weil sheaves.
- `AlgebraicGeometry.ProEtaleWeilSheaf.exists_distTriang_openClosed`: the open–closed triangle.
-/

@[expose] public section

universe u

open CategoryTheory Limits Pretriangulated Endofunctor

namespace AlgebraicGeometry

open ProEtale

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime]

section ExtensionByZero

variable {U X : Scheme.{u}} [U.Over (Spec (CommRingCat.of k₀))]
  [X.Over (Spec (CommRingCat.of k₀))] (j : U ⟶ X) [IsOpenImmersion j]
  [j.IsOver (Spec (CommRingCat.of k₀))]

variable (k₀ l) in
/-- The left adjoint `j_!` of the pullback `j^*` of pro-étale Weil sheaves along an open
immersion `j`: the extension by zero `j̄_!` along the base change `j̄ : Ū ⟶ X̄`, with the Weil
structure for which `j̄_! ⊣ j̄^*` lifts to pro-étale Weil sheaves. -/
noncomputable def ProEtaleWeilSheaf.upperStarLeftAdjoint :
    ProEtaleWeilSheaf k₀ l U ⥤ ProEtaleWeilSheaf k₀ l X :=
  IsoAlgebra.mapOfNatIso (IsoAlgebra.leftMateIso
    (adicOpenImmersionLowerShriekAdjunction l (Scheme.Hom.geometricFiberMap j (comp_over j _)))
    (adicUpperStarGeometricFiberMapCompFrobeniusIso l j (comp_over j _)))

variable (k₀ l) in
/-- The adjunction `j_! ⊣ j^*` of pro-étale Weil sheaves along an open immersion `j`, lifting the
adjunction `j̄_! ⊣ j̄^*` of the underlying sheaves. -/
noncomputable def ProEtaleWeilSheaf.upperStarLeftAdjointAdjunction :
    ProEtaleWeilSheaf.upperStarLeftAdjoint k₀ l j ⊣ ProEtaleWeilSheaf.upperStar k₀ l j :=
  IsoAlgebra.mapOfNatIsoLeftMateIsoAdjunction _ _

instance : (ProEtaleWeilSheaf.upperStarLeftAdjoint k₀ l j).Additive :=
  IsoAlgebra.additive_mapOfNatIso _

instance : PreservesFiniteLimits (ProEtaleWeilSheaf.upperStarLeftAdjoint k₀ l j) :=
  IsoAlgebra.preservesFiniteLimits_mapOfNatIso _

instance : PreservesFiniteColimits (ProEtaleWeilSheaf.upperStarLeftAdjoint k₀ l j) :=
  IsoAlgebra.preservesFiniteColimits_mapOfNatIso _

/-- The unit `F ⟶ j^* j_! F` is invertible, as is the unit of `j̄_! ⊣ j̄^*`. -/
instance : IsIso (ProEtaleWeilSheaf.upperStarLeftAdjointAdjunction k₀ l j).unit :=
  IsoAlgebra.isIso_mapOfNatIsoAdjunction_unit _ _ _ (IsoAlgebra.mateEquiv_leftMateIso_inv _ _)

omit [IsOpenImmersion j] in
/-- The ranges of the base changes to `k̄` of morphisms with disjoint ranges are disjoint. -/
lemma Scheme.Hom.inter_range_geometricFiberMap_eq_empty {W : Scheme.{u}}
    [W.Over (Spec (CommRingCat.of k₀))] (φ : W ⟶ X) [φ.IsOver (Spec (CommRingCat.of k₀))]
    (h : Disjoint (Set.range j.base) (Set.range φ.base)) :
    Set.range (Scheme.Hom.geometricFiberMap j (comp_over j (Spec (CommRingCat.of k₀)))).base ∩
      Set.range (Scheme.Hom.geometricFiberMap φ (comp_over φ (Spec (CommRingCat.of k₀)))).base =
        ∅ := by
  rw [Scheme.Hom.range_geometricFiberMap, Scheme.Hom.range_geometricFiberMap]
  exact Set.disjoint_iff_inter_eq_empty.1 (h.preimage _)

/-- `φ^* j_! = 0` for a morphism `φ` whose range misses that of `j`. -/
lemma ProEtaleWeilSheaf.isZero_upperStar_obj_upperStarLeftAdjoint_obj {W : Scheme.{u}}
    [W.Over (Spec (CommRingCat.of k₀))] (φ : W ⟶ X) [φ.IsOver (Spec (CommRingCat.of k₀))]
    (h : Disjoint (Set.range j.base) (Set.range φ.base)) (F : ProEtaleWeilSheaf k₀ l U) :
    IsZero ((ProEtaleWeilSheaf.upperStar k₀ l φ).obj
      ((ProEtaleWeilSheaf.upperStarLeftAdjoint k₀ l j).obj F)) :=
  (ProEtaleWeilSheaf.isZero_iff _).2 (isZero_adicUpperStar_adicOpenImmersionLowerShriek _ _
    (Scheme.Hom.inter_range_geometricFiberMap_eq_empty j φ h) F.carrier)

/-- `φ^* j_! = 0`, for the extension by zero `j_!` of pro-étale Weil sheaves, along a morphism
`φ` whose range misses that of `j`. -/
lemma ProEtaleWeilSheaf.isZero_upperStar_obj_extensionByZero_obj {W : Scheme.{u}}
    [W.Over (Spec (CommRingCat.of k₀))] (φ : W ⟶ X) [φ.IsOver (Spec (CommRingCat.of k₀))]
    (h : Disjoint (Set.range j.base) (Set.range φ.base)) (F : ProEtaleWeilSheaf k₀ l U) :
    IsZero ((ProEtaleWeilSheaf.upperStar k₀ l φ).obj
      ((ProEtaleWeilSheaf.extensionByZero k₀ l j).obj F)) :=
  (ProEtaleWeilSheaf.isZero_iff _).2 (isZero_adicUpperStar_adicOpenImmersionLowerShriek _ _
    (Scheme.Hom.inter_range_geometricFiberMap_eq_empty j φ h) F.carrier)

end ExtensionByZero

section Triangle

variable {Z U X : Scheme.{u}} [Z.Over (Spec (CommRingCat.of k₀))]
  [U.Over (Spec (CommRingCat.of k₀))] [X.Over (Spec (CommRingCat.of k₀))]
  (j : U ⟶ X) [IsOpenImmersion j] [QuasiCompact j] [j.IsOver (Spec (CommRingCat.of k₀))]
  (i : Z ⟶ X) [IsClosedImmersion i] [i.IsOver (Spec (CommRingCat.of k₀))]

variable (k₀ l) in
/-- The derived adjunction `D(j_!) ⊣ D(j^*)` of pro-étale Weil sheaves along an open immersion. -/
noncomputable def ProEtaleWeilSheaf.derivedUpperStarLeftAdjointAdjunction :
    (ProEtaleWeilSheaf.upperStarLeftAdjoint k₀ l j).mapDerivedCategory ⊣
      (ProEtaleWeilSheaf.upperStar k₀ l j).mapDerivedCategory :=
  (ProEtaleWeilSheaf.upperStarLeftAdjointAdjunction k₀ l j).mapDerivedCategoryRightDerivedAdjunction.ofNatIsoRight
    (ProEtaleWeilSheaf.upperStar k₀ l j).rightDerivedFunctorIsoMapDerivedCategory

/-- The unit of `D(j_!) ⊣ D(j^*)` is invertible: `D(j^*) ∘ D(j_!) ≅ D(j^* j_!) ≅ 𝟭`, so `D(j_!)` is
fully faithful. -/
instance : IsIso (ProEtaleWeilSheaf.derivedUpperStarLeftAdjointAdjunction k₀ l j).unit := by
  have h := (ProEtaleWeilSheaf.derivedUpperStarLeftAdjointAdjunction k₀ l j).fullyFaithfulLOfCompIsoId
    ((Functor.mapDerivedCategoryCompIso _ _).symm ≪≫
      Functor.mapDerivedCategoryNatIso
        (asIso (ProEtaleWeilSheaf.upperStarLeftAdjointAdjunction k₀ l j).unit).symm ≪≫
        Functor.mapDerivedCategoryIdIso _)
  have := h.full
  have := h.faithful
  infer_instance

/-- **The open–closed triangle of pro-étale Weil sheaves** (blueprint
`sk-prop-sf-open-closed-triangle`, for pro-étale Weil sheaves): for complementary `j` and `i`
and `M` in the derived category of pro-étale Weil sheaves on `X`, the counit of
`D(j_!) ⊣ D(j^*)` and the unit of `D(i^*) ⊣ Ri_*` extend to a distinguished triangle
`j_! j^* M ⟶ M ⟶ Ri_* i^* M ⟶ (j_! j^* M)[1]`.

Complete the counit to a distinguished triangle `j_! j^* M ⟶ M ⟶[g] C`. Then `j^* C = 0`, the
unit of `D(j_!) ⊣ D(j^*)` being invertible, so the unit `C ⟶ Ri_* i^* C` is invertible
(`DerivedCategory.isIso_mapDerivedCategoryRightDerivedAdjunction_unit_app_of_isZero`); and
`i^* g` is invertible, as `i^* j_! = 0`. -/
theorem ProEtaleWeilSheaf.exists_distTriang_openClosed
    (hij : IsCompl (Set.range i.base) (Set.range j.base))
    (M : DerivedCategory (ProEtaleWeilSheaf k₀ l X)) :
    ∃ w, Triangle.mk ((ProEtaleWeilSheaf.derivedUpperStarLeftAdjointAdjunction k₀ l j).counit.app M)
      ((ProEtaleWeilSheaf.derivedUpperStarLowerStarAdjunction k₀ l i).unit.app M) w ∈
        distTriang _ := by
  have := ProEtaleWeilSheaf.preservesFiniteColimits_lowerStar_of_isCompl (k₀ := k₀) (l := l)
    i j hij
  let adj := ProEtaleWeilSheaf.derivedUpperStarLowerStarAdjunction k₀ l i
  let adj' := ProEtaleWeilSheaf.derivedUpperStarLeftAdjointAdjunction k₀ l j
  let jU := (ProEtaleWeilSheaf.upperStar k₀ l j).mapDerivedCategory
  let iU := (ProEtaleWeilSheaf.upperStar k₀ l i).mapDerivedCategory
  obtain ⟨C, g, h, hT⟩ := distinguished_cocone_triangle (adj'.counit.app M)
  -- `j^* C = 0`, since `j^*` of the counit is invertible
  have hCj : IsZero (jU.obj C) := by
    refine (Triangle.isZero₃_iff_isIso₁ _ (jU.map_distinguished _ hT)).2 ?_
    change IsIso (jU.map (adj'.counit.app M))
    rw [← IsIso.inv_eq_of_hom_inv_id (adj'.right_triangle_components M)]
    infer_instance
  -- `i^* g` is invertible, since `i^* j_! j^* M = 0`
  have hgi : IsIso (iU.map g) := by
    refine (Triangle.isZero₁_iff_isIso₂ _ (iU.map_distinguished _ hT)).1 ?_
    have h0 (F : ProEtaleWeilSheaf k₀ l U) : IsZero ((ProEtaleWeilSheaf.upperStarLeftAdjoint k₀ l j ⋙
        ProEtaleWeilSheaf.upperStar k₀ l i).obj F) :=
      ProEtaleWeilSheaf.isZero_upperStar_obj_upperStarLeftAdjoint_obj j i hij.symm.disjoint F
    exact (Functor.isZero_mapDerivedCategory_obj
      (ProEtaleWeilSheaf.upperStarLeftAdjoint k₀ l j ⋙ ProEtaleWeilSheaf.upperStar k₀ l i) _
      fun _ ↦ h0 _).of_iso
      (((ProEtaleWeilSheaf.upperStarLeftAdjoint k₀ l j).mapDerivedCategoryCompIso
        (ProEtaleWeilSheaf.upperStar k₀ l i)).symm.app _)
  -- the unit `C ⟶ Ri_* i^* C` is invertible
  have hηC : IsIso (adj.unit.app C) :=
    DerivedCategory.isIso_mapDerivedCategoryRightDerivedAdjunction_unit_app_of_isZero
      (ProEtaleWeilSheaf.upperStarLowerStarAdjunction k₀ l i)
      (ProEtaleWeilSheaf.isZero_upperStar_obj_lowerStar_obj i j hij)
      (ProEtaleWeilSheaf.isZero_of_isZero_upperStar_of_isCompl i j hij) hCj
  let e : C ≅ (ProEtaleWeilSheaf.lowerStar k₀ l i).rightDerivedFunctor.obj (iU.obj M) :=
    asIso (adj.unit.app C) ≪≫
      (ProEtaleWeilSheaf.lowerStar k₀ l i).rightDerivedFunctor.mapIso (asIso (iU.map g)).symm
  have he : g ≫ e.hom = adj.unit.app M := by
    have := adj.unit.naturality g
    dsimp at this
    simp only [e, Iso.trans_hom, asIso_hom, Functor.mapIso_hom, Iso.symm_hom, asIso_inv]
    rw [reassoc_of% this, ← Functor.map_comp, IsIso.hom_inv_id, CategoryTheory.Functor.map_id,
      Category.comp_id]
  refine ⟨e.inv ≫ h, isomorphic_distinguished _ hT _ ?_⟩
  have he' : adj.unit.app M ≫ e.inv = g := by rw [← he, Category.assoc, e.hom_inv_id, Category.comp_id]
  refine Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _) e.symm ?_ ?_ ?_
  · exact (Category.comp_id _).trans (Category.id_comp _).symm
  · exact he'.trans (Category.id_comp _).symm
  · exact (congrArg _ (CategoryTheory.Functor.map_id _ _)).trans (Category.comp_id _)

end Triangle

end AlgebraicGeometry
