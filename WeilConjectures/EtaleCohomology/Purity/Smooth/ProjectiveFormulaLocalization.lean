/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.EtaleCohomology.Purity.Smooth.ChernPowMapNaturality
public import WeilConjectures.EtaleCohomology.Purity.Smooth.ProjectiveFormulaTopClass
public import WeilConjectures.EtaleCohomology.Purity.Smooth.ProjectivePointClass

/-!
# The localization step of the projective space formula

Let `P = [0 : ⋯ : 0 : 1] ∈ ℙ = ℙ(Option m; S)`, with complement the total space `W` of `𝒪(1)` on
the hyperplane `H = ℙ(m; S)`. Applying `Rq_*` to the supported localization triangle
`RP_! RP^! Λ ⟶ Λ ⟶ Rj_* Lj^* Λ` gives a distinguished triangle in which:

* the classes `1, h, …, h^{#m - 1}` map isomorphically to `Rq_* Rj_* Λ_W ≅ Rq_{H*} Λ_H`, by homotopy
  invariance for `W ⟶ H` and the projective space formula for `H`, as `h` restricts to the class
  `h` of `H`;
* the class `h^{#m}` is the class of the point `P` with supports forgotten
  (`AlgebraicGeometry.Etale.nonempty_pointClassData`), and maps isomorphically to
  `Rq_* RP_! RP^! Λ ≅ Λ_S(-#m)[-2#m]` by purity for the point.

Hence `(1, h, …, h^{#m})` is an isomorphism (`AlgebraicGeometry.Etale.projectiveFormula_option`).
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

open ProjectiveSpace

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ] [HasKummerClass Λ] (n : Type u)
  (S : Scheme.{u}) [HasInvertibleExponent Λ S]

variable {Λ n S}

variable [HasKummerClass.IsNormalized Λ] {k : Type u} [Field k] (aS : S ⟶ Spec (.of k))
  [IsSeparated aS] [LocallyOfFiniteType aS]

attribute [local instance] HasInvertibleExponent.opens

omit [HasInvertibleExponent Λ S] in
/-- *Homotopy invariance of cohomology classes*: for a vector bundle `π : V ⟶ T` with zero
section `z`, every class `c ∈ H^{2r}(V, Λ(r))` is pulled back from its restriction to the zero
section, `π^* z^* c = c`, since the unit `Λ_T(r)[2r] ⟶ Rπ_* Lπ^* Λ_T(r)[2r]` is invertible
(`AlgebraicGeometry.VectorBundle.isIso_unit_tateObjectShift`). -/
theorem VectorBundle.classRestriction_classRestriction_zero
    {V T : Scheme.{u}} {d : ℕ} {π : V ⟶ T} (E : VectorBundle d π) [HasInvertibleExponent Λ V]
    [HasInvertibleExponent Λ T] (aT : T ⟶ Spec (.of k)) [IsSeparated aT]
    [LocallyOfFiniteType aT] {r : ℕ}
    (c : constantComplex Λ V ⟶ (tateObject Λ V r)⟦2 * (r : ℤ)⟧) :
    VectorBundle.classRestriction Λ π (VectorBundle.classRestriction Λ E.zero c) = c := by
  let adj := derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) π
  have hπ := E.isIso_unit_tateObjectShift Λ aT r
  let b : constantComplex Λ T ⟶ (tateObject Λ T r)⟦2 * (r : ℤ)⟧ :=
    adj.homEquiv _ _ ((leftDerivedUpperStarConstantComplexIso Λ π).hom ≫ c ≫
      (leftDerivedUpperStarTateShiftIso Λ π r).inv) ≫
      inv (adj.unit.app ((tateObject Λ T r)⟦2 * (r : ℤ)⟧))
  have hb : VectorBundle.classRestriction Λ π b = c := by
    have h₁ : (L((π)^*[ModuleCat.{u + 1} Λ])).map b =
        (leftDerivedUpperStarConstantComplexIso Λ π).hom ≫ c ≫
          (leftDerivedUpperStarTateShiftIso Λ π r).inv := by
      apply (adj.homEquiv _ _).injective
      have hn := adj.unit.naturality b
      simp only [Functor.id_map, Functor.comp_map] at hn
      rw [Adjunction.homEquiv_unit, ← hn]
      simp only [b, Category.assoc, IsIso.inv_hom_id, Category.comp_id]
    simp only [VectorBundle.classRestriction, h₁, Category.assoc, Iso.inv_hom_id_assoc,
      Iso.inv_hom_id, Category.comp_id]
  rw [← hb, ← VectorBundle.classRestriction_comp Λ E.zero π (𝟙 T) E.zero_comp.symm,
    VectorBundle.classRestriction_id]

include aS in
/-- *The classes `1, h, …, hʳ` on the complement of the point.* Let `W ⊆ ℙ(Option (Option n); S)`
be the total space of `𝒪(1)` on the hyperplane `H = ℙ(Option n; S)`, the complement of the point
`[0 : ⋯ : 0 : 1]`. If the projective space formula holds for `H`, then
`(1, h, …, hʳ) : ⊕_{a ≤ r} Λ_S(-a)[-2a] ⟶ Rq_* Λ ⟶ Rq_* Rj_* Λ_W` is an isomorphism: the class `h`
restricts on `W` to the pullback of the class `h` of `H`
(`AlgebraicGeometry.Etale.classRestriction_hyperplane_hyperplaneChernClass_eq` and homotopy
invariance), the map is natural (`AlgebraicGeometry.Etale.chernPowMap_comp`) and
`Λ_H ⟶ Rπ_* Λ_W` is invertible. -/
theorem isIso_biproduct_desc_chernPowMap_comp_unit {n : Type u} [Fintype n]
    (IH : IsIso (projectiveFormulaMap (ℙ(Option n; S) ↘ S)
      (hyperplaneChernClass (hyperplaneClass Λ n aS)) (Fintype.card n))) :
    IsIso (biproduct.desc (fun a : Fin (Fintype.card n + 1) ↦
        chernPowMap (ℙ(Option (Option n); S) ↘ S)
          (hyperplaneChernClass (hyperplaneClass Λ (Option n) aS)) a) ≫
      (R((ℙ(Option (Option n); S) ↘ S)_*[ModuleCat.{u + 1} Λ])).map
        ((derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ)
          (twistBundleOpen (Option n) S).ι).unit.app
            (constantComplex Λ ℙ(Option (Option n); S)))) := by
  set q := ℙ(Option (Option n); S) ↘ S
  set qH := ℙ(Option n; S) ↘ S
  set j := (twistBundleOpen (Option n) S).ι
  set π := twistBundleπ (Option n) S
  set hP := hyperplaneChernClass (hyperplaneClass Λ (Option n) aS)
  set hH := hyperplaneChernClass (hyperplaneClass Λ n aS)
  have hc : j ≫ q = π ≫ qH := (twistBundleπ_over (Option n) S).symm
  have hW : VectorBundle.classRestriction Λ (r := 1) j hP =
      VectorBundle.classRestriction Λ (r := 1) π hH := by
    simp only [hP, hH]
    rw [← classRestriction_hyperplane_hyperplaneChernClass_eq aS (m := n),
      VectorBundle.classRestriction_comp Λ (twistBundleZero (Option n) S) j
        (hyperplane (Option n) S) (twistBundleZero_ι (Option n) S).symm,
      ← twistBundle_zero,
      VectorBundle.classRestriction_classRestriction_zero (twistBundle (Option n) S) (qH ≫ aS)]
  -- the unit `Λ_H ⟶ Rπ_* Λ_W` is invertible
  have hu : IsIso (constantComplexUnit Λ π) := by
    have h₀ := (twistBundle (Option n) S).isIso_unit_tateObjectShift Λ (qH ≫ aS) 0
    have := isIso_unit_app_of_iso (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) π)
      (tateObjectShiftZeroIso' (Λ := Λ) (X := ℙ(Option n; S))) h₀
    exact IsIso.comp_isIso' this inferInstance
  let Z₁ := (R((q)_*[ModuleCat.{u + 1} Λ])).map ((R((j)_*[ModuleCat.{u + 1} Λ])).map
      (leftDerivedUpperStarConstantComplexIso Λ j).hom) ≫
    (rightDerivedLowerStarCompIso j q (j ≫ q) rfl).hom.app _
  let Z₂ := (R((qH)_*[ModuleCat.{u + 1} Λ])).map (constantComplexUnit Λ π) ≫
    (rightDerivedLowerStarCompIso π qH (j ≫ q) hc).hom.app _
  have key : (biproduct.desc (fun a : Fin (Fintype.card n + 1) ↦ chernPowMap q hP a) ≫
      (R((q)_*[ModuleCat.{u + 1} Λ])).map
        ((derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) j).unit.app
          (constantComplex Λ ℙ(Option (Option n); S)))) ≫ Z₁ =
      projectiveFormulaMap qH hH (Fintype.card n) ≫ Z₂ := by
    refine biproduct.hom_ext' _ _ fun a ↦ ?_
    have h₁ := chernPowMap_comp j q (j ≫ q) rfl hP a
    have h₂ := chernPowMap_comp π qH (j ≫ q) hc hH a
    rw [hW, h₂] at h₁
    simp only [projectiveFormulaMap, biproduct.ι_desc_assoc, Category.assoc, Z₁, Z₂]
    rw [h₁, ← Functor.map_comp_assoc]
    rfl
  have : IsIso Z₁ := by
    dsimp only [Z₁]
    infer_instance
  have : IsIso Z₂ := by
    dsimp only [Z₂]
    infer_instance
  have : IsIso ((biproduct.desc (fun a : Fin (Fintype.card n + 1) ↦ chernPowMap q hP a) ≫
      (R((q)_*[ModuleCat.{u + 1} Λ])).map
        ((derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) j).unit.app
          (constantComplex Λ ℙ(Option (Option n); S)))) ≫ Z₁) := by
    rw [key]
    infer_instance
  exact IsIso.of_isIso_comp_right _ Z₁

include aS in
/-- *Induction step of the projective space formula*: if it holds for `ℙ(Option n; S)`, it holds
for `ℙ(Option (Option n); S)`.

Let `P = [0 : ⋯ : 0 : 1]`, with complement the total space `W` of `𝒪(1)` on the hyperplane. Apply
`Rq_*` to the supported localization triangle `RP_! RP^! Λ ⟶ Λ ⟶ Rj_* Lj^* Λ`
(`AlgebraicGeometry.Etale.supportedLocalizationTriangle_mem_distTriang`). The classes
`1, h, …, hʳ` map isomorphically to the third term
(`AlgebraicGeometry.Etale.isIso_biproduct_desc_chernPowMap_comp_unit`), and `h^{r+1}` is the class
of the point with supports forgotten (`AlgebraicGeometry.Etale.nonempty_pointClassData`), which
by purity for the point factors through an isomorphism onto the first term
(`AlgebraicGeometry.Etale.exists_isIso_comp_map_counit_eq_chernPowMap`). Conclude by the morphism
from the split triangle (`AlgebraicGeometry.Etale.isIso_biprod_desc_of_distTriang`). -/
lemma projectiveFormula_option {n : Type u} [Fintype n] (h : ProjectiveFormula Λ S n) :
    ProjectiveFormula Λ S (Option n) := by
  intro γ hγ
  obtain rfl := eq_hyperplaneClass aS hγ
  obtain ⟨D⟩ := nonempty_pointClassData Λ (Option n) aS
  have := D.isIso_comp
  obtain ⟨ψ, hψ, hψε⟩ := exists_isIso_comp_map_counit_eq_chernPowMap
    (ℙ(Option (Option n); S) ↘ S) D.i _ _ D.γ D.isIso_supportedClassMap D.forget_eq
  have hT := supportedLocalizationTriangle_mem_distTriang (ModuleCat.{u + 1} Λ) D.i
    (twistBundleOpen (Option n) S).ι D.range_eq (constantComplex Λ ℙ(Option (Option n); S))
  have : (R((ℙ(Option (Option n); S) ↘ S)_*[ModuleCat.{u + 1} Λ])).IsTriangulated :=
    (mapDerivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ)
      (ℙ(Option (Option n); S) ↘ S)).isTriangulated_rightAdjoint
  have := isIso_biproduct_desc_chernPowMap_comp_unit aS
    (h _ (isHyperplaneClass_hyperplaneClass aS))
  have hiso := isIso_biprod_desc_of_distTriang
    ((R((ℙ(Option (Option n); S) ↘ S)_*[ModuleCat.{u + 1} Λ])).map
      ((rightDerivedUpperShriekAdjunction (ModuleCat.{u + 1} Λ) D.i).counit.app
        (constantComplex Λ ℙ(Option (Option n); S))))
    ((R((ℙ(Option (Option n); S) ↘ S)_*[ModuleCat.{u + 1} Λ])).map
      ((derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ)
        (twistBundleOpen (Option n) S).ι).unit.app (constantComplex Λ ℙ(Option (Option n); S))))
    _ ((R((ℙ(Option (Option n); S) ↘ S)_*[ModuleCat.{u + 1} Λ])).map_distinguished _ hT) ψ
    (biproduct.desc fun a : Fin (Fintype.card n + 1) ↦ chernPowMap (ℙ(Option (Option n); S) ↘ S)
      (hyperplaneChernClass (hyperplaneClass Λ (Option n) aS)) a)
  rw [hψε, Fintype.card_option] at hiso
  suffices key : ∀ r, r = Fintype.card n + 1 → IsIso (projectiveFormulaMap
      (ℙ(Option (Option n); S) ↘ S) (hyperplaneChernClass (hyperplaneClass Λ (Option n) aS)) r) from
    key _ Fintype.card_option
  rintro r rfl
  exact isIso_biproduct_desc_of_isIso_biprod_desc (fun a ↦ chernPowMap _ _ a) hiso

end Etale

end AlgebraicGeometry
