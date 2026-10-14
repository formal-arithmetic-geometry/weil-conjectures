/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.CategoryTheory.Functor.OfSequence
public import WeilConjectures.Algebra.Homology.DerivedCategory.KInjectiveTower
public import WeilConjectures.CategoryTheory.Triangulated.DerivedCountableProductsCore
public import WeilConjectures.CategoryTheory.Triangulated.DerivedCountableProductsProperties
public import WeilConjectures.CategoryTheory.Triangulated.HomotopyLimit

/-!
# Existence and computation of derived limits

A derived limit of a tower `⋯ ⟶ K₂ ⟶ K₁ ⟶ K₀` in a pretriangulated category is the point of a
homotopy limit cone (`CategoryTheory.Pretriangulated.IsHomotopyLimit`), i.e. the first term of
a distinguished Roos triangle `R lim Kₙ ⟶ ∏ Kₙ ──1 - t──▶ ∏ Kₙ ⟶ (R lim Kₙ)[1]`.

## Main statements

- `CategoryTheory.Pretriangulated.exists_isHomotopyLimit_ofOpSequence`: if `∏ Kₙ` exists, a
  homotopy limit cone exists, and homotopy limits are unique up to isomorphism.
- `DerivedCategory.hasCountableProducts_and_preservesLimitsOfShape`: if `A` has exact countable
  products, so does `D(A)`; termwise products of complexes represent them, and cohomology
  commutes with them.
- `DerivedCategory.isHomotopyLimit_mapCone_of_isKInjective`: if `I` is a K-injective complex
  of towers, the limit `lim Iₙ` represents the derived limit `R lim Iₙ`.

(blueprint: `lem-weil-derived-limit-existence`)
-/

@[expose] public section

universe w v u

open CategoryTheory Limits Opposite

namespace CategoryTheory.Pretriangulated

variable {C : Type*} [Category C] [HasZeroObject C] [HasShift C ℤ] [Preadditive C]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]

/-- Part (1) of `lem-weil-derived-limit-existence`: if the product `∏ Kₙ` of the terms of a
tower `(Kₙ, fₙ)` exists, the tower has a homotopy limit cone (by TR1, completing `1 - t` to a
distinguished triangle), and any two homotopy limit cones have isomorphic points (by TR3).

(blueprint: `lem-weil-derived-limit-existence`) -/
theorem exists_isHomotopyLimit_ofOpSequence {K : ℕ → C} [HasProduct K]
    (f : ∀ n : ℕ, K (n + 1) ⟶ K n) :
    (∃ c : Cone (Functor.ofOpSequence f), IsHomotopyLimit c) ∧
      ∀ c c' : Cone (Functor.ofOpSequence f), IsHomotopyLimit c → IsHomotopyLimit c' →
        Nonempty (c.pt ≅ c'.pt) := by
  refine ⟨?_, fun c c' hc hc' ↦ ⟨(hc.exists_iso hc').choose⟩⟩
  let F := Functor.ofOpSequence f
  let P : Fan fun n : ℕ ↦ F.obj (op n) := Fan.mk (∏ᶜ K) (Pi.π K)
  let hP : IsLimit P := productIsProduct K
  obtain ⟨L, p, δ, hT⟩ := distinguished_cocone_triangle₁ (𝟙 P.pt - towerShift hP)
  have hp : p ≫ towerShift hP = p := by
    have : p ≫ (𝟙 P.pt - towerShift hP) = 0 := comp_distTriang_mor_zero₁₂ _ hT
    rw [Preadditive.comp_sub, Category.comp_id, sub_eq_zero] at this
    exact this.symm
  let c : Cone F :=
    { pt := L
      π := NatTrans.ofOpSequence (F := (Functor.const ℕᵒᵖ).obj L) (fun n ↦ p ≫ P.proj n)
        fun n ↦ by
          have h := hp =≫ P.proj n
          simp only [Category.assoc, towerShift, Fan.IsLimit.fac] at h
          simpa [F, Functor.ofOpSequence_map_homOfLE_succ] using
            h.symm.trans (Category.assoc _ _ _).symm }
  refine ⟨c, P, hP, δ, ?_⟩
  convert hT
  exact Fan.IsLimit.hom_ext hP _ _ fun n ↦ by simp [c]

end CategoryTheory.Pretriangulated

namespace DerivedCategory

section Products

variable (A : Type u) [Category.{v} A] [Abelian A] [HasDerivedCategory.{w} A]
  [HasCountableProducts A] [CountableAB4Star A]

/-- If `A` has exact countable products, so does its derived category: every object is
`Q.obj X`, and the termwise product of complexes is a product in `D(A)`
(`derivedCategory_termwiseProduct_isLimit`).

(blueprint: `lem-weil-derived-limit-existence`) -/
lemma hasCountableProducts : HasCountableProducts (DerivedCategory A) where
  out J _ := ⟨fun F ↦ by
    let X : J → CochainComplex A ℤ := fun j ↦ Q.objPreimage (F.obj ⟨j⟩)
    obtain ⟨hX⟩ := derivedCategory_termwiseProduct_isLimit A J X
    have : HasLimit (Discrete.functor X ⋙ Q) := HasLimit.mk ⟨_, hX⟩
    exact hasLimit_of_iso (show Discrete.functor X ⋙ Q ≅ F from
      Discrete.natIso fun ⟨j⟩ ↦ Q.objObjPreimageIso (F.obj ⟨j⟩))⟩

/-- Part (2) of `lem-weil-derived-limit-existence`: if `A` has exact countable products, then
`D(A)` has countable products, represented by termwise products of complexes, and the
cohomology functors commute with them.

(blueprint: `lem-weil-derived-limit-existence`) -/
theorem hasCountableProducts_and_preservesLimitsOfShape :
    ∃ _ : HasCountableProducts (DerivedCategory A),
      (∀ (J : Type) [Countable J] (C : J → CochainComplex A ℤ),
        Nonempty (IsLimit (Q.mapCone (limit.cone (Discrete.functor C))))) ∧
      ∀ (J : Type) [Countable J] (p : ℤ),
        PreservesLimitsOfShape (Discrete J) (homologyFunctor A p) :=
  have := hasCountableProducts A
  ⟨this, derivedCategory_countableProducts_properties A⟩

end Products

section KInjective

set_option backward.isDefEq.respectTransparency false

open Tower Pretriangulated

variable {A : Type u} [Category.{v} A] [Abelian A] [HasDerivedCategory.{w} A]
  [HasCountableProducts A] [CountableAB4Star A]

variable (A) in
/-- `Q` sends a product of countably many complexes to a product. -/
noncomputable def isLimitFanMkQ {K : ℕ → CochainComplex A ℤ} (s : Fan K) (hs : IsLimit s) :
    IsLimit (Fan.mk (Q.obj s.pt) fun n ↦ Q.map (s.proj n)) :=
  have : PreservesLimit (Discrete.functor K) Q :=
    preservesLimit_of_preserves_limit_cone (limit.isLimit _)
      (derivedCategory_termwiseProduct_isLimit A ℕ K).some
  (isLimitMapConeFanMkEquiv Q _ _) (isLimitOfPreserves Q (hs.ofIsoLimit (Fan.ext (Iso.refl _)
    (fun _ ↦ by simp))))

/-- Part (3) of `lem-weil-derived-limit-existence`: if `I` is a K-injective complex of towers
in an abelian category with exact countable products, then the image in `D(A)` of a limit cone
of the tower of complexes `I` is a homotopy limit cone. In other words, `lim Iₙ` computes the
derived limit `R lim Iₙ`.

The proof uses the Roos sequence `0 ⟶ I ⟶ ∏ₙ Rₙ(Iₙ) ⟶ ∏ₙ Rₙ₊₁(Iₙ) ⟶ 0` of complexes of
towers (`Tower.roosComplexShortComplex`): its terms are K-injective, so it gives a
distinguished triangle in the homotopy category of towers, which `lim` takes to the Roos
triangle `lim I ⟶ ∏ Iₙ ──1 - t──▶ ∏ Iₙ ⟶`.

(blueprint: `lem-weil-derived-limit-existence`) -/
theorem isHomotopyLimit_mapCone_of_isKInjective (I : CochainComplex (ℕᵒᵖ ⥤ A) ℤ)
    [I.IsKInjective] {c : Cone I.asFunctor} (hc : IsLimit c) :
    IsHomotopyLimit (Q.mapCone c) := by
  let S := roosComplexShortComplex I
  let q := HomotopyCategory.quotient (ℕᵒᵖ ⥤ A) (ComplexShape.up ℤ)
  let desc := CochainComplex.mappingCone.descShortComplex S
  have : QuasiIso desc :=
    CochainComplex.mappingCone.quasiIso_descShortComplex (roosComplexShortComplex_shortExact I)
  have : S.X₂.IsKInjective := isKInjective_roosComplex _ I
  have : S.X₃.IsKInjective := isKInjective_roosComplex _ I
  have : S.X₁.IsKInjective := ‹I.IsKInjective›
  have : IsIso (q.map desc) := CochainComplex.isIso_quotient_map_of_isKInjective desc
  -- The Roos triangle in the homotopy category of towers.
  let T₀ := Triangle.mk (q.map S.f) (q.map S.g)
    (inv (q.map desc) ≫ (CochainComplex.mappingCone.triangleh S.f).mor₃)
  have hT₀ : T₀ ∈ distTriang _ := by
    refine isomorphic_distinguished _ (HomotopyCategory.mappingCone_triangleh_distinguished S.f)
      _ (Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _) (asIso (q.map desc)).symm
        (by simp only [T₀, Triangle.mk_mor₁, Iso.refl_hom, Category.comp_id, Category.id_comp]; rfl)
        ?_ (by simp [T₀]))
    simp only [T₀, Triangle.mk_mor₂, Iso.symm_hom, asIso_inv, Iso.refl_hom, Category.id_comp,
      IsIso.comp_inv_eq]
    rw [← CochainComplex.mappingCone.inr_descShortComplex, Functor.map_comp]
    rfl
  -- Its image in `D(A)` under `lim`.
  have hT₁ := ((lim : (ℕᵒᵖ ⥤ A) ⥤ A).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
    Qh).map_distinguished T₀ hT₀
  let L := (lim : (ℕᵒᵖ ⥤ A) ⥤ A).mapHomologicalComplex (ComplexShape.up ℤ)
  let F := (lim : (ℕᵒᵖ ⥤ A) ⥤ A).mapHomotopyCategory (ComplexShape.up ℤ) ⋙ Qh
  let Ψ : q ⋙ F ≅ L ⋙ Q := (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight
      ((lim : (ℕᵒᵖ ⥤ A) ⥤ A).mapHomotopyCategoryFactors (ComplexShape.up ℤ)) Qh ≪≫
      Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft L (quotientCompQhIso A)
  let T₁ := F.mapTriangle.obj T₀
  let T₂ := Triangle.mk (Q.map (L.map S.f)) (Q.map (L.map S.g))
    ((Ψ.app S.X₃).inv ≫ T₁.mor₃ ≫ (shiftFunctor _ (1 : ℤ)).map (Ψ.app S.X₁).hom)
  have hT₂ : T₂ ∈ distTriang _ := by
    refine isomorphic_distinguished _ hT₁ _ (Triangle.isoMk T₂ T₁ (Ψ.app _).symm
      (Ψ.app _).symm (Ψ.app _).symm (Ψ.inv.naturality S.f) (Ψ.inv.naturality S.g) ?_)
    simp only [T₂, Triangle.mk_mor₃, Iso.symm_hom, Iso.app_inv, Category.assoc,
      ← Functor.map_comp, Iso.app_hom, Iso.hom_inv_id_app]
    exact congrArg (Ψ.inv.app S.X₃ ≫ ·)
      ((congrArg (T₁.mor₃ ≫ ·) (CategoryTheory.Functor.map_id _ _)).trans (Category.comp_id _))
  -- The products `∏ Iₙ`.
  let P := Fan.mk (Q.obj (limRoosFan (fun n ↦ n) I).pt) fun n ↦
    Q.map ((limRoosFan (fun n ↦ n) I).proj n)
  have hP : IsLimit P := isLimitFanMkQ A _ (isLimitLimRoosFan _ I)
  let P' := Fan.mk (Q.obj (limRoosFan (· + 1) I).pt) fun n ↦
    Q.map ((limRoosFan (· + 1) I).proj n)
  have hP' : IsLimit P' := isLimitFanMkQ A _ (isLimitLimRoosFan _ I)
  let eP := hP'.conePointUniqueUpToIso hP
  have heP (n : ℕ) : eP.hom ≫ P.proj n = P'.proj n :=
    hP'.conePointUniqueUpToIso_hom_comp hP ⟨n⟩
  have hc' : IsHomotopyLimit (Q.mapCone (limCone I)) := by
    refine ⟨P, hP, eP.inv ≫ T₂.mor₃, isomorphic_distinguished _ hT₂ _
      (Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _) eP.symm ?_ ?_ (by simp))⟩
    · refine Fan.IsLimit.hom_ext hP _ _ fun n ↦ ?_
      simp only [Triangle.mk_mor₁, Iso.refl_hom, Category.comp_id, Fan.IsLimit.fac,
        Functor.mapCone_π_app, Category.id_comp, T₂, P]
      exact (congrArg Q.map (limCone_π_eq I n).symm).trans (Q.map_comp _ _)
    · simp only [Triangle.mk_mor₂, Iso.symm_hom, Iso.refl_hom, Category.id_comp, T₂]
      rw [Iso.comp_inv_eq]
      refine Fan.IsLimit.hom_ext hP _ _ fun n ↦ ?_
      rw [Category.assoc, heP, Preadditive.sub_comp, Category.id_comp, towerShift,
        Fan.IsLimit.fac]
      have key := congrArg Q.map (limRoosFan_d_eq I n)
      rw [Q.map_sub, Q.map_comp, Q.map_comp] at key
      simp only [P', P, fan_mk_proj, Functor.comp_map] at key ⊢
      exact key.symm
  exact hc'.of_iso (Iso.refl _) (Q.mapCone c)
    (Q.mapIso ((isLimitLimCone I).conePointUniqueUpToIso hc))
    fun n ↦ by
      simp [← Q.map_comp, IsLimit.conePointUniqueUpToIso_hom_comp]

end KInjective

end DerivedCategory
