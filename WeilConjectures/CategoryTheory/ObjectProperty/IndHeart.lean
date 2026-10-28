/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Abelian.CommSq
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.ColimCoyoneda
public import Mathlib.CategoryTheory.Comma.Final
public import Mathlib.CategoryTheory.Limits.FunctorCategory.BinaryBiproducts
public import Mathlib.CategoryTheory.ObjectProperty.Ind
public import WeilConjectures.CategoryTheory.DerivedCategory.CompactOfBoundedExt

/-!
# Ind-objects of a Serre-type subcategory
-/

@[expose] public section

universe w v u

open CategoryTheory Category Limits


namespace DerivedCategory

variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory C]

namespace HomFactorsThroughFilteredColimits

attribute [local instance] IsFiltered.isConnected

variable {X : C}
  (hX : DerivedCategory.HomFactorsThroughFilteredColimits.{w} ((singleFunctor C 0).obj X))
include hX

/-- The case `n = 0` of `HomFactorsThroughFilteredColimits`, in `C`: a morphism from `X` to a
filtered colimit factors through some term of the diagram. -/
lemma exists_hom {I : Type w} [SmallCategory I] [IsFiltered I] {F : I ⥤ C} {c : Cocone F}
    (hc : IsColimit c) (f : X ⟶ c.pt) : ∃ (i : I) (g : X ⟶ F.obj i), g ≫ c.ι.app i = f := by
  obtain ⟨i, g, hg⟩ := hX I F c hc 0 ((singleFunctor C 0).map f)
  refine ⟨i, (singleFunctor C 0).preimage g, (singleFunctor C 0).map_injective ?_⟩
  simp [hg]

/-- Blueprint `det-ind-heart-full-faithfulness`: if morphisms out of `X[0]` factor through
filtered colimits, then `X` is finitely presentable. Injectivity of
`colim Hom(X, Bᵢ) ⟶ Hom(X, colim Bᵢ)` follows from surjectivity applied to the filtered diagram
of the kernels of `X ⟶ Bⱼ`, whose colimit is `X` by exactness of filtered colimits. -/
lemma isFinitelyPresentable [IsGrothendieckAbelian.{w} C] : IsFinitelyPresentable.{w} X := by
  rw [isFinitelyPresentable_iff_preservesFilteredColimitsOfSize]
  refine ⟨fun I _ _ ↦ ⟨fun {F} ↦ ⟨fun {c} hc ↦ ⟨Types.FilteredColimit.isColimitOf' _ _
    (fun f ↦ ?_) (fun i x y hxy ↦ ?_)⟩⟩⟩⟩
  · obtain ⟨i, g, hg⟩ := exists_hom hX hc f
    exact ⟨i, g, hg.symm⟩
  · open IsGrothendieckAbelian.IsPresentable.injectivity₀ in
    let x' : X ⟶ F.obj i := x
    let y' : X ⟶ F.obj i := y
    let z : X ⟶ F.obj i := x' - y'
    have hz : z ≫ c.ι.app i = 0 := by
      simpa [z, sub_eq_zero] using hxy
    have := epi_f hc hz
    have : Mono (f z) := colim.map_mono' (kernel.ι (g z)) (colimit.isColimit _)
      (isColimitConstCocone _ _) _ (fun j ↦ (hf z j).trans (comp_id _).symm)
    have := isIso_of_mono_of_epi (f z)
    obtain ⟨j, a, ha⟩ := exists_hom hX (colimit.isColimit (kernel (g z))) (inv (f z))
    refine ⟨j.right, j.hom, ?_⟩
    have h₁ : a ≫ (kernel.ι (g z)).app j = 𝟙 X := by
      rw [← hf, ← assoc, show a ≫ colimit.ι (kernel (g z)) j = inv (f z) from ha, IsIso.inv_hom_id]
    have h₂ := NatTrans.congr_app (kernel.condition (g z)) j
    simp only [NatTrans.comp_app, NatTrans.app_zero, g_app] at h₂
    have h₃ : z ≫ F.map j.hom = 0 := by
      rw [← id_comp (z ≫ _), ← h₁, assoc]
      exact (congrArg (a ≫ ·) h₂).trans comp_zero
    simpa [z, x', y', sub_eq_zero] using h₃

end HomFactorsThroughFilteredColimits

end DerivedCategory


namespace CategoryTheory.Limits.ColimitPresentation

variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C] [HasBinaryBiproducts C]

/-- The pointwise biproduct of two colimit presentations indexed by the same category is a
colimit presentation of the biproduct. -/
@[simps]
noncomputable def biprod {K : Type*} [Category* K] {X Y : C} (pX : ColimitPresentation K X)
    (pY : ColimitPresentation K Y) : ColimitPresentation K (X ⊞ Y) where
  diag :=
    { obj k := pX.diag.obj k ⊞ pY.diag.obj k
      map t := biprod.map (pX.diag.map t) (pY.diag.map t) }
  ι := { app k := biprod.map (pX.ι.app k) (pY.ι.app k) }
  isColimit :=
    { desc s := biprod.desc
        (pX.isColimit.desc (Cocone.mk s.pt
          { app k := biprod.inl ≫ s.ι.app k
            naturality k k' t := by simp [← s.w t] }))
        (pY.isColimit.desc (Cocone.mk s.pt
          { app k := biprod.inr ≫ s.ι.app k
            naturality k k' t := by simp [← s.w t] }))
      fac s k := by
        ext
        · simpa using pX.isColimit.fac _ k
        · simpa using pY.isColimit.fac _ k
      uniq s m hm := by
        ext
        · exact pX.isColimit.hom_ext fun k ↦ by simp [← hm k]
        · exact pY.isColimit.hom_ext fun k ↦ by simp [← hm k] }

end CategoryTheory.Limits.ColimitPresentation

namespace CategoryTheory.ObjectProperty

variable {C : Type u} [Category.{v} C] {P : ObjectProperty C}

attribute [local instance] Cardinal.fact_isRegular_aleph0 in
/-- If the objects of `P` are finitely presentable, a presentation of `X` as a filtered colimit
of objects of `P` is final in the category of all morphisms from objects of `P` to `X`. -/
lemma ColimitOfShape.final_toCostructuredArrow (hP : P ≤ isFinitelyPresentable.{w} C)
    {J : Type w} [SmallCategory J] [IsFiltered J] {X : C} (p : P.ColimitOfShape J X) :
    p.toCostructuredArrow.Final := by
  have : IsCardinalFiltered J Cardinal.aleph0.{w} := by
    rwa [isCardinalFiltered_aleph0_iff]
  rw [Functor.final_iff_of_isFiltered]
  refine ⟨fun g ↦ ?_, fun {g j} g₁ g₂ ↦ ?_⟩
  · have : IsFinitelyPresentable.{w} (P.ι.obj g.left) := hP _ g.left.property
    obtain ⟨j, a, ha⟩ := IsFinitelyPresentable.exists_hom_of_isColimit p.isColimit g.hom
    exact ⟨j, ⟨CostructuredArrow.homMk (ObjectProperty.homMk a) ha⟩⟩
  · have : IsFinitelyPresentable.{w} g.left.obj := hP _ g.left.property
    obtain ⟨k, a, h⟩ := IsCardinalPresentable.exists_eq_of_isColimit' Cardinal.aleph0.{w}
      p.isColimit g₁.left.hom g₂.left.hom
      ((CostructuredArrow.w g₁).trans (CostructuredArrow.w g₂).symm)
    exact ⟨k, a, by cat_disch⟩

/-- Blueprint `det-ind-heart-kernels-cokernels` (the category `P_f`): if the objects of `P` are
finitely presentable, a morphism `f : X ⟶ Y` between filtered colimits of objects of `P` is a
filtered colimit of morphisms between objects of `P`, indexed by the category of squares from
morphisms of the given presentations to `f`. -/
lemma exists_colimitOfShape_hom (hP : P ≤ isFinitelyPresentable.{w} C) [LocallySmall.{w} C]
    {X Y : C} (f : X ⟶ Y) (hX : ind.{w} P X) (hY : ind.{w} P Y) :
    ∃ (K : Type w) (_ : SmallCategory K) (_ : IsFiltered K) (pX : P.ColimitOfShape K X)
      (pY : P.ColimitOfShape K Y) (α : pX.diag ⟶ pY.diag),
      ∀ k, α.app k ≫ pY.ι.app k = pX.ι.app k ≫ f := by
  obtain ⟨I, _, _, pX, hpX⟩ := hX
  obtain ⟨J, _, _, pY, hpY⟩ := hY
  let qX : P.ColimitOfShape I X := ⟨pX, hpX⟩
  let qY : P.ColimitOfShape J Y := ⟨pY, hpY⟩
  have := qY.final_toCostructuredArrow hP
  let L := qX.toCostructuredArrow ⋙ CostructuredArrow.map f
  let K := Comma L qY.toCostructuredArrow
  have : Small.{w} K := small_of_injective
    (f := fun k : K ↦ (⟨k.left, k.right, k.hom⟩ : Σ i j, L.obj i ⟶ qY.toCostructuredArrow.obj j))
    (by
      rintro ⟨_, _, _⟩ ⟨_, _, _⟩ h
      cases h
      rfl)
  have := essentiallySmall_of_small_of_locallySmall.{w} K
  let e := equivSmallModel.{w} K
  have : IsFiltered (SmallModel.{w} K) := IsFiltered.of_equivalence e
  refine ⟨SmallModel.{w} K, inferInstance, inferInstance,
    (qX.reindex (Comma.fst _ _)).reindex e.inverse,
    (qY.reindex (Comma.snd _ _)).reindex e.inverse,
    e.inverse.whiskerLeft
      { app k := k.hom.left.hom
        naturality k k' φ := congr_arg (fun ψ ↦ ψ.left.hom) φ.w }, fun k ↦ ?_⟩
  exact CostructuredArrow.w (e.inverse.obj k).hom

section Abelian

variable [Abelian C] [IsGrothendieckAbelian.{w} C]

/-- Blueprint `det-ind-heart-kernels-cokernels`: if the objects of `P` are finitely
presentable and `P` is closed under kernels, then so is `ind P`, filtered colimits being exact. -/
lemma ind_isClosedUnderKernels (hP : P ≤ isFinitelyPresentable.{w} C)
    [P.IsClosedUnderKernels] : (ind.{w} P).IsClosedUnderKernels where
  kernels_le := by
    rintro _ ⟨f, k, hk, ⟨hX, hY⟩⟩
    obtain ⟨K, _, _, pX, pY, α, hα⟩ := exists_colimitOfShape_hom hP f hX hY
    let φ : colimit (kernel α) ⟶ _ := IsColimit.map (colimit.isColimit _) pX.cocone (kernel.ι α)
    have hφ (j : K) : colimit.ι (kernel α) j ≫ φ = (kernel.ι α).app j ≫ pX.ι.app j :=
      IsColimit.ι_map _ _ _ _
    let T := colim.mapShortComplex (ShortComplex.mk _ _ (kernel.condition α))
      (colimit.isColimit _) pX.cocone pY.cocone φ f hφ (fun j ↦ (hα j).symm)
    have hS : T.Exact := colim.exact_mapShortComplex
      ((ShortComplex.mk _ _ (kernel.condition α)).exact_of_f_is_kernel (kernelIsKernel α))
      (colimit.isColimit _) pX.isColimit pY.isColimit φ f hφ (fun j ↦ (hα j).symm)
    have : Mono T.f := colim.map_mono' (kernel.ι α) (colimit.isColimit _) pX.isColimit φ hφ
    refine (ind.{w} P).prop_of_iso
      (IsLimit.conePointUniqueUpToIso hS.fIsKernel hk) ⟨K, inferInstance, inferInstance,
        ColimitPresentation.colimit (kernel α), fun j ↦ ?_⟩
    exact P.prop_of_isLimit_kernelFork
      (KernelFork.mapIsLimit _ (kernelIsKernel α) ((evaluation K C).obj j))
      (pX.prop_diag_obj j) (pY.prop_diag_obj j)

/-- Blueprint `det-ind-heart-kernels-cokernels`: if the objects of `P` are finitely
presentable and `P` is closed under cokernels, then so is `ind P`. -/
lemma ind_isClosedUnderCokernels (hP : P ≤ isFinitelyPresentable.{w} C)
    [P.IsClosedUnderCokernels] : (ind.{w} P).IsClosedUnderCokernels where
  cokernels_le := by
    rintro _ ⟨f, k, hk, ⟨hX, hY⟩⟩
    obtain ⟨K, _, _, pX, pY, α, hα⟩ := exists_colimitOfShape_hom hP f hX hY
    let φ : _ ⟶ colimit (cokernel α) :=
      IsColimit.map pY.isColimit (colimit.cocone _) (cokernel.π α)
    have hφ (j : K) : pY.ι.app j ≫ φ = (cokernel.π α).app j ≫ colimit.ι (cokernel α) j :=
      IsColimit.ι_map pY.isColimit (colimit.cocone _) (cokernel.π α) j
    let T := colim.mapShortComplex (ShortComplex.mk _ _ (cokernel.condition α))
      pX.isColimit pY.cocone (colimit.cocone _) f φ (fun j ↦ (hα j).symm) hφ
    have hS : T.Exact := colim.exact_mapShortComplex
      ((ShortComplex.mk _ _ (cokernel.condition α)).exact_of_g_is_cokernel
        (cokernelIsCokernel α))
      pX.isColimit pY.isColimit (colimit.isColimit _) f φ (fun j ↦ (hα j).symm) hφ
    have : Epi T.g := colim.map_epi' (cokernel.π α) pY.cocone (colimit.isColimit _) φ hφ
    refine (ind.{w} P).prop_of_iso
      (IsColimit.coconePointUniqueUpToIso hS.gIsCokernel hk) ⟨K, inferInstance, inferInstance,
        ColimitPresentation.colimit (cokernel α), fun j ↦ ?_⟩
    exact P.prop_of_isColimit_cokernelCofork
      (CokernelCofork.mapIsColimit _ (cokernelIsCokernel α) ((evaluation K C).obj j))
      (pX.prop_diag_obj j) (pY.prop_diag_obj j)

/-- If the objects of `P` are finitely presentable and `P` is closed under extensions, then
`ind P` is closed under binary biproducts: two filtered colimits may be indexed by the same
category, and the pointwise biproduct of colimit cocones is a colimit cocone. -/
lemma ind_biprod (hP : P ≤ isFinitelyPresentable.{w} C) [P.IsClosedUnderExtensions]
    {X Y : C} (hX : ind.{w} P X) (hY : ind.{w} P Y) : ind.{w} P (X ⊞ Y) := by
  obtain ⟨K, _, _, pX, pY, -, -⟩ := exists_colimitOfShape_hom hP (0 : X ⟶ Y) hX hY
  exact ⟨K, inferInstance, inferInstance, pX.biprod pY.toColimitPresentation,
    fun k ↦ P.prop_biprod (pX.prop_diag_obj k) (pY.prop_diag_obj k)⟩

end Abelian

end CategoryTheory.ObjectProperty
