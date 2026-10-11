/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Homology.ShortComplex.Limits
public import Mathlib.Algebra.Homology.ShortComplex.Abelian
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels

/-!
# Homology commutes with exact limits

Let `C` be an abelian category and `J` a category such that limits of shape `J` exist in `C`
and are exact (`HasExactLimitsOfShape J C`), for instance countable products in a category
satisfying AB4*. Then the cycles of a short complex commute with all limits
(`CategoryTheory.ShortComplex.isLimitCyclesFunctorMapCone`), and the homology functor of short
complexes preserves limits of shape `J`
(`CategoryTheory.ShortComplex.preservesLimitsOfShape_homologyFunctor`): the homology of a short
complex is the cokernel of `X₁ ⟶ cycles`, and the limit functor preserves cokernels.
-/

@[expose] public section

open CategoryTheory Category Limits

namespace CategoryTheory.ShortComplex

variable {C : Type*} [Category C] [Abelian C] {J : Type*} [Category J]

variable [HasLimitsOfShape J C]

/-- The cycles of a limit of short complexes are the limit of the cycles. -/
noncomputable def isLimitCyclesFunctorMapCone {F : J ⥤ ShortComplex C} {c : Cone F}
    (hc : IsLimit c) : IsLimit ((cyclesFunctor C).mapCone c) := by
  have h₂ : IsLimit (π₂.mapCone c) := isLimitOfPreserves π₂ hc
  have h₃ : IsLimit (π₃.mapCone c) := isLimitOfPreserves π₃ hc
  let σ (s : Cone (F ⋙ cyclesFunctor C)) (j : J) : s.pt ⟶ (F.obj j).cycles := s.π.app j
  have hσ (s : Cone (F ⋙ cyclesFunctor C)) {j j' : J} (f : j ⟶ j') :
      σ s j ≫ cyclesMap (F.map f) = σ s j' := s.w f
  let k (s : Cone (F ⋙ cyclesFunctor C)) : s.pt ⟶ c.pt.X₂ :=
    h₂.lift
      { pt := s.pt
        π :=
          { app j := σ s j ≫ (F.obj j).iCycles
            naturality j j' f := by
              change 𝟙 _ ≫ σ s j' ≫ (F.obj j').iCycles =
                (σ s j ≫ (F.obj j).iCycles) ≫ (F.map f).τ₂
              rw [id_comp, ← hσ s f, assoc, assoc, cyclesMap_i] } }
  have hk (s : Cone (F ⋙ cyclesFunctor C)) (j : J) :
      k s ≫ (c.π.app j).τ₂ = σ s j ≫ (F.obj j).iCycles :=
    h₂.fac _ j
  have hkg (s : Cone (F ⋙ cyclesFunctor C)) : k s ≫ c.pt.g = 0 :=
    h₃.hom_ext fun j ↦ by
      change (k s ≫ c.pt.g) ≫ (c.π.app j).τ₃ = 0 ≫ (c.π.app j).τ₃
      have h : (c.π.app j).τ₂ ≫ (F.obj j).g = c.pt.g ≫ (c.π.app j).τ₃ := (c.π.app j).comm₂₃
      rw [assoc, ← h, reassoc_of% (hk s j), iCycles_g, comp_zero, zero_comp]
  refine
    { lift s := c.pt.liftCycles (k s) (hkg s)
      fac s j := ?_
      uniq s m hm := ?_ }
  · change c.pt.liftCycles (k s) (hkg s) ≫ cyclesMap (c.π.app j) = σ s j
    rw [← cancel_mono (F.obj j).iCycles, assoc, cyclesMap_i, liftCycles_i_assoc, hk]
  · let m' : s.pt ⟶ c.pt.cycles := m
    change m' = _
    rw [← cancel_mono c.pt.iCycles, liftCycles_i]
    refine h₂.hom_ext fun j ↦ ?_
    have hm' : m' ≫ cyclesMap (c.π.app j) = σ s j := hm j
    change (m' ≫ c.pt.iCycles) ≫ (c.π.app j).τ₂ = k s ≫ (c.π.app j).τ₂
    rw [hk, assoc, ← cyclesMap_i, ← hm', assoc]

variable [HasExactLimitsOfShape J C]

/-- If limits of shape `J` are exact in `C`, the homology of a limit of short complexes is the
limit of their homologies. -/
noncomputable def isLimitHomologyFunctorMapCone {F : J ⥤ ShortComplex C} {c : Cone F}
    (hc : IsLimit c) : IsLimit ((homologyFunctor C).mapCone c) := by
  -- The cokernel cofork `X₁ ⟶ cycles ⟶ homology`, in the functor category `J ⥤ C`.
  let τ : F ⋙ π₁ ⟶ F ⋙ cyclesFunctor C := Functor.whiskerLeft F (toCyclesNatTrans C)
  let p : F ⋙ cyclesFunctor C ⟶ F ⋙ homologyFunctor C :=
    { app j := (F.obj j).homologyπ
      naturality j j' f := (homologyπ_naturality (F.map f)).symm }
  have hτp : τ ≫ p = 0 := by
    ext j
    exact (F.obj j).toCycles_comp_homologyπ
  have hcok : IsColimit (CokernelCofork.ofπ p hτp) :=
    evaluationJointlyReflectsColimits _ fun j ↦
      (isColimitMapCoconeCoforkEquiv' ((evaluation J C).obj j) hτp).symm
        ((F.obj j).homologyIsCokernel)
  -- Its image under `lim` is a cokernel cofork, by exactness of `lim`.
  have hcok' := isColimitCoforkMapOfIsColimit' lim hτp hcok
  have h₁ : IsLimit (π₁.mapCone c) := isLimitOfPreserves π₁ hc
  have hZ := isLimitCyclesFunctorMapCone hc
  let e₁ : c.pt.X₁ ≅ limit (F ⋙ π₁) := h₁.conePointUniqueUpToIso (limit.isLimit _)
  let e₂ : c.pt.cycles ≅ limit (F ⋙ cyclesFunctor C) :=
    hZ.conePointUniqueUpToIso (limit.isLimit _)
  have he₁ (j : J) : e₁.hom ≫ limit.π (F ⋙ π₁) j = (c.π.app j).τ₁ :=
    h₁.conePointUniqueUpToIso_hom_comp (limit.isLimit _) j
  have he₂ (j : J) : e₂.hom ≫ limit.π (F ⋙ cyclesFunctor C) j = cyclesMap (c.π.app j) :=
    hZ.conePointUniqueUpToIso_hom_comp (limit.isLimit _) j
  have hcomm : c.pt.toCycles ≫ e₂.hom = e₁.hom ≫ lim.map τ := by
    refine limit.hom_ext fun j ↦ ?_
    rw [assoc, he₂, assoc, lim_map, limMap_π, reassoc_of% he₁]
    exact toCycles_naturality (c.π.app j)
  let φ : c.pt.homology ⟶ limit (F ⋙ homologyFunctor C) :=
    c.pt.descHomology (e₂.hom ≫ lim.map p) (by
      rw [reassoc_of% hcomm, ← lim.map_comp, hτp, Functor.map_zero, comp_zero])
  let ψ : limit (F ⋙ homologyFunctor C) ⟶ c.pt.homology :=
    Cofork.IsColimit.desc hcok' (e₂.inv ≫ c.pt.homologyπ) (by
      rw [zero_comp, ← cancel_epi e₁.hom, ← reassoc_of% hcomm, comp_zero,
        Iso.hom_inv_id_assoc, toCycles_comp_homologyπ])
  have hψ : lim.map p ≫ ψ = e₂.inv ≫ c.pt.homologyπ :=
    Cofork.IsColimit.π_desc hcok'
  have hφψ : φ ≫ ψ = 𝟙 _ := by
    rw [← cancel_epi c.pt.homologyπ, π_descHomology_assoc, assoc, hψ,
      Iso.hom_inv_id_assoc, comp_id]
  have hψφ : ψ ≫ φ = 𝟙 _ := by
    refine Cofork.IsColimit.hom_ext hcok' ?_
    change lim.map p ≫ ψ ≫ φ = lim.map p ≫ 𝟙 _
    rw [reassoc_of% hψ, π_descHomology, Iso.inv_hom_id_assoc, comp_id]
  have : IsIso φ := ⟨ψ, hφψ, hψφ⟩
  let e : limit (F ⋙ homologyFunctor C) ≅ c.pt.homology := ⟨ψ, φ, hψφ, hφψ⟩
  refine IsLimit.ofIsoLimit (limit.isLimit _) (Cone.ext e fun j ↦ ?_)
  change limit.π (F ⋙ homologyFunctor C) j = ψ ≫ homologyMap (c.π.app j)
  refine (cancel_epi φ).1 ?_
  refine (cancel_epi c.pt.homologyπ).1 ?_
  have h₁ : c.pt.homologyπ ≫ φ ≫ ψ ≫ homologyMap (c.π.app j) =
      c.pt.homologyπ ≫ homologyMap (c.π.app j) := by
    rw [reassoc_of% hφψ]
  have h₂ : c.pt.homologyπ ≫ φ ≫ limit.π (F ⋙ homologyFunctor C) j =
      cyclesMap (c.π.app j) ≫ (F.obj j).homologyπ := by
    rw [π_descHomology_assoc, assoc, lim_map, limMap_π, reassoc_of% he₂]
    rfl
  exact h₂.trans ((homologyπ_naturality (c.π.app j)).symm.trans h₁.symm)

instance preservesLimitsOfShape_homologyFunctor :
    PreservesLimitsOfShape J (homologyFunctor C) where
  preservesLimit {F} := preservesLimit_of_preserves_limit_cone (limit.isLimit F)
    (isLimitHomologyFunctorMapCone (limit.isLimit F))

end CategoryTheory.ShortComplex
