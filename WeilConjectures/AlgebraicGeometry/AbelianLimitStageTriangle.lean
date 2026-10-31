/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.AbelianLimitStages
public import WeilConjectures.Mathlib.CategoryTheory.Triangulated.HomologicalFunctor
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.CategoryTheory.Abelian.DiagramLemmas.Four
import Mathlib.Algebra.Homology.ShortComplex.FunctorEquivalence

/-! # The five-lemma step for a system of derived image comparisons

Source: Stacks Tag 0GIU, the five-term exact diagram.
(blueprint: lem-sf-abelian-limit-stage-triangle).
-/

@[expose] public section

universe u' u

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

private theorem exact_of_evaluations {J C : Type*} [Category J] [Category C] [Abelian C]
    (E : ShortComplex (J ⥤ C))
    (h : ∀ j, (E.map ((evaluation J C).obj j)).Exact) : E.Exact := by
  rw [E.exact_iff_isZero_homology, IsZero.iff_id_eq_zero]
  ext j
  have hj : IsZero (E.homology.obj j) :=
    ((E.map ((evaluation J C).obj j)).exact_iff_isZero_homology.mp (h j)).of_iso
      (E.mapHomologyIso ((evaluation J C).obj j)).symm
  exact hj.eq_of_src _ _

namespace AlgebraicGeometry.Etale.AbelianLimitStageSystem

variable {B W : Scheme.{u}} {I : Type u} [Category.{u} I]
  (A : Type u') [Category.{u + 1} A] [Abelian A]
  [IsGrothendieckAbelian.{u + 1} A] [HasSmallSiteSheafify A]
  (S : LimitStageSystem B W I)

/-- The map of the homology diagrams induced by a coefficient morphism. -/
noncomputable def diagramMap
    {K L : DerivedCategory.Plus (Sheaf W.smallEtaleTopology A)} (f : K ⟶ L) (q : ℤ) :
    diagram A S K q ⟶ diagram A S L q where
  app i := (DerivedCategory.Plus.homologyFunctor _ q).map
    ((AbelianLimitStage.functor A (S.obj i.unop)).map f)
  naturality i j h := by
    dsimp only [diagram, derivedDiagram, Functor.comp_map]
    rw [← Functor.map_comp, ← Functor.map_comp]
    exact (DerivedCategory.Plus.homologyFunctor _ q).congr_map
      ((AbelianLimitStage.transition A (S.map h.unop)).naturality f).symm

/-- The connecting map of the point-stage image triangle. -/
noncomputable def pointConnecting
    (T : Triangle (DerivedCategory.Plus (Sheaf W.smallEtaleTopology A)))
    (q r : ℤ) (h : q + 1 = r) :
    (cocone A S T.obj₃ q).pt ⟶ (cocone A S T.obj₁ r).pt :=
  (DerivedCategory.Plus.homologyFunctor _ 0).homologySequenceδ
    ((AbelianLimitStage.functor A S.pt).mapTriangle.obj T) q r h

/-- The connecting maps of stage image triangles form a natural transformation. -/
noncomputable def diagramConnecting
    (T : Triangle (DerivedCategory.Plus (Sheaf W.smallEtaleTopology A)))
    (q r : ℤ) (h : q + 1 = r) :
    diagram A S T.obj₃ q ⟶ diagram A S T.obj₁ r where
  app i := (DerivedCategory.Plus.homologyFunctor _ 0).homologySequenceδ
    ((AbelianLimitStage.functor A (S.obj i.unop)).mapTriangle.obj T) q r h
  naturality i j f := by
    exact ((DerivedCategory.Plus.homologyFunctor _ 0).homologySequenceδ_mapTriangle_naturality
      (AbelianLimitStage.transition A (S.map f.unop)) T q r h).symm

@[reassoc]
lemma comparison_naturality
    {K L : DerivedCategory.Plus (Sheaf W.smallEtaleTopology A)} (f : K ⟶ L) (q : ℤ) :
    colim.map (diagramMap A S f q) ≫ comparison A S L q =
      comparison A S K q ≫ (DerivedCategory.Plus.homologyFunctor _ q).map
        ((AbelianLimitStage.functor A S.pt).map f) := by
  apply colimit.hom_ext
  intro i
  simp only [comparison, colimit.ι_map_assoc,
    colimit.ι_desc, colimit.ι_desc_assoc]
  dsimp only [diagramMap, cocone, derivedCocone, Functor.mapCocone_ι_app]
  rw [← Functor.map_comp, ← Functor.map_comp]
  exact (DerivedCategory.Plus.homologyFunctor _ q).congr_map
    ((AbelianLimitStage.transition A (S.π i.unop)).naturality f)

@[reassoc]
lemma comparison_connecting
    (T : Triangle (DerivedCategory.Plus (Sheaf W.smallEtaleTopology A)))
    (q r : ℤ) (h : q + 1 = r) :
    colim.map (diagramConnecting A S T q r h) ≫ comparison A S T.obj₁ r =
      comparison A S T.obj₃ q ≫ pointConnecting A S T q r h := by
  apply colimit.hom_ext
  intro i
  simp only [comparison, colimit.ι_map_assoc,
    colimit.ι_desc, colimit.ι_desc_assoc]
  exact (DerivedCategory.Plus.homologyFunctor _ 0).homologySequenceδ_mapTriangle_naturality
    (AbelianLimitStage.transition A (S.π i.unop)) T q r h

/-- The continuity comparison satisfies the five-lemma step of a distinguished triangle.

Proof: take the five-term segment `T₃[p-1], T₁[p], T₂[p], T₃[p], T₁[p+1]`
of each stage image triangle. Shift compatibility of transitions makes the connecting
maps natural. Exactness is checked by evaluation, then is preserved by the filtered
colimit of sheaves. The canonical cocone maps commute with all four arrows by
naturality and shift compatibility. The five lemma now applies to the middle map.
Source: Stacks Tag 0GIU, the displayed diagram and its exact columns.
(blueprint: lem-sf-abelian-limit-stage-triangle). -/
theorem isIso_comparison_triangle [IsCofiltered I]
    (T : Triangle (DerivedCategory.Plus (Sheaf W.smallEtaleTopology A)))
    (hT : T ∈ distTriang _) (p : ℤ)
    (h₀ : IsIso (comparison A S T.obj₃ (p - 1)))
    (h₁ : IsIso (comparison A S T.obj₁ p))
    (h₃ : IsIso (comparison A S T.obj₃ p))
    (h₄ : IsIso (comparison A S T.obj₁ (p + 1))) :
    IsIso (comparison A S T.obj₂ p) := by
  let : HasFilteredColimitsOfSize.{u, u} A :=
    hasFilteredColimitsOfSize_of_univLE.{u, u, u + 1, u + 1}
  let : AB5OfSize.{u, u} A := AB5OfSize_of_univLE.{u, u, u + 1, u + 1} A
  let d₀ := diagramConnecting A S T (p - 1) p (by omega)
  let d₁ := diagramMap A S T.mor₁ p
  let d₂ := diagramMap A S T.mor₂ p
  let d₃ := diagramConnecting A S T p (p + 1) rfl
  have w₀ : d₀ ≫ d₁ = 0 := by
    apply NatTrans.ext
    funext i
    exact (DerivedCategory.Plus.homologyFunctor _ 0).homologySequenceδ_comp _
      ((AbelianLimitStage.functor A (S.obj i.unop)).map_distinguished T hT)
      (p - 1) p (by omega)
  have w₁ : d₁ ≫ d₂ = 0 := by
    apply NatTrans.ext
    funext i
    exact (DerivedCategory.Plus.homologyFunctor _ 0).homologySequence_comp _
      ((AbelianLimitStage.functor A (S.obj i.unop)).map_distinguished T hT) p
  have w₂ : d₂ ≫ d₃ = 0 := by
    apply NatTrans.ext
    funext i
    exact (DerivedCategory.Plus.homologyFunctor _ 0).comp_homologySequenceδ _
      ((AbelianLimitStage.functor A (S.obj i.unop)).map_distinguished T hT) p (p + 1) rfl
  have e₀ : (ShortComplex.mk d₀ d₁ w₀).Exact := by
    apply exact_of_evaluations
    intro i
    exact (DerivedCategory.Plus.homologyFunctor _ 0).homologySequence_exact₁ _
      ((AbelianLimitStage.functor A (S.obj i.unop)).map_distinguished T hT)
      (p - 1) p (by omega)
  have e₁ : (ShortComplex.mk d₁ d₂ w₁).Exact := by
    apply exact_of_evaluations
    intro i
    exact (DerivedCategory.Plus.homologyFunctor _ 0).homologySequence_exact₂ _
      ((AbelianLimitStage.functor A (S.obj i.unop)).map_distinguished T hT) p
  have e₂ : (ShortComplex.mk d₂ d₃ w₂).Exact := by
    apply exact_of_evaluations
    intro i
    exact (DerivedCategory.Plus.homologyFunctor _ 0).homologySequence_exact₃ _
      ((AbelianLimitStage.functor A (S.obj i.unop)).map_distinguished T hT) p (p + 1) rfl
  let H := DerivedCategory.Plus.homologyFunctor (Sheaf B.smallEtaleTopology A) 0
  let TP := (AbelianLimitStage.functor A S.pt).mapTriangle.obj T
  have hTP : TP ∈ distTriang _ := (AbelianLimitStage.functor A S.pt).map_distinguished T hT
  let R := ComposableArrows.mk₄ (colim.map d₀) (colim.map d₁)
    (colim.map d₂) (colim.map d₃)
  let R' := ComposableArrows.mk₄ (pointConnecting A S T (p - 1) p (by omega))
    ((DerivedCategory.Plus.homologyFunctor _ p).map
      ((AbelianLimitStage.functor A S.pt).map T.mor₁))
    ((DerivedCategory.Plus.homologyFunctor _ p).map
      ((AbelianLimitStage.functor A S.pt).map T.mor₂))
    (pointConnecting A S T p (p + 1) rfl)
  have hR : R.Exact := ComposableArrows.exact_of_δ₀
    (e₀.map colim).exact_toComposableArrows (ComposableArrows.exact_of_δ₀
      (e₁.map colim).exact_toComposableArrows (e₂.map colim).exact_toComposableArrows)
  have hR' : R'.Exact := ComposableArrows.exact_of_δ₀
    (H.homologySequence_exact₁ TP hTP (p - 1) p (by omega)).exact_toComposableArrows
    (ComposableArrows.exact_of_δ₀
      (H.homologySequence_exact₂ TP hTP p).exact_toComposableArrows
      (H.homologySequence_exact₃ TP hTP p (p + 1) rfl).exact_toComposableArrows)
  let φ : R ⟶ R' := ComposableArrows.homMk₄
    (comparison A S T.obj₃ (p - 1)) (comparison A S T.obj₁ p)
    (comparison A S T.obj₂ p) (comparison A S T.obj₃ p)
    (comparison A S T.obj₁ (p + 1))
    (comparison_connecting A S T (p - 1) p (by omega))
    (comparison_naturality A S T.mor₁ p)
    (comparison_naturality A S T.mor₂ p)
    (comparison_connecting A S T p (p + 1) rfl)
  exact Abelian.isIso_of_epi_of_isIso_of_isIso_of_mono hR hR' φ
    (by exact inferInstanceAs (Epi (comparison A S T.obj₃ (p - 1)))) h₁ h₃
    (by exact inferInstanceAs (Mono (comparison A S T.obj₁ (p + 1))))

end AlgebraicGeometry.Etale.AbelianLimitStageSystem
