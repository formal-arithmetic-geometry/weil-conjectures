/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group P2
-/
module

public import Sheaf.AlgebraicGeometry.CompactFlatBarIndex
import Sheaf.AlgebraicGeometry.PreorderBarTotalSplit
import Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatCoproduct

/-! # The explicit enlarged bar tower

Source: the full-subdiagram bar-total paragraph of
`lem-sc-compact-flat-bar-union-augmentation`.
(blueprint: def-sc-compact-flat-enlarged-bar-tower).
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry
namespace CompactFlatBarIndex

variable {Y : Scheme.{u}}
  {L : ℕ → CochainComplex (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) ℤ}
  {l : ∀ n : ℕ, L n ⟶ L (n + 1)}
  (D : CompactFlatFiniteSubcomplexDiagrams Y L l)
  (E : ℕ → CochainComplex (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) ℤ)
  (t : ∀ n : ℕ, E n ⟶ E (n + 1))
  (p : ∀ n : ℕ, L n ⟶ CochainComplex.mappingCone (flatTelescopeDifferential E t))
  (hp : ∀ n : ℕ, l n ≫ p (n + 1) = p n)

/-- The full stage contains sources present by n and target blocks indexed at most n.
This label is deliberately not asserted to be monotone along source-to-target arrows. -/
def stage : Index D E t p hp → ℕ
  | .inl j => D.stage j
  | .inr k => k

noncomputable def stageDiagram (n : ℕ) :=
  compactFlatStageInclusion (stage D E t p hp) n ⋙ diagram D E t p hp

noncomputable def enlargedBar (n : ℕ) := PreorderBar.total (stageDiagram D E t p hp n)

def stageOrder (n : ℕ) :
    {j : Index D E t p hp // stage D E t p hp j ≤ n} →o
      {j : Index D E t p hp // stage D E t p hp j ≤ n + 1} where
  toFun j := ⟨j.1, Nat.le_trans j.2 (Nat.le_succ n)⟩
  monotone' := fun _ _ h ↦ h

noncomputable def stageMap (n : ℕ) : stageDiagram D E t p hp n ⟶
    PreorderBar.orderFunctor (stageOrder D E t p hp n) ⋙
      stageDiagram D E t p hp (n + 1) where
  app _ := 𝟙 _

noncomputable def enlargedBarMap (n : ℕ) :
    enlargedBar D E t p hp n ⟶ enlargedBar D E t p hp (n + 1) :=
  PreorderBar.totalMap _ _ (stageOrder D E t p hp n) (stageMap D E t p hp n)

noncomputable def stageCocone (n : ℕ) : Cocone (stageDiagram D E t p hp n) where
  pt := CochainComplex.mappingCone (flatTelescopeDifferential E t)
  ι.app j := augmentation D E t p hp j.1
  ι.naturality _ _ h := by
    simpa [stageDiagram, compactFlatStageInclusion, diagram] using
      map_augmentation D E t p hp (homOfLE (leOfHom h))

noncomputable def enlargedBarAugmentation (n : ℕ) :
    enlargedBar D E t p hp n ⟶ CochainComplex.mappingCone (flatTelescopeDifferential E t) :=
  PreorderBar.totalAugmentation _ (stageCocone D E t p hp n)

def sourceStageOrder (n : ℕ) : {j : D.index // D.stage j ≤ n} →o
    {j : Index D E t p hp // stage D E t p hp j ≤ n} where
  toFun j := ⟨Sum.inl j.1, j.2⟩
  monotone' := fun _ _ h ↦ h

noncomputable def sourceStageMap (n : ℕ) : D.stageDiagram n ⟶
    PreorderBar.orderFunctor (sourceStageOrder D E t p hp n) ⋙
      stageDiagram D E t p hp n where
  app _ := 𝟙 _
  naturality _ _ h := by
    simp [CompactFlatFiniteSubcomplexDiagrams.stageDiagram, stageDiagram,
      compactFlatStageInclusion, diagram, map, sourceStageOrder, PreorderBar.orderFunctor]

noncomputable def sourceToBar (n : ℕ) : D.sourceBar n ⟶ enlargedBar D E t p hp n :=
  PreorderBar.totalMap _ _ (sourceStageOrder D E t p hp n) (sourceStageMap D E t p hp n)

lemma enlargedBarAugmentation_naturality (n : ℕ) :
    enlargedBarMap D E t p hp n ≫ enlargedBarAugmentation D E t p hp (n + 1) =
      enlargedBarAugmentation D E t p hp n := by
  have h := PreorderBar.totalAugmentation_naturality
    (stageDiagram D E t p hp n) (stageDiagram D E t p hp (n + 1))
    (stageOrder D E t p hp n)
    (stageCocone D E t p hp n) (stageCocone D E t p hp (n + 1))
    (stageMap D E t p hp n) (𝟙 _)
    (fun _ ↦ by simp [stageMap, stageCocone, stageOrder])
  simpa [enlargedBarMap, enlargedBarAugmentation] using h

lemma sourceToBar_augmentation (n : ℕ) :
    sourceToBar D E t p hp n ≫ enlargedBarAugmentation D E t p hp n =
      D.sourceBarAugmentation n ≫ p n := by
  apply PreorderBar.totalAugmentation_naturality
  intro j
  simp only [sourceStageMap, stageCocone, sourceStageOrder, augmentation, Category.id_comp]
  exact D.augmentationTo_eq p hp j.1 n j.2

lemma enlargedBarMap_split (n : ℕ) (i : ℤ) :
    IsSplitMono ((enlargedBarMap D E t p hp n).f i) := by
  apply PreorderBar.totalMap_split
  · intro j k h
    apply Subtype.ext
    exact congrArg
      (fun x : {j : Index D E t p hp // stage D E t p hp j ≤ n + 1} ↦ x.1) h
  · intro j q
    change IsSplitMono ((𝟙 _ : (stageDiagram D E t p hp n).obj j ⟶ _).f q)
    infer_instance

/-- The enlarged stage retains a common upper bound. -/
lemma enlargedBar_bounded
    (hb : ∀ k : ℕ, ∃ b : ℤ, ∀ i : ℤ, b < i → IsZero ((E k).X i)) (n : ℕ) :
    ∃ b : ℤ, ∀ i : ℤ, b < i → IsZero ((enlargedBar D E t p hp n).X i) := by
  obtain ⟨bD, hbD⟩ := D.stageBound n
  choose b hb using FlatTelescopeBlocks.block_bounded E t hb
  obtain ⟨bC, hbC⟩ := Finite.exists_le (fun k : Fin (n + 1) ↦ b k)
  refine ⟨max bD bC, PreorderBar.bounded_total (stageDiagram D E t p hp n) _ ?_⟩
  intro j i hi
  rcases j with ⟨j, hj⟩
  cases j with
  | inl j => exact hbD ⟨j, hj⟩ i (lt_of_le_of_lt (le_max_left _ _) hi)
  | inr k =>
    exact hb k i (lt_of_le_of_lt
      (le_trans (hbC ⟨k, Nat.lt_succ_of_le hj⟩) (le_max_right _ _)) hi)

private theorem flat_of_iso
    {M N : SheafOfModules.{u} (moduleRings Y.toRingedSpace)} (e : M ≅ N)
    (hN : SheafOfModules.IsFlat N) : SheafOfModules.IsFlat M := by
  let := SheafOfModules.monoidalCategory Y.sheaf
  exact (exactFunctor _ _).prop_of_iso
    ((MonoidalCategory.curriedTensor _).flip.mapIso e.symm) hN

private theorem flat_coproduct_small {K : Type*} [Small.{u} K]
    (M : K → SheafOfModules.{u} (moduleRings Y.toRingedSpace))
    (hM : ∀ k : K, SheafOfModules.IsFlat (M k)) : SheafOfModules.IsFlat (∐ M) := by
  apply flat_of_iso (Sigma.reindex (equivShrink K).symm M).symm
  exact SheafOfModules.isFlat_coproduct Y.sheaf _ (fun k ↦ hM _)

/-- Every enlarged bar term is a coproduct of flat source and target-block terms. -/
lemma enlargedBar_flat (hf : ∀ k : ℕ, ∀ i : ℤ, SheafOfModules.IsFlat ((E k).X i))
    (n : ℕ) (i : ℤ) : SheafOfModules.IsFlat ((enlargedBar D E t p hp n).X i) := by
  apply flat_coproduct_small
  rintro ⟨⟨a, b⟩, _⟩
  apply flat_of_iso (PreorderBar.columnXIso (stageDiagram D E t p hp n) a b)
  apply flat_coproduct_small
  intro σ
  rcases σ 0 with ⟨j, hj⟩
  cases j with
  | inl j => exact D.diagram_flat j b
  | inr k => exact FlatTelescopeBlocks.block_flat E t hf k b

/-- Inclusion of source bars strictly commutes with all tower transitions. -/
lemma sourceToBar_naturality (n : ℕ) :
    D.sourceBarMap n ≫ sourceToBar D E t p hp (n + 1) =
      sourceToBar D E t p hp n ≫ enlargedBarMap D E t p hp n := by
  let f := D.stageOrderInclusion n
  let g := sourceStageOrder D E t p hp (n + 1)
  let h := sourceStageOrder D E t p hp n
  let k := stageOrder D E t p hp n
  let φ : D.stageDiagram n ⟶ PreorderBar.orderFunctor (g.comp f) ⋙
      stageDiagram D E t p hp (n + 1) :=
    { app _ := 𝟙 _
      naturality _ _ α := by
        simp [f, g, CompactFlatFiniteSubcomplexDiagrams.stageDiagram,
          CompactFlatFiniteSubcomplexDiagrams.stageOrderInclusion, sourceStageOrder,
          stageDiagram, compactFlatStageInclusion, diagram, map, PreorderBar.orderFunctor] }
  let ψ : D.stageDiagram n ⟶ PreorderBar.orderFunctor (k.comp h) ⋙
      stageDiagram D E t p hp (n + 1) :=
    { app _ := 𝟙 _
      naturality _ _ α := by
        simp [h, k, CompactFlatFiniteSubcomplexDiagrams.stageDiagram, sourceStageOrder,
          stageOrder, stageDiagram, compactFlatStageInclusion, diagram, map,
          PreorderBar.orderFunctor] }
  have h₁ := PreorderBar.totalMap_comp (D.stageDiagram n) (D.stageDiagram (n + 1))
    (stageDiagram D E t p hp (n + 1)) f g (D.stageDiagramMap n)
    (sourceStageMap D E t p hp (n + 1)) φ (fun _ ↦ by
      simp only [φ, CompactFlatFiniteSubcomplexDiagrams.stageDiagramMap,
        sourceStageMap, Category.id_comp]
      rfl)
  have h₂ := PreorderBar.totalMap_comp (D.stageDiagram n) (stageDiagram D E t p hp n)
    (stageDiagram D E t p hp (n + 1)) h k (sourceStageMap D E t p hp n)
    (stageMap D E t p hp n) ψ (fun _ ↦ by
      simp only [ψ, sourceStageMap, stageMap, Category.id_comp]
      rfl)
  change PreorderBar.totalMap _ _ f _ ≫ PreorderBar.totalMap _ _ g _ =
    PreorderBar.totalMap _ _ h _ ≫ PreorderBar.totalMap _ _ k _
  rw [h₁, h₂]
  rfl

end CompactFlatBarIndex
end AlgebraicGeometry
