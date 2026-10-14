/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group P2
-/
module

public import Sheaf.AlgebraicGeometry.CompactFlatFiniteSubcomplexDiagrams
public import Sheaf.AlgebraicGeometry.PreorderBarTotal
import Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatCoproduct

/-! # The explicit source bar tower

Source: the source-bar paragraph of `lem-sc-compact-flat-bar-union-augmentation`.
(blueprint: def-sc-compact-flat-source-bar-tower).
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry

variable {Y : Scheme.{u}}
  {L : ℕ → CochainComplex (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) ℤ}
  {l : ∀ n : ℕ, L n ⟶ L (n + 1)}

/-- The actual stage diagram used to construct its source bar resolution. -/
def CompactFlatFiniteSubcomplexDiagrams.stageDiagram
    (D : CompactFlatFiniteSubcomplexDiagrams Y L l) (n : ℕ) :=
  compactFlatStageInclusion D.stage n ⋙ D.diagram

/-- The source bar total, with simplicial degree p in degree -p. -/
noncomputable def CompactFlatFiniteSubcomplexDiagrams.sourceBar
    (D : CompactFlatFiniteSubcomplexDiagrams Y L l) (n : ℕ) :=
  PreorderBar.total (D.stageDiagram n)

/-- The stage inclusion on the indexing preorder. -/
def CompactFlatFiniteSubcomplexDiagrams.stageOrderInclusion
    (D : CompactFlatFiniteSubcomplexDiagrams Y L l) (n : ℕ) :
    {j : D.index // D.stage j ≤ n} →o {j : D.index // D.stage j ≤ n + 1} where
  toFun j := ⟨j.1, Nat.le_trans j.2 (Nat.le_succ n)⟩
  monotone' := fun _ _ h ↦ h

/-- The natural transformation on stage diagrams induced by their inclusion. -/
def CompactFlatFiniteSubcomplexDiagrams.stageDiagramMap
    (D : CompactFlatFiniteSubcomplexDiagrams Y L l) (n : ℕ) :
    D.stageDiagram n ⟶ PreorderBar.orderFunctor (D.stageOrderInclusion n) ⋙
      D.stageDiagram (n + 1) where
  app _ := 𝟙 _

/-- Transition maps on the explicitly constructed source bar totals. -/
noncomputable def CompactFlatFiniteSubcomplexDiagrams.sourceBarMap
    (D : CompactFlatFiniteSubcomplexDiagrams Y L l) (n : ℕ) :
    D.sourceBar n ⟶ D.sourceBar (n + 1) :=
  PreorderBar.totalMap (D.stageDiagram n) (D.stageDiagram (n + 1))
    (D.stageOrderInclusion n) (D.stageDiagramMap n)

/-- The canonical augmentation supplied by the stage cocone. -/
noncomputable def CompactFlatFiniteSubcomplexDiagrams.sourceBarAugmentation
    (D : CompactFlatFiniteSubcomplexDiagrams Y L l) (n : ℕ) : D.sourceBar n ⟶ L n :=
  PreorderBar.totalAugmentation (D.stageDiagram n) { pt := L n, ι := D.augmentation n }

/-- The bar augmentation strictly commutes with the tower transitions.
Source: the source-bar paragraph of `lem-sc-compact-flat-bar-union-augmentation`.
(blueprint: lem-sc-compact-flat-source-bar-naturality). -/
theorem CompactFlatFiniteSubcomplexDiagrams.sourceBarAugmentation_naturality
    (D : CompactFlatFiniteSubcomplexDiagrams Y L l) (n : ℕ) :
    D.sourceBarMap n ≫ D.sourceBarAugmentation (n + 1) =
      D.sourceBarAugmentation n ≫ l n := by
  apply PreorderBar.totalAugmentation_naturality
  intro j
  convert! (by simpa [CompactFlatFiniteSubcomplexDiagrams.stageDiagramMap] using
    (D.compatibility n j.1 j.2).symm) using 1

/-- Each source bar total inherits the stage's common upper bound.
Source: the common-stage-bound paragraph of `lem-sc-compact-flat-bar-union-augmentation`.
(blueprint: lem-sc-compact-flat-source-bar-bounded). -/
theorem CompactFlatFiniteSubcomplexDiagrams.sourceBar_bounded
    (D : CompactFlatFiniteSubcomplexDiagrams Y L l) (n : ℕ) :
    ∃ b : ℤ, ∀ i : ℤ, b < i → IsZero ((D.sourceBar n).X i) := by
  obtain ⟨b, hb⟩ := D.stageBound n
  exact ⟨b, PreorderBar.bounded_total (D.stageDiagram n) b hb⟩

/-- The compatible tower cocones give an augmentation of the whole source diagram. -/
noncomputable def CompactFlatFiniteSubcomplexDiagrams.augmentationTo
    (D : CompactFlatFiniteSubcomplexDiagrams Y L l)
    {T : CochainComplex (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) ℤ}
    (p : ∀ n : ℕ, L n ⟶ T) (j : D.index) : D.diagram.obj j ⟶ T :=
  (D.augmentation (D.stage j)).app ⟨j, le_rfl⟩ ≫ p (D.stage j)

/-- The whole-diagram augmentation can be evaluated at any later source stage. -/
theorem CompactFlatFiniteSubcomplexDiagrams.augmentationTo_eq
    (D : CompactFlatFiniteSubcomplexDiagrams Y L l)
    {T : CochainComplex (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) ℤ}
    (p : ∀ n : ℕ, L n ⟶ T) (hp : ∀ n : ℕ, l n ≫ p (n + 1) = p n)
    (j : D.index) (n : ℕ) (hn : D.stage j ≤ n) :
    D.augmentationTo p j = (D.augmentation n).app ⟨j, hn⟩ ≫ p n := by
  induction n, hn using Nat.le_induction with
  | base => rfl
  | succ n hn ih =>
    rw [ih, ← hp n, ← Category.assoc, D.compatibility]

set_option backward.isDefEq.respectTransparency false in
/-- The whole-diagram augmentation is natural along all source arrows. -/
theorem CompactFlatFiniteSubcomplexDiagrams.augmentationTo_naturality
    (D : CompactFlatFiniteSubcomplexDiagrams Y L l)
    {T : CochainComplex (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) ℤ}
    (p : ∀ n : ℕ, L n ⟶ T) (hp : ∀ n : ℕ, l n ≫ p (n + 1) = p n)
    {j k : D.index} (h : j ⟶ k) :
    D.diagram.map h ≫ D.augmentationTo p k = D.augmentationTo p j := by
  rw [D.augmentationTo_eq p hp j (D.stage k) (D.stage_mono (leOfHom h))]
  unfold CompactFlatFiniteSubcomplexDiagrams.augmentationTo
  convert! (D.augmentation (D.stage k)).naturality_assoc
    (homOfLE (leOfHom h) : ⟨j, D.stage_mono (leOfHom h)⟩ ⟶
      (⟨k, le_rfl⟩ : {j // D.stage j ≤ D.stage k})) (p (D.stage k)) using 1

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

/-- Every diagram term is flat, by its given finite summand decomposition.
Source: the finite-generator hypothesis of `lem-sc-compact-flat-finite-subcomplex-diagrams`.
(blueprint: lem-sc-compact-flat-diagram-term-flat). -/
theorem CompactFlatFiniteSubcomplexDiagrams.diagram_flat
    (D : CompactFlatFiniteSubcomplexDiagrams Y L l) (j : D.index) (i : ℤ) :
    SheafOfModules.IsFlat ((D.diagram.obj j).X i) := by
  obtain ⟨K, _, G, ⟨e⟩, hG, _⟩ := D.generators j i
  exact flat_of_iso e (SheafOfModules.isFlat_coproduct Y.sheaf G hG)

/-- Bar total terms are coproducts of flat diagram terms.
Source: the source-bar paragraph of `lem-sc-compact-flat-bar-union-augmentation`.
(blueprint: lem-sc-compact-flat-source-bar-flat). -/
theorem CompactFlatFiniteSubcomplexDiagrams.sourceBar_flat
    (D : CompactFlatFiniteSubcomplexDiagrams Y L l) (n : ℕ) (i : ℤ) :
    SheafOfModules.IsFlat ((D.sourceBar n).X i) := by
  apply flat_coproduct_small
  rintro ⟨⟨p, q⟩, _⟩
  apply flat_of_iso (PreorderBar.columnXIso (D.stageDiagram n) p q)
  apply flat_coproduct_small
  intro σ
  exact D.diagram_flat (σ 0).1 q

end AlgebraicGeometry
