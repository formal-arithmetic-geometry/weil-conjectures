/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group P2
-/
module
public import Sheaf.AlgebraicGeometry.PreorderBarUnitHomotopy
public import Sheaf.AlgebraicGeometry.PreorderBarTotalHomotopy
public import Mathlib.AlgebraicTopology.SimplicialObject.ChainHomotopy
public import Mathlib.Algebra.Homology.HomotopyCategory
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.AlgebraicTopology.ExtraDegeneracy

/-! # A terminal preorder bar contracts to its value

Explicit constructions and proved properties for the bar-union argument.
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
universe u v w
open CategoryTheory CategoryTheory.Limits Opposite Simplicial
namespace CategoryTheory.PreorderBar
variable {I : Type u} [Preorder I] {C : Type w} [Category.{v} C]
  [HasCoproducts.{u} C] (D : I ⥤ C) (j : I) (hj : ∀ i, i ≤ j)

noncomputable def terminalCocone : Cocone D where
  pt := D.obj j
  ι := { app i := D.map (homOfLE (hj i))
         naturality {i k} g := by
           dsimp
           rw [← D.map_comp, Category.comp_id]
           congr 1 }

noncomputable def terminalSection :
    (SimplicialObject.const C).obj (D.obj j) ⟶ simplicial D where
  app n := Sigma.ι (fun σ : Fin (n.unop.len + 1) →o I ↦ D.obj (σ 0))
    (OrderHom.const _ j)
  naturality {n m} α := by
    dsimp [simplicial]
    simp only [ι_map, Category.id_comp]
    change Sigma.ι (fun σ : Fin (m.unop.len + 1) →o I ↦ D.obj (σ 0))
      (OrderHom.const _ j) = D.map (𝟙 j) ≫
        Sigma.ι (fun σ : Fin (m.unop.len + 1) →o I ↦ D.obj (σ 0)) (OrderHom.const _ j)
    rw [D.map_id, Category.id_comp]

lemma terminalSection_augmentation :
    terminalSection D j ≫ augmentation D (terminalCocone D j hj) = 𝟙 _ := by
  ext n
  change Sigma.ι (fun σ : Fin (n.unop.len + 1) →o I ↦ D.obj (σ 0))
    (OrderHom.const _ j) ≫ Sigma.desc (fun σ : Fin (n.unop.len + 1) →o I ↦
      D.map (homOfLE (hj (σ 0)))) = 𝟙 _
  rw [Sigma.ι_desc]
  change D.map (𝟙 j) = 𝟙 _
  exact D.map_id _

lemma terminalUnitMap_eq :
    reindex D D (OrderHom.const _ j) (unitMap (OrderHom.const _ j) hj D) =
      augmentation D (terminalCocone D j hj) ≫ terminalSection D j := by
  ext n
  apply Sigma.hom_ext
  intro σ
  change Sigma.ι (fun τ : Fin (n.unop.len + 1) →o I ↦ D.obj (τ 0)) σ ≫
    Sigma.desc (fun τ : Fin (n.unop.len + 1) →o I ↦
      D.map (homOfLE (hj (τ 0))) ≫ Sigma.ι
        (fun ρ : Fin (n.unop.len + 1) →o I ↦ D.obj (ρ 0))
        ((OrderHom.const I j).comp τ)) =
    Sigma.ι (fun τ : Fin (n.unop.len + 1) →o I ↦ D.obj (τ 0)) σ ≫
      (Sigma.desc (fun τ : Fin (n.unop.len + 1) →o I ↦
        D.map (homOfLE (hj (τ 0)))) ≫
        Sigma.ι (fun τ : Fin (n.unop.len + 1) →o I ↦ D.obj (τ 0)) (OrderHom.const _ j))
  rw [Sigma.ι_desc, Sigma.ι_desc_assoc]
  rfl


variable {A : Type w} [Category.{v} A] [Preadditive A] [HasZeroObject A]
  [HasCoproducts.{u} A] [HasCoproducts.{0} A]

noncomputable def totalizeHomotopyEquiv
    {K L : HomologicalComplex₂ A (ComplexShape.down ℕ) (ComplexShape.up ℤ)}
    [K.HasTotal (ComplexShape.up ℤ)] [L.HasTotal (ComplexShape.up ℤ)]
    (e : HomotopyEquiv K L) :
    HomotopyEquiv (K.total (ComplexShape.up ℤ)) (L.total (ComplexShape.up ℤ)) where
  hom := HomologicalComplex₂.total.map e.hom _
  inv := HomologicalComplex₂.total.map e.inv _
  homotopyHomInvId := by
    let h := horizontalHomotopy e.homotopyHomInvId
    simpa only [HomologicalComplex₂.total.map_comp, HomologicalComplex₂.total.map_id] using h
  homotopyInvHomId := by
    let h := horizontalHomotopy e.homotopyInvHomId
    simpa only [HomologicalComplex₂.total.map_comp, HomologicalComplex₂.total.map_id] using h

noncomputable def terminalAlternatingEquiv
    (D' : I ⥤ CochainComplex A ℤ) (j : I) (hj : ∀ i, i ≤ j) :
    HomotopyEquiv (bicomplex D')
      ((AlgebraicTopology.alternatingFaceMapComplex (CochainComplex A ℤ)).obj
        ((SimplicialObject.const _).obj (D'.obj j))) where
  hom := (AlgebraicTopology.alternatingFaceMapComplex _).map
    (augmentation D' (terminalCocone D' j hj))
  inv := (AlgebraicTopology.alternatingFaceMapComplex _).map (terminalSection D' j)
  homotopyHomInvId := by
    let h := (unitSimplicialHomotopy (OrderHom.const _ j) hj D').toChainHomotopy.symm
    rw [terminalUnitMap_eq D' j hj] at h
    simpa only [bicomplex, AlgebraicTopology.alternatingFaceMapComplex,
      Functor.map_comp, Functor.map_id] using h
  homotopyInvHomId := Homotopy.ofEq (by
    rw [← Functor.map_comp, terminalSection_augmentation, Functor.map_id])

omit [HasCoproducts.{0} A] in
lemma terminalAlternatingEquiv_augmentation
    (D' : I ⥤ CochainComplex A ℤ) (j : I) (hj : ∀ i, i ≤ j) :
    (terminalAlternatingEquiv D' j hj).hom ≫
      AlgebraicTopology.AlternatingFaceMapComplex.ε.app
        (SimplicialObject.Augmented.const.obj (D'.obj j)) =
      AlgebraicTopology.AlternatingFaceMapComplex.ε.app
        (augmented D' (terminalCocone D' j hj)) := by
  apply HomologicalComplex.hom_ext
  intro p
  cases p with
  | zero =>
    simp only [HomologicalComplex.comp_f,
      AlgebraicTopology.AlternatingFaceMapComplex.ε_app_f_zero]
    change (augmentation D' (terminalCocone D' j hj)).app (op ⦋0⦌) ≫ 𝟙 _ = _
    rw [Category.comp_id]
    rfl
  | succ p =>
    simp only [HomologicalComplex.comp_f,
      AlgebraicTopology.AlternatingFaceMapComplex.ε_app_f_succ, comp_zero]

/-- A terminal preorder bar contracts to its value.

Source: the source-bar and finite-cone-block argument in
`lem-sc-compact-flat-bar-union-augmentation`.
(blueprint: lem-sc-preorder-bar-terminal-augmentation).

Proof: Include D(j) in every simplicial degree using the constant string at j. This section
followed by
augmentation is identity. In the other order its composite is the reindexing induced by the
constant order map i↦j and the unit i≤j, so the unit prism supplies a homotopy. Apply the
alternating face-map functor and totalize the homotopy equivalence. The constant simplicial object
contracts to the single column by Mathlib ExtraDegeneracy.const; finally use the actual single-
column collapse isomorphism. The composite hom map is exactly the canonical augmentation. -/
noncomputable def terminalTotalEquiv
    (D' : I ⥤ CochainComplex A ℤ) (j : I) (hj : ∀ i, i ≤ j) :
    HomotopyEquiv (total D') (D'.obj j) := by
  let e₁ := totalizeHomotopyEquiv (terminalAlternatingEquiv D' j hj)
  let e₂ := totalizeHomotopyEquiv
    ((SimplicialObject.Augmented.ExtraDegeneracy.const (D'.obj j)).homotopyEquiv)
  haveI := collapse_isIso (D'.obj j)
  let e₃ := HomotopyEquiv.ofIso (asIso (collapse (D'.obj j)))
  exact e₁.trans (e₂.trans e₃)

lemma terminalTotalEquiv_hom
    (D' : I ⥤ CochainComplex A ℤ) (j : I) (hj : ∀ i, i ≤ j) :
    (terminalTotalEquiv D' j hj).hom =
      totalAugmentation D' (terminalCocone D' j hj) := by
  change HomologicalComplex₂.total.map (terminalAlternatingEquiv D' j hj).hom _ ≫
    (HomologicalComplex₂.total.map
      (AlgebraicTopology.AlternatingFaceMapComplex.ε.app
        (SimplicialObject.Augmented.const.obj (D'.obj j))) _ ≫ collapse (D'.obj j)) = _
  rw [← Category.assoc, ← HomologicalComplex₂.total.map_comp,
    terminalAlternatingEquiv_augmentation]
  rfl

theorem terminalAugmentation_isIsoHomotopy
    (D' : I ⥤ CochainComplex A ℤ) (j : I) (hj : ∀ i, i ≤ j) :
    IsIso ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).map
      (totalAugmentation D' (terminalCocone D' j hj))) := by
  rw [← terminalTotalEquiv_hom D' j hj]
  exact (HomotopyCategory.isoOfHomotopyEquiv (terminalTotalEquiv D' j hj)).isIso_hom

theorem terminalAugmentation_quasiIso
    {B : Type w} [Category.{v} B] [Abelian B]
    [HasCoproducts.{u} B] [HasCoproducts.{0} B]
    (D' : I ⥤ CochainComplex B ℤ) (j : I) (hj : ∀ i, i ≤ j) :
    QuasiIso (totalAugmentation D' (terminalCocone D' j hj)) := by
  rw [← terminalTotalEquiv_hom D' j hj]
  infer_instance

end CategoryTheory.PreorderBar
