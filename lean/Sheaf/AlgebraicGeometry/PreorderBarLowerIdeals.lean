/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group P2
-/
module
import Sheaf.AlgebraicGeometry.PreorderBarTotalSplit
public import Sheaf.AlgebraicGeometry.PreorderBarTerminalAugmentation

/-! # A bar total is the colimit of its principal lower ideals

Explicit constructions and proved properties for the bar-union argument.
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
universe u v w
open CategoryTheory CategoryTheory.Limits
namespace CategoryTheory.PreorderBar
variable {I : Type u} [Preorder I] {A : Type w} [Category.{v} A] [Preadditive A]
  [HasZeroObject A] [HasCoproducts.{u} A] [HasCoproducts.{0} A]
  (D : I ⥤ CochainComplex A ℤ)

def lowerFullOrder (j : I) : {i : I // i ≤ j} →o I where
  toFun := Subtype.val
  monotone' := fun _ _ h ↦ h

def lowerDiagram (j : I) := orderFunctor (lowerFullOrder j) ⋙ D

noncomputable def lowerBar (j : I) := total (lowerDiagram D j)

def lowerOrder {j k : I} (h : j ≤ k) : {i : I // i ≤ j} →o {i : I // i ≤ k} where
  toFun i := ⟨i.1, i.2.trans h⟩
  monotone' := fun _ _ h ↦ h

def lowerMap {j k : I} (h : j ≤ k) :
    lowerDiagram D j ⟶ orderFunctor (lowerOrder h) ⋙ lowerDiagram D k where
  app _ := 𝟙 _

noncomputable def lowerBarMap {j k : I} (h : j ≤ k) : lowerBar D j ⟶ lowerBar D k :=
  totalMap _ _ (lowerOrder h) (lowerMap D h)

omit [HasZeroObject A] in
lemma lowerBarMap_id (j : I) : lowerBarMap D (le_refl j) = 𝟙 _ := by
  have hr : reindex (lowerDiagram D j) (lowerDiagram D j) (lowerOrder (le_refl j))
      (lowerMap D (le_refl j)) = 𝟙 _ := by
    ext n : 1
    apply Sigma.hom_ext
    intro σ
    simp only [reindex, lowerMap, Sigma.ι_desc, Category.id_comp,
      NatTrans.id_app]
    simp only [simplicial, obj, Category.comp_id]
    rfl
  change HomologicalComplex₂.total.map
    (AlgebraicTopology.AlternatingFaceMapComplex.map _) _ = _
  rw [hr]
  change HomologicalComplex₂.total.map
    ((AlgebraicTopology.alternatingFaceMapComplex _).map (𝟙 _)) _ = _
  rw [Functor.map_id, HomologicalComplex₂.total.map_id]
  rfl

omit [HasZeroObject A] in
lemma lowerBarMap_comp {i j k : I} (h : i ≤ j) (h' : j ≤ k) :
    lowerBarMap D h ≫ lowerBarMap D h' = lowerBarMap D (h.trans h') := by
  exact totalMap_comp (lowerDiagram D i) (lowerDiagram D j) (lowerDiagram D k)
    (lowerOrder h) (lowerOrder h') (lowerMap D h) (lowerMap D h')
    (lowerMap D (h.trans h')) (fun _ ↦ (Category.id_comp _).symm)

noncomputable def lowerBars : I ⥤ CochainComplex A ℤ where
  obj := lowerBar D
  map g := lowerBarMap D (leOfHom g)
  map_id j := lowerBarMap_id D j
  map_comp g h := (lowerBarMap_comp D (leOfHom g) (leOfHom h)).symm

def lowerFullMap (j : I) : lowerDiagram D j ⟶ orderFunctor (lowerFullOrder j) ⋙ D :=
  𝟙 _

noncomputable def lowerToFull (j : I) : lowerBar D j ⟶ total D :=
  totalMap _ _ (lowerFullOrder j) (lowerFullMap D j)

omit [HasZeroObject A] in
lemma lowerToFull_naturality {j k : I} (h : j ≤ k) :
    lowerBarMap D h ≫ lowerToFull D k = lowerToFull D j := by
  exact totalMap_comp (lowerDiagram D j) (lowerDiagram D k) D
    (lowerOrder h) (lowerFullOrder k) (lowerMap D h) (lowerFullMap D k)
    (lowerFullMap D j) (fun _ ↦ (Category.id_comp _).symm)

noncomputable def lowerBarsCocone : Cocone (lowerBars D) where
  pt := total D
  ι := { app j := lowerToFull D j
         naturality {j k} g := by
           change lowerBarMap D (leOfHom g) ≫ lowerToFull D k = _ ≫ 𝟙 _
           rw [Category.comp_id]
           exact lowerToFull_naturality D (leOfHom g) }

noncomputable def lowerAugmentation (j : I) : lowerBar D j ⟶ D.obj j :=
  totalAugmentation (lowerDiagram D j)
    (terminalCocone (lowerDiagram D j) ⟨j, le_rfl⟩ (fun i ↦ i.2))

lemma lowerAugmentation_naturality {j k : I} (h : j ≤ k) :
    lowerBarMap D h ≫ lowerAugmentation D k = lowerAugmentation D j ≫ D.map (homOfLE h) := by
  apply totalAugmentation_naturality
  intro i
  change 𝟙 _ ≫ D.map (homOfLE (i.2.trans h)) =
    D.map (homOfLE i.2) ≫ D.map (homOfLE h)
  rw [Category.id_comp, ← D.map_comp]
  congr 1

noncomputable def lowerAugmentationNat : lowerBars D ⟶ D where
  app := lowerAugmentation D
  naturality _ _ g := lowerAugmentation_naturality D (leOfHom g)

lemma lowerToFull_augmentation (c : Cocone D) (j : I) :
    lowerToFull D j ≫ totalAugmentation D c = lowerAugmentation D j ≫ c.ι.app j := by
  apply totalAugmentation_naturality
  intro i
  change 𝟙 _ ≫ c.ι.app i.1 = D.map (homOfLE i.2) ≫ c.ι.app j
  rw [Category.id_comp, c.w (homOfLE i.2)]

private def lowerLiftString {a : ℕ} (σ : Fin (a + 1) →o I) (j : I)
    (h : ∀ i, σ i ≤ j) : Fin (a + 1) →o {i : I // i ≤ j} where
  toFun i := ⟨σ i, h i⟩
  monotone' := fun _ _ hij ↦ σ.monotone hij

private lemma le_stringLast {a : ℕ} (σ : Fin (a + 1) →o I) (i : Fin (a + 1)) :
    σ i ≤ σ (Fin.last a) := σ.monotone (Fin.le_last i)

private noncomputable def lowerGen (n : ℤ)
    (c : Cocone (lowerBars D ⋙ HomologicalComplex.eval _ (ComplexShape.up ℤ) n))
    {a : ℕ} {q : ℤ} (h : q - (a : ℤ) = n) (σ : Fin (a + 1) →o I) (j : I)
    (hj : ∀ i, σ i ≤ j) : (D.obj (σ 0)).X q ⟶ c.pt :=
  ιTerm (lowerDiagram D j) a q n h (lowerLiftString σ j hj) ≫ c.ι.app j

omit [HasZeroObject A] in
private lemma lowerGen_stable (n : ℤ)
    (c : Cocone (lowerBars D ⋙ HomologicalComplex.eval _ (ComplexShape.up ℤ) n))
    {a : ℕ} {q : ℤ} (h : q - (a : ℤ) = n) (σ : Fin (a + 1) →o I) (j : I)
    (hj : ∀ i, σ i ≤ j) :
    lowerGen D n c h σ j hj =
      lowerGen D n c h σ (σ (Fin.last a)) (le_stringLast σ) := by
  have hc := c.w (homOfLE (hj (Fin.last a)))
  change (lowerBarMap D (hj (Fin.last a))).f n ≫ c.ι.app j =
    c.ι.app (σ (Fin.last a)) at hc
  have hg := ιTerm_map (lowerDiagram D (σ (Fin.last a))) (lowerDiagram D j)
    (lowerOrder (hj (Fin.last a))) (lowerMap D (hj (Fin.last a)))
    a q n h (lowerLiftString σ (σ (Fin.last a)) (le_stringLast σ))
  simp only [lowerMap, HomologicalComplex.id_f, Category.id_comp] at hg
  change ιTerm (lowerDiagram D (σ (Fin.last a))) a q n h
    (lowerLiftString σ (σ (Fin.last a)) (le_stringLast σ)) ≫
      (lowerBarMap D (hj (Fin.last a))).f n =
        ιTerm (lowerDiagram D j) a q n h (lowerLiftString σ j hj) at hg
  unfold lowerGen
  rw [← hg, Category.assoc, hc]

private noncomputable def lowerFullDesc (n : ℤ)
    (c : Cocone (lowerBars D ⋙ HomologicalComplex.eval _ (ComplexShape.up ℤ) n)) :
    (total D).X n ⟶ c.pt :=
  (bicomplex D).totalDesc (fun a q h ↦ (columnXIso D a q).hom ≫
    Sigma.desc (fun σ : Fin (a + 1) →o I ↦
      lowerGen D n c h σ (σ (Fin.last a)) (le_stringLast σ)))

omit [HasZeroObject A] in
private lemma ιTerm_lowerFullDesc (n : ℤ)
    (c : Cocone (lowerBars D ⋙ HomologicalComplex.eval _ (ComplexShape.up ℤ) n))
    (a : ℕ) (q : ℤ) (h : q - (a : ℤ) = n) (σ : Fin (a + 1) →o I) :
    ιTerm D a q n h σ ≫ lowerFullDesc D n c =
      lowerGen D n c h σ (σ (Fin.last a)) (le_stringLast σ) := by
  simp [ιTerm, lowerFullDesc, Category.assoc]

omit [HasZeroObject A] in
private lemma lowerFullDesc_fac (n : ℤ)
    (c : Cocone (lowerBars D ⋙ HomologicalComplex.eval _ (ComplexShape.up ℤ) n))
    (j : I) : (lowerToFull D j).f n ≫ lowerFullDesc D n c = c.ι.app j := by
  apply ιTerm_hom_ext (lowerDiagram D j) n
  intro a q h σ
  let τ := (lowerFullOrder j).comp σ
  have hb (i : Fin (a + 1)) : τ i ≤ j := (σ i).2
  have hg := ιTerm_map (lowerDiagram D j) D (lowerFullOrder j)
    (lowerFullMap D j) a q n h σ
  simp only [lowerFullMap, NatTrans.id_app, HomologicalComplex.id_f, Category.id_comp] at hg
  change ιTerm (lowerDiagram D j) a q n h σ ≫ (lowerToFull D j).f n =
    ιTerm D a q n h τ at hg
  calc
    ιTerm (lowerDiagram D j) a q n h σ ≫
        ((lowerToFull D j).f n ≫ lowerFullDesc D n c) =
      ιTerm D a q n h τ ≫ lowerFullDesc D n c := by rw [← Category.assoc, hg]
    _ = lowerGen D n c h τ (τ (Fin.last a)) (le_stringLast τ) :=
      ιTerm_lowerFullDesc D n c a q h τ
    _ = lowerGen D n c h τ j hb := (lowerGen_stable D n c h τ j hb).symm
    _ = ιTerm (lowerDiagram D j) a q n h σ ≫ c.ι.app j := by rfl

private noncomputable def lowerBarsIsColimitEval (n : ℤ) :
    IsColimit ((HomologicalComplex.eval _ (ComplexShape.up ℤ) n).mapCocone
      (lowerBarsCocone D)) where
  desc c := lowerFullDesc D n c
  fac c j := lowerFullDesc_fac D n c j
  uniq c m hm := by
    apply ιTerm_hom_ext D n
    intro a q h σ
    let j := σ (Fin.last a)
    let σ' := lowerLiftString σ j (le_stringLast σ)
    have hg := ιTerm_map (lowerDiagram D j) D (lowerFullOrder j)
      (lowerFullMap D j) a q n h σ'
    simp only [lowerFullMap, NatTrans.id_app, HomologicalComplex.id_f, Category.id_comp] at hg
    change ιTerm (lowerDiagram D j) a q n h σ' ≫ (lowerToFull D j).f n =
      ιTerm D a q n h σ at hg
    have hmk := hm j
    change (lowerToFull D j).f n ≫ m = c.ι.app j at hmk
    calc
      ιTerm D a q n h σ ≫ m =
        (ιTerm (lowerDiagram D j) a q n h σ' ≫ (lowerToFull D j).f n) ≫ m :=
          congrArg (fun z ↦ z ≫ m) hg.symm
      _ = ιTerm (lowerDiagram D j) a q n h σ' ≫ c.ι.app j := by rw [Category.assoc, hmk]
      _ = ιTerm D a q n h σ ≫ lowerFullDesc D n c := by
        rw [← hg, Category.assoc, lowerFullDesc_fac]

omit [HasZeroObject A] in
/-- A bar total is the colimit of its principal lower ideals.

Source: the source-bar and finite-cone-block argument in
`lem-sc-compact-flat-bar-union-augmentation`.
(blueprint: lem-sc-preorder-bar-lower-ideals-colimit).

Proof: A monotone finite string lies in the principal lower ideal of its last vertex. Given a
cocone on
the lower-ideal bars, define its map out of each full-bar generator using that last vertex. If the
string also lies below j, cocone naturality identifies this map with the map from the j-th lower-
ideal bar. Therefore the degreewise maps are well defined and satisfy every cocone equation.
Commutation with differentials follows by testing on the lower-ideal generators, since their
inclusions are chain maps and jointly generate. Coproduct extensionality proves uniqueness.
Evaluation of complexes creates colimits, giving the stated universal property. -/
theorem lowerBarsIsColimit_nonempty : Nonempty (IsColimit (lowerBarsCocone D)) := by
  exact ⟨HomologicalComplex.isColimitOfEval _ _ (lowerBarsIsColimitEval D)⟩

noncomputable def lowerBarsIsColimit : IsColimit (lowerBarsCocone D) :=
  (lowerBarsIsColimit_nonempty D).some

end CategoryTheory.PreorderBar
