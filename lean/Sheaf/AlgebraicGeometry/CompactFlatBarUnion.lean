/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group P2
-/
module

public import Sheaf.AlgebraicGeometry.CompactFlatEnlargedBarTower
public import Sheaf.AlgebraicGeometry.FlatTelescopeCokernelColimit
import Sheaf.AlgebraicGeometry.PreorderBarTotalSplit
import Mathlib.Data.Finset.Lattice.Fold

/-! # The union of the explicit enlarged bar tower

Source: the union-cokernel paragraph of `lem-sc-compact-flat-bar-union-augmentation`.
(blueprint: lem-sc-compact-flat-bar-union-colimit).
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

noncomputable def fullBar := PreorderBar.total (diagram D E t p hp)

noncomputable def fullBarAugmentation :
    fullBar D E t p hp ⟶ CochainComplex.mappingCone (flatTelescopeDifferential E t) :=
  PreorderBar.totalAugmentation _ (cocone D E t p hp)

def fullOrder (n : ℕ) :
    {j : Index D E t p hp // stage D E t p hp j ≤ n} →o Index D E t p hp where
  toFun := Subtype.val
  monotone' := fun _ _ h ↦ h

noncomputable def fullMap (n : ℕ) : stageDiagram D E t p hp n ⟶
    PreorderBar.orderFunctor (fullOrder D E t p hp n) ⋙ diagram D E t p hp where
  app _ := 𝟙 _

noncomputable def toFullBar (n : ℕ) : enlargedBar D E t p hp n ⟶ fullBar D E t p hp :=
  PreorderBar.totalMap _ _ (fullOrder D E t p hp n) (fullMap D E t p hp n)

lemma toFullBar_naturality (n : ℕ) :
    enlargedBarMap D E t p hp n ≫ toFullBar D E t p hp (n + 1) =
      toFullBar D E t p hp n := by
  have h := PreorderBar.totalMap_comp (stageDiagram D E t p hp n)
    (stageDiagram D E t p hp (n + 1)) (diagram D E t p hp)
    (stageOrder D E t p hp n) (fullOrder D E t p hp (n + 1))
    (stageMap D E t p hp n) (fullMap D E t p hp (n + 1))
    (fullMap D E t p hp n) (fun _ ↦ by
      simp only [fullMap, stageMap, Category.id_comp]
      rfl)
  exact h

lemma toFullBar_augmentation (n : ℕ) :
    toFullBar D E t p hp n ≫ fullBarAugmentation D E t p hp =
      enlargedBarAugmentation D E t p hp n := by
  have h := PreorderBar.totalAugmentation_naturality
    (stageDiagram D E t p hp n) (diagram D E t p hp) (fullOrder D E t p hp n)
    (stageCocone D E t p hp n) (cocone D E t p hp) (fullMap D E t p hp n) (𝟙 _)
    (fun _ ↦ by simp [fullMap, stageCocone, cocone, fullOrder])
  simpa [toFullBar, fullBarAugmentation, enlargedBarAugmentation] using h

noncomputable def unionCocone : Cocone (Functor.ofSequence (enlargedBarMap D E t p hp)) where
  pt := fullBar D E t p hp
  ι := NatTrans.ofSequence (toFullBar D E t p hp) (fun n ↦ by
    simpa only [Functor.ofSequence_map_homOfLE_succ, Functor.const_obj_map] using
      (toFullBar_naturality D E t p hp n).trans (Category.comp_id _).symm)

private def liftString {a k : ℕ} (σ : Fin (a + 1) →o Index D E t p hp)
    (h : ∀ i, stage D E t p hp (σ i) ≤ k) :
    Fin (a + 1) →o {j : Index D E t p hp // stage D E t p hp j ≤ k} where
  toFun i := ⟨σ i, h i⟩
  monotone' := fun _ _ hij ↦ σ.monotone hij

private def stringStage {a : ℕ} (σ : Fin (a + 1) →o Index D E t p hp) : ℕ :=
  Finset.univ.sup (fun i ↦ stage D E t p hp (σ i))

private lemma le_stringStage {a : ℕ} (σ : Fin (a + 1) →o Index D E t p hp)
    (i : Fin (a + 1)) : stage D E t p hp (σ i) ≤ stringStage D E t p hp σ :=
  Finset.le_sup (f := fun i ↦ stage D E t p hp (σ i)) (Finset.mem_univ i)

private lemma stringStage_le {a k : ℕ} (σ : Fin (a + 1) →o Index D E t p hp)
    (h : ∀ i, stage D E t p hp (σ i) ≤ k) : stringStage D E t p hp σ ≤ k := by
  exact Finset.sup_le (fun i _ ↦ h i)

private noncomputable def genToCocone (n : ℤ)
    (c : Cocone (Functor.ofSequence (enlargedBarMap D E t p hp) ⋙
      HomologicalComplex.eval _ (ComplexShape.up ℤ) n))
    {a : ℕ} {q : ℤ} (h : q - (a : ℤ) = n)
    (σ : Fin (a + 1) →o Index D E t p hp) (k : ℕ)
    (hk : ∀ i, stage D E t p hp (σ i) ≤ k) :
    ((diagram D E t p hp).obj (σ 0)).X q ⟶ c.pt :=
  PreorderBar.ιTerm (stageDiagram D E t p hp k) a q n h
    (liftString D E t p hp σ hk) ≫ c.ι.app k

private lemma genToCocone_step (n : ℤ)
    (c : Cocone (Functor.ofSequence (enlargedBarMap D E t p hp) ⋙
      HomologicalComplex.eval _ (ComplexShape.up ℤ) n))
    {a : ℕ} {q : ℤ} (h : q - (a : ℤ) = n)
    (σ : Fin (a + 1) →o Index D E t p hp) (k : ℕ)
    (hk : ∀ i, stage D E t p hp (σ i) ≤ k) :
    genToCocone D E t p hp n c h σ (k + 1)
      (fun i ↦ Nat.le_trans (hk i) (Nat.le_succ k)) =
        genToCocone D E t p hp n c h σ k hk := by
  have hc := c.w (homOfLE (Nat.le_succ k))
  simp only [Functor.comp_map, Functor.ofSequence_map_homOfLE_succ,
    HomologicalComplex.eval_map] at hc
  have hg := PreorderBar.ιTerm_map (stageDiagram D E t p hp k)
    (stageDiagram D E t p hp (k + 1)) (stageOrder D E t p hp k)
    (stageMap D E t p hp k) a q n h (liftString D E t p hp σ hk)
  simp only [stageMap, HomologicalComplex.id_f, Category.id_comp] at hg
  change PreorderBar.ιTerm (stageDiagram D E t p hp k) a q n h
    (liftString D E t p hp σ hk) ≫ (enlargedBarMap D E t p hp k).f n =
      PreorderBar.ιTerm (stageDiagram D E t p hp (k + 1)) a q n h
        (liftString D E t p hp σ (fun i ↦ Nat.le_trans (hk i) (Nat.le_succ k))) at hg
  unfold genToCocone
  rw [← hg, Category.assoc, hc]

private lemma genToCocone_stable (n : ℤ)
    (c : Cocone (Functor.ofSequence (enlargedBarMap D E t p hp) ⋙
      HomologicalComplex.eval _ (ComplexShape.up ℤ) n))
    {a : ℕ} {q : ℤ} (h : q - (a : ℤ) = n)
    (σ : Fin (a + 1) →o Index D E t p hp) (k : ℕ)
    (hk : ∀ i, stage D E t p hp (σ i) ≤ k) :
    genToCocone D E t p hp n c h σ k hk =
      genToCocone D E t p hp n c h σ (stringStage D E t p hp σ)
        (le_stringStage D E t p hp σ) := by
  have hbound := stringStage_le D E t p hp σ hk
  induction k, hbound using Nat.le_induction with
  | base => rfl
  | succ k hbound ih =>
    rw [genToCocone_step D E t p hp n c h σ k
      (fun i ↦ le_trans (le_stringStage D E t p hp σ i) hbound)]
    exact ih _

private noncomputable def fullDesc (n : ℤ)
    (c : Cocone (Functor.ofSequence (enlargedBarMap D E t p hp) ⋙
      HomologicalComplex.eval _ (ComplexShape.up ℤ) n)) : (fullBar D E t p hp).X n ⟶ c.pt :=
  (PreorderBar.bicomplex (diagram D E t p hp)).totalDesc (fun a q h ↦
    (PreorderBar.columnXIso (diagram D E t p hp) a q).hom ≫
      Sigma.desc (fun σ : Fin (a + 1) →o Index D E t p hp ↦
        genToCocone D E t p hp n c h σ (stringStage D E t p hp σ)
          (le_stringStage D E t p hp σ)))

private lemma ιTerm_fullDesc (n : ℤ)
    (c : Cocone (Functor.ofSequence (enlargedBarMap D E t p hp) ⋙
      HomologicalComplex.eval _ (ComplexShape.up ℤ) n))
    (a : ℕ) (q : ℤ) (h : q - (a : ℤ) = n)
    (σ : Fin (a + 1) →o Index D E t p hp) :
    PreorderBar.ιTerm (diagram D E t p hp) a q n h σ ≫ fullDesc D E t p hp n c =
      genToCocone D E t p hp n c h σ (stringStage D E t p hp σ)
        (le_stringStage D E t p hp σ) := by
  simp [PreorderBar.ιTerm, fullDesc, Category.assoc]

set_option backward.isDefEq.respectTransparency false in
private lemma fullDesc_fac (n : ℤ)
    (c : Cocone (Functor.ofSequence (enlargedBarMap D E t p hp) ⋙
      HomologicalComplex.eval _ (ComplexShape.up ℤ) n)) (k : ℕ) :
    (toFullBar D E t p hp k).f n ≫ fullDesc D E t p hp n c = c.ι.app k := by
  apply PreorderBar.ιTerm_hom_ext (stageDiagram D E t p hp k) n
  intro a q h σ
  let τ := (fullOrder D E t p hp k).comp σ
  have hb (i : Fin (a + 1)) : stage D E t p hp (τ i) ≤ k := (σ i).2
  have hg := PreorderBar.ιTerm_map (stageDiagram D E t p hp k) (diagram D E t p hp)
    (fullOrder D E t p hp k) (fullMap D E t p hp k) a q n h σ
  simp only [fullMap, HomologicalComplex.id_f, Category.id_comp] at hg
  change PreorderBar.ιTerm (stageDiagram D E t p hp k) a q n h σ ≫
    (toFullBar D E t p hp k).f n = PreorderBar.ιTerm (diagram D E t p hp) a q n h τ at hg
  calc
    PreorderBar.ιTerm (stageDiagram D E t p hp k) a q n h σ ≫
        ((toFullBar D E t p hp k).f n ≫ fullDesc D E t p hp n c) =
      PreorderBar.ιTerm (diagram D E t p hp) a q n h τ ≫ fullDesc D E t p hp n c := by
        rw [← Category.assoc]
        rw [hg]
    _ = genToCocone D E t p hp n c h τ (stringStage D E t p hp τ)
        (le_stringStage D E t p hp τ) := ιTerm_fullDesc D E t p hp n c a q h τ
    _ = genToCocone D E t p hp n c h τ k hb :=
      (genToCocone_stable D E t p hp n c h τ k hb).symm
    _ = PreorderBar.ιTerm (stageDiagram D E t p hp k) a q n h σ ≫ c.ι.app k := by
      rfl

/-- Every term of the full bar is the union of its stage terms. -/
private noncomputable def unionIsColimitEval (n : ℤ) :
    IsColimit ((HomologicalComplex.eval _ (ComplexShape.up ℤ) n).mapCocone
      (unionCocone D E t p hp)) where
  desc c := fullDesc D E t p hp n c
  fac c k := fullDesc_fac D E t p hp n c k
  uniq c m hm := by
    apply PreorderBar.ιTerm_hom_ext (diagram D E t p hp) n
    intro a q h σ
    let k := stringStage D E t p hp σ
    let σ' := liftString D E t p hp σ (le_stringStage D E t p hp σ)
    have hg := PreorderBar.ιTerm_map (stageDiagram D E t p hp k) (diagram D E t p hp)
      (fullOrder D E t p hp k) (fullMap D E t p hp k) a q n h σ'
    simp only [fullMap, HomologicalComplex.id_f, Category.id_comp] at hg
    change PreorderBar.ιTerm (stageDiagram D E t p hp k) a q n h σ' ≫
      (toFullBar D E t p hp k).f n = PreorderBar.ιTerm (diagram D E t p hp) a q n h σ at hg
    have hmk := hm k
    change (toFullBar D E t p hp k).f n ≫ m = c.ι.app k at hmk
    calc
      PreorderBar.ιTerm (diagram D E t p hp) a q n h σ ≫ m =
        (PreorderBar.ιTerm (stageDiagram D E t p hp k) a q n h σ' ≫
          (toFullBar D E t p hp k).f n) ≫ m := congrArg (fun z ↦ z ≫ m) hg.symm
      _ = PreorderBar.ιTerm (stageDiagram D E t p hp k) a q n h σ' ≫ c.ι.app k := by
        rw [Category.assoc, hmk]
      _ = PreorderBar.ιTerm (diagram D E t p hp) a q n h σ ≫ fullDesc D E t p hp n c := by
        rw [← hg, Category.assoc, fullDesc_fac]


/-- The full bar is the colimit of the explicitly constructed stage bars.

Source: the union-cokernel paragraph of `lem-sc-compact-flat-bar-union-augmentation`.
(blueprint: lem-sc-compact-flat-bar-union-colimit).

Proof: A bar string contains finitely many vertices, so their stage labels have
a maximum. Define a map from each full-bar generator using its copy in this stage.
A compatible cocone assigns the same map in every later stage. This gives a unique
map from each full-bar term. Evaluation of complexes jointly reflects colimits,
so these termwise universal properties give the colimit of complexes. -/
theorem unionIsColimit_nonempty : Nonempty (IsColimit (unionCocone D E t p hp)) := by
  exact ⟨HomologicalComplex.isColimitOfEval _ _ (unionIsColimitEval D E t p hp)⟩

/-- The colimit structure determined uniquely by the proved universal property. -/
noncomputable def unionIsColimit : IsColimit (unionCocone D E t p hp) :=
  (unionIsColimit_nonempty D E t p hp).some

/-- The sequential cokernel is canonically the full enlarged bar. -/
noncomputable def unionIso :
    cokernel (flatTelescopeDifferential (enlargedBar D E t p hp)
      (enlargedBarMap D E t p hp)) ≅ fullBar D E t p hp :=
  (flatTelescopeCokernelIsColimit (enlargedBar D E t p hp)
    (enlargedBarMap D E t p hp)).coconePointUniqueUpToIso (unionIsColimit D E t p hp)

lemma unionIso_ι (n : ℕ) :
    Sigma.ι (enlargedBar D E t p hp) n ≫
      cokernel.π (flatTelescopeDifferential (enlargedBar D E t p hp)
        (enlargedBarMap D E t p hp)) ≫ (unionIso D E t p hp).hom =
          toFullBar D E t p hp n := by
  exact IsColimit.comp_coconePointUniqueUpToIso_hom
    (flatTelescopeCokernelIsColimit (enlargedBar D E t p hp)
      (enlargedBarMap D E t p hp)) (unionIsColimit D E t p hp) n

/-- The cokernel augmentation is exactly the full-bar augmentation under this iso. -/
lemma unionIso_augmentation
    (hz : flatTelescopeDifferential (enlargedBar D E t p hp)
      (enlargedBarMap D E t p hp) ≫
        Sigma.desc (enlargedBarAugmentation D E t p hp) = 0) :
    (unionIso D E t p hp).hom ≫ fullBarAugmentation D E t p hp =
      cokernel.desc (flatTelescopeDifferential (enlargedBar D E t p hp)
        (enlargedBarMap D E t p hp))
          (Sigma.desc (enlargedBarAugmentation D E t p hp)) hz := by
  apply (cancel_epi (cokernel.π (flatTelescopeDifferential (enlargedBar D E t p hp)
    (enlargedBarMap D E t p hp)))).1
  apply Sigma.hom_ext
  intro n
  simp only [cokernel.π_desc, Sigma.ι_desc]
  have h := congrArg (fun z ↦ z ≫ fullBarAugmentation D E t p hp)
    (unionIso_ι D E t p hp n)
  simpa only [Category.assoc] using h.trans (toFullBar_augmentation D E t p hp n)

end CompactFlatBarIndex
end AlgebraicGeometry
