/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group P1
-/
module

public import WeilConjectures.AlgebraicGeometry.FlatTelescopeStageMap

public import Mathlib.CategoryTheory.Filtered.Basic

import WeilConjectures.CategoryTheory.GrothendieckAbelian.Subcomplex
import Mathlib.CategoryTheory.Limits.MonoCoprod
import Mathlib.CategoryTheory.Functor.OfSequence
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian

/-! # Compatible filtered diagrams of finite compact-flat subcomplexes

Source: the finite-subcomplex paragraph of
`lem-sc-compact-flat-telescope-bar-enlargement`.
(blueprint: lem-sc-compact-flat-finite-subcomplex-diagrams).
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry

/-- Inclusion of the objects appearing by stage n into the full indexing preorder. -/
def compactFlatStageInclusion {I : Type u} [Preorder I] (stage : I → ℕ) (n : ℕ) :
    {j : I // stage j ≤ n} ⥤ I where
  obj j := j.1
  map f := homOfLE (leOfHom f)

/-- A stage-filtered small diagram of finite compact-flat complexes whose stage
colimits are the given tower. The indexing order and the complexes are actual
data, and every augmentation is a specified cocone, not an existence choice. -/
structure CompactFlatFiniteSubcomplexDiagrams (Y : Scheme.{u})
    (L : ℕ → CochainComplex (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) ℤ)
    (l : ∀ n : ℕ, L n ⟶ L (n + 1)) where
  /-- Stage-labelled finite subcomplexes. -/
  index : Type u
  /-- The order includes transition-carried inclusions. -/
  [indexPreorder : Preorder index]
  /-- The first stage at which an object appears. -/
  stage : index → ℕ
  /-- Arrows never decrease the source-stage label. -/
  stage_mono : Monotone stage
  /-- The finite complexes and their inclusion maps. -/
  diagram : index ⥤ CochainComplex
    (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) ℤ
  /-- Every initial-stage diagram is filtered and nonempty. -/
  filtered : ∀ n : ℕ, IsFiltered {j : index // stage j ≤ n}
  /-- The stage n cocone, with vertex exactly L n. -/
  augmentation : ∀ n : ℕ, compactFlatStageInclusion stage n ⋙ diagram ⟶
    (Functor.const {j : index // stage j ≤ n}).obj (L n)
  /-- These cocones exhibit the stage colimits. -/
  isColimit : ∀ n : ℕ, IsColimit { pt := L n, ι := augmentation n }
  /-- The cocones commute strictly with the tower maps. -/
  compatibility : ∀ (n : ℕ) (j : index) (hj : stage j ≤ n),
    (augmentation n).app ⟨j, hj⟩ ≫ l n =
      (augmentation (n + 1)).app ⟨j, Nat.le_trans hj (Nat.le_succ n)⟩
  /-- Each finite piece has only finitely many nonzero degrees. -/
  finiteDegrees : ∀ j : index, ∃ lo hi : ℤ, ∀ i : ℤ,
    i < lo ∨ hi < i → IsZero ((diagram.obj j).X i)
  /-- All pieces appearing by stage n have a common upper bound. -/
  stageBound : ∀ n : ℕ, ∃ hi : ℤ, ∀ j : {j : index // stage j ≤ n}, ∀ i : ℤ,
    hi < i → IsZero ((diagram.obj j.1).X i)
  /-- The finite pieces really embed into their stage colimits. -/
  mono : ∀ (n : ℕ) (j : {j : index // stage j ≤ n}) (i : ℤ),
    Mono (((augmentation n).app j).f i)
  /-- Every term is a finite coproduct of coproduct-compact flat sheaves. -/
  generators : ∀ (j : index) (i : ℤ), ∃ (I : Type u), Finite I ∧
    ∃ G : I → SheafOfModules.{u} (moduleRings Y.toRingedSpace),
      Nonempty ((diagram.obj j).X i ≅ ∐ G) ∧
      (∀ k : I, SheafOfModules.IsFlat (G k)) ∧
      ∀ (k : I) (K : Type u)
        (H : K → SheafOfModules.{u} (moduleRings Y.toRingedSpace)) (f : G k ⟶ ∐ H),
        ∃ (S : Finset K) (g : G k ⟶ ∐ (fun t : {t // t ∈ S} ↦ H t.1)),
          g ≫ Sigma.desc (fun t : {t // t ∈ S} ↦ Sigma.ι H t.1) = f

attribute [instance] CompactFlatFiniteSubcomplexDiagrams.indexPreorder

/- The auxiliary constructions are generic: flatness is only used when recording
   the generators in the final diagram. -/
-- A strictly decreasing natural-number rank makes closure under finite successor
-- supports finite, even when the original generator indexing types are infinite.
private theorem finite_closed_support {α : Type u} (next : α → Finset α)
    (height : α → ℕ) (hnext : ∀ a b, b ∈ next a → height b < height a)
    (S : Finset α) :
    ∃ T : Finset α, S ⊆ T ∧ ∀ a ∈ T, next a ⊆ T := by
  classical
  have single (n : ℕ) : ∀ a, height a = n →
      ∃ T : Finset α, a ∈ T ∧ ∀ b ∈ T, next b ⊆ T := by
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro a ha
      have each : ∀ b : {b // b ∈ next a},
          ∃ T : Finset α, b.1 ∈ T ∧ ∀ c ∈ T, next c ⊆ T := by
        intro b
        exact ih (height b.1) (ha ▸ hnext a b.1 b.2) b.1 rfl
      choose T hmem hclosed using each
      let U := (next a).attach.biUnion T
      refine ⟨insert a U, by simp, ?_⟩
      intro b hb c hc
      rcases Finset.mem_insert.mp hb with rfl | hb
      · apply Finset.mem_insert_of_mem
        exact Finset.mem_biUnion.mpr
          ⟨⟨c, hc⟩, Finset.mem_attach _ _, hmem ⟨c, hc⟩⟩
      · obtain ⟨b', hb', hb⟩ := Finset.mem_biUnion.mp hb
        apply Finset.mem_insert_of_mem
        exact Finset.mem_biUnion.mpr ⟨b', hb', hclosed b' b hb hc⟩
  have each : ∀ a : {a // a ∈ S},
      ∃ T : Finset α, a.1 ∈ T ∧ ∀ b ∈ T, next b ⊆ T :=
    fun a ↦ single (height a.1) a.1 rfl
  choose T hmem hclosed using each
  refine ⟨S.attach.biUnion T, ?_, ?_⟩
  · intro a ha
    exact Finset.mem_biUnion.mpr ⟨⟨a, ha⟩, Finset.mem_attach _ _, hmem ⟨a, ha⟩⟩
  · intro a ha b hb
    obtain ⟨a', ha', ha⟩ := Finset.mem_biUnion.mp ha
    exact Finset.mem_biUnion.mpr ⟨a', ha', hclosed a' a ha hb⟩

private instance finite_degree_support (I : ℤ → Type u) (S : Finset (Σ i, I i))
    (i : ℤ) : Finite {j : I i // (⟨i, j⟩ : Σ i, I i) ∈ S} :=
  Finite.of_injective
    (fun j ↦ (⟨⟨i, j.1⟩, j.2⟩ : {a // a ∈ S}))
    (fun _ _ h ↦ Subtype.ext (by simpa using congrArg Subtype.val h))

section FinitePieces

variable {C : Type*} [Category.{u} C] [Abelian C] [HasCoproducts.{u} C]
    {K : CochainComplex C ℤ} {I : ℤ → Type u} (G : ∀ i, I i → C)
    (e : ∀ i, K.X i ≅ ∐ G i)

private noncomputable def pieceTerm (S : Finset (Σ i, I i)) (i : ℤ) : C :=
  ∐ (fun j : {j : I i // (⟨i, j⟩ : Σ i, I i) ∈ S} ↦ G i j.1)

private noncomputable def pieceInclusion (S : Finset (Σ i, I i)) (i : ℤ) :
    pieceTerm G S i ⟶ K.X i :=
  Sigma.desc (fun j : {j : I i // (⟨i, j⟩ : Σ i, I i) ∈ S} ↦ Sigma.ι (G i) j.1) ≫
    (e i).inv

private instance pieceInclusion_mono (S : Finset (Σ i, I i)) (i : ℤ) :
    Mono (pieceInclusion G e S i) := by
  dsimp only [pieceInclusion]
  have : Mono (Sigma.desc
      (fun j : {j : I i // (⟨i, j⟩ : Σ i, I i) ∈ S} ↦ Sigma.ι (G i) j.1)) :=
    MonoCoprod.mono_of_injective' (G i) Subtype.val Subtype.val_injective
  infer_instance

private def PieceStable (S : Finset (Σ i, I i)) : Prop :=
  ∀ i : ℤ, ∃ d : pieceTerm G S i ⟶ pieceTerm G S (i + 1),
    d ≫ pieceInclusion G e S (i + 1) = pieceInclusion G e S i ≫ K.d i (i + 1)

-- The factor through a subcoproduct is unique because its inclusion is monic.
private noncomputable def pieceDifferential (S : Finset (Σ i, I i))
    (hS : PieceStable G e S) (i : ℤ) : pieceTerm G S i ⟶ pieceTerm G S (i + 1) :=
  Classical.choose (hS i)

private theorem pieceDifferential_inclusion (S : Finset (Σ i, I i))
    (hS : PieceStable G e S) (i : ℤ) :
    pieceDifferential G e S hS i ≫ pieceInclusion G e S (i + 1) =
      pieceInclusion G e S i ≫ K.d i (i + 1) :=
  Classical.choose_spec (hS i)

private noncomputable def pieceComplex (S : Finset (Σ i, I i))
    (hS : PieceStable G e S) : CochainComplex C ℤ :=
  CochainComplex.of (pieceTerm G S) (pieceDifferential G e S hS) (fun i ↦ by
    rw [← cancel_mono (pieceInclusion G e S (i + 1 + 1)), Category.assoc,
      pieceDifferential_inclusion, ← Category.assoc, pieceDifferential_inclusion,
      Category.assoc, K.d_comp_d, comp_zero, zero_comp])

private noncomputable def pieceι (S : Finset (Σ i, I i)) (hS : PieceStable G e S) :
    pieceComplex G e S hS ⟶ K :=
  CochainComplex.ofHom (pieceInclusion G e S)
    (fun i ↦ by
      simpa only [pieceComplex, CochainComplex.of_d] using
        (pieceDifferential_inclusion G e S hS i).symm)

private instance pieceι_f_mono (S : Finset (Σ i, I i)) (hS : PieceStable G e S)
    (i : ℤ) : Mono ((pieceι G e S hS).f i) := pieceInclusion_mono G e S i

private instance pieceι_mono (S : Finset (Σ i, I i)) (hS : PieceStable G e S) :
    Mono (pieceι G e S hS) := HomologicalComplex.mono_of_mono_f _ (fun _ ↦ inferInstance)

private theorem pieceTerm_zero (S : Finset (Σ i, I i)) (i : ℤ)
    (hi : ∀ j : I i, (⟨i, j⟩ : Σ i, I i) ∉ S) : IsZero (pieceTerm G S i) := by
  rw [IsZero.iff_id_eq_zero]
  apply Sigma.hom_ext
  intro j
  exact False.elim (hi j.1 j.2)

private theorem pieceFiniteDegrees (S : Finset (Σ i, I i)) (hS : PieceStable G e S) :
    ∃ lo hi : ℤ, ∀ i : ℤ, i < lo ∨ hi < i → IsZero ((pieceComplex G e S hS).X i) := by
  classical
  have bounds : ∀ S : Finset (Σ i, I i),
      ∃ lo hi : ℤ, ∀ a ∈ S, lo ≤ a.1 ∧ a.1 ≤ hi := by
    intro S
    induction S using Finset.induction_on with
    | empty => exact ⟨0, 0, by simp⟩
    | @insert a S ha ih =>
      obtain ⟨lo, hi, h⟩ := ih
      refine ⟨min lo a.1, max hi a.1, ?_⟩
      intro b hb
      rcases Finset.mem_insert.mp hb with rfl | hb
      · exact ⟨min_le_right _ _, le_max_right _ _⟩
      · exact ⟨(min_le_left _ _).trans (h b hb).1, (h b hb).2.trans (le_max_left _ _)⟩
  obtain ⟨lo, hi, h⟩ := bounds S
  refine ⟨lo, hi, fun i outside ↦ pieceTerm_zero G S i ?_⟩
  intro j hj
  have hh : lo ≤ i ∧ i ≤ hi := h ⟨i, j⟩ hj
  omega

private def HasFiniteSigmaSupport (X : C) : Prop :=
  ∀ (J : Type u) (H : J → C) (f : X ⟶ ∐ H),
    ∃ (S : Finset J) (g : X ⟶ ∐ (fun j : {j // j ∈ S} ↦ H j.1)),
      g ≫ Sigma.desc (fun j : {j // j ∈ S} ↦ Sigma.ι H j.1) = f

-- Close a finite set upwards in degree. Above the bound the differential is zero,
-- so successor supports can be empty and the rank strictly decreases.
private theorem exists_stable_piece
    (hcompact : ∀ i j, HasFiniteSigmaSupport (G i j))
    (b : ℤ) (hb : ∀ i : ℤ, b < i → IsZero (K.X i))
    (S : Finset (Σ i, I i)) :
    ∃ T : Finset (Σ i, I i), S ⊆ T ∧ PieceStable G e T := by
  classical
  have supports (a : Σ i, I i) :=
    hcompact a.1 a.2 (I (a.1 + 1)) (G (a.1 + 1))
      (Sigma.ι (G a.1) a.2 ≫ (e a.1).inv ≫ K.d a.1 (a.1 + 1) ≫ (e (a.1 + 1)).hom)
  choose support factor hfactor using supports
  let embed (i : ℤ) : I i ↪ (Σ j, I j) :=
    ⟨fun j ↦ ⟨i, j⟩, fun _ _ h ↦ by simpa using h⟩
  let next (a : Σ i, I i) : Finset (Σ i, I i) :=
    if a.1 < b then (support a).map (embed (a.1 + 1)) else ∅
  have next_degree (a c : Σ i, I i) (hc : c ∈ next a) :
      a.1 < b ∧ c.1 = a.1 + 1 := by
    dsimp only [next] at hc
    split_ifs at hc with ha
    · obtain ⟨j, hj, rfl⟩ := Finset.mem_map.mp hc
      exact ⟨ha, rfl⟩
    · simp at hc
  obtain ⟨T, hST, hT⟩ := finite_closed_support next
    (fun a ↦ (b - a.1 + 1).toNat)
    (fun a c hc ↦ by have := next_degree a c hc; omega) S
  have lift (a : Σ i, I i) (ha : a ∈ T) :
      ∃ g : G a.1 a.2 ⟶ pieceTerm G T (a.1 + 1),
        g ≫ pieceInclusion G e T (a.1 + 1) =
          Sigma.ι (G a.1) a.2 ≫ (e a.1).inv ≫ K.d a.1 (a.1 + 1) := by
    by_cases hab : a.1 < b
    · have hmem (j : {j // j ∈ support a}) :
          (⟨a.1 + 1, j.1⟩ : Σ i, I i) ∈ T := by
        apply hT a ha
        simp only [next, if_pos hab]
        exact Finset.mem_map.mpr ⟨j.1, j.2, rfl⟩
      let f : (∐ fun j : {j // j ∈ support a} ↦ G (a.1 + 1) j.1) ⟶
          pieceTerm G T (a.1 + 1) :=
        Sigma.desc (fun j ↦ Sigma.ι
          (fun k : {k : I (a.1 + 1) // (⟨a.1 + 1, k⟩ : Σ i, I i) ∈ T} ↦
            G (a.1 + 1) k.1) ⟨j.1, hmem j⟩)
      have hf : f ≫ pieceInclusion G e T (a.1 + 1) =
          Sigma.desc (fun j : {j // j ∈ support a} ↦ Sigma.ι (G (a.1 + 1)) j.1) ≫
            (e (a.1 + 1)).inv := by
        apply Sigma.hom_ext
        intro j
        simp [f, pieceInclusion]
      refine ⟨factor a ≫ f, ?_⟩
      rw [Category.assoc, hf, ← Category.assoc, hfactor]
      simp
    · refine ⟨0, ?_⟩
      rw [zero_comp]
      exact (hb (a.1 + 1) (by omega)).eq_of_tgt _ _
  choose d hd using lift
  refine ⟨T, hST, fun i ↦ ?_⟩
  refine ⟨Sigma.desc (fun j : {j : I i // (⟨i, j⟩ : Σ i, I i) ∈ T} ↦
    d ⟨i, j.1⟩ j.2), ?_⟩
  apply Sigma.hom_ext
  intro j
  simpa [pieceInclusion] using hd ⟨i, j.1⟩ j.2

-- Factor the finitely many source generators, unite their supports, and then
-- close the resulting target support. Monicity makes the factor a chain map.
private theorem factor_through_stable_piece
    (hcompact : ∀ i j, HasFiniteSigmaSupport (G i j))
    (b : ℤ) (hb : ∀ i : ℤ, b < i → IsZero (K.X i))
    {K' : CochainComplex C ℤ} {I' : ℤ → Type u} (G' : ∀ i, I' i → C)
    (e' : ∀ i, K'.X i ≅ ∐ G' i)
    (hcompact' : ∀ i j, HasFiniteSigmaSupport (G' i j))
    (S : Finset (Σ i, I' i)) (hS : PieceStable G' e' S)
    (a : pieceComplex G' e' S hS ⟶ K) :
    ∃ (T : Finset (Σ i, I i)) (hT : PieceStable G e T),
      ∃ f : pieceComplex G' e' S hS ⟶ pieceComplex G e T hT,
        f ≫ pieceι G e T hT = a := by
  classical
  have supports (j : {j // j ∈ S}) :=
    hcompact' j.1.1 j.1.2 (I j.1.1) (G j.1.1)
      (Sigma.ι (fun k : {k : I' j.1.1 // (⟨j.1.1, k⟩ : Σ i, I' i) ∈ S} ↦
        G' j.1.1 k.1) ⟨j.1.2, j.2⟩ ≫ a.f j.1.1 ≫ (e j.1.1).hom)
  choose support factor hfactor using supports
  let embed (i : ℤ) : I i ↪ (Σ j, I j) :=
    ⟨fun j ↦ ⟨i, j⟩, fun _ _ h ↦ by simpa using h⟩
  let R := S.attach.biUnion (fun j ↦ (support j).map (embed j.1.1))
  obtain ⟨T, hRT, hT⟩ := exists_stable_piece G e hcompact b hb R
  have lift (i : ℤ) (j : {j : I' i // (⟨i, j⟩ : Σ i, I' i) ∈ S}) :
      ∃ g : G' i j.1 ⟶ pieceTerm G T i,
        g ≫ pieceInclusion G e T i =
          Sigma.ι (fun k : {k : I' i // (⟨i, k⟩ : Σ i, I' i) ∈ S} ↦ G' i k.1) j ≫
            a.f i := by
    let j' : {j // j ∈ S} := ⟨⟨i, j.1⟩, j.2⟩
    have hmem (k : {k // k ∈ support j'}) : (⟨i, k.1⟩ : Σ i, I i) ∈ T := by
      apply hRT
      apply Finset.mem_biUnion.mpr
      refine ⟨j', Finset.mem_attach _ _, ?_⟩
      exact Finset.mem_map.mpr ⟨k.1, k.2, rfl⟩
    let f : (∐ fun k : {k // k ∈ support j'} ↦ G i k.1) ⟶ pieceTerm G T i :=
      Sigma.desc (fun k ↦ Sigma.ι
        (fun t : {t : I i // (⟨i, t⟩ : Σ i, I i) ∈ T} ↦ G i t.1) ⟨k.1, hmem k⟩)
    have hf : f ≫ pieceInclusion G e T i =
        Sigma.desc (fun k : {k // k ∈ support j'} ↦ Sigma.ι (G i) k.1) ≫ (e i).inv := by
      apply Sigma.hom_ext
      intro k
      simp [f, pieceInclusion]
    refine ⟨factor j' ≫ f, ?_⟩
    rw [Category.assoc, hf, ← Category.assoc, hfactor]
    simp [j']
  choose f hf using lift
  let g (i : ℤ) : (pieceComplex G' e' S hS).X i ⟶ (pieceComplex G e T hT).X i :=
    Sigma.desc (f i)
  have hg (i : ℤ) : g i ≫ (pieceι G e T hT).f i = a.f i := by
    apply Sigma.hom_ext
    intro j
    simpa [g, pieceι] using hf i j
  refine ⟨T, hT, { f := g, comm' := fun i j _ ↦ ?_ }, ?_⟩
  · rw [← cancel_mono ((pieceι G e T hT).f j), Category.assoc,
      ← (pieceι G e T hT).comm, ← Category.assoc, hg, a.comm, Category.assoc, hg]
  · ext i
    exact hg i

private theorem piece_subset_le {S T : Finset (Σ i, I i)}
    (hS : PieceStable G e S) (hT : PieceStable G e T) (h : S ⊆ T) :
    Subobject.mk (pieceι G e S hS) ≤ Subobject.mk (pieceι G e T hT) := by
  apply (HomologicalComplex.le_iff_forall_subobjectEval_le _ _).2
  intro i
  simp only [HomologicalComplex.subobjectEval_mk]
  let f : pieceTerm G S i ⟶ pieceTerm G T i :=
    Sigma.desc (fun j : {j : I i // (⟨i, j⟩ : Σ i, I i) ∈ S} ↦ Sigma.ι
      (fun k : {k : I i // (⟨i, k⟩ : Σ i, I i) ∈ T} ↦ G i k.1) ⟨j.1, h j.2⟩)
  apply Subobject.mk_le_mk_of_comm f
  apply Sigma.hom_ext
  intro j
  simp [f, pieceι, pieceInclusion]

end FinitePieces

section TowerPieces

variable {C : Type*} [Category.{u} C] [Abelian C] [HasCoproducts.{u} C]
    (L : ℕ → CochainComplex C ℤ) (l : ∀ n, L n ⟶ L (n + 1))
    (I : ℕ → ℤ → Type u) (G : ∀ n i, I n i → C)
    (e : ∀ n i, (L n).X i ≅ ∐ G n i)

private structure TowerPiece : Type u where
  stage : ℕ
  support : Finset (Σ i, I stage i)
  stable : PieceStable (G stage) (e stage) support

private noncomputable def towerPieceObj (j : TowerPiece L I G e) : CochainComplex C ℤ :=
  pieceComplex (G j.stage) (e j.stage) j.support j.stable

private noncomputable def towerPieceι (j : TowerPiece L I G e) :
    towerPieceObj L I G e j ⟶ L j.stage :=
  pieceι (G j.stage) (e j.stage) j.support j.stable

private instance towerPieceι_mono (j : TowerPiece L I G e) :
    Mono (towerPieceι L I G e j) := pieceι_mono _ _ _ _

private instance towerPieceι_f_mono (j : TowerPiece L I G e) (i : ℤ) :
    Mono ((towerPieceι L I G e j).f i) := pieceι_f_mono _ _ _ _ _

private def towerMap {n m : ℕ} (h : n ≤ m) : L n ⟶ L m :=
  (Functor.ofSequence l).map (homOfLE h)

omit [HasCoproducts.{u} C] in
private theorem towerMap_refl (n : ℕ) : towerMap L l (le_refl n) = 𝟙 (L n) :=
  (Functor.ofSequence l).map_id n

omit [HasCoproducts.{u} C] in
private theorem towerMap_comp {n m k : ℕ} (h : n ≤ m) (h' : m ≤ k) :
    towerMap L l h ≫ towerMap L l h' = towerMap L l (h.trans h') :=
  ((Functor.ofSequence l).map_comp (homOfLE h) (homOfLE h')).symm

private def TowerPieceLE (j k : TowerPiece L I G e) : Prop :=
  ∃ h : j.stage ≤ k.stage,
    ∃ f : towerPieceObj L I G e j ⟶ towerPieceObj L I G e k,
      f ≫ towerPieceι L I G e k = towerPieceι L I G e j ≫ towerMap L l h

-- The order depends on the transitions, so it is installed locally in the final
-- construction rather than registered as an instance with an undetermined tower.
private abbrev towerPiecePreorder : Preorder (TowerPiece L I G e) where
  le := TowerPieceLE L l I G e
  le_refl j := ⟨le_refl _, 𝟙 _, by rw [Category.id_comp, towerMap_refl, Category.comp_id]⟩
  le_trans j k r := by
    rintro ⟨h, f, hf⟩ ⟨h', f', hf'⟩
    refine ⟨h.trans h', f ≫ f', ?_⟩
    rw [Category.assoc, hf', ← Category.assoc, hf, Category.assoc, towerMap_comp]

private theorem towerPieceLE_stage {j k : TowerPiece L I G e}
    (h : TowerPieceLE L l I G e j k) : j.stage ≤ k.stage := Classical.choose h

private noncomputable def towerPieceLift {j k : TowerPiece L I G e}
    (h : TowerPieceLE L l I G e j k) :
    towerPieceObj L I G e j ⟶ towerPieceObj L I G e k :=
  Classical.choose (Classical.choose_spec h)

private theorem towerPieceLift_ι {j k : TowerPiece L I G e}
    (h : TowerPieceLE L l I G e j k) :
    towerPieceLift L l I G e h ≫ towerPieceι L I G e k =
      towerPieceι L I G e j ≫ towerMap L l (towerPieceLE_stage L l I G e h) :=
  Classical.choose_spec (Classical.choose_spec h)

private noncomputable def towerPieceDiagram :
    let _ := towerPiecePreorder L l I G e
    TowerPiece L I G e ⥤ CochainComplex C ℤ := by
  let _ := towerPiecePreorder L l I G e
  refine { obj := towerPieceObj L I G e
           map := fun f ↦ towerPieceLift L l I G e (leOfHom f)
           map_id := ?_
           map_comp := ?_ }
  · intro j
    apply (cancel_mono (towerPieceι L I G e j)).mp
    rw [towerPieceLift_ι, towerMap_refl, Category.comp_id, Category.id_comp]
  · intro j k r f g
    apply (cancel_mono (towerPieceι L I G e r)).mp
    rw [towerPieceLift_ι, Category.assoc, towerPieceLift_ι, ← Category.assoc,
      towerPieceLift_ι, Category.assoc, towerMap_comp]

private noncomputable def towerPieceAugmentation (n : ℕ) :
    let _ := towerPiecePreorder L l I G e
    compactFlatStageInclusion (fun j : TowerPiece L I G e ↦ j.stage) n ⋙
      towerPieceDiagram L l I G e ⟶
        (Functor.const {j : TowerPiece L I G e // j.stage ≤ n}).obj (L n) := by
  let _ := towerPiecePreorder L l I G e
  refine { app := fun j ↦ towerPieceι L I G e j.1 ≫ towerMap L l j.2
           naturality := ?_ }
  intro j k f
  change towerPieceLift L l I G e (leOfHom f) ≫
    (towerPieceι L I G e k.1 ≫ towerMap L l k.2) =
      (towerPieceι L I G e j.1 ≫ towerMap L l j.2) ≫ 𝟙 _
  rw [Category.comp_id, ← Category.assoc, towerPieceLift_ι, Category.assoc, towerMap_comp]

omit [HasCoproducts.{u} C] in
private theorem towerMap_mono_f
    (hl : ∀ n i, Mono ((l n).f i)) {n m : ℕ} (h : n ≤ m) (i : ℤ) :
    Mono ((towerMap L l h).f i) := by
  induction m with
  | zero =>
    obtain rfl : n = 0 := by omega
    simpa only [towerMap_refl, HomologicalComplex.id_f] using (inferInstance : Mono (𝟙 _))
  | succ m ih =>
    by_cases hn : n = m + 1
    · subst n
      simpa only [towerMap_refl, HomologicalComplex.id_f] using (inferInstance : Mono (𝟙 _))
    · have hnm : n ≤ m := by omega
      have := ih hnm
      have := hl m i
      have hs : towerMap L l (Nat.le_succ m) = l m :=
        Functor.ofSequence_map_homOfLE_succ l m
      rw [← towerMap_comp L l hnm (Nat.le_succ m), hs, HomologicalComplex.comp_f]
      infer_instance

private theorem towerPiece_upper
    (hb : ∀ n, ∃ b : ℤ, ∀ i : ℤ, b < i → IsZero ((L n).X i))
    (hcompact : ∀ n i j, HasFiniteSigmaSupport (G n i j))
    (n : ℕ) (j k : TowerPiece L I G e) (hj : j.stage ≤ n) (hk : k.stage ≤ n) :
    ∃ r : TowerPiece L I G e, r.stage = n ∧
      TowerPieceLE L l I G e j r ∧ TowerPieceLE L l I G e k r := by
  classical
  obtain ⟨b, hb⟩ := hb n
  obtain ⟨S, hS, f, hf⟩ := factor_through_stable_piece (G n) (e n)
    (hcompact n) b hb (G j.stage) (e j.stage) (hcompact j.stage) j.support j.stable
      (towerPieceι L I G e j ≫ towerMap L l hj)
  obtain ⟨T, hT, g, hg⟩ := factor_through_stable_piece (G n) (e n)
    (hcompact n) b hb (G k.stage) (e k.stage) (hcompact k.stage) k.support k.stable
      (towerPieceι L I G e k ≫ towerMap L l hk)
  obtain ⟨U, hU, hu⟩ := exists_stable_piece (G n) (e n) (hcompact n) b hb (S ∪ T)
  have hSU : S ⊆ U := (Finset.subset_union_left).trans hU
  have hTU : T ⊆ U := (Finset.subset_union_right).trans hU
  have h₁ := piece_subset_le (G n) (e n) hS hu hSU
  have h₂ := piece_subset_le (G n) (e n) hT hu hTU
  let f' := Subobject.ofMkLEMk (pieceι (G n) (e n) S hS) (pieceι (G n) (e n) U hu) h₁
  let g' := Subobject.ofMkLEMk (pieceι (G n) (e n) T hT) (pieceι (G n) (e n) U hu) h₂
  refine ⟨⟨n, U, hu⟩, rfl, ⟨hj, f ≫ f', ?_⟩, ⟨hk, g ≫ g', ?_⟩⟩
  · change (f ≫ f') ≫ pieceι (G n) (e n) U hu = _
    rw [Category.assoc, Subobject.ofMkLEMk_comp, hf]
  · change (g ≫ g') ≫ pieceι (G n) (e n) U hu = _
    rw [Category.assoc, Subobject.ofMkLEMk_comp, hg]

private theorem towerPiece_filtered
    (hb : ∀ n, ∃ b : ℤ, ∀ i : ℤ, b < i → IsZero ((L n).X i))
    (hcompact : ∀ n i j, HasFiniteSigmaSupport (G n i j)) (n : ℕ) :
    let _ := towerPiecePreorder L l I G e
    IsFiltered {j : TowerPiece L I G e // j.stage ≤ n} := by
  let _ := towerPiecePreorder L l I G e
  obtain ⟨b, hbn⟩ := hb n
  obtain ⟨S, _, hS⟩ := exists_stable_piece (G n) (e n) (hcompact n) b hbn ∅
  have : Nonempty {j : TowerPiece L I G e // j.stage ≤ n} :=
    ⟨⟨⟨n, S, hS⟩, le_refl n⟩⟩
  have : IsDirectedOrder {j : TowerPiece L I G e // j.stage ≤ n} := ⟨by
    intro j k
    obtain ⟨r, hr, hj, hk⟩ := towerPiece_upper L l I G e hb hcompact n j.1 k.1 j.2 k.2
    exact ⟨⟨r, hr ▸ le_refl n⟩, hj, hk⟩⟩
  infer_instance

private theorem towerPieceAugmentation_mono_f
    (hl : ∀ n i, Mono ((l n).f i)) (n : ℕ)
    (j : {j : TowerPiece L I G e // j.stage ≤ n}) (i : ℤ) :
    let _ := towerPiecePreorder L l I G e
    Mono (((towerPieceAugmentation L l I G e n).app j).f i) := by
  let _ := towerPiecePreorder L l I G e
  have := towerMap_mono_f L l hl j.2 i
  change Mono (((towerPieceι L I G e j.1).f i) ≫ (towerMap L l j.2).f i)
  infer_instance

-- Every generator occurs in one finite piece at its own stage. Consequently
-- the degreewise union of all augmentation images is the whole ambient term.
private theorem towerPieceAugmentation_iSup [IsGrothendieckAbelian.{u} C]
    (hb : ∀ n, ∃ b : ℤ, ∀ i : ℤ, b < i → IsZero ((L n).X i))
    (hcompact : ∀ n i j, HasFiniteSigmaSupport (G n i j))
    (hl : ∀ n i, Mono ((l n).f i)) (n : ℕ) (i : ℤ) :
    let _ := towerPiecePreorder L l I G e
    let _ (j : {j : TowerPiece L I G e // j.stage ≤ n}) :=
      towerPieceAugmentation_mono_f L l I G e hl n j i
    (⨆ j : {j : TowerPiece L I G e // j.stage ≤ n},
      (Subobject.mk (((towerPieceAugmentation L l I G e n).app j).f i) :
        Subobject ((L n).X i))) = ⊤ := by
  classical
  let _ := towerPiecePreorder L l I G e
  let _ (j : {j : TowerPiece L I G e // j.stage ≤ n}) :=
    towerPieceAugmentation_mono_f L l I G e hl n j i
  let U : Subobject ((L n).X i) :=
    ⨆ j : {j : TowerPiece L I G e // j.stage ≤ n},
      Subobject.mk (((towerPieceAugmentation L l I G e n).app j).f i)
  have hgen (a : I n i) : U.Factors (Sigma.ι (G n i) a ≫ (e n i).inv) := by
    obtain ⟨b, hbn⟩ := hb n
    obtain ⟨S, hS, hs⟩ := exists_stable_piece (G n) (e n) (hcompact n) b hbn {⟨i, a⟩}
    have ha : (⟨i, a⟩ : Σ i, I n i) ∈ S := hS (by simp)
    let j : {j : TowerPiece L I G e // j.stage ≤ n} := ⟨⟨n, S, hs⟩, le_refl n⟩
    have hfac : (Subobject.mk (((towerPieceAugmentation L l I G e n).app j).f i)).Factors
        (Sigma.ι (G n i) a ≫ (e n i).inv) := by
      apply (Subobject.mk_factors_iff _ _).2
      refine ⟨Sigma.ι (fun k : {k : I n i // (⟨i, k⟩ : Σ i, I n i) ∈ S} ↦
        G n i k.1) ⟨a, ha⟩, ?_⟩
      simp [towerPieceAugmentation, towerPieceι, pieceι, pieceInclusion, j,
        towerMap_refl]
    exact Subobject.factors_of_le _ (le_iSup _ j) hfac
  have htotal : U.Factors (e n i).inv := by
    apply (Subobject.factors_iff _ _).2
    refine ⟨Sigma.desc (fun a ↦ U.factorThru _ (hgen a)), ?_⟩
    apply Sigma.hom_ext
    intro a
    simp
  have ht : Subobject.mk (e n i).inv ≤ U := (Subobject.mk_le_iff_factors _ _).2 htotal
  exact le_antisymm le_top (by simpa only [Subobject.mk_eq_top_of_isIso] using ht)

-- A filtered union of subobjects is its supremum in a Grothendieck abelian
-- category; apply this to the complex, using degreewise detection of subobjects.
set_option backward.isDefEq.respectTransparency false in
private noncomputable def towerPieceAugmentation_isColimit [IsGrothendieckAbelian.{u} C]
    (hb : ∀ n, ∃ b : ℤ, ∀ i : ℤ, b < i → IsZero ((L n).X i))
    (hcompact : ∀ n i j, HasFiniteSigmaSupport (G n i j))
    (hl : ∀ n i, Mono ((l n).f i)) (n : ℕ) :
    let _ := towerPiecePreorder L l I G e
    IsColimit { pt := L n, ι := towerPieceAugmentation L l I G e n } := by
  let _ := towerPiecePreorder L l I G e
  have : IsFiltered {j : TowerPiece L I G e // j.stage ≤ n} :=
    towerPiece_filtered L l I G e hb hcompact n
  let D := compactFlatStageInclusion (fun j : TowerPiece L I G e ↦ j.stage) n ⋙
    towerPieceDiagram L l I G e
  let c : Cocone D := ⟨L n, towerPieceAugmentation L l I G e n⟩
  have hm (j : {j : TowerPiece L I G e // j.stage ≤ n}) : Mono (c.ι.app j) :=
    HomologicalComplex.mono_of_mono_f _
      (fun i ↦ towerPieceAugmentation_mono_f L l I G e hl n j i)
  let M : {j : TowerPiece L I G e // j.stage ≤ n} ⥤ MonoOver (L n) :=
    { obj := fun j ↦ MonoOver.mk (c.ι.app j)
      map := fun f ↦ MonoOver.homMk (D.map f) (c.w f) }
  let rc : Cocone (M ⋙ MonoOver.forget _) :=
    { pt := Over.mk (𝟙 (L n))
      ι :=
        { app := fun j ↦ Over.homMk (c.ι.app j) (by
            change c.ι.app j ≫ 𝟙 _ = c.ι.app j
            exact Category.comp_id _)
          naturality := fun j k f ↦ by
            apply Over.OverMorphism.ext
            change D.map f ≫ c.ι.app k = c.ι.app j ≫ 𝟙 (L n)
            exact (c.w f).trans (Category.comp_id (c.ι.app j)).symm } }
  have hcover : (⨆ j, Subobject.mk (c.ι.app j)) = ⊤ := by
    apply HomologicalComplex.subobjectEval_injective
    funext i
    dsimp only
    have htop : HomologicalComplex.subobjectEval (L n) i ⊤ = ⊤ := by
      simpa only [Subobject.mk_eq_top_of_isIso, HomologicalComplex.id_f] using
        HomologicalComplex.subobjectEval_mk (L n) i (𝟙 (L n))
    rw [HomologicalComplex.subobjectEval_iSup, htop]
    simp only [HomologicalComplex.subobjectEval_mk]
    exact towerPieceAugmentation_iSup L l I G e hb hcompact hl n i
  have : Mono rc.pt.hom := inferInstanceAs (Mono (𝟙 (L n)))
  have hrc : Subobject.mk rc.pt.hom = ⨆ j, Subobject.mk (M.obj j).obj.hom := by
    change Subobject.mk (𝟙 (L n)) = ⨆ j, Subobject.mk (c.ι.app j)
    rw [Subobject.mk_eq_top_of_isIso]
    exact hcover.symm
  exact IsGrothendieckAbelian.isColimitMapCoconeOfSubobjectMkEqISup M rc hrc

end TowerPieces

/-- Construct the finite-subcomplex diagrams before any target or bar construction
is introduced.

Source: `lem-sc-compact-flat-telescope-bar-enlargement`, the paragraph beginning
"Fix generator decompositions in each term" and ending with the colimit L_n.

Proof. Fix the summand decompositions in every term of L_m. For each generator
summand, choose a finite support for its differential in the next degree. A finite
set of summands in finitely many degrees can be enlarged to a finite subcomplex:
add those chosen supports, and repeat upwards. Boundedness above makes the
iteration terminate. The initial finite set bounds its nonzero degrees below.
Each term of this subcomplex is a finite coproduct of the original compact flat
summands; its differential is the restriction determined by these inclusions.

Index by labelled pairs (m, a finite summand subcomplex of L_m). Order two pairs
with labels m ≤ m' when the iterated transition carries the earlier subcomplex
into the later one. Inclusion maps into L_m' are monic, so this factorization is
unique, respects composition, and defines the diagram functor. The stage label
is monotone. At stage n keep all labels at most n. A finite collection can be
carried to stage n and included in one finite subcomplex: compactness factors
its finitely many generators through finite subcoproducts of L_n in each of its
finitely many degrees; close these supports under the differential. Thus the
stage-n subdiagram is cofinal and the stage diagram is filtered. The zero
subcomplex at stage zero supplies nonemptiness, including the zero tower.

The stage-n subcomplexes have union L_n, because every summand lies in one of
them. A compatible family of maps out of these subcomplexes defines the unique
map out of L_n termwise, using the original coproduct summands. It commutes with
the differentials since every finite collection is contained in a subcomplex.
This proves the stated cochain-complex colimit universal property. Carry the
cocones to later stages by the tower transitions to obtain strict compatibility.
Their components are monic: the finite summand inclusions are split monic and
the tower transitions are degreewise split monic. For stageBound, take the maximum
of the upper bounds of L_0 through L_n. The finite-degree and finite-generator
fields hold by construction, with the inherited compactness factorizations.
All these are existential witnesses; no definition selects an arbitrary object
from an unproved existence theorem.
(blueprint: lem-sc-compact-flat-finite-subcomplex-diagrams). -/
theorem exists_compact_flat_finite_subcomplex_diagrams (Y : Scheme.{u})
    (L : ℕ → CochainComplex (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) ℤ)
    (l : ∀ n : ℕ, L n ⟶ L (n + 1))
    (hb : ∀ n : ℕ, ∃ z : ℤ, ∀ i : ℤ, z < i → IsZero ((L n).X i))
    (hsplit : ∀ (n : ℕ) (i : ℤ), IsSplitMono ((l n).f i))
    (hgen :
      ∀ (n : ℕ) (i : ℤ), ∃ (I : Type u)
        (G : I → SheafOfModules.{u} (moduleRings Y.toRingedSpace)),
        Nonempty ((L n).X i ≅ ∐ G) ∧
        (∀ j : I, SheafOfModules.IsFlat (G j)) ∧
        ∀ (j : I) (K : Type u)
          (H : K → SheafOfModules.{u} (moduleRings Y.toRingedSpace))
          (f : G j ⟶ ∐ H),
          ∃ (S : Finset K) (g : G j ⟶ ∐ (fun k : {k // k ∈ S} ↦ H k.1)),
            g ≫ Sigma.desc (fun k : {k // k ∈ S} ↦ Sigma.ι H k.1) = f)
 :
    Nonempty (CompactFlatFiniteSubcomplexDiagrams Y L l) := by
  classical
  let C := SheafOfModules.{u} (moduleRings Y.toRingedSpace)
  have : IsGrothendieckAbelian.{u} C := SheafOfModules.isGrothendieckAbelian _
  choose I G he hflat hcompact using hgen
  let e (n : ℕ) (i : ℤ) : (L n).X i ≅ ∐ G n i := Classical.choice (he n i)
  have hc : ∀ n i j, HasFiniteSigmaSupport (G n i j) := hcompact
  have hl (n : ℕ) (i : ℤ) : Mono ((l n).f i) := by
    have := hsplit n i
    infer_instance
  let _ := towerPiecePreorder L l I G e
  refine ⟨{
    index := TowerPiece L I G e
    stage := fun j ↦ j.stage
    stage_mono := fun _ _ h ↦ towerPieceLE_stage L l I G e h
    diagram := towerPieceDiagram L l I G e
    filtered := towerPiece_filtered L l I G e hb hc
    augmentation := towerPieceAugmentation L l I G e
    isColimit := towerPieceAugmentation_isColimit L l I G e hb hc hl
    compatibility := ?_
    finiteDegrees := ?_
    stageBound := ?_
    mono := towerPieceAugmentation_mono_f L l I G e hl
    generators := ?_
  }⟩
  · intro n j hj
    change (towerPieceι L I G e j ≫ towerMap L l hj) ≫ l n =
      towerPieceι L I G e j ≫ towerMap L l (hj.trans (Nat.le_succ n))
    have hs : towerMap L l (Nat.le_succ n) = l n :=
      Functor.ofSequence_map_homOfLE_succ l n
    rw [Category.assoc, ← hs, towerMap_comp]
  · intro j
    exact pieceFiniteDegrees (G j.stage) (e j.stage) j.support j.stable
  · intro n
    obtain ⟨b, hb⟩ := hb n
    refine ⟨b, fun j i hi ↦ ?_⟩
    have := towerPieceAugmentation_mono_f L l I G e hl n j i
    exact (hb i hi).of_mono (((towerPieceAugmentation L l I G e n).app j).f i)
  · intro j i
    refine ⟨{k : I j.stage i // (⟨i, k⟩ : Σ i, I j.stage i) ∈ j.support},
      inferInstance, (fun k ↦ G j.stage i k.1), ⟨Iso.refl _⟩,
      (fun k ↦ hflat j.stage i k.1), (fun k ↦ hcompact j.stage i k.1)⟩

end AlgebraicGeometry

