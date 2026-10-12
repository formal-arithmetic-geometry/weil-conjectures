/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Adjunction.Additive
public import Mathlib.CategoryTheory.Adjunction.PartialAdjoint
public import Mathlib.CategoryTheory.Functor.OfSequence
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
public import Mathlib.CategoryTheory.Triangulated.Functor

/-!
# Brown representability for a compactly generated triangulated category

Let `C` be a pretriangulated category with coproducts, and let `G : ι → C` be a family of
objects which is *compact* (every morphism from `G i` to a countable coproduct factors through
a finite partial sum) and *generating* (an object receiving only zero morphisms from all `G i`
is zero). Let `Φ : C ⥤ D` be a triangulated functor preserving coproducts. Then for every
`K : D` the functor `Y ↦ (Φ Y ⟶ K)` is representable, so that `Φ` is a left adjoint
(`CategoryTheory.Pretriangulated.isLeftAdjoint_of_compactGenerators`).

The proof is Neeman's: one builds a tower `X₀ ⟶ X₁ ⟶ ⋯` by successively attaching coproducts of
the `G i` so as to kill the kernels of the universal elements, and takes the homotopy colimit
of the tower, given by the triangle `∐ Xₖ ──1 - σ──▶ ∐ Xₖ ⟶ X ⟶ (∐ Xₖ)[1]`. The resulting
transformation `(- ⟶ X) ⟶ (Φ - ⟶ K)` is bijective on the `G i`, and the objects on which it is
bijective (together with all their shifts) are stable under coproducts and cones. Applying the
same tower construction to the functor `(- ⟶ Y)` shows that every object `Y` is built from the
`G i` by coproducts and cones, so the transformation is bijective everywhere.

## References

* [Stacks Project, Tag 0A8F](https://stacks.math.columbia.edu/tag/0A8F)
* [A. Neeman, *The Grothendieck duality theorem via Bousfield's techniques and Brown
  representability*]
-/

@[expose] public section

universe w u u'

namespace CategoryTheory.Pretriangulated

open Limits Category Preadditive

namespace Brown

variable {C : Type u} [Category.{w} C] [Preadditive C]

section Tower

variable (F : ℕ ⥤ C) {P : C} {ι : ∀ k, F.obj k ⟶ P} (hc : IsColimit (Cofan.mk P ι))

/-- The shift endomorphism `σ : ∐ Fₖ ⟶ ∐ Fₖ` of the coproduct of the terms of a sequence
`F : ℕ ⥤ C`, with components `Fₖ ⟶ Fₖ₊₁ ⟶ ∐ Fₖ`. -/
noncomputable def seqShift : P ⟶ P :=
  Cofan.IsColimit.desc hc fun k ↦ F.map (homOfLE k.le_succ) ≫ ι (k + 1)

@[reassoc (attr := simp)]
lemma ι_seqShift (k : ℕ) : ι k ≫ seqShift F hc = F.map (homOfLE k.le_succ) ≫ ι (k + 1) :=
  Cofan.IsColimit.fac hc _ k

/-- The iterates of `seqShift`. -/
noncomputable def seqShiftPow : ℕ → (P ⟶ P)
  | 0 => 𝟙 P
  | m + 1 => seqShiftPow m ≫ seqShift F hc

lemma ι_seqShiftPow (k m : ℕ) :
    ι k ≫ seqShiftPow F hc m = F.map (homOfLE (Nat.le_add_right k m)) ≫ ι (k + m) := by
  induction m with
  | zero =>
    have : F.map (homOfLE (Nat.le_add_right k 0)) = 𝟙 _ := by
      rw [← F.map_id]; rfl
    rw [this, id_comp]; exact comp_id _
  | succ m ih =>
    rw [seqShiftPow, ← assoc, ih, assoc]
    erw [ι_seqShift F hc (k + m)]
    rw [← assoc, ← F.map_comp]
    rfl

/-- The projection of `∐ Fₖ` onto the partial sum of the first `N` terms. -/
noncomputable def seqTrunc (N : ℕ) : P ⟶ P :=
  Cofan.IsColimit.desc hc fun k ↦ if k < N then ι k else 0

lemma ι_seqTrunc (N k : ℕ) : ι k ≫ seqTrunc F hc N = if k < N then ι k else 0 :=
  Cofan.IsColimit.fac hc _ k

lemma seqShiftPow_seqTrunc (N : ℕ) : seqShiftPow F hc N ≫ seqTrunc F hc N = 0 :=
  Cofan.IsColimit.hom_ext hc _ _ fun k ↦ by
    change ι k ≫ _ = ι k ≫ _
    rw [reassoc_of% (ι_seqShiftPow F hc k N), ι_seqTrunc, if_neg (by omega)]
    simp

lemma sum_comp_seqTrunc {Y : C} (N : ℕ) (g : ∀ k, Y ⟶ F.obj k) :
    (∑ k ∈ Finset.range N, g k ≫ ι k) ≫ seqTrunc F hc N = ∑ k ∈ Finset.range N, g k ≫ ι k := by
  rw [Preadditive.sum_comp]
  refine Finset.sum_congr rfl fun k hk ↦ ?_
  rw [assoc, ι_seqTrunc, if_pos (Finset.mem_range.1 hk)]

lemma comp_seqShiftPow_of_comp_eq {Y : C} (g : Y ⟶ P) (hg : g ≫ seqShift F hc = g) (m : ℕ) :
    g ≫ seqShiftPow F hc m = g := by
  induction m with
  | zero => exact comp_id _
  | succ m ih => rw [seqShiftPow, ← assoc, ih, hg]

/-- `1 - σ` is injective on morphisms factoring through a finite partial sum. -/
lemma eq_zero_of_comp_one_sub_seqShift {Y : C} (N : ℕ) (g : ∀ k, Y ⟶ F.obj k)
    (h : (∑ k ∈ Finset.range N, g k ≫ ι k) ≫ (𝟙 P - seqShift F hc) = 0) :
    ∑ k ∈ Finset.range N, g k ≫ ι k = 0 := by
  have hf : (∑ k ∈ Finset.range N, g k ≫ ι k) ≫ seqShift F hc =
      ∑ k ∈ Finset.range N, g k ≫ ι k := by
    rw [comp_sub, comp_id, sub_eq_zero] at h
    exact h.symm
  calc ∑ k ∈ Finset.range N, g k ≫ ι k
      = (∑ k ∈ Finset.range N, g k ≫ ι k) ≫ seqTrunc F hc N := (sum_comp_seqTrunc F hc N g).symm
    _ = ((∑ k ∈ Finset.range N, g k ≫ ι k) ≫ seqShiftPow F hc N) ≫ seqTrunc F hc N := by
        rw [comp_seqShiftPow_of_comp_eq F hc _ hf N]
    _ = 0 := by rw [assoc, seqShiftPow_seqTrunc, comp_zero]

/-- If `π : ∐ Fₖ ⟶ L` is killed by `1 - σ`, then `ιₖ ≫ π` factors through every later term. -/
lemma ι_comp_eq_of_one_sub_seqShift_comp {L : C} (π : P ⟶ L)
    (hπ : (𝟙 P - seqShift F hc) ≫ π = 0) {k N : ℕ} (hkN : k ≤ N) :
    ι k ≫ π = F.map (homOfLE hkN) ≫ ι N ≫ π := by
  have h₁ : seqShift F hc ≫ π = π := by
    rw [sub_comp, id_comp, sub_eq_zero] at hπ
    exact hπ.symm
  have h₂ (m : ℕ) : seqShiftPow F hc m ≫ π = π := by
    induction m with
    | zero => exact id_comp _
    | succ m ih => rw [seqShiftPow, assoc, h₁, ih]
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hkN
  calc ι k ≫ π = ι k ≫ seqShiftPow F hc m ≫ π := by rw [h₂]
    _ = _ := by rw [reassoc_of% (ι_seqShiftPow F hc k m)]

end Tower

section Preserves

variable {D : Type*} [Category.{w} D] [Preadditive D] (Φ : C ⥤ D)

/-- A morphism out of `Φ (∐ f)` is determined by its restrictions along the `Φ (ι j)`, when
`Φ` preserves the coproduct. -/
lemma hom_ext_of_preserves {J : Type*} {f : J → C} {P : C} {ιf : ∀ j, f j ⟶ P}
    (hc : IsColimit (Cofan.mk P ιf)) [PreservesColimit (Discrete.functor f) Φ] {T : D}
    {x y : Φ.obj P ⟶ T} (h : ∀ j, Φ.map (ιf j) ≫ x = Φ.map (ιf j) ≫ y) : x = y :=
  Cofan.IsColimit.hom_ext (isColimitCofanMkObjOfIsColimit Φ _ _ hc) _ _ h

/-- The morphism out of `Φ (∐ f)` with prescribed restrictions along the `Φ (ι j)`, when
`Φ` preserves the coproduct. -/
noncomputable def descOfPreserves {J : Type*} {f : J → C} {P : C} {ιf : ∀ j, f j ⟶ P}
    (hc : IsColimit (Cofan.mk P ιf)) [PreservesColimit (Discrete.functor f) Φ] {T : D}
    (x : ∀ j, Φ.obj (f j) ⟶ T) : Φ.obj P ⟶ T :=
  Cofan.IsColimit.desc (isColimitCofanMkObjOfIsColimit Φ _ _ hc) x

@[reassoc (attr := simp)]
lemma map_ι_descOfPreserves {J : Type*} {f : J → C} {P : C} {ιf : ∀ j, f j ⟶ P}
    (hc : IsColimit (Cofan.mk P ιf)) [PreservesColimit (Discrete.functor f) Φ] {T : D}
    (x : ∀ j, Φ.obj (f j) ⟶ T) (j : J) : Φ.map (ιf j) ≫ descOfPreserves Φ hc x = x j :=
  Cofan.IsColimit.fac (isColimitCofanMkObjOfIsColimit Φ _ _ hc) _ j

end Preserves

section Construction

variable [HasZeroObject C] [HasShift C ℤ] [∀ n : ℤ, (shiftFunctor C n).Additive]
  [Pretriangulated C]
  {D : Type*} [Category.{w} D] [Preadditive D] [HasZeroObject D] [HasShift D ℤ]
  [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]
  (Φ : C ⥤ D) [Φ.CommShift ℤ] [Φ.IsTriangulated]
  [HasCoproducts.{w} C] [∀ J : Type w, PreservesColimitsOfShape (Discrete J) Φ]
  [HasCoproductsOfShape ℕ C] [PreservesColimitsOfShape (Discrete ℕ) Φ]
  {ι : Type w} (G : ι → C) (K : D)

/-- A stage of the cellular tower: an object `X` together with an element `u ∈ H(X)`,
where `H = (Φ - ⟶ K)`. -/
structure Stage where
  /-- the object -/
  X : C
  /-- the element of `H(X)` -/
  u : Φ.obj X ⟶ K

variable {Φ K}

/-- The morphisms from the generators to `s.X` that are killed by `s.u`. -/
abbrev KillIdx (s : Stage Φ K) : Type w := Σ i, {g : G i ⟶ s.X // Φ.map g ≫ s.u = 0}

/-- The morphism `∐ G i ⟶ s.X` from the coproduct of the generators indexed by `KillIdx`. -/
noncomputable def killMap (s : Stage Φ K) : (∐ fun j : KillIdx G s ↦ G j.1) ⟶ s.X :=
  Sigma.desc fun j ↦ j.2.1

lemma map_killMap_u (s : Stage Φ K) : Φ.map (killMap G s) ≫ s.u = 0 :=
  hom_ext_of_preserves Φ (coproductIsCoproduct _) fun j ↦ by
    rw [comp_zero, ← Functor.map_comp_assoc]
    simp only [cofan_mk_inj, killMap, Sigma.ι_desc]
    exact j.2.2

lemma exists_next (s : Stage Φ K) :
    ∃ (Z : C) (g : s.X ⟶ Z) (h : Z ⟶ (∐ fun j : KillIdx G s ↦ G j.1)⟦(1 : ℤ)⟧)
      (u' : Φ.obj Z ⟶ K), Triangle.mk (killMap G s) g h ∈ distTriang C ∧ Φ.map g ≫ u' = s.u := by
  obtain ⟨Z, g, h, mem⟩ := distinguished_cocone_triangle (killMap G s)
  obtain ⟨u', hu'⟩ := Triangle.yoneda_exact₂ _ (Φ.map_distinguished _ mem) s.u
    (map_killMap_u G s)
  exact ⟨Z, g, h, u', mem, hu'.symm⟩

/-- The next stage of the tower. -/
noncomputable def Stage.next (s : Stage Φ K) : Stage Φ K :=
  ⟨(exists_next G s).choose, (exists_next G s).choose_spec.choose_spec.choose_spec.choose⟩

/-- The transition morphism to the next stage. -/
noncomputable def Stage.nextMap (s : Stage Φ K) : s.X ⟶ (s.next G).X :=
  (exists_next G s).choose_spec.choose

lemma Stage.exists_mem_distTriang (s : Stage Φ K) :
    ∃ h, Triangle.mk (killMap G s) (s.nextMap G) h ∈ distTriang C :=
  ⟨_, (exists_next G s).choose_spec.choose_spec.choose_spec.choose_spec.1⟩

@[reassoc (attr := simp)]
lemma Stage.map_nextMap_u (s : Stage Φ K) : Φ.map (s.nextMap G) ≫ (s.next G).u = s.u :=
  (exists_next G s).choose_spec.choose_spec.choose_spec.choose_spec.2

@[reassoc (attr := simp)]
lemma Stage.killMap_nextMap (s : Stage Φ K) : killMap G s ≫ s.nextMap G = 0 := by
  obtain ⟨h, mem⟩ := s.exists_mem_distTriang G
  exact comp_distTriang_mor_zero₁₂ _ mem

variable (Φ K)

/-- The index type of the first stage: all pairs of a generator and an element of `H`. -/
abbrev StartIdx : Type w := Σ i, (Φ.obj (G i) ⟶ K)

/-- The first stage: `∐_{(i, x)} G i`, with the universal element `(x)`. -/
noncomputable def startStage : Stage Φ K :=
  ⟨∐ fun j : StartIdx Φ G K ↦ G j.1, descOfPreserves Φ (coproductIsCoproduct _) fun j ↦ j.2⟩

/-- The stages of the tower. -/
noncomputable def stage : ℕ → Stage Φ K
  | 0 => startStage Φ G K
  | k + 1 => (stage k).next G

/-- The tower `X₀ ⟶ X₁ ⟶ ⋯`. -/
noncomputable def tower : ℕ ⥤ C :=
  Functor.ofSequence fun k ↦ (stage Φ G K k).nextMap G

lemma tower_map_succ (k : ℕ) :
    (tower Φ G K).map (homOfLE k.le_succ) = (stage Φ G K k).nextMap G :=
  Functor.ofSequence_map_homOfLE_succ _ k

/-- The coproduct `∐ Xₖ` of the terms of the tower. -/
noncomputable abbrev towerSum : C := ∐ fun k ↦ (tower Φ G K).obj k

/-- The universal element on `∐ Xₖ`. -/
noncomputable def towerSumU : Φ.obj (towerSum Φ G K) ⟶ K :=
  descOfPreserves Φ (coproductIsCoproduct _) fun k ↦ (stage Φ G K k).u

lemma map_ι_towerSumU (k : ℕ) :
    Φ.map (Sigma.ι _ k) ≫ towerSumU Φ G K = (stage Φ G K k).u :=
  map_ι_descOfPreserves Φ (coproductIsCoproduct (fun k ↦ (tower Φ G K).obj k)) _ k

lemma map_one_sub_seqShift_towerSumU :
    Φ.map (𝟙 _ - seqShift (tower Φ G K) (coproductIsCoproduct _)) ≫ towerSumU Φ G K = 0 :=
  hom_ext_of_preserves Φ (coproductIsCoproduct _) fun k ↦ by
    rw [← Functor.map_comp_assoc, comp_sub, comp_id]
    erw [ι_seqShift (tower Φ G K) (coproductIsCoproduct _) k]
    rw [Functor.map_sub, sub_comp, Functor.map_comp_assoc, map_ι_towerSumU,
      map_ι_towerSumU, tower_map_succ, comp_zero]
    erw [Stage.map_nextMap_u]
    exact sub_self _

lemma exists_hocolim : ∃ (L : C) (π : towerSum Φ G K ⟶ L)
    (δ : L ⟶ (towerSum Φ G K)⟦(1 : ℤ)⟧) (u : Φ.obj L ⟶ K),
    Triangle.mk (𝟙 _ - seqShift (tower Φ G K) (coproductIsCoproduct _)) π δ ∈ distTriang C ∧
      Φ.map π ≫ u = towerSumU Φ G K := by
  obtain ⟨L, π, δ, mem⟩ :=
    distinguished_cocone_triangle (𝟙 _ - seqShift (tower Φ G K) (coproductIsCoproduct _))
  obtain ⟨u, hu⟩ := Triangle.yoneda_exact₂ _ (Φ.map_distinguished _ mem) _
    (map_one_sub_seqShift_towerSumU Φ G K)
  exact ⟨L, π, δ, u, mem, hu.symm⟩

/-- The homotopy colimit of the tower. -/
noncomputable def hocolim : C := (exists_hocolim Φ G K).choose

/-- The morphism `∐ Xₖ ⟶ hocolim`. -/
noncomputable def hocolimπ : towerSum Φ G K ⟶ hocolim Φ G K :=
  (exists_hocolim Φ G K).choose_spec.choose

/-- The universal element on the homotopy colimit. -/
noncomputable def hocolimU : Φ.obj (hocolim Φ G K) ⟶ K :=
  (exists_hocolim Φ G K).choose_spec.choose_spec.choose_spec.choose

lemma exists_mem_distTriang_hocolim : ∃ δ,
    Triangle.mk (𝟙 _ - seqShift (tower Φ G K) (coproductIsCoproduct _)) (hocolimπ Φ G K) δ ∈
      distTriang C :=
  ⟨_, (exists_hocolim Φ G K).choose_spec.choose_spec.choose_spec.choose_spec.1⟩

lemma map_hocolimπ_hocolimU : Φ.map (hocolimπ Φ G K) ≫ hocolimU Φ G K = towerSumU Φ G K :=
  (exists_hocolim Φ G K).choose_spec.choose_spec.choose_spec.choose_spec.2

lemma one_sub_seqShift_hocolimπ :
    (𝟙 _ - seqShift (tower Φ G K) (coproductIsCoproduct _)) ≫ hocolimπ Φ G K = 0 := by
  obtain ⟨δ, mem⟩ := exists_mem_distTriang_hocolim Φ G K
  exact comp_distTriang_mor_zero₁₂ _ mem

lemma map_ι_hocolimπ_hocolimU (k : ℕ) :
    Φ.map (Sigma.ι _ k ≫ hocolimπ Φ G K) ≫ hocolimU Φ G K = (stage Φ G K k).u := by
  rw [Φ.map_comp, assoc, map_hocolimπ_hocolimU, map_ι_towerSumU]

/-- Compactness of a family of objects `G i`: every morphism from `G i` to a countable
coproduct factors through a finite partial sum. -/
def IsCompactFamily : Prop :=
  ∀ (i : ι) (F : ℕ → C) (P : C) (ιF : ∀ k, F k ⟶ P) (_ : IsColimit (Cofan.mk P ιF))
    (f : G i ⟶ P), ∃ (N : ℕ) (g : ∀ k, G i ⟶ F k), f = ∑ k ∈ Finset.range N, g k ≫ ιF k

variable {G} in
lemma shift_one_sub_seqShift (F : ℕ ⥤ C) [HasCoproduct F.obj] :
    (shiftFunctor C (1 : ℤ)).map (𝟙 _ - seqShift F (coproductIsCoproduct F.obj)) =
      𝟙 _ - seqShift (F ⋙ shiftFunctor C (1 : ℤ))
        (isColimitCofanMkObjOfIsColimit (shiftFunctor C (1 : ℤ)) _ _
          (coproductIsCoproduct F.obj)) := by
  refine Cofan.IsColimit.hom_ext (isColimitCofanMkObjOfIsColimit (shiftFunctor C (1 : ℤ)) _ _
    (coproductIsCoproduct F.obj)) _ _ fun k ↦ ?_
  simp only [cofan_mk_inj, comp_sub, comp_id, ← Functor.map_comp]
  erw [ι_seqShift F (coproductIsCoproduct F.obj) k]
  erw [ι_seqShift (F ⋙ shiftFunctor C (1 : ℤ)) (isColimitCofanMkObjOfIsColimit
    (shiftFunctor C (1 : ℤ)) _ _ (coproductIsCoproduct F.obj)) k]
  simp

variable {G} in
lemma exists_eq_comp_hocolimπ (hG : IsCompactFamily G) {i : ι} (f : G i ⟶ hocolim Φ G K) :
    ∃ (N : ℕ) (g : G i ⟶ (tower Φ G K).obj N), f = g ≫ Sigma.ι _ N ≫ hocolimπ Φ G K := by
  obtain ⟨δ, mem⟩ := exists_mem_distTriang_hocolim Φ G K
  have h₁ : f ≫ δ = 0 := by
    obtain ⟨N, g, hg⟩ := hG i _ _ _ (isColimitCofanMkObjOfIsColimit (shiftFunctor C (1 : ℤ)) _ _
      (coproductIsCoproduct (tower Φ G K).obj)) (f ≫ δ)
    rw [hg]
    refine eq_zero_of_comp_one_sub_seqShift (tower Φ G K ⋙ shiftFunctor C (1 : ℤ))
      (isColimitCofanMkObjOfIsColimit (shiftFunctor C (1 : ℤ)) _ _
        (coproductIsCoproduct (tower Φ G K).obj)) N g ?_
    rw [← hg, ← shift_one_sub_seqShift, assoc]
    erw [comp_distTriang_mor_zero₃₁ _ mem]
    exact comp_zero
  obtain ⟨g, rfl⟩ := Triangle.coyoneda_exact₃ _ mem f h₁
  obtain ⟨N, g', rfl⟩ := hG i _ _ _ (coproductIsCoproduct (tower Φ G K).obj) g
  refine ⟨N, ∑ k ∈ Finset.range N,
    g' k ≫ if h : k ≤ N then (tower Φ G K).map (homOfLE h) else 0, ?_⟩
  change _ ≫ hocolimπ Φ G K = _
  rw [Preadditive.sum_comp, Preadditive.sum_comp]
  refine Finset.sum_congr rfl fun k hk ↦ ?_
  have hkN : k ≤ N := (Finset.mem_range.1 hk).le
  rw [dif_pos hkN]; simp only [assoc]
  congr 1
  exact ι_comp_eq_of_one_sub_seqShift_comp (tower Φ G K) (coproductIsCoproduct _)
    (hocolimπ Φ G K) (one_sub_seqShift_hocolimπ Φ G K) hkN

variable {G} in
/-- The universal element of the homotopy colimit induces a bijection on the generators. -/
lemma bijective_hocolim (hG : IsCompactFamily G) (i : ι) :
    Function.Bijective fun f : G i ⟶ hocolim Φ G K ↦ Φ.map f ≫ hocolimU Φ G K := by
  have key (f : G i ⟶ hocolim Φ G K) (hf : Φ.map f ≫ hocolimU Φ G K = 0) : f = 0 := by
    obtain ⟨N, g, rfl⟩ := exists_eq_comp_hocolimπ Φ K hG f
    have hg : Φ.map g ≫ (stage Φ G K N).u = 0 := by
      rw [← map_ι_hocolimπ_hocolimU, ← assoc, ← Φ.map_comp]
      simpa using hf
    let j : KillIdx G (stage Φ G K N) := ⟨i, g, hg⟩
    have hj : g = Sigma.ι (fun j : KillIdx G (stage Φ G K N) ↦ G j.1) j ≫
        killMap G (stage Φ G K N) := by simp [killMap, j]
    rw [ι_comp_eq_of_one_sub_seqShift_comp (tower Φ G K) (coproductIsCoproduct _)
      (hocolimπ Φ G K) (one_sub_seqShift_hocolimπ Φ G K) N.le_succ, tower_map_succ]
    have hg0 : g ≫ (stage Φ G K N).nextMap G = 0 := by
      have := Sigma.ι (fun j : KillIdx G (stage Φ G K N) ↦ G j.1) j ≫=
        Stage.killMap_nextMap G (stage Φ G K N)
      simp only [killMap, j, comp_zero] at this
      rw [Sigma.ι_desc_assoc] at this
      exact this
    exact (assoc _ _ _).symm.trans (by erw [hg0]; exact zero_comp)
  refine ⟨fun f₁ f₂ h ↦ ?_, fun x ↦ ?_⟩
  · rw [← sub_eq_zero]
    exact key _ (by simp only [Φ.map_sub, sub_comp]; exact sub_eq_zero.2 h)
  · refine ⟨Sigma.ι (fun j : StartIdx Φ G K ↦ G j.1) ⟨i, x⟩ ≫ Sigma.ι (tower Φ G K).obj 0 ≫ hocolimπ Φ G K, ?_⟩
    dsimp only
    rw [Φ.map_comp, assoc]
    erw [map_ι_hocolimπ_hocolimU]
    exact map_ι_descOfPreserves Φ (coproductIsCoproduct (fun j : StartIdx Φ G K ↦ G j.1)) _ _

variable {G} in
/-- The homotopy colimit is built from the generators by coproducts and cones. -/
lemma prop_hocolim (Q : ObjectProperty C) (hG : ∀ i, Q (G i))
    (hcoprod : ∀ (J : Type w) (f : J → C), (∀ j, Q (f j)) → Q (∐ f))
    (hcoprodℕ : ∀ f : ℕ → C, (∀ k, Q (f k)) → Q (∐ f))
    (htri : ∀ T ∈ distTriang C, Q T.obj₁ → Q T.obj₂ → Q T.obj₃) : Q (hocolim Φ G K) := by
  have hs (k : ℕ) : Q (stage Φ G K k).X := by
    induction k with
    | zero => exact hcoprod _ _ fun j ↦ hG j.1
    | succ k ih =>
      obtain ⟨h, mem⟩ := (stage Φ G K k).exists_mem_distTriang G
      exact htri _ mem (hcoprod _ _ fun j ↦ hG j.1) ih
  obtain ⟨δ, mem⟩ := exists_mem_distTriang_hocolim Φ G K
  exact htri _ mem (hcoprodℕ _ hs) (hcoprodℕ _ hs)

end Construction

section Bijective

variable [HasZeroObject C] [HasShift C ℤ] [∀ n : ℤ, (shiftFunctor C n).Additive]
  [Pretriangulated C]
  {D : Type*} [Category.{w} D] [Preadditive D] [HasZeroObject D] [HasShift D ℤ]
  [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]
  (Φ : C ⥤ D) [Φ.CommShift ℤ] [Φ.IsTriangulated] {K : D} {X : C} (u : Φ.obj X ⟶ K)

/-- The transformation `(Y ⟶ X) → (Φ Y ⟶ K)` induced by `u : Φ X ⟶ K` is bijective at `Y`. -/
def IsBij (Y : C) : Prop := Function.Bijective fun f : Y ⟶ X ↦ Φ.map f ≫ u

variable {Φ u}

lemma IsBij.eq_zero {Y : C} (h : IsBij Φ u Y) {f : Y ⟶ X} (hf : Φ.map f ≫ u = 0) : f = 0 :=
  h.1 (by simpa using hf)

lemma IsBij.of_iso {Y Y' : C} (e : Y ≅ Y') (h : IsBij Φ u Y) : IsBij Φ u Y' := by
  refine ⟨fun f₁ f₂ hf ↦ ?_, fun x ↦ ?_⟩
  · rw [← cancel_epi e.hom]
    exact h.1 (by simp only [Φ.map_comp, assoc]; exact congrArg _ hf)
  · obtain ⟨f, hf⟩ := h.2 (Φ.map e.hom ≫ x)
    refine ⟨e.inv ≫ f, ?_⟩
    simp only [Φ.map_comp, assoc] at hf ⊢
    rw [hf, ← Φ.map_comp_assoc, e.inv_hom_id, Φ.map_id, id_comp]

lemma IsBij.of_isColimit {J : Type*} {f : J → C} {P : C} {ιf : ∀ j, f j ⟶ P}
    (hc : IsColimit (Cofan.mk P ιf)) [PreservesColimit (Discrete.functor f) Φ]
    (h : ∀ j, IsBij Φ u (f j)) : IsBij Φ u P := by
  refine ⟨fun f₁ f₂ hf ↦ Cofan.IsColimit.hom_ext hc _ _ fun j ↦ (h j).1 ?_, fun x ↦ ?_⟩
  · simp only [cofan_mk_inj, Φ.map_comp, assoc]
    exact congrArg _ hf
  · choose g hg using fun j ↦ (h j).2 (Φ.map (ιf j) ≫ x)
    refine ⟨Cofan.IsColimit.desc hc g, hom_ext_of_preserves Φ hc fun j ↦ ?_⟩
    dsimp only at hg ⊢
    rw [← Φ.map_comp_assoc, show ιf j ≫ Cofan.IsColimit.desc hc g = g j from
      Cofan.IsColimit.fac hc g j, hg]

/-- The five lemma: bijectivity at the first two vertices of a distinguished triangle and at
their shifts by one implies bijectivity at the third vertex. -/
lemma IsBij.three (T : Triangle C) (hT : T ∈ distTriang C) (h₁ : IsBij Φ u T.obj₁)
    (h₂ : IsBij Φ u T.obj₂) (h₁' : IsBij Φ u (T.obj₁⟦(1 : ℤ)⟧))
    (h₂' : IsBij Φ u (T.obj₂⟦(1 : ℤ)⟧)) : IsBij Φ u T.obj₃ := by
  have hΦT := Φ.map_distinguished _ hT
  have hΦT' := Φ.map_distinguished _ (rot_of_distTriang _ hT)
  -- exactness of `(Φ - ⟶ K)` at `Φ T.obj₃`
  have ex₃ (x : Φ.obj T.obj₃ ⟶ K) (hx : Φ.map T.mor₂ ≫ x = 0) :
      ∃ y : Φ.obj (T.obj₁⟦(1 : ℤ)⟧) ⟶ K, x = Φ.map T.mor₃ ≫ y := by
    obtain ⟨y, hy⟩ := Triangle.yoneda_exact₃ _ hΦT x hx
    exact ⟨_, hy.trans (assoc _ _ _)⟩
  -- exactness of `(Φ - ⟶ K)` at `Φ (T.obj₁⟦1⟧)`
  have ex₁ (x : Φ.obj (T.obj₁⟦(1 : ℤ)⟧) ⟶ K) (hx : Φ.map T.mor₃ ≫ x = 0) :
      ∃ y : Φ.obj (T.obj₂⟦(1 : ℤ)⟧) ⟶ K, x = Φ.map (-T.mor₁⟦(1 : ℤ)⟧') ≫ y := by
    obtain ⟨y, hy⟩ := Triangle.yoneda_exact₃ _ hΦT' x hx
    exact ⟨_, hy.trans (assoc _ _ _)⟩
  have key (f : T.obj₃ ⟶ X) (hf : Φ.map f ≫ u = 0) : f = 0 := by
    have hf₂ : T.mor₂ ≫ f = 0 := h₂.eq_zero (by rw [Φ.map_comp, assoc, hf, comp_zero])
    obtain ⟨g, rfl⟩ := Triangle.yoneda_exact₃ _ hT f hf₂
    obtain ⟨z, hz⟩ := ex₁ (Φ.map g ≫ u) (by rw [← assoc, ← Φ.map_comp]; exact hf)
    obtain ⟨w, rfl⟩ := h₂'.2 z
    have : g = (-T.mor₁⟦(1 : ℤ)⟧') ≫ w :=
      h₁'.1 (by dsimp only; rw [Φ.map_comp, assoc]; exact hz)
    rw [this, ← Category.assoc, comp_neg, comp_distTriang_mor_zero₃₁ _ hT, neg_zero,
      zero_comp]
  refine ⟨fun f₁ f₂ hf ↦ ?_, fun x ↦ ?_⟩
  · rw [← sub_eq_zero]
    exact key _ (by simp only [Φ.map_sub, sub_comp]; exact sub_eq_zero.2 hf)
  · obtain ⟨b, hb⟩ := h₂.2 (Φ.map T.mor₂ ≫ x)
    have hb₁ : T.mor₁ ≫ b = 0 := h₁.eq_zero (by
      dsimp only at hb
      rw [Φ.map_comp, assoc, hb, ← Φ.map_comp_assoc, comp_distTriang_mor_zero₁₂ _ hT,
        Φ.map_zero, zero_comp])
    obtain ⟨c, rfl⟩ := Triangle.yoneda_exact₂ _ hT b hb₁
    obtain ⟨y, hy⟩ := ex₃ (x - Φ.map c ≫ u) (by
      dsimp only at hb
      rw [comp_sub, ← hb, Φ.map_comp, assoc, sub_self])
    obtain ⟨a, rfl⟩ := h₁'.2 y
    refine ⟨c + T.mor₃ ≫ a, ?_⟩
    dsimp only at hy ⊢
    rw [Φ.map_add, add_comp, Φ.map_comp, assoc, ← hy, add_sub_cancel]

end Bijective

section Representability

variable [HasZeroObject C] [HasShift C ℤ] [∀ n : ℤ, (shiftFunctor C n).Additive]
  [Pretriangulated C]
  {D : Type*} [Category.{w} D] [Preadditive D] [HasZeroObject D] [HasShift D ℤ]
  [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]
  (Φ : C ⥤ D) [Φ.CommShift ℤ] [Φ.IsTriangulated]
  [HasCoproducts.{w} C] [∀ J : Type w, PreservesColimitsOfShape (Discrete J) Φ]
  [HasCoproductsOfShape ℕ C] [PreservesColimitsOfShape (Discrete ℕ) Φ]
  {ι : Type w} {G : ι → C}

/-- The objects `Y` such that `u` induces a bijection at every shift of `Y`. -/
def IsBijShifts {K : D} {X : C} (u : Φ.obj X ⟶ K) (Y : C) : Prop :=
  ∀ n : ℤ, IsBij Φ u (Y⟦n⟧)

variable {Φ}

lemma IsBijShifts.of_iso {K : D} {X : C} {u : Φ.obj X ⟶ K} {Y Y' : C} (e : Y ≅ Y')
    (h : IsBijShifts Φ u Y) : IsBijShifts Φ u Y' :=
  fun n ↦ (h n).of_iso ((shiftFunctor C n).mapIso e)

lemma IsBijShifts.three {K : D} {X : C} {u : Φ.obj X ⟶ K} (T : Triangle C)
    (hT : T ∈ distTriang C) (h₁ : IsBijShifts Φ u T.obj₁) (h₂ : IsBijShifts Φ u T.obj₂) :
    IsBijShifts Φ u T.obj₃ := fun n ↦ by
  have e (Y : C) : Y⟦n + 1⟧ ≅ Y⟦n⟧⟦(1 : ℤ)⟧ := (shiftFunctorAdd' C n 1 (n + 1) rfl).app Y
  exact IsBij.three _ (Triangle.shift_distinguished T hT n) (h₁ n) (h₂ n)
    ((h₁ (n + 1)).of_iso (e _)) ((h₂ (n + 1)).of_iso (e _))

lemma IsBijShifts.sigma {K : D} {X : C} {u : Φ.obj X ⟶ K} {J : Type*} (f : J → C)
    [HasCoproduct f] [∀ n : ℤ, PreservesColimit (Discrete.functor fun j ↦ (f j)⟦n⟧) Φ]
    (h : ∀ j, IsBijShifts Φ u (f j)) : IsBijShifts Φ u (∐ f) := fun n ↦
  IsBij.of_isColimit (isColimitCofanMkObjOfIsColimit (shiftFunctor C n) _ _
    (coproductIsCoproduct f)) fun j ↦ h j n

variable (Φ G) in
/-- **Brown representability.** Let `Φ : C ⥤ D` be a triangulated functor preserving
coproducts, and let `G` be a compact family of objects of `C` which is stable under shifts and
generating. Then for every `K : D` there is an object `X : C` and `u : Φ X ⟶ K` such that
`f ↦ Φ f ≫ u` is a bijection `(Y ⟶ X) ≃ (Φ Y ⟶ K)` for every `Y : C`. -/
theorem exists_bijective (hG : IsCompactFamily G)
    (hshift : ∀ (i : ι) (n : ℤ), ∃ j, Nonempty ((G i)⟦n⟧ ≅ G j))
    (hgen : ∀ Z : C, (∀ (i : ι) (f : G i ⟶ Z), f = 0) → IsZero Z) (K : D) :
    ∃ (X : C) (u : Φ.obj X ⟶ K), ∀ Y : C, Function.Bijective fun f : Y ⟶ X ↦ Φ.map f ≫ u := by
  refine ⟨hocolim Φ G K, hocolimU Φ G K, fun Y ↦ ?_⟩
  -- the class of objects at all of whose shifts `u` is bijective
  have hGS (i : ι) : IsBijShifts Φ (hocolimU Φ G K) (G i) := fun n ↦ by
    obtain ⟨j, ⟨e⟩⟩ := hshift i n
    exact (show IsBij Φ _ (G j) from bijective_hocolim Φ K hG j).of_iso e.symm
  have hS : IsBijShifts Φ (hocolimU Φ G K) (hocolim (𝟭 C) G Y) :=
    prop_hocolim (𝟭 C) Y (IsBijShifts Φ (hocolimU Φ G K)) hGS
      (fun J f hf ↦ IsBijShifts.sigma f hf) (fun f hf ↦ IsBijShifts.sigma f hf)
      (fun T hT h₁ h₂ ↦ IsBijShifts.three T hT h₁ h₂)
  -- the object `Y` is the homotopy colimit of its own cellular tower
  set X' := hocolim (𝟭 C) G Y
  set u' : X' ⟶ Y := hocolimU (𝟭 C) G Y
  have hu' (i : ι) : Function.Bijective fun f : G i ⟶ X' ↦ f ≫ u' :=
    bijective_hocolim (𝟭 C) Y hG i
  obtain ⟨Z, g, h, mem⟩ := distinguished_cocone_triangle u'
  have hZ : IsZero Z := hgen Z fun i f ↦ by
    obtain ⟨j, ⟨e₀⟩⟩ := hshift i (-1)
    let e : G i ≅ (G j)⟦(1 : ℤ)⟧ :=
      ((shiftFunctorCompIsoId C (-1 : ℤ) 1 (by norm_num)).app (G i)).symm ≪≫
        (shiftFunctor C (1 : ℤ)).mapIso e₀
    have h0 : h ≫ (shiftFunctor C (1 : ℤ)).map u' = 0 := comp_distTriang_mor_zero₃₁ _ mem
    have h1 : u' ≫ g = 0 := comp_distTriang_mor_zero₁₂ _ mem
    obtain ⟨a, ha⟩ := (shiftFunctor C (1 : ℤ)).map_surjective (e.inv ≫ f ≫ h)
    have hau : a ≫ u' = 0 := (shiftFunctor C (1 : ℤ)).map_injective (by
      rw [Functor.map_comp, ha, Functor.map_zero, assoc, assoc, h0, comp_zero, comp_zero])
    have ha0 : a = 0 := (hu' j).1 (by simpa using hau)
    have hfh : f ≫ h = 0 := by
      rw [← cancel_epi e.inv, comp_zero, ← ha, ha0, Functor.map_zero]
    obtain ⟨b, rfl⟩ := Triangle.coyoneda_exact₃ _ mem f hfh
    obtain ⟨c, rfl⟩ := (hu' i).2 b
    dsimp only
    show (c ≫ u') ≫ g = 0
    rw [assoc, h1, comp_zero]
  have : IsIso u' := (Triangle.isZero₃_iff_isIso₁ _ mem).1 hZ
  exact (hS.of_iso (asIso u') 0).of_iso ((shiftFunctorZero C ℤ).app Y)

/-- **Brown representability.** A triangulated functor `Φ : C ⥤ D` preserving coproducts,
whose source has a compact generating family stable under shifts, is a left adjoint. -/
theorem isLeftAdjoint_of_isCompactFamily (hG : IsCompactFamily G)
    (hshift : ∀ (i : ι) (n : ℤ), ∃ j, Nonempty ((G i)⟦n⟧ ≅ G j))
    (hgen : ∀ Z : C, (∀ (i : ι) (f : G i ⟶ Z), f = 0) → IsZero Z) : Φ.IsLeftAdjoint := by
  refine Functor.isLeftAdjoint_of_rightAdjointObjIsDefined_eq_top ?_
  ext K
  simp only [Pi.top_apply, Prop.top_eq_true, iff_true]
  obtain ⟨X, u, hu⟩ := exists_bijective Φ G hG hshift hgen K
  exact Functor.RepresentableBy.isRepresentable
    { homEquiv := Equiv.ofBijective _ (hu _)
      homEquiv_comp := fun f g ↦ by simp }

end Representability

section Reflective

variable [HasZeroObject C] [HasShift C ℤ] [∀ n : ℤ, (shiftFunctor C n).Additive]
  [Pretriangulated C]
  {C' : Type*} [Category.{w} C'] [Preadditive C'] [HasZeroObject C'] [HasShift C' ℤ]
  [∀ n : ℤ, (shiftFunctor C' n).Additive] [Pretriangulated C']
  {D : Type*} [Category.{w} D] [Preadditive D]

/-- Let `L : C ⥤ C'` be a triangulated functor with a fully faithful right adjoint `R` (i.e. the
counit is an isomorphism), and let `Φ : C' ⥤ D` be additive. If `L ⋙ Φ` is a left adjoint, then
so is `Φ`: for `K : D`, the value at `K` of the right adjoint of `L ⋙ Φ` is right orthogonal to
the kernel of `L`, hence lies in the essential image of `R`. -/
theorem isLeftAdjoint_of_isLeftAdjoint_comp {L : C ⥤ C'} {R : C' ⥤ C} (adj : L ⊣ R)
    [IsIso adj.counit] [L.CommShift ℤ] [L.IsTriangulated] (Φ : C' ⥤ D) [Φ.Additive]
    [(L ⋙ Φ).IsLeftAdjoint] : Φ.IsLeftAdjoint := by
  have := adj.right_adjoint_additive
  refine Functor.isLeftAdjoint_of_rightAdjointObjIsDefined_eq_top ?_
  ext K
  simp only [Pi.top_apply, Prop.top_eq_true, iff_true]
  let adj₂ := Adjunction.ofIsLeftAdjoint (L ⋙ Φ)
  set N := (L ⋙ Φ).rightAdjoint.obj K
  let ε₂ : Φ.obj (L.obj N) ⟶ K := adj₂.counit.app K
  -- the unit `N ⟶ R (L N)` is an isomorphism
  have hη : IsIso (adj.unit.app N) := by
    obtain ⟨M, a, b, mem⟩ := distinguished_cocone_triangle₁ (adj.unit.app N)
    have hLη : IsIso (L.map (adj.unit.app N)) := by
      have h := adj.left_triangle_components N
      have : L.map (adj.unit.app N) = inv (adj.counit.app (L.obj N)) := by
        rw [← cancel_mono (adj.counit.app (L.obj N)), h, IsIso.inv_hom_id]
        rfl
      rw [this]
      infer_instance
    have hLM : IsZero (L.obj M) :=
      (Triangle.isZero₁_iff_isIso₂ _ (L.map_distinguished _ mem)).2 hLη
    have ha : a = 0 := by
      apply adj₂.homEquiv _ _ |>.symm.injective
      exact (Φ.map_isZero hLM).eq_of_src _ _
    obtain ⟨s, hs⟩ := Triangle.coyoneda_exact₁ _ mem (𝟙 (M⟦(1 : ℤ)⟧)) (by
      subst ha; exact (id_comp _).trans (Functor.map_zero _ _ _))
    have hs₀ : s = 0 := by
      have hz : IsZero (L.obj (M⟦(1 : ℤ)⟧)) :=
        IsZero.of_iso ((shiftFunctor C' (1 : ℤ)).map_isZero hLM) ((L.commShiftIso 1).app M)
      exact (adj.homEquiv _ (L.obj N)).symm.injective (hz.eq_of_src _ _)
    have hM₁ : IsZero (M⟦(1 : ℤ)⟧) := by
      rw [IsZero.iff_id_eq_zero, hs, hs₀]
      exact zero_comp
    have hM : IsZero M := IsZero.of_iso ((shiftFunctor C (-1 : ℤ)).map_isZero hM₁)
      ((shiftFunctorCompIsoId C (1 : ℤ) (-1) (by norm_num)).app M).symm
    exact (Triangle.isZero₁_iff_isIso₂ _ mem).1 hM
  have hbij (A : C') : Function.Bijective fun f : A ⟶ L.obj N ↦ Φ.map f ≫ ε₂ := by
    refine ⟨fun f₁ f₂ hf ↦ ?_, fun x ↦ ?_⟩
    · -- the morphisms `ε_A ≫ fᵢ` are of the form `L hᵢ`
      have hL (f : A ⟶ L.obj N) : ∃ h : R.obj A ⟶ N, adj.counit.app A ≫ f = L.map h := by
        refine ⟨adj.homEquiv _ _ (adj.counit.app A ≫ f) ≫ inv (adj.unit.app N), ?_⟩
        apply (adj.homEquiv _ _).injective
        conv_rhs => rw [Adjunction.homEquiv_unit, adj.unit_naturality, assoc,
          IsIso.inv_hom_id, comp_id]
      obtain ⟨h₁, hh₁⟩ := hL f₁
      obtain ⟨h₂, hh₂⟩ := hL f₂
      have : h₁ = h₂ := by
        apply (adj₂.homEquiv _ _).symm.injective
        simp only [Adjunction.homEquiv_counit, Functor.comp_map]
        rw [← hh₁, ← hh₂, Φ.map_comp, Φ.map_comp, assoc, assoc]
        exact congrArg _ hf
      rw [← cancel_epi (adj.counit.app A), hh₁, hh₂, this]
    · obtain ⟨h, hh⟩ : ∃ h : R.obj A ⟶ N, Φ.map (L.map h) ≫ ε₂ = Φ.map (adj.counit.app A) ≫ x :=
        ⟨adj₂.homEquiv _ _ (Φ.map (adj.counit.app A) ≫ x), by
          rw [← Functor.comp_map, ← Adjunction.homEquiv_counit, Equiv.symm_apply_apply]⟩
      refine ⟨inv (adj.counit.app A) ≫ L.map h, ?_⟩
      dsimp only
      rw [Φ.map_comp, assoc, hh, ← Φ.map_comp_assoc, IsIso.inv_hom_id, Φ.map_id, id_comp]
  exact Functor.RepresentableBy.isRepresentable
    { homEquiv := Equiv.ofBijective _ (hbij _)
      homEquiv_comp := fun f g ↦ by simp }

end Reflective

end Brown

end CategoryTheory.Pretriangulated
