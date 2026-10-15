/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
-/
module

public import Sheaf.Paper.HypercoverResolutionModel
import Sheaf.Paper.HypercoverRefinementSectionLifts
import WeilConjectures.Algebra.Homology.TotalComplexRowResolution
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.Algebra.Homology.TotalComplexSymmetry

/-! # Refinement descent for the bottom row of an injective-resolution bicomplex

Source: Stacks Project, Hypercoverings, Tag 01H0, first proof.
The finite cochain correction uses the resolution degree first; a signed transposition
identifies its total complex with the explicit comparison model.
(blueprint: lem-sc-hypercover-bottom-refinement-descent).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.Preadditive Opposite

namespace AlgebraicGeometry.FiniteSplitEtaleHypercover

variable {X : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X]
variable (R : Type (u + 1)) [Ring R]

private noncomputable def staircase (U : FiniteSplitEtaleHypercover X)
    (I : CochainComplex (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} R)) ℕ) :
    HomologicalComplex₂ (ModuleCat.{u + 1} R) (.up ℕ) (.up ℕ) :=
  ((sectionComplexFunctor R U).mapHomologicalComplex (.up ℕ)).obj I

private noncomputable def staircaseMap {U V : FiniteSplitEtaleHypercover X}
    (f : V.Refinement U)
    (I : CochainComplex (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} R)) ℕ) :
    staircase R U I ⟶ staircase R V I :=
  (NatTrans.mapHomologicalComplex (sectionRefinement R f) (.up ℕ)).app I

private lemma totalπ_naturality
    {K L : HomologicalComplex₂ (ModuleCat.{u + 1} R) (.up ℕ) (.up ℕ)}
    (φ : K ⟶ L) (n p q : ℕ) :
    (HomologicalComplex₂.total.map φ (.up ℕ)).f n ≫ L.totalπ n p q =
      K.totalπ n p q ≫ (φ.f p).f q := by
  apply HomologicalComplex₂.total.hom_ext
  intro a b hab
  rw [HomologicalComplex₂.ιTotal_map_assoc,
    HomologicalComplex₂.ιTotal_totalπ,
    HomologicalComplex₂.ιTotal_totalπ_assoc]
  split_ifs with h
  · obtain ⟨rfl, rfl⟩ := h
    simp
  · simp

private lemma vanishesFrom_map
    {K L : HomologicalComplex₂ (ModuleCat.{u + 1} R) (.up ℕ) (.up ℕ)}
    (φ : K ⟶ L) {n : ℕ} (x : ModuleCat.of R R ⟶ (K.total (.up ℕ)).X n)
    {j : ℕ} (hx : K.VanishesFrom x j) :
    L.VanishesFrom (x ≫ (HomologicalComplex₂.total.map φ (.up ℕ)).f n) j := by
  intro p q hp
  rw [Category.assoc, totalπ_naturality, ← Category.assoc, hx p q hp, zero_comp]

private lemma staircase_step
    {K L : HomologicalComplex₂ (ModuleCat.{u + 1} R) (.up ℕ) (.up ℕ)}
    (φ : K ⟶ L) {m k : ℕ} (hk : k ≤ m)
    (x : ModuleCat.of R R ⟶ (K.total (.up ℕ)).X (m + 1))
    (hx : K.VanishesFrom x (k + 2))
    (z : ModuleCat.of R R ⟶ (L.X k).X (m - k))
    (hz : z ≫ (L.d k (k + 1)).f (m - k) =
      (x ≫ K.totalπ (m + 1) (k + 1) (m - k)) ≫ (φ.f (k + 1)).f (m - k)) :
    L.VanishesFrom
      (x ≫ (HomologicalComplex₂.total.map φ (.up ℕ)).f (m + 1) -
        (z ≫ L.ιTotal (.up ℕ) k (m - k) m (by change k + (m - k) = m; omega)) ≫
          (L.total (.up ℕ)).d m (m + 1)) (k + 1) := by
  have hx' := vanishesFrom_map R φ x hx
  intro p q hp
  rw [sub_comp, Category.assoc, Category.assoc, Category.assoc,
    HomologicalComplex₂.ιTotal_d_totalπ,
    dif_neg (show ¬ (k = p ∧ m - k + 1 = q) by omega)]
  simp only [comp_zero, smul_zero, add_zero]
  by_cases hp' : p = k + 1 ∧ m - k = q
  · obtain ⟨rfl, rfl⟩ := hp'
    rw [dif_pos ⟨rfl, rfl⟩]
    simp only [HomologicalComplex₂.XXIsoOfEq, eqToIso_refl, Iso.refl_hom,
      Category.comp_id]
    rw [totalπ_naturality, ← Category.assoc, ← hz, sub_self]
  · rw [dif_neg (fun h ↦ hp' ⟨h.1.symm, h.2⟩), comp_zero, comp_zero, sub_zero]
    by_cases hp'' : p = k + 1
    · subst hp''
      rw [HomologicalComplex₂.totalπ_eq_zero _ _ _ _ (by omega), comp_zero, comp_zero]
    · exact hx' p q (by omega)

private theorem exists_staircase_step
    {F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} R)}
    (I : InjectiveResolution F) (U : FiniteSplitEtaleHypercover X)
    {m k : ℕ} (hk : k ≤ m)
    (x : ModuleCat.of R R ⟶ ((staircase R U I.cocomplex).total (.up ℕ)).X (m + 1))
    (hx : (staircase R U I.cocomplex).VanishesFrom x (k + 2))
    (hdx : x ≫ ((staircase R U I.cocomplex).total (.up ℕ)).d (m + 1) (m + 2) ≫
      (staircase R U I.cocomplex).totalπ (m + 2) (k + 2) (m - k) = 0) :
    ∃ (V : FiniteSplitEtaleHypercover X) (f : V.Refinement U)
      (w : ModuleCat.of R R ⟶ ((staircase R V I.cocomplex).total (.up ℕ)).X m),
      (staircase R V I.cocomplex).VanishesFrom
        (x ≫ (HomologicalComplex₂.total.map (staircaseMap R f I.cocomplex)
          (.up ℕ)).f (m + 1) -
          w ≫ ((staircase R V I.cocomplex).total (.up ℕ)).d m (m + 1)) (k + 1) := by
  classical
  let K := staircase R U I.cocomplex
  have hd : (x ≫ K.totalπ (m + 1) (k + 1) (m - k)) ≫
      (K.d (k + 1) (k + 2)).f (m - k) = 0 := by
    simpa only [HomologicalComplex₂.comp_d_totalπ_succ x (k + 1) (m - k)
      (fun q' ↦ hx _ _ le_rfl)] using hdx
  let s := (x ≫ K.totalπ (m + 1) (k + 1) (m - k)) 1
  let S := ShortComplex.mk (I.cocomplex.d k (k + 1))
    (I.cocomplex.d (k + 1) (k + 2)) (I.cocomplex.d_comp_d k (k + 1) (k + 2))
  have hs : S.g.hom.app _ s = 0 := by
    exact ConcreteCategory.congr_hom hd 1
  obtain ⟨V, f, t, ht⟩ := exists_refinement_primitive U R S (I.exact_succ k) (m - k) s hs
  let L := staircase R V I.cocomplex
  let z : ModuleCat.of R R ⟶ (L.X k).X (m - k) :=
    ModuleCat.ofHom (LinearMap.toSpanSingleton R _ t)
  have hz : z ≫ (L.d k (k + 1)).f (m - k) =
      (x ≫ K.totalπ (m + 1) (k + 1) (m - k)) ≫
        ((staircaseMap R f I.cocomplex).f (k + 1)).f (m - k) := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro a
    have ha : (x ≫ K.totalπ (m + 1) (k + 1) (m - k)) a = a • s := by
      simpa only [smul_eq_mul, mul_one] using
        (map_smul (x ≫ K.totalπ (m + 1) (k + 1) (m - k)).hom a (1 : R))
    change S.f.hom.app _ (a • t) =
      S.X₂.obj.map (f.app (op (SimplexCategory.mk (m - k)))).op
        ((x ≫ K.totalπ (m + 1) (k + 1) (m - k)) a)
    rw [map_smul, ht, ha, map_smul]
  refine ⟨V, f, z ≫ L.ιTotal (.up ℕ) k (m - k) m
    (by change k + (m - k) = m; omega), ?_⟩
  exact staircase_step R (staircaseMap R f I.cocomplex) hk x hx z hz

private lemma staircaseMap_id (U : FiniteSplitEtaleHypercover X)
    (I : CochainComplex (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} R)) ℕ) :
    staircaseMap R (𝟙 U.simplicial) I = 𝟙 _ := by
  apply HomologicalComplex.hom_ext
  intro p
  apply HomologicalComplex.hom_ext
  intro q
  change (I.X p).obj.map (𝟙 _) = 𝟙 _
  simp

private lemma staircaseMap_comp {U V W : FiniteSplitEtaleHypercover X}
    (f : V.Refinement U) (g : W.Refinement V)
    (I : CochainComplex (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} R)) ℕ) :
    staircaseMap R (g ≫ f) I = staircaseMap R f I ≫ staircaseMap R g I := by
  apply HomologicalComplex.hom_ext
  intro p
  apply HomologicalComplex.hom_ext
  intro q
  change (I.X p).obj.map (g.app _ ≫ f.app _).op =
    (I.X p).obj.map (f.app _).op ≫ (I.X p).obj.map (g.app _).op
  rw [op_comp, Functor.map_comp]

private lemma total_staircase_id (U : FiniteSplitEtaleHypercover X)
    (I : CochainComplex (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} R)) ℕ) :
    HomologicalComplex₂.total.map (staircaseMap R (𝟙 U.simplicial) I) (.up ℕ) = 𝟙 _ := by
  rw [staircaseMap_id, HomologicalComplex₂.total.map_id]

private lemma total_staircase_comp {U V W : FiniteSplitEtaleHypercover X}
    (f : V.Refinement U) (g : W.Refinement V)
    (I : CochainComplex (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} R)) ℕ) :
    HomologicalComplex₂.total.map (staircaseMap R (g ≫ f) I) (.up ℕ) =
      HomologicalComplex₂.total.map (staircaseMap R f I) (.up ℕ) ≫
        HomologicalComplex₂.total.map (staircaseMap R g I) (.up ℕ) := by
  rw [staircaseMap_comp, HomologicalComplex₂.total.map_comp]

private theorem exists_staircase_one
    {F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} R)}
    (I : InjectiveResolution F) (U : FiniteSplitEtaleHypercover X) {m : ℕ}
    (x : ModuleCat.of R R ⟶ ((staircase R U I.cocomplex).total (.up ℕ)).X m)
    (hdx : (staircase R U I.cocomplex).VanishesFrom
      (x ≫ ((staircase R U I.cocomplex).total (.up ℕ)).d m (m + 1)) 2) :
    ∃ (V : FiniteSplitEtaleHypercover X) (f : V.Refinement U)
      (w : ModuleCat.of R R ⟶ ((staircase R V I.cocomplex).total (.up ℕ)).X (m - 1)),
      (staircase R V I.cocomplex).VanishesFrom
        (x ≫ (HomologicalComplex₂.total.map (staircaseMap R f I.cocomplex)
          (.up ℕ)).f m -
          w ≫ ((staircase R V I.cocomplex).total (.up ℕ)).d (m - 1) m) 1 := by
  cases m with
  | zero =>
    refine ⟨U, 𝟙 U.simplicial, 0, ?_⟩
    simpa [total_staircase_id] using
      (HomologicalComplex₂.vanishesFrom_of_lt x 1 (by omega))
  | succ m =>
    suffices H : ∀ j : ℕ, ∀ (U : FiniteSplitEtaleHypercover X)
        (x : ModuleCat.of R R ⟶ ((staircase R U I.cocomplex).total (.up ℕ)).X (m + 1)),
        (staircase R U I.cocomplex).VanishesFrom
          (x ≫ ((staircase R U I.cocomplex).total (.up ℕ)).d (m + 1) (m + 2)) 2 →
        (staircase R U I.cocomplex).VanishesFrom x (j + 1) →
        ∃ (V : FiniteSplitEtaleHypercover X) (f : V.Refinement U)
          (w : ModuleCat.of R R ⟶ ((staircase R V I.cocomplex).total (.up ℕ)).X m),
          (staircase R V I.cocomplex).VanishesFrom
            (x ≫ (HomologicalComplex₂.total.map (staircaseMap R f I.cocomplex)
              (.up ℕ)).f (m + 1) -
              w ≫ ((staircase R V I.cocomplex).total (.up ℕ)).d m (m + 1)) 1 by
      simpa using H (m + 1) U x hdx
        (HomologicalComplex₂.vanishesFrom_of_lt x (m + 2) (by omega))
    intro j
    induction j with
    | zero =>
      intro U x _ hx
      refine ⟨U, 𝟙 U.simplicial, 0, ?_⟩
      simpa [total_staircase_id] using hx
    | succ j ih =>
      intro U x hdx hx
      by_cases hj : j ≤ m
      · obtain ⟨V, f, w₁, hw₁⟩ := exists_staircase_step R I U hj x hx (by
          rw [← Category.assoc]
          exact hdx _ _ (by omega))
        let τ := HomologicalComplex₂.total.map (staircaseMap R f I.cocomplex) (.up ℕ)
        let y := x ≫ τ.f (m + 1) -
          w₁ ≫ ((staircase R V I.cocomplex).total (.up ℕ)).d m (m + 1)
        have hdy : (staircase R V I.cocomplex).VanishesFrom
            (y ≫ ((staircase R V I.cocomplex).total (.up ℕ)).d (m + 1) (m + 2)) 2 := by
          have hh := vanishesFrom_map R (staircaseMap R f I.cocomplex)
            (x ≫ ((staircase R U I.cocomplex).total (.up ℕ)).d (m + 1) (m + 2)) hdx
          convert hh using 1
          simp only [y, sub_comp, Category.assoc, HomologicalComplex.d_comp_d,
            comp_zero, sub_zero, τ.comm]
          rfl
        obtain ⟨W, g, w₂, hw₂⟩ := ih V y hdy hw₁
        let σ := HomologicalComplex₂.total.map (staircaseMap R g I.cocomplex) (.up ℕ)
        refine ⟨W, g ≫ f, w₁ ≫ σ.f m + w₂, ?_⟩
        convert hw₂ using 1
        simp only [total_staircase_comp, HomologicalComplex.comp_f, add_comp,
          sub_comp, y, Category.assoc]
        rw [← σ.comm m (m + 1)]
        dsimp only [τ, σ]
        abel
      · exact ih U x hdx (HomologicalComplex₂.vanishesFrom_of_lt x _ (by omega))

private noncomputable def staircaseAugmentation
    {F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} R)}
    (I : InjectiveResolution F) (U : FiniteSplitEtaleHypercover X) :
    (sectionComplexFunctor R U).obj F ⟶ (staircase R U I.cocomplex).X 0 :=
  (sectionComplexFunctor R U).map (I.ι.f 0)

private lemma staircaseAugmentation_d
    {F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} R)}
    (I : InjectiveResolution F) (U : FiniteSplitEtaleHypercover X) :
    staircaseAugmentation R I U ≫ (staircase R U I.cocomplex).d 0 1 = 0 := by
  change (sectionComplexFunctor R U).map (I.ι.f 0) ≫
    (sectionComplexFunctor R U).map (I.cocomplex.d 0 1) = 0
  rw [← Functor.map_comp, I.ι_f_zero_comp_complex_d, Functor.map_zero]

private noncomputable def staircaseBottom
    {F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} R)}
    (I : InjectiveResolution F) (U : FiniteSplitEtaleHypercover X) :
    (sectionComplexFunctor R U).obj F ⟶ (staircase R U I.cocomplex).total (.up ℕ) :=
  (staircase R U I.cocomplex).toTotalOfAugmentation
    (staircaseAugmentation R I U) (staircaseAugmentation_d R I U)

private lemma staircaseAugmentation_mono
    {F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} R)}
    (I : InjectiveResolution F) (U : FiniteSplitEtaleHypercover X) (q : ℕ) :
    Mono ((staircaseAugmentation R I U).f q) := by
  let ev : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} R) ⥤ ModuleCat R :=
    sheafToPresheaf _ _ ⋙
      (evaluation _ _).obj (op (U.simplicial.obj (op (SimplexCategory.mk q))))
  change Mono (ev.map (I.ι.f 0))
  infer_instance

private lemma staircaseBottom_mono
    {F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} R)}
    (I : InjectiveResolution F) (U : FiniteSplitEtaleHypercover X) (q : ℕ) :
    Mono ((staircaseBottom R I U).f q) := by
  have : Mono ((staircaseBottom R I U).f q ≫
      (staircase R U I.cocomplex).totalπ q 0 q) := by
    change Mono (((staircase R U I.cocomplex).toTotalOfAugmentation _ _).f q ≫ _)
    rw [HomologicalComplex₂.toTotalOfAugmentation_f_totalπ_zero]
    exact staircaseAugmentation_mono R I U q
  exact mono_of_mono ((staircaseBottom R I U).f q)
    ((staircase R U I.cocomplex).totalπ q 0 q)

private theorem staircase_lift_bottom
    {F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} R)}
    (I : InjectiveResolution F) (U : FiniteSplitEtaleHypercover X) {m : ℕ}
    (x : ModuleCat.of R R ⟶ ((staircase R U I.cocomplex).total (.up ℕ)).X m)
    (hx : (staircase R U I.cocomplex).VanishesFrom x 1)
    (hdx : x ≫ ((staircase R U I.cocomplex).total (.up ℕ)).d m (m + 1) ≫
      (staircase R U I.cocomplex).totalπ (m + 1) 1 m = 0) :
    ∃ l : ModuleCat.of R R ⟶ ((sectionComplexFunctor R U).obj F).X m,
      x = l ≫ (staircaseBottom R I U).f m := by
  let K := staircase R U I.cocomplex
  have hd : (x ≫ K.totalπ m 0 m) ≫ (K.d 0 1).f m = 0 := by
    simpa only [HomologicalComplex₂.comp_d_totalπ_succ x 0 m
      (fun q' ↦ hx _ _ le_rfl)] using hdx
  let ev : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} R) ⥤ ModuleCat R :=
    sheafToPresheaf _ _ ⋙
      (evaluation _ _).obj (op (U.simplicial.obj (op (SimplexCategory.mk m))))
  have hker := isLimitForkMapOfIsLimit' ev I.ι_f_zero_comp_complex_d I.isLimitKernelFork
  obtain ⟨l, hl⟩ := KernelFork.IsLimit.lift' hker (x ≫ K.totalπ m 0 m) hd
  refine ⟨l, ?_⟩
  rw [HomologicalComplex₂.eq_totalπ_ιTotal_of_vanishesFrom_one hx]
  change (x ≫ K.totalπ m 0 m) ≫ _ =
    l ≫ (staircaseAugmentation R I U).f m ≫ _
  have hl' : l ≫ (staircaseAugmentation R I U).f m = x ≫ K.totalπ m 0 m := hl
  rw [← Category.assoc, hl']

private theorem exists_staircase_cochain
    {F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} R)}
    (I : InjectiveResolution F) (U : FiniteSplitEtaleHypercover X) {m : ℕ}
    (x : ModuleCat.of R R ⟶ ((staircase R U I.cocomplex).total (.up ℕ)).X m)
    (hdx : (staircase R U I.cocomplex).VanishesFrom
      (x ≫ ((staircase R U I.cocomplex).total (.up ℕ)).d m (m + 1)) 1) :
    ∃ (V : FiniteSplitEtaleHypercover X) (f : V.Refinement U)
      (l : ModuleCat.of R R ⟶ ((sectionComplexFunctor R V).obj F).X m)
      (w : ModuleCat.of R R ⟶ ((staircase R V I.cocomplex).total (.up ℕ)).X (m - 1)),
      x ≫ (HomologicalComplex₂.total.map (staircaseMap R f I.cocomplex) (.up ℕ)).f m =
        l ≫ (staircaseBottom R I V).f m +
          w ≫ ((staircase R V I.cocomplex).total (.up ℕ)).d (m - 1) m := by
  obtain ⟨V, f, w, hw⟩ := exists_staircase_one R I U x
    (fun p q hp ↦ hdx p q (by omega))
  let τ := HomologicalComplex₂.total.map (staircaseMap R f I.cocomplex) (.up ℕ)
  let y := x ≫ τ.f m -
    w ≫ ((staircase R V I.cocomplex).total (.up ℕ)).d (m - 1) m
  have hd : y ≫ ((staircase R V I.cocomplex).total (.up ℕ)).d m (m + 1) ≫
      (staircase R V I.cocomplex).totalπ (m + 1) 1 m = 0 := by
    have hh := vanishesFrom_map R (staircaseMap R f I.cocomplex)
      (x ≫ ((staircase R U I.cocomplex).total (.up ℕ)).d m (m + 1)) hdx
    have he : y ≫ ((staircase R V I.cocomplex).total (.up ℕ)).d m (m + 1) =
        (x ≫ ((staircase R U I.cocomplex).total (.up ℕ)).d m (m + 1)) ≫ τ.f (m + 1) := by
      simp only [y, sub_comp, Category.assoc, HomologicalComplex.d_comp_d, comp_zero,
        sub_zero, τ.comm]
    rw [← Category.assoc, he]
    exact hh 1 m le_rfl
  obtain ⟨l, hl⟩ := staircase_lift_bottom R I V y hw hd
  refine ⟨V, f, l, w, ?_⟩
  exact sub_eq_iff_eq_add.mp hl

private lemma staircaseBottom_refinement
    {F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} R)} (I : InjectiveResolution F)
    {U V : FiniteSplitEtaleHypercover X} (f : V.Refinement U) :
    staircaseBottom R I U ≫
        HomologicalComplex₂.total.map (staircaseMap R f I.cocomplex) (.up ℕ) =
      (sectionRefinement R f).app F ≫ staircaseBottom R I V := by
  apply HomologicalComplex.hom_ext
  intro n
  simp only [HomologicalComplex.comp_f, staircaseBottom,
    HomologicalComplex₂.toTotalOfAugmentation, Category.assoc,
    HomologicalComplex₂.ιTotal_map]
  have h := congrArg (fun g ↦ g ≫
    (staircase R V I.cocomplex).ιTotal (.up ℕ) 0 n n (by simp))
    ((I.ι.f 0).hom.naturality (f.app (op (SimplexCategory.mk n))).op)
  simp only [Category.assoc] at h
  convert h.symm using 1 <;> rfl

private lemma homologyπ_eq_of_boundary
    (K : CochainComplex (ModuleCat.{u + 1} R) ℕ) (n : ℕ)
    (z z' : K.cycles n) (b : K.X (n - 1))
    (h : K.iCycles n z = K.iCycles n z' + K.d (n - 1) n b) :
    K.homologyπ n z = K.homologyπ n z' := by
  have hh : z - z' = K.toCycles (n - 1) n b := by
    apply (ModuleCat.mono_iff_injective (K.iCycles n)).mp inferInstance
    rw [map_sub]
    have hb := ConcreteCategory.congr_hom (K.toCycles_i (n - 1) n) b
    change K.iCycles n (K.toCycles (n - 1) n b) = K.d (n - 1) n b at hb
    rw [hb]
    rw [h]
    abel
  have hp := congrArg (K.homologyπ n) hh
  rw [map_sub] at hp
  have hb := ConcreteCategory.congr_hom (K.toCycles_comp_homologyπ (n - 1) n) b
  change K.homologyπ n (K.toCycles (n - 1) n b) = 0 at hb
  rw [hb] at hp
  exact sub_eq_zero.mp hp

private lemma homology_boundary
    (K : CochainComplex (ModuleCat.{u + 1} R) ℕ) (n : ℕ)
    (z : K.cycles n) (hz : K.homologyπ n z = 0) :
    ∃ b : K.X (n - 1), K.d (n - 1) n b = K.iCycles n z := by
  let S := ShortComplex.mk (K.toCycles (n - 1) n) (K.homologyπ n)
    (K.toCycles_comp_homologyπ (n - 1) n)
  have hS : S.Exact := ShortComplex.exact_of_g_is_cokernel S
    (K.homologyIsCokernel (n - 1) n (by cases n <;> simp))
  obtain ⟨b, hb⟩ := (ShortComplex.moduleCat_exact_iff S).mp hS z hz
  refine ⟨b, ?_⟩
  have hh := congrArg (K.iCycles n) hb
  have hi := ConcreteCategory.congr_hom (K.toCycles_i (n - 1) n) b
  change K.iCycles n (K.toCycles (n - 1) n b) = K.d (n - 1) n b at hi
  exact hi.symm.trans hh

private theorem staircase_surjective
    {F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} R)}
    (I : InjectiveResolution F) (U : FiniteSplitEtaleHypercover X) (n : ℕ)
    (y : ((staircase R U I.cocomplex).total (.up ℕ)).homology n) :
    ∃ (V : FiniteSplitEtaleHypercover X) (f : V.Refinement U)
      (x : ((sectionComplexFunctor R V).obj F).homology n),
      HomologicalComplex.homologyMap (staircaseBottom R I V) n x =
        HomologicalComplex.homologyMap
          (HomologicalComplex₂.total.map (staircaseMap R f I.cocomplex) (.up ℕ)) n y := by
  classical
  let K := (staircase R U I.cocomplex).total (.up ℕ)
  obtain ⟨z, rfl⟩ := (ModuleCat.epi_iff_surjective (K.homologyπ n)).mp inferInstance y
  let a : ModuleCat.of R R ⟶ K.cycles n :=
    ModuleCat.ofHom (LinearMap.toSpanSingleton R _ z)
  let b := a ≫ K.iCycles n
  have hbd : b ≫ K.d n (n + 1) = 0 := by
    simp only [b, Category.assoc, HomologicalComplex.iCycles_d, comp_zero]
  obtain ⟨V, f, l, w, hl⟩ := exists_staircase_cochain R I U b (by
    rw [hbd]
    exact fun _ _ _ ↦ zero_comp)
  let L := (staircase R V I.cocomplex).total (.up ℕ)
  let C := (sectionComplexFunctor R V).obj F
  let τ := HomologicalComplex₂.total.map (staircaseMap R f I.cocomplex) (.up ℕ)
  let ε := staircaseBottom R I V
  have : Mono (ε.f (n + 1)) := staircaseBottom_mono R I V (n + 1)
  have hld : l ≫ C.d n (n + 1) = 0 := by
    rw [← cancel_mono (ε.f (n + 1)), zero_comp, Category.assoc, ← ε.comm]
    have hh := congrArg (fun g ↦ g ≫ L.d n (n + 1)) hl
    change (b ≫ τ.f n) ≫ L.d n (n + 1) =
      (l ≫ ε.f n + w ≫ L.d (n - 1) n) ≫ L.d n (n + 1) at hh
    have hτ : τ.f n ≫ L.d n (n + 1) = K.d n (n + 1) ≫ τ.f (n + 1) :=
      τ.comm n (n + 1)
    simp only [add_comp, Category.assoc, HomologicalComplex.d_comp_d, comp_zero,
      add_zero] at hh
    rw [hτ] at hh
    rw [← Category.assoc b, hbd, zero_comp] at hh
    exact hh.symm
  let c := C.liftCycles l (n + 1) (by simp) hld 1
  refine ⟨V, f, C.homologyπ n c, ?_⟩
  have he : L.homologyπ n (HomologicalComplex.cyclesMap ε n c) =
      L.homologyπ n (HomologicalComplex.cyclesMap τ n z) := by
    symm
    apply homologyπ_eq_of_boundary R L n _ _ (w 1)
    have hh := ConcreteCategory.congr_hom hl 1
    have hc := ConcreteCategory.congr_hom (C.liftCycles_i l (n + 1) (by simp) hld) 1
    have hτ := ConcreteCategory.congr_hom (HomologicalComplex.cyclesMap_i τ n) z
    have hε := ConcreteCategory.congr_hom (HomologicalComplex.cyclesMap_i ε n) c
    change L.iCycles n (HomologicalComplex.cyclesMap τ n z) = τ.f n (K.iCycles n z) at hτ
    change L.iCycles n (HomologicalComplex.cyclesMap ε n c) = ε.f n (C.iCycles n c) at hε
    change C.iCycles n c = l 1 at hc
    rw [hτ, hε, hc]
    change τ.f n (K.iCycles n (a 1)) = ε.f n (l 1) + L.d (n - 1) n (w 1) at hh
    rw [show a 1 = z from LinearMap.toSpanSingleton_apply_one R _ _] at hh
    exact hh
  have hε := ConcreteCategory.congr_hom (HomologicalComplex.homologyπ_naturality ε n) c
  have hτ := ConcreteCategory.congr_hom (HomologicalComplex.homologyπ_naturality τ n) z
  change HomologicalComplex.homologyMap ε n (C.homologyπ n c) =
    L.homologyπ n (HomologicalComplex.cyclesMap ε n c) at hε
  change HomologicalComplex.homologyMap τ n (K.homologyπ n z) =
    L.homologyπ n (HomologicalComplex.cyclesMap τ n z) at hτ
  exact hε.trans (he.trans hτ.symm)

private theorem staircase_kernel
    {F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} R)}
    (I : InjectiveResolution F) (U : FiniteSplitEtaleHypercover X) (n : ℕ)
    (x : ((sectionComplexFunctor R U).obj F).homology n)
    (hx : HomologicalComplex.homologyMap (staircaseBottom R I U) n x = 0) :
    ∃ (V : FiniteSplitEtaleHypercover X) (f : V.Refinement U),
      HomologicalComplex.homologyMap ((sectionRefinement R f).app F) n x = 0 := by
  classical
  let C := (sectionComplexFunctor R U).obj F
  let K := (staircase R U I.cocomplex).total (.up ℕ)
  let ε := staircaseBottom R I U
  obtain ⟨z, rfl⟩ := (ModuleCat.epi_iff_surjective (C.homologyπ n)).mp inferInstance x
  have hz : K.homologyπ n (HomologicalComplex.cyclesMap ε n z) = 0 := by
    have hh := ConcreteCategory.congr_hom (HomologicalComplex.homologyπ_naturality ε n) z
    change HomologicalComplex.homologyMap ε n (C.homologyπ n z) =
      K.homologyπ n (HomologicalComplex.cyclesMap ε n z) at hh
    exact hh.symm.trans hx
  obtain ⟨b, hb⟩ := homology_boundary R K n (HomologicalComplex.cyclesMap ε n z) hz
  have hε := ConcreteCategory.congr_hom (HomologicalComplex.cyclesMap_i ε n) z
  change K.iCycles n (HomologicalComplex.cyclesMap ε n z) = ε.f n (C.iCycles n z) at hε
  rw [hε] at hb
  cases n with
  | zero =>
    have hzb : ε.f 0 (C.iCycles 0 z) = 0 := by
      rw [← hb, HomologicalComplex.shape K 0 0 (by simp)]
      rfl
    have hm : Mono (ε.f 0) := staircaseBottom_mono R I U 0
    have hz₁ : C.iCycles 0 z = 0 :=
      (ModuleCat.mono_iff_injective (ε.f 0)).mp hm (hzb.trans (map_zero _).symm)
    have hz₂ : z = 0 := (ModuleCat.mono_iff_injective (C.iCycles 0)).mp
      inferInstance (hz₁.trans (map_zero _).symm)
    refine ⟨U, 𝟙 U.simplicial, ?_⟩
    rw [hz₂, map_zero, map_zero]
  | succ m =>
    change K.d m (m + 1) b = ε.f (m + 1) (C.iCycles (m + 1) z) at hb
    let a : ModuleCat.of R R ⟶ C.cycles (m + 1) :=
      ModuleCat.ofHom (LinearMap.toSpanSingleton R _ z)
    let x₀ := a ≫ C.iCycles (m + 1)
    let w₀ : ModuleCat.of R R ⟶ K.X m :=
      ModuleCat.ofHom (LinearMap.toSpanSingleton R _ b)
    have hbound : w₀ ≫ K.d m (m + 1) = x₀ ≫ ε.f (m + 1) := by
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro r
      change K.d m (m + 1) (r • b) = ε.f (m + 1) (C.iCycles (m + 1) (r • z))
      simp only [map_smul, hb]
    obtain ⟨V, f, l, w, hl⟩ := exists_staircase_cochain R I U w₀ (by
      rw [hbound]
      exact HomologicalComplex₂.vanishesFrom_toTotalOfAugmentation
        (staircase R U I.cocomplex) (staircaseAugmentation R I U)
        (staircaseAugmentation_d R I U) x₀)
    let D := (sectionComplexFunctor R V).obj F
    let L := (staircase R V I.cocomplex).total (.up ℕ)
    let δ := staircaseBottom R I V
    let τ := HomologicalComplex₂.total.map (staircaseMap R f I.cocomplex) (.up ℕ)
    let ρ := (sectionRefinement R f).app F
    have hm : Mono (δ.f (m + 1)) := staircaseBottom_mono R I V (m + 1)
    have hnat : ε.f (m + 1) ≫ τ.f (m + 1) = ρ.f (m + 1) ≫ δ.f (m + 1) :=
      congrArg (fun g ↦ g.f (m + 1)) (staircaseBottom_refinement R I f)
    have hd : x₀ ≫ ρ.f (m + 1) = l ≫ D.d m (m + 1) := by
      rw [← cancel_mono (δ.f (m + 1))]
      calc
        (x₀ ≫ ρ.f (m + 1)) ≫ δ.f (m + 1) =
            (w₀ ≫ K.d m (m + 1)) ≫ τ.f (m + 1) := by
          rw [hbound]
          simp only [Category.assoc, hnat]
        _ = (w₀ ≫ τ.f m) ≫ L.d m (m + 1) := by
          simpa only [Category.assoc] using
            (congrArg (fun g ↦ w₀ ≫ g) (τ.comm m (m + 1))).symm
        _ = (l ≫ D.d m (m + 1)) ≫ δ.f (m + 1) := by
          rw [hl]
          change (l ≫ δ.f m + w ≫ L.d (m - 1) m) ≫ L.d m (m + 1) = _
          simp only [add_comp, Category.assoc, HomologicalComplex.d_comp_d,
            comp_zero, add_zero]
          have hδ : δ.f m ≫ L.d m (m + 1) = D.d m (m + 1) ≫ δ.f (m + 1) :=
            δ.comm m (m + 1)
          rw [hδ]
    have hπ : D.homologyπ (m + 1) (HomologicalComplex.cyclesMap ρ (m + 1) z) = 0 := by
      have hh := homologyπ_eq_of_boundary R D (m + 1)
        (HomologicalComplex.cyclesMap ρ (m + 1) z) 0 (l 1) (by
          have hi := ConcreteCategory.congr_hom
            (HomologicalComplex.cyclesMap_i ρ (m + 1)) z
          change D.iCycles (m + 1) (HomologicalComplex.cyclesMap ρ (m + 1) z) =
            ρ.f (m + 1) (C.iCycles (m + 1) z) at hi
          rw [hi, map_zero, zero_add]
          have h := ConcreteCategory.congr_hom hd 1
          change ρ.f (m + 1) (C.iCycles (m + 1) (a 1)) = D.d m (m + 1) (l 1) at h
          rw [show a 1 = z from LinearMap.toSpanSingleton_apply_one R _ _] at h
          exact h)
      exact hh.trans (map_zero _)
    refine ⟨V, f, ?_⟩
    have hh := ConcreteCategory.congr_hom (HomologicalComplex.homologyπ_naturality ρ (m + 1)) z
    change HomologicalComplex.homologyMap ρ (m + 1) (C.homologyπ (m + 1) z) =
      D.homologyπ (m + 1) (HomologicalComplex.cyclesMap ρ (m + 1) z) at hh
    exact hh.trans hπ

private noncomputable def staircaseFlipIso (U : FiniteSplitEtaleHypercover X)
    (I : CochainComplex (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} R)) ℕ) :
    (staircase R U I).total (.up ℕ) ≅
      (resolutionDoubleComplex R U I).total (.up ℕ) := by
  unfold resolutionDoubleComplex
  exact ((staircase R U I).totalFlipIso (.up ℕ)).symm

private lemma staircaseBottom_flip
    {F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} R)}
    (I : InjectiveResolution F) (U : FiniteSplitEtaleHypercover X) :
    staircaseBottom R I U ≫ (staircaseFlipIso R U I.cocomplex).hom =
      bottomInclusion R U I := by
  unfold staircaseBottom staircaseFlipIso bottomInclusion resolutionDoubleComplex
  apply HomologicalComplex.hom_ext
  intro n
  dsimp only [id, Iso.symm_hom]
  simp only [HomologicalComplex.comp_f, HomologicalComplex₂.toTotalOfAugmentation,
    Category.assoc,
    HomologicalComplex₂.ιTotal_totalFlipIso_f_inv]
  have hs : ComplexShape.σ (.up ℕ) (.up ℕ) (.up ℕ) 0 n = 1 := by
    change (-1 : ℤˣ) ^ (0 * n) = 1
    simp
  rw [hs, one_smul]
  rfl

private lemma totalFlipIso_inv_naturality
    {K L : HomologicalComplex₂ (ModuleCat.{u + 1} R) (.up ℕ) (.up ℕ)}
    (φ : K ⟶ L) :
    HomologicalComplex₂.total.map φ (.up ℕ) ≫ (L.totalFlipIso (.up ℕ)).inv =
      (K.totalFlipIso (.up ℕ)).inv ≫ HomologicalComplex₂.total.map
        ((HomologicalComplex₂.flipFunctor _ _ _).map φ) (.up ℕ) := by
  apply HomologicalComplex.hom_ext
  intro n
  apply HomologicalComplex₂.total.hom_ext
  intro p q hpq
  simp only [HomologicalComplex.comp_f,
    HomologicalComplex₂.ιTotal_map_assoc,
    HomologicalComplex₂.ιTotal_totalFlipIso_f_inv_assoc,
    HomologicalComplex₂.ιTotal_totalFlipIso_f_inv,
    Linear.comp_units_smul, Linear.units_smul_comp,
    HomologicalComplex₂.ιTotal_map]
  rfl

private lemma staircaseFlipIso_refinement
    {U V : FiniteSplitEtaleHypercover X} (f : V.Refinement U)
    (I : CochainComplex (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} R)) ℕ) :
    HomologicalComplex₂.total.map (staircaseMap R f I) (.up ℕ) ≫
        (staircaseFlipIso R V I).hom =
      (staircaseFlipIso R U I).hom ≫ totalRefinement R f I := by
  unfold staircaseFlipIso totalRefinement resolutionDoubleComplex
  exact totalFlipIso_inv_naturality R (staircaseMap R f I)

/-- Bottom-row inclusion becomes an isomorphism on cohomology after finite refinement.
Source: Stacks Project, Hypercoverings, Tag 01H0, first proof, finite cocycle corrections.
(blueprint: lem-sc-hypercover-bottom-refinement-descent).

Proof: use the resolution degree as the vertical degree. For a total q-cocycle, start
with its component of largest positive resolution degree. The total-cycle equation
says this component is a vertical cocycle. Exactness of the injective resolution as
sheaves gives a covering sieve on which this component is a vertical boundary. Solve
the finitely many lifting requirements on a finite split refinement, using
exists_refinement_primitive. This theorem supplies primitives on the whole
refined term by sheaf gluing over its disjoint constituents. Subtract their total differential, with
the total-complex sign in that bidegree. This removes the chosen component, and creates
terms only in smaller resolution degree. Repeat at most q times, composing the
refinements. The last component lies in the kernel of I^0 → I^1, hence lifts uniquely
to F; its horizontal differential is zero because F → I^0 is monic. This proves the
first assertion, including q = 0, where the unique kernel lift is the only step.
For the second assertion, represent the vanishing total class by a total boundary.
If q = 0 there is no preceding total term, and the monomorphism F → I^0 makes the
original cocycle zero. If q > 0, apply the same descending corrections to a bounding
total (q-1)-cochain. Its total differential is in the bottom row, so every equation
above that row is the vertical cocycle equation needed for the next correction.
After finitely many refinements the bounding cochain itself lies in the image of F.
Its differential is the refined original cocycle, proving that class zero.
Only degrees through q+1 and finitely many lifting conditions are used. The zero ring,
zero sheaf, and empty base require no nonempty family of constituent pieces. -/
theorem bottom_refinement_descent {X : Scheme.{u}} [CompactSpace X]
    [QuasiSeparatedSpace X] (R : Type (u + 1)) [Ring R]
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} R)) (I : InjectiveResolution F)
    (U : FiniteSplitEtaleHypercover X) (q : ℕ) :
    (∀ y : ((resolutionDoubleComplex R U I.cocomplex).total (.up ℕ)).homology q,
      ∃ (V : FiniteSplitEtaleHypercover X) (f : V.Refinement U)
        (x : ((sectionComplexFunctor R V).obj F).homology q),
      HomologicalComplex.homologyMap (bottomInclusion R V I) q x =
        HomologicalComplex.homologyMap (totalRefinement R f I.cocomplex) q y) ∧
    (∀ x : ((sectionComplexFunctor R U).obj F).homology q,
      HomologicalComplex.homologyMap (bottomInclusion R U I) q x = 0 →
      ∃ (V : FiniteSplitEtaleHypercover X) (f : V.Refinement U),
        (cohomologyRefinement (ModuleCat R) f q).app F x = 0) := by
  classical
  let H := HomologicalComplex.homologyFunctor (ModuleCat.{u + 1} R) (.up ℕ) q
  have hb (V : FiniteSplitEtaleHypercover X) :
      H.map (staircaseBottom R I V) ≫ H.map (staircaseFlipIso R V I.cocomplex).hom =
        H.map (bottomInclusion R V I) := by
    rw [← Functor.map_comp, staircaseBottom_flip]
  constructor
  · intro y
    obtain ⟨V, f, x, hx⟩ := staircase_surjective R I U q
      (H.map (staircaseFlipIso R U I.cocomplex).inv y)
    refine ⟨V, f, x, ?_⟩
    change H.map (staircaseBottom R I V) x =
      H.map (HomologicalComplex₂.total.map (staircaseMap R f I.cocomplex) (.up ℕ))
        (H.map (staircaseFlipIso R U I.cocomplex).inv y) at hx
    change H.map (bottomInclusion R V I) x = H.map (totalRefinement R f I.cocomplex) y
    have hs : H.map (staircaseFlipIso R U I.cocomplex).inv ≫
        H.map (HomologicalComplex₂.total.map (staircaseMap R f I.cocomplex) (.up ℕ)) ≫
          H.map (staircaseFlipIso R V I.cocomplex).hom =
        H.map (totalRefinement R f I.cocomplex) := by
      rw [← Functor.map_comp, staircaseFlipIso_refinement, Functor.map_comp,
        ← Category.assoc, ← Functor.map_comp, Iso.inv_hom_id,
        H.map_id, Category.id_comp]
    have hh := ConcreteCategory.congr_hom hs y
    change H.map (staircaseFlipIso R V I.cocomplex).hom
      (H.map (HomologicalComplex₂.total.map (staircaseMap R f I.cocomplex) (.up ℕ))
        (H.map (staircaseFlipIso R U I.cocomplex).inv y)) =
      H.map (totalRefinement R f I.cocomplex) y at hh
    have hv := ConcreteCategory.congr_hom (hb V) x
    change H.map (staircaseFlipIso R V I.cocomplex).hom
      (H.map (staircaseBottom R I V) x) = H.map (bottomInclusion R V I) x at hv
    exact hv.symm.trans ((congrArg (H.map (staircaseFlipIso R V I.cocomplex).hom) hx).trans hh)
  · intro x hx
    have hx' : H.map (staircaseBottom R I U) x = 0 := by
      have : IsIso (H.map (staircaseFlipIso R U I.cocomplex).hom) := inferInstance
      apply (ModuleCat.mono_iff_injective
        (H.map (staircaseFlipIso R U I.cocomplex).hom)).mp inferInstance
      rw [← ModuleCat.comp_apply, hb U]
      exact hx.trans (map_zero _).symm
    obtain ⟨V, f, hf⟩ := staircase_kernel R I U q x hx'
    exact ⟨V, f, hf⟩

end AlgebraicGeometry.FiniteSplitEtaleHypercover
