/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CoefficientSequenceCoinducedComplexes
import Mathlib.CategoryTheory.Limits.Types.Limits
import Mathlib.Algebra.Homology.HomologicalComplexLimits

/-! # Epimorphy of the ordinary coinduced difference

Source: Stacks 0941, with the explicit downward recursion for finite prefixes.
(blueprint: lem-coef-sequence-coinduced-difference-epi).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
namespace WeilConjectures.CoefficientCoinduction

attribute [local irreducible] constantSheaf presheafToSheaf

section ProductSections
universe c cv w
variable {C : Type c} [Category.{cv} C] (F : C ⥤ Type w)
  [PreservesLimitsOfShape (Discrete ℕ) F]

private theorem product_sections (X : ℕ → C) [HasProduct X]
    (x : ∀ n, F.obj (X n)) :
    ∃ y : F.obj (∏ᶜ X), ∀ n, F.map (Pi.π X n) y = x n := by
  let c := F.mapCone (limit.cone (Discrete.functor X))
  let h : IsLimit c := isLimitOfPreserves F (limit.isLimit (Discrete.functor X))
  let s : (Discrete.functor X ⋙ F).sections := ⟨fun n ↦ x n.as, by
    intro i j f
    discrete_cases
    cases f
    simp⟩
  refine ⟨(Types.isLimitEquivSections h).symm s, ?_⟩
  intro n
  exact Types.isLimitEquivSections_symm_apply h s ⟨n⟩

private theorem product_sections_ext (X : ℕ → C) [HasProduct X]
    (x y : F.obj (∏ᶜ X))
    (h : ∀ n, F.map (Pi.π X n) x = F.map (Pi.π X n) y) : x = y := by
  apply (Types.isLimitEquivSections
    (isLimitOfPreserves F (limit.isLimit (Discrete.functor X)))).injective
  apply Subtype.ext
  funext n
  exact h n.as

end ProductSections

private theorem descending_lifts (A : ℕ → Type*) [∀ n, AddCommGroup (A n)]
    (t : ∀ n, A (n + 1) → A n) (y : ∀ n, A n) (m : ℕ) (b : A m) :
    ∃ x : ∀ n, A n, x m = b ∧ ∀ n, n < m → t n (x (n + 1)) - x n = y n := by
  induction m with
  | zero =>
    exact ⟨fun n ↦ if h : n = 0 then h.symm ▸ b else 0,
      by simp, fun n h ↦ (Nat.not_lt_zero n h).elim⟩
  | succ m ih =>
    obtain ⟨x, hx, he⟩ := ih (t m b - y m)
    let z : ∀ n, A n := fun n ↦ if h : n = m + 1 then h.symm ▸ b else x n
    refine ⟨z, by simp [z], ?_⟩
    intro n hn
    by_cases hnm : n = m
    · subst n
      simp only [z, dif_pos rfl, dif_neg (by omega : m ≠ m + 1), hx]
      exact sub_sub_cancel _ _
    · have hn' : n < m := by omega
      simpa only [z, dif_neg (by omega : n + 1 ≠ m + 1),
        dif_neg (by omega : n ≠ m + 1)] using he n hn'

private theorem homEquiv_degree {A B : Type*} [Category A] [Category B]
    [Preadditive A] [Preadditive B] {L : A ⥤ B} {R : B ⥤ A}
    (adj : L ⊣ R) [L.Additive] [R.Additive]
    (X : CochainComplex A ℤ) (Y : CochainComplex B ℤ)
    (f : (L.mapHomologicalComplex (.up ℤ)).obj X ⟶ Y) (q : ℤ) :
    ((adj.mapHomologicalComplex (.up ℤ)).homEquiv X Y f).f q =
      adj.homEquiv (X.X q) (Y.X q) (f.f q) := rfl

private theorem homEquiv_degree_apply {A B : Type*} [Category A] [Category B]
    [Preadditive A] [Preadditive B] {L : A ⥤ B} {R : B ⥤ A}
    (adj : L ⊣ R) [L.Additive] [R.Additive]
    (X : CochainComplex A ℤ) (Y : CochainComplex B ℤ)
    (f : (L.mapHomologicalComplex (.up ℤ)).obj X ⟶ Y) (q : ℤ)
    {α β : Type*} (F : (X.X q ⟶ R.obj (Y.X q)) → α → β) (x : α) :
    F (((adj.mapHomologicalComplex (.up ℤ)).homEquiv X Y f).f q) x =
      F (adj.homEquiv (X.X q) (Y.X q) (f.f q)) x := by
  rw [homEquiv_degree]

universe c₁ v₁ r₁

private def above_sections {C : Type c₁} [Category.{v₁} C]
    {J : GrothendieckTopology C}
    [J.HasSheafCompose (forget₂ CommRingCat.{r₁} RingCat.{r₁})]
    [J.WEqualsLocallyBijective AddCommGrpCat.{r₁}] [HasSheafify J AddCommGrpCat.{r₁}]
    (B : ℕᵒᵖ ⥤ Sheaf J CommRingCat.{r₁}) (n m : ℕ) (hn : n ≤ m)
    (M : SheafOfModules.systemLevel B n) (U : Cᵒᵖ) :
    (SheafOfModules.SequenceCoinduced.rightLevel B n M m).val.obj U ≃ M.val.obj U :=
  ((forget _).mapIso ((SheafOfModules.evaluation _ U).mapIso
    (SheafOfModules.SequenceCoinduced.rightAboveIso B n M hn))).toEquiv

set_option maxHeartbeats 400000 in
-- Reduce scalar restriction only in this generic section computation.
private theorem transported_transpose {C : Type c₁} [Category.{v₁} C]
    {J : GrothendieckTopology C} [EssentiallySmall.{r₁} C]
    [J.HasSheafCompose (forget₂ CommRingCat.{r₁} RingCat.{r₁})]
    [J.WEqualsLocallyBijective AddCommGrpCat.{r₁}] [HasSheafify J AddCommGrpCat.{r₁}]
    (B : ℕᵒᵖ ⥤ Sheaf J CommRingCat.{r₁}) (n m : ℕ) (hn : n ≤ m)
    (X : SheafOfModules.systemSequenceModules B) (M : SheafOfModules.systemLevel B n)
    (f : ((SheafOfModules.strictSystemSequenceEquivalence B).inverse ⋙
      SheafOfModules.systemEvaluation B n).obj X ⟶ M)
    (U : Cᵒᵖ) (x : X.val.obj (op (m, U.unop))) :
    above_sections B n m hn M U
      (((((SheafOfModules.strictSystemSequenceEquivalence B).symm.toAdjunction.comp
        (SheafOfModules.SequenceCoinduced.adjunction B n)).homEquiv X M f).val.app
          (op (m, U.unop))) x) =
      f.val.app U (X.val.map (Prod.mkHom (homOfLE hn) (𝟙 U.unop)).op x) := by
  rw [Adjunction.comp_homEquiv]
  dsimp only [SheafOfModules.SequenceCoinduced.adjunction]
  rw [Adjunction.mkOfHomEquiv_homEquiv]
  change ((SheafOfModules.SequenceCoinduced.coextendApp B n
      ((SheafOfModules.strictSystemSequenceEquivalence B).inverse.obj X) M f m) ≫
        (SheafOfModules.SequenceCoinduced.rightAboveIso B n M hn).hom
      ).val.app U x = _
  erw [SheafOfModules.SequenceCoinduced.coextendApp_above B n
    ((SheafOfModules.strictSystemSequenceEquivalence B).inverse.obj X) M f hn]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rfl

section GeneralSystem
variable {C : Type c₁} [Category.{v₁} C]
    {J : GrothendieckTopology C} [EssentiallySmall.{r₁} C]
    [J.HasSheafCompose (forget₂ CommRingCat.{r₁} RingCat.{r₁})]
    [J.WEqualsLocallyBijective AddCommGrpCat.{r₁}] [HasSheafify J AddCommGrpCat.{r₁}]
    [HasSheafify (coefficientSequenceTopology J) AddCommGrpCat.{r₁}]
    [(coefficientSequenceTopology J).WEqualsLocallyBijective AddCommGrpCat.{r₁}]
    (B : ℕᵒᵖ ⥤ Sheaf J CommRingCat.{r₁})

private abbrev evalB (n : ℕ) :=
  (SheafOfModules.strictSystemSequenceEquivalence B).inverse ⋙
    SheafOfModules.systemEvaluation B n
private abbrev rightB (n : ℕ) :=
  SheafOfModules.SequenceCoinduced.rightExtension B n ⋙
    (SheafOfModules.strictSystemSequenceEquivalence B).functor
private instance inverseB_additive :
    (SheafOfModules.strictSystemSequenceEquivalence B).symm.functor.Additive := by
  change (SheafOfModules.sequenceToStrictSystemFunctor B).Additive
  infer_instance

private instance evalB_additive (n : ℕ) : (evalB B n).Additive := by
  change (SheafOfModules.sequenceToStrictSystemFunctor B ⋙
    SheafOfModules.systemEvaluation B n).Additive
  infer_instance

private instance rightB_additive (n : ℕ) : (rightB B n).Additive := by
  change (SheafOfModules.SequenceCoinduced.rightExtension B n ⋙
    SheafOfModules.strictSystemToSequenceFunctor B).Additive
  infer_instance

private abbrev adjB (n : ℕ) : evalB B n ⊣ rightB B n :=
  (SheafOfModules.strictSystemSequenceEquivalence B).symm.toAdjunction.comp
    (SheafOfModules.SequenceCoinduced.adjunction B n)
private abbrev ce (n : ℕ) := (evalB B n).mapHomologicalComplex (.up ℤ)
private abbrev cr (n : ℕ) := (rightB B n).mapHomologicalComplex (.up ℤ)
private abbrev ca (n : ℕ) := (adjB B n).mapHomologicalComplex (.up ℤ)

variable (φ : ∀ n, SheafOfModules.derivedChangeRingIndependentCoefficients J
      (B.obj (op (n + 1))) ⟶
    SheafOfModules.derivedChangeRingIndependentCoefficients J (B.obj (op n)))
private abbrev resB (n : ℕ) :
    SheafOfModules.systemLevel B n ⥤ SheafOfModules.systemLevel B (n + 1) :=
  SheafOfModules.restrictScalars.{r₁} (φ n)
private abbrev cs (n : ℕ) := (resB B φ n).mapHomologicalComplex (.up ℤ)
private abbrev ct
    (T : ∀ n, evalB B (n + 1) ⟶ evalB B n ⋙ resB B φ n) (n : ℕ) :
    ce B (n + 1) ⟶ ce B n ⋙ cs B φ n :=
  (T n).mapHomologicalComplex (.up ℤ)
variable [HasCountableProducts (CochainComplex (SheafOfModules.systemSequenceModules B) ℤ)]
private abbrev cp (K : CochainComplex (SheafOfModules.systemSequenceModules B) ℤ) :=
  CoinducedSequence.product (ce B) (cr B) K
private abbrev cd
    (T : ∀ n, evalB B (n + 1) ⟶ evalB B n ⋙ resB B φ n)
    (K : CochainComplex (SheafOfModules.systemSequenceModules B) ℤ) :=
  CoinducedSequence.difference (ce B) (cr B) (ca B) (cs B φ) (ct B φ T) K

private abbrev right_section_equivB (n m : ℕ) (hn : n ≤ m)
    (M : SheafOfModules.systemLevel B n) (U : Cᵒᵖ) := above_sections B n m hn M U

private theorem right_section_subsingleton (n m : ℕ) (hn : m < n)
    (M : SheafOfModules.systemLevel B n) (U : Cᵒᵖ) :
    Subsingleton (((rightB B n).obj M).val.obj (op (m, U.unop))) := by
  change Subsingleton ((SheafOfModules.SequenceCoinduced.rightLevel
    (B) n M m).val.obj U)
  dsimp only [SheafOfModules.SequenceCoinduced.rightLevel]
  rw [dif_neg (by omega : ¬ n ≤ m)]
  exact ModuleCat.subsingleton_of_isZero
    ((SheafOfModules.evaluation _ U).map_isZero (isZero_zero _))

private theorem transpose_section (n m : ℕ) (hn : n ≤ m)
    (X : SheafOfModules.systemSequenceModules B) (M : SheafOfModules.systemLevel B n)
    (f : (evalB B n).obj X ⟶ M)
    (U : Cᵒᵖ) (x : X.val.obj (op (m, U.unop))) :
    above_sections B n m hn M U
      (((adjB B n).homEquiv X M f).val.app (op (m, U.unop)) x) =
      f.val.app U (X.val.map (Prod.mkHom (homOfLE hn) (𝟙 U.unop)).op x) :=
  transported_transpose B n m hn X M f U x

set_option maxHeartbeats 800000 in
-- Section identifications reduce through the transported functors.
private theorem complex_transpose_section (n m : ℕ) (hn : n ≤ m)
    (X : CochainComplex (SheafOfModules.systemSequenceModules B) ℤ)
    (M : CochainComplex (SheafOfModules.systemLevel B n) ℤ)
    (f : (ce B n).obj X ⟶ M) (q : ℤ)
    (U : Cᵒᵖ) (x : (X.X q).val.obj (op (m, U.unop))) :
    right_section_equivB B n m hn (M.X q) U
      ((((ca B n).homEquiv X M f).f q).val.app
        (op (m, U.unop)) x) =
      (f.f q).val.app U ((X.X q).val.map
        (Prod.mkHom (homOfLE hn) (𝟙 U.unop)).op x) := by
  dsimp only [ca]
  have h := homEquiv_degree_apply (adjB B n) X M f q
    (fun (g : X.X q ⟶ (rightB B n).obj (M.X q))
      (z : (X.X q).val.obj (op (m, U.unop))) ↦
        right_section_equivB B n m hn (M.X q) U
          (g.val.app (op (m, U.unop)) z)) x
  exact h.trans (transpose_section B n m hn (X.X q) (M.X q) (f.f q) U x)

private def coordinate
    (K : CochainComplex (SheafOfModules.systemSequenceModules B) ℤ)
    (q : ℤ) (m : ℕ) (U : Cᵒᵖ)
    (x : ((cp B K).X q).val.obj (op (m, U.unop)))
    (n : ℕ) (hn : n ≤ m) : (K.X q).val.obj (op (n, U.unop)) :=
  right_section_equivB B n m hn
    (((ce B n).obj K).X q) U
      (((Pi.π (fun n ↦ (cr B n).obj
        ((ce B n).obj K)) n).f q).val.app (op (m, U.unop)) x)

set_option maxHeartbeats 800000 in
-- Section identifications reduce through the transported functors.
private theorem component_section
    (K : CochainComplex (SheafOfModules.systemSequenceModules B) ℤ)
    (q : ℤ) (m : ℕ) (U : Cᵒᵖ)
    (x : ((cp B K).X q).val.obj (op (m, U.unop)))
    (n : ℕ) (hn : n ≤ m) :
    ((CoinducedSequence.components (ce B) (cr B)
      (ca B) (𝟙 (cp B K)) n).f q).val.app U
        (((cp B K).X q).val.map
          (Prod.mkHom (homOfLE hn) (𝟙 U.unop)).op x) =
      coordinate B K q m U x n hn := by
  dsimp only [coordinate]
  let p := Pi.π (fun k ↦ (cr B k).obj
    ((ce B k).obj K)) n
  dsimp only [CoinducedSequence.components]
  erw [Category.id_comp]
  have h := complex_transpose_section B n m hn (cp B K)
    ((ce B n).obj K)
    (((ca B n).homEquiv (cp B K)
      ((ce B n).obj K)).symm p) q U x
  have hp := congrArg
    (fun (g : cp B K ⟶ (cr B n).obj ((ce B n).obj K)) ↦
      right_section_equivB B n m hn (((ce B n).obj K).X q) U
        ((g.f q).val.app (op (m, U.unop)) x))
    (((ca B n).homEquiv (cp B K) ((ce B n).obj K)).apply_symm_apply p)
  exact h.symm.trans hp

set_option maxHeartbeats 800000 in
-- Section identifications reduce through the transported functors.
private theorem difference_coordinate
    (φ : ∀ n, SheafOfModules.derivedChangeRingIndependentCoefficients J
        (B.obj (op (n + 1))) ⟶
      SheafOfModules.derivedChangeRingIndependentCoefficients J (B.obj (op n)))
    (T : ∀ n, evalB B (n + 1) ⟶ evalB B n ⋙ resB B φ n)
    (hT : ∀ (N : SheafOfModules.systemSequenceModules B) (n : ℕ) (U : Cᵒᵖ)
        (x : N.val.obj (op (n + 1, U.unop))),
      ((T n).app N).val.app U x =
        N.val.map (Prod.mkHom (homOfLE (Nat.le_succ n)) (𝟙 U.unop)).op x)
    (K : CochainComplex (SheafOfModules.systemSequenceModules B) ℤ)
    (q : ℤ) (m : ℕ) (U : Cᵒᵖ)
    (x : ((cp B K).X q).val.obj (op (m, U.unop)))
    (n : ℕ) (hn : n < m) :
    right_section_equivB B (n + 1) m hn
      (((cs B φ n).obj ((ce B n).obj K)).X q) U
      (((Pi.π (fun n ↦ (cr B (n + 1)).obj
          ((cs B φ n).obj ((ce B n).obj K))) n
        ).f q).val.app (op (m, U.unop))
          (((cd B φ T K).f q).val.app (op (m, U.unop)) x)) =
      (show (K.X q).val.obj (op (n, U.unop)) from
        (K.X q).val.map (Prod.mkHom (homOfLE (Nat.le_succ n)) (𝟙 U.unop)).op
          (coordinate B K q m U x (n + 1) hn)) -
      coordinate B K q m U x n (Nat.le_of_lt hn) := by
  let A := cp B K
  let c := CoinducedSequence.components (ce B) (cr B)
    (ca B) (𝟙 A)
  change right_section_equivB B (n + 1) m hn _ U
    ((((cd B φ T K ≫ Pi.π _ n).f q).val.app
      (op (m, U.unop))) x) = _
  have hp : cd B φ T K ≫ Pi.π _ n =
      (ca B (n + 1)).homEquiv _ _
        ((show (ce B (n + 1)).obj A ⟶
            (cs B φ n).obj ((ce B n).obj K) from
          c (n + 1) ≫ (ct B φ T n).app K) -
          (ct B φ T n).app A ≫ (cs B φ n).map (c n)) := by
    dsimp only [cd, CoinducedSequence.difference]
    exact Pi.lift_π _ n
  erw [hp]
  erw [complex_transpose_section]
  change (show (K.X q).val.obj (op (n, U.unop)) from
    ((T n).app (K.X q)).val.app U
      (((c (n + 1)).f q).val.app U ((A.X q).val.map
        (Prod.mkHom (homOfLE hn) (𝟙 U.unop)).op x))) -
    (show (K.X q).val.obj (op (n, U.unop)) from ((c n).f q).val.app U
      (((T n).app (A.X q)).val.app U
        ((A.X q).val.map (Prod.mkHom (homOfLE hn) (𝟙 U.unop)).op x))) = _
  have hK := hT (K.X q) n U (((c (n + 1)).f q).val.app U
    ((A.X q).val.map (Prod.mkHom (homOfLE hn) (𝟙 U.unop)).op x))
  have hA := hT (A.X q) n U
    ((A.X q).val.map (Prod.mkHom (homOfLE hn) (𝟙 U.unop)).op x)
  rw [hK, hA]
  have hh := (SheafOfModules.sequenceToStrictSystem (B) (A.X q)).compose
    (Nat.le_succ n) hn U x
  change (A.X q).val.map
      (Prod.mkHom (homOfLE (Nat.le_of_lt hn)) (𝟙 U.unop)).op x =
    (A.X q).val.map (Prod.mkHom (homOfLE (Nat.le_succ n)) (𝟙 U.unop)).op
      ((A.X q).val.map (Prod.mkHom (homOfLE hn) (𝟙 U.unop)).op x) at hh
  rw [← hh]
  rw [show ((c (n + 1)).f q).val.app U
      ((A.X q).val.map (Prod.mkHom (homOfLE hn) (𝟙 U.unop)).op x) =
        coordinate B K q m U x (n + 1) hn from
      component_section B K q m U x (n + 1) hn]
  rw [show ((c n).f q).val.app U
      ((A.X q).val.map (Prod.mkHom (homOfLE (Nat.le_of_lt hn)) (𝟙 U.unop)).op x) =
        coordinate B K q m U x n (Nat.le_of_lt hn) from
      component_section B K q m U x n (Nat.le_of_lt hn)]

private abbrev sectionEvaluation (q : ℤ) (V : (ℕ × C)ᵒᵖ) :
    CochainComplex (SheafOfModules.systemSequenceModules B) ℤ ⥤ Type r₁ :=
  HomologicalComplex.eval _ (.up ℤ) q ⋙ SheafOfModules.evaluation _ V ⋙ forget _

set_option maxHeartbeats 800000 in
-- Section identifications reduce through the transported functors.
private theorem difference_surjective
    (φ : ∀ n, SheafOfModules.derivedChangeRingIndependentCoefficients J
        (B.obj (op (n + 1))) ⟶
      SheafOfModules.derivedChangeRingIndependentCoefficients J (B.obj (op n)))
    (T : ∀ n, evalB B (n + 1) ⟶ evalB B n ⋙ resB B φ n)
    (hT : ∀ (N : SheafOfModules.systemSequenceModules B) (n : ℕ) (U : Cᵒᵖ)
        (x : N.val.obj (op (n + 1, U.unop))),
      ((T n).app N).val.app U x =
        N.val.map (Prod.mkHom (homOfLE (Nat.le_succ n)) (𝟙 U.unop)).op x)
    (K : CochainComplex (SheafOfModules.systemSequenceModules B) ℤ)
    (q : ℤ) (m : ℕ) (U : Cᵒᵖ) :
    Function.Surjective (((cd B φ T K).f q).val.app (op (m, U.unop))) := by
  intro y
  let P := fun n ↦ (cr B n).obj ((ce B n).obj K)
  let Q := fun n ↦ (cr B (n + 1)).obj
    ((cs B φ n).obj ((ce B n).obj K))
  let F := sectionEvaluation B q (op (m, U.unop))
  let a : ℕ → Type r₁ := fun n ↦ (K.X q).val.obj (op (n, U.unop))
  let t : ∀ n, a (n + 1) → a n := fun n ↦
    (K.X q).val.map (Prod.mkHom (homOfLE (Nat.le_succ n)) (𝟙 U.unop)).op
  let v : ∀ n, a n := fun n ↦ if hn : n < m then
    right_section_equivB B (n + 1) m hn
      (((cs B φ n).obj ((ce B n).obj K)).X q) U
        (((Pi.π Q n).f q).val.app (op (m, U.unop)) y) else 0
  obtain ⟨z, _, hz⟩ := descending_lifts a t v m 0
  let w : ∀ n, F.obj (P n) := fun n ↦ if hn : n ≤ m then
    (right_section_equivB B n m hn
      (((ce B n).obj K).X q) U).symm (z n) else
      (0 : ((P n).X q).val.obj (op (m, U.unop)))
  obtain ⟨x, hx⟩ := product_sections F P w
  refine ⟨x, ?_⟩
  apply product_sections_ext F Q
  intro n
  by_cases hn : n < m
  · apply (right_section_equivB B (n + 1) m hn
      (((cs B φ n).obj ((ce B n).obj K)).X q)
        U).injective
    change right_section_equivB B (n + 1) m hn _ U
      (((Pi.π Q n).f q).val.app (op (m, U.unop))
        (((cd B φ T K).f q).val.app (op (m, U.unop)) x)) = _
    erw [difference_coordinate B φ T hT K q m U x n hn]
    have hc (k : ℕ) (hk : k ≤ m) : coordinate B K q m U x k hk = z k := by
      dsimp only [coordinate]
      change right_section_equivB B k m hk _ U (F.map (Pi.π P k) x) = z k
      rw [hx]
      have hw : w k = (right_section_equivB B k m hk
          (((ce B k).obj K).X q) U).symm (z k) := by
        exact dif_pos hk
      exact (congrArg (right_section_equivB B k m hk
        (((ce B k).obj K).X q) U) hw).trans (Equiv.apply_symm_apply _ _)
    rw [hc (n + 1) hn, hc n (Nat.le_of_lt hn)]
    change t n (z (n + 1)) - z n =
      right_section_equivB B (n + 1) m hn
        (((cs B φ n).obj ((ce B n).obj K)).X q) U
          (((Pi.π Q n).f q).val.app (op (m, U.unop)) y)
    have hv : v n = right_section_equivB B (n + 1) m hn
        (((cs B φ n).obj ((ce B n).obj K)).X q) U
          (((Pi.π Q n).f q).val.app (op (m, U.unop)) y) := by
      exact dif_pos hn
    exact (hz n hn).trans hv
  · have hs := right_section_subsingleton B (n + 1) m (by omega)
      (((cs B φ n).obj ((ce B n).obj K)).X q) U
    exact hs.elim _ _

private theorem general_difference_epi
    (φ : ∀ n, SheafOfModules.derivedChangeRingIndependentCoefficients J
        (B.obj (op (n + 1))) ⟶
      SheafOfModules.derivedChangeRingIndependentCoefficients J (B.obj (op n)))
    (T : ∀ n, evalB B (n + 1) ⟶ evalB B n ⋙ resB B φ n)
    (hT : ∀ (N : SheafOfModules.systemSequenceModules B) (n : ℕ) (U : Cᵒᵖ)
        (x : N.val.obj (op (n + 1, U.unop))),
      ((T n).app N).val.app U x =
        N.val.map (Prod.mkHom (homOfLE (Nat.le_succ n)) (𝟙 U.unop)).op x)
    (K : CochainComplex (SheafOfModules.systemSequenceModules B) ℤ) :
    Epi (cd B φ T K) := by
  constructor
  intro L a b hab
  apply HomologicalComplex.Hom.ext
  funext q
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro V
  ext y
  obtain ⟨x, hx⟩ := difference_surjective B φ T hT K q V.unop.1 (op V.unop.2) y
  have hh := congrArg (fun f ↦ ((f.f q).val.app V) x) hab
  change (a.f q).val.app V (((cd B φ T K).f q).val.app V x) =
    (b.f q).val.app V (((cd B φ T K).f q).val.app V x) at hh
  rw [hx] at hh
  exact hh

private theorem identified_difference_epi
    (φ : ∀ n, SheafOfModules.derivedChangeRingIndependentCoefficients J
        (B.obj (op (n + 1))) ⟶
      SheafOfModules.derivedChangeRingIndependentCoefficients J (B.obj (op n)))
    (G : ∀ n, SheafOfModules.systemSequenceModules B ⥤ SheafOfModules.systemLevel B n)
    [Gadd : ∀ n, (G n).Additive]
    (hG : ∀ n, evalB B n = G n)
    (t : ∀ n, G (n + 1) ⟶ G n ⋙ resB B φ n)
    (ht : ∀ (N : SheafOfModules.systemSequenceModules B) (n : ℕ) (U : Cᵒᵖ),
      HEq (fun x : ((G (n + 1)).obj N).val.obj U ↦
        ((t n).app N).val.app U x)
      (fun x : N.val.obj (op (n + 1, U.unop)) ↦
        N.val.map (Prod.mkHom (homOfLE (Nat.le_succ n)) (𝟙 U.unop)).op x))
    (K : CochainComplex (SheafOfModules.systemSequenceModules B) ℤ) :
    Epi (CoinducedSequence.difference
      (fun n ↦ (G n).mapHomologicalComplex (.up ℤ)) (cr B)
      (fun n ↦ ((adjB B n).ofNatIsoLeft (eqToIso (hG n))).mapHomologicalComplex (.up ℤ))
      (cs B φ) (fun n ↦ (t n).mapHomologicalComplex (.up ℤ)) K) := by
  have hh : evalB B = G := funext hG
  subst G
  have ha (n : ℕ) : (adjB B n).ofNatIsoLeft (eqToIso (hG n)) = adjB B n := by
    apply Adjunction.ext
    simp
  have haa : (fun n ↦ ((adjB B n).ofNatIsoLeft (eqToIso (hG n))).mapHomologicalComplex
      (.up ℤ)) = ca B := by
    funext n
    rw [ha]
  rw [haa]
  apply general_difference_epi B φ t
  intro N n U x
  exact congrFun (eq_of_heq (ht N n U)) x

end GeneralSystem

private theorem conjugate_apply
    {A B A' B' : AddCommGrpCat.{u}} (hA : A = A') (hB : B = B')
    (f : A ⟶ B) (g : A' ⟶ B')
    (h : eqToHom hA.symm ≫ f ≫ eqToHom hB = g)
    (x : A) (y : A') (hxy : HEq x y) : HEq (f x) (g y) := by
  subst A' B'
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id] at h
  subst g
  have hx : x = y := eq_of_heq hxy
  subst y
  rfl

set_option maxHeartbeats 400000 in
-- The concrete coefficient ring identifications require extra reduction.
private theorem transition_section
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (W : Scheme.{u})
    (N : coefficientSequenceModules l E W) {m n : ℕ} (h : n ≤ m)
    (U : W.ProEtᵒᵖ)
    (x : N.val.obj (op (m, U.unop))) :
    ((coefficientSequenceTransition l E W h).app N).val.app U x =
      N.val.map (Prod.mkHom (homOfLE h) (𝟙 U.unop)).op x := by
  have ht := (coefficientSequenceTransition_exists l E W h).exists.choose_spec N U
  have hh := conjugate_apply
    (coefficientSequenceEvaluationAb_eq l E W N m U)
    (coefficientSequenceRestrictedEvaluationAb_eq l E W N h U)
    ((forget₂ (ModuleCat.{u + 1}
      ((integralCoefficientSheaf l E W m).obj.obj U)) AddCommGrpCat).map
        (((coefficientSequenceTransition l E W h).app N).val.app U))
    (N.val.presheaf.map (Prod.mkHom (homOfLE h) (𝟙 U.unop)).op) ht x x (HEq.refl x)
  exact eq_of_heq hh

/-- The ordinary coinduced adjacent-difference map is an epimorphism.
Source: Stacks 0941 and 07A6; the downward-recursion step of the proof of
lem-coef-sequence-coinduced-complex-short-exact.
(blueprint: lem-coef-sequence-coinduced-difference-epi).

Proof: in degree q and at the section (m,U), coinduction and product evaluation
identify the source with coordinates indexed by n≤m, and the target with coordinates
y_n indexed by n<m. The specified difference is transition(x_(n+1))−x_n. Given y,
set x_m=0, and recursively set x_n=transition(x_(n+1))−y_n for n=m−1 down to zero.
Then transition(x_(n+1))−x_n=y_n by cancellation. Give the remaining coinduced
coordinates, which are zero objects, their unique element. The product universal
property reconstructs a source section. Thus each degree and section of the
specified difference map is surjective. Sectionwise surjectivity implies epimorphy
for module presheaves and then module sheaves by the faithful forgetful functor;
degree evaluation jointly reflects epimorphy of complexes. For m=0 the target is
zero and the empty recursion applies. This does not assert a global splitting:
the boundary choice x_m=0 is used only to prove sectionwise surjectivity. -/
theorem complexDifference_epi
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (W : Scheme.{u})
    (K : CochainComplex (coefficientSequenceModules l E W) ℤ) :
    Epi (complexDifference l E W K) := by
  refine @identified_difference_epi.{u + 1, u, u + 1}
    W.ProEt inferInstance (Scheme.ProEt.topology W) (coefficientSiteSmall W)
    inferInstance (coefficientSiteAbLocallyBijective W) (coefficientSiteAbSheafify W)
    (sequenceAbSheafify W) (sequenceAbLocallyBijective W)
    (rings l E W) (complexProducts l E W)
    (fun n ↦ normalizedDVRQuotient.{u, u} l E W (Nat.le_succ n))
    (coefficientSequenceEvaluation.{u, u} l E W)
    (fun n ↦ coefficientSequenceEvaluation_additiveInstance.{u, u} l E W n)
    (evaluation_eq l E W)
    (fun n ↦ coefficientSequenceTransition.{u, u} l E W (Nat.le_succ n))
    ?_ K
  intro N n U
  have hh : (fun x : N.val.obj (op (n + 1, U.unop)) ↦
      ((coefficientSequenceTransition.{u, u} l E W (Nat.le_succ n)).app N).val.app U x) =
      (fun x : N.val.obj (op (n + 1, U.unop)) ↦
        N.val.map (Prod.mkHom (homOfLE (Nat.le_succ n)) (𝟙 U.unop)).op x) := by
    funext x
    exact transition_section l E W N (Nat.le_succ n) U x
  exact heq_of_eq hh

end WeilConjectures.CoefficientCoinduction
