/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Data.Int.Interval
public import WeilConjectures.Algebra.Homology.FilteredComplexGradedProjection
public import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.ClosedTriangulated

/-!
# The filtered internal hom of filtered cochain complexes

Let `C` be an abelian monoidal closed category with countable products, in which cochain
complexes can be tensored. For filtered cochain complexes `(M, F)` and `(N, G)` in `C`, the
internal hom complex `iHom(M, N)` (`CochainComplex.internalHomObj`) carries the filtration

`Fʳ iHom(M, N) = {v : v(FᵃM) ⊆ F^{a+r}N for every a}`,

defined as the kernel of the map `iHom(M, N) ⟶ ∏ₐ iHom(FᵃM, N / F^{a+r}N)`
(`CategoryTheory.DecreasingFiltration.internalHom`).

## Main results

* `CategoryTheory.DecreasingFiltration.isIso_grInternalHomComparison`: for finite filtrations
  which split in each cochain degree, the graded pieces of the filtered internal hom are
  `grʳ iHom(M, N) ≅ ∏ₐ iHom(grᵃM, gr^{a+r}N)` (only finitely many factors are nonzero). The
  comparison map is canonical: on the factor `a` it restricts a map to `FᵃM` and projects it to
  `gr^{a+r}N`.
* `CategoryTheory.DecreasingFiltration.grInternalHomTrivialIso`: the special case of the dual
  `𝔻_F K = iHom_F(K, ω)` with `ω` filtered in weight zero, `grʳ 𝔻_F K ≅ iHom(gr⁻ʳ K, ω)`.
* `CategoryTheory.DecreasingFiltration.tensorHom_arrow_comp_counit_eq_zero` and
  `CategoryTheory.DecreasingFiltration.tensorHom_gradedπ_comp_counit`: the evaluation
  `K ⊗ 𝔻_F K ⟶ ω` is filtered for the convolution filtration, and on the summand
  `grᵃK ⊗ gr⁻ᵃ 𝔻_F K ≅ grᵃK ⊗ iHom(grᵃK, ω)` of `gr⁰(K ⊗ 𝔻_F K)` it is the evaluation of
  `grᵃK`.

Degreewise split filtrations with suitable graded pieces are the filtered resolutions used to
derive the filtered operations; on them the formulas above hold on the nose. The analogous
statement for the convolution filtration of a tensor product is
`SheafOfModules.FilteredConvolution.graded_quotient`.
-/

@[expose] public section

open CategoryTheory Category Limits MonoidalCategory
open MonoidalClosed hiding assoc id_comp comp_id

universe v u

namespace CategoryTheory.Limits.Pi

/-- The projection from a product to a factor is an isomorphism when all the other factors are
zero. -/
private lemma isIso_π_of_isZero {C : Type u} [Category.{v} C] [HasZeroMorphisms C] {ι : Type*}
    (X : ι → C) [HasProduct X] (i : ι) (hX : ∀ j, j ≠ i → IsZero (X j)) :
    IsIso (Pi.π X i) := by
  classical
  exact ⟨Pi.lift fun j ↦ if h : j = i then eqToHom (congr_arg X h.symm) else 0,
    Pi.hom_ext _ _ fun j ↦ by
      by_cases h : j = i
      · subst h
        simp
      · exact (hX j h).eq_of_tgt _ _,
      by simp⟩

end CategoryTheory.Limits.Pi

namespace CochainComplex

variable {C : Type u} [Category.{v} C] [Abelian C] [MonoidalCategory C] [MonoidalClosed C]
  [MonoidalPreadditive C] [HasCountableProducts C]
  [∀ (X₁ X₂ : GradedObject ℤ C), X₁.HasTensor X₂]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ C), GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ C), GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃]
  [∀ (X₁ X₂ X₃ X₄ : GradedObject ℤ C), GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄]

omit [HasCountableProducts C]
  [∀ (X₁ X₂ : GradedObject ℤ C), X₁.HasTensor X₂]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ C), GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ C), GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃]
  [∀ (X₁ X₂ X₃ X₄ : GradedObject ℤ C), GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄] in
/-- The internal hom `ihom X` is left exact: it carries a short exact sequence
`0 ⟶ S.X₁ ⟶ S.X₂ ⟶ S.X₃` to an exact sequence. -/
private lemma exact_map_ihom (X : C) {S : ShortComplex C} (hS : S.Exact) [Mono S.f] :
    (S.map (ihom X)).Exact :=
  hS.map_of_mono_of_preservesKernel _ inferInstance inferInstance

instance (P : CochainComplex C ℤ) : (internalHom P).IsRightAdjoint :=
  (tensorHomAdjunction P).isRightAdjoint

/-- The internal hom complex functor `iHom(P, -)` is left exact. -/
lemma exact_map_internalHom (P : CochainComplex C ℤ) {S : ShortComplex (CochainComplex C ℤ)}
    (hS : S.Exact) [Mono S.f] : (S.map (internalHom P)).Exact :=
  hS.map_of_mono_of_preservesKernel _ inferInstance inferInstance

/-- Postcomposition `iHom(P, Y) ⟶ iHom(P, Y')` with a morphism `k : Y ⟶ Y'`. -/
noncomputable def internalHomPost (P : CochainComplex C ℤ) {Y Y' : CochainComplex C ℤ}
    (k : Y ⟶ Y') : internalHomObj P Y ⟶ internalHomObj P Y' :=
  (internalHom P).map k

variable (P : CochainComplex C ℤ) {Y Y' Y'' : CochainComplex C ℤ}

@[reassoc (attr := simp)]
lemma internalHomPost_f_π (k : Y ⟶ Y') (n p q : ℤ) (h : p + n = q) :
    (internalHomPost P k).f n ≫ internalHomπ P Y' n p q h =
      internalHomπ P Y n p q h ≫ (ihom (P.X p)).map (k.f q) :=
  internalHom_map_f_π k n p q h

@[reassoc]
lemma internalHomPost_comp (k : Y ⟶ Y') (k' : Y' ⟶ Y'') :
    internalHomPost P (k ≫ k') = internalHomPost P k ≫ internalHomPost P k' :=
  (internalHom P).map_comp k k'

@[simp]
lemma internalHomPost_zero : internalHomPost P (0 : Y ⟶ Y') = 0 :=
  (internalHom P).map_zero _ _

@[simp]
lemma internalHomPost_id : internalHomPost P (𝟙 Y) = 𝟙 _ :=
  (internalHom P).map_id Y

/-- Postcomposition with an isomorphism `Y ≅ Y'`, as an isomorphism
`iHom(P, Y) ≅ iHom(P, Y')`. -/
@[simps]
noncomputable def internalHomPostIso (e : Y ≅ Y') : internalHomObj P Y ≅ internalHomObj P Y' where
  hom := internalHomPost P e.hom
  inv := internalHomPost P e.inv
  hom_inv_id := by rw [← internalHomPost_comp, e.hom_inv_id, internalHomPost_id]
  inv_hom_id := by rw [← internalHomPost_comp, e.inv_hom_id, internalHomPost_id]

lemma isZero_internalHomObj {Z : CochainComplex C ℤ} (hZ : IsZero Z) :
    IsZero (internalHomObj P Z) :=
  (internalHom P).map_isZero hZ

instance (k : Y ⟶ Y') [Mono k] : Mono (internalHomPost P k) :=
  inferInstanceAs (Mono ((internalHom P).map k))

variable {P} in
/-- Precomposition and postcomposition of internal hom complexes commute. -/
@[reassoc]
lemma internalHomPre_comp_internalHomPost {P' : CochainComplex C ℤ} (f : P ⟶ P')
    (k : Y ⟶ Y') :
    internalHomPre f Y ≫ internalHomPost P k = internalHomPost P' k ≫ internalHomPre f Y' := by
  refine HomologicalComplex.hom_ext _ _ fun n ↦ internalHomObj_hom_ext fun p q h ↦ ?_
  simp only [HomologicalComplex.comp_f, assoc, internalHomPost_f_π, internalHomPre_f_π,
    internalHomPre_f_π_assoc, internalHomPost_f_π_assoc, pre_comm_ihom_map]

/-- The lift of a map into `iHom(P, S.X₂)` killed by postcomposition with `S.g` to
`iHom(P, S.X₁)`, for a left exact sequence `S`. -/
noncomputable def liftInternalHomPost {S : ShortComplex (CochainComplex C ℤ)} (hS : S.Exact)
    [Mono S.f] {T : CochainComplex C ℤ} (w : T ⟶ internalHomObj P S.X₂)
    (hw : w ≫ internalHomPost P S.g = 0) : T ⟶ internalHomObj P S.X₁ :=
  haveI : Mono (S.map (internalHom P)).f := inferInstanceAs (Mono ((internalHom P).map S.f))
  (exact_map_internalHom P hS).lift w hw

@[reassoc (attr := simp)]
lemma liftInternalHomPost_comp {S : ShortComplex (CochainComplex C ℤ)} (hS : S.Exact)
    [Mono S.f] {T : CochainComplex C ℤ} (w : T ⟶ internalHomObj P S.X₂)
    (hw : w ≫ internalHomPost P S.g = 0) :
    liftInternalHomPost P hS w hw ≫ internalHomPost P S.f = w :=
  haveI : Mono (S.map (internalHom P)).f := inferInstanceAs (Mono ((internalHom P).map S.f))
  (exact_map_internalHom P hS).lift_f w hw

/-- Precomposition carries a degreewise split short exact sequence to a short exact
sequence. -/
lemma shortExact_internalHomShortComplex (Y : CochainComplex C ℤ)
    (S : ShortComplex (CochainComplex C ℤ))
    (σ : ∀ n, (S.map (HomologicalComplex.eval C _ n)).Splitting) :
    (internalHomShortComplex Y S).ShortExact :=
  HomologicalComplex.shortExact_of_degreewise_shortExact _ fun n ↦
    (internalHomShortComplexSplitting Y S σ n).shortExact

omit [HasCountableProducts C]
  [∀ (X₁ X₂ : GradedObject ℤ C), X₁.HasTensor X₂]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ C), GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ C), GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃]
  [∀ (X₁ X₂ X₃ X₄ : GradedObject ℤ C), GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄] in
/-- Maps into `ihom Z Y` agree when `Z` is zero. -/
private lemma ext_of_isZero_ihom {Z : C} (hZ : IsZero Z) {Y A : C} (f g : A ⟶ (ihom Z).obj Y) :
    f = g := by
  have h : (pre (𝟙 Z)).app Y = 0 := by rw [hZ.eq_of_src (𝟙 Z) 0, pre_zero_app]
  rw [← comp_id f, ← comp_id g, ← NatTrans.id_app, ← pre_id, h, comp_zero, comp_zero]

omit [Abelian C] [MonoidalPreadditive C] [HasCountableProducts C]
  [∀ (X₁ X₂ : GradedObject ℤ C), X₁.HasTensor X₂]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ C), GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ C), GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃]
  [∀ (X₁ X₂ X₃ X₄ : GradedObject ℤ C), GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄] in
/-- Precompositions and postcompositions of internal homs combine. -/
@[reassoc]
private lemma pre_app_comp_ihom_map_comp_pre_app {A A' A'' B B' : C} (f : A' ⟶ A) (g : B ⟶ B')
    (f' : A'' ⟶ A') :
    (pre f).app B ≫ (ihom A').map g ≫ (pre f').app B' =
      (pre (f' ≫ f)).app B ≫ (ihom A'').map g := by
  rw [← pre_comm_ihom_map, pre_map, NatTrans.comp_app, assoc]

omit [Abelian C] [MonoidalCategory C] [MonoidalClosed C] [MonoidalPreadditive C]
  [∀ (X₁ X₂ : GradedObject ℤ C), X₁.HasTensor X₂]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ C), GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ C), GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃]
  [∀ (X₁ X₂ X₃ X₄ : GradedObject ℤ C), GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄] in
/-- Maps into the degree `n` part of a product of complexes agree when their components do. -/
private lemma pi_X_hom_ext [HasZeroMorphisms C] {ι : Type*} [Countable ι]
    {X : ι → CochainComplex C ℤ} {n : ℤ} {A : C}
    {f g : A ⟶ (∏ᶜ X).X n} (h : ∀ i, f ≫ (Pi.π X i).f n = g ≫ (Pi.π X i).f n) : f = g :=
  (isLimitOfPreserves (HomologicalComplex.eval C _ n) (limit.isLimit _)).hom_ext
    fun ⟨i⟩ ↦ h i

end CochainComplex

namespace CategoryTheory.DecreasingFiltration

open CochainComplex

variable {C : Type u} [Category.{v} C] [Abelian C]

section Quotient

variable {N : CochainComplex C ℤ} (G : DecreasingFiltration N)

/-- The projection `N / F^{b'} N ⟶ N / Fᵇ N` for `b ≤ b'`. -/
noncomputable def quotientMap {b b' : ℤ} (h : b ≤ b') :
    cokernel (G.F b').arrow ⟶ cokernel (G.F b).arrow :=
  cokernel.desc _ (cokernel.π _) (by
    rw [← Subobject.ofLE_arrow (G.antitone h), assoc, cokernel.condition, comp_zero])

@[reassoc (attr := simp)]
lemma π_quotientMap {b b' : ℤ} (h : b ≤ b') :
    cokernel.π (G.F b').arrow ≫ G.quotientMap h = cokernel.π (G.F b).arrow :=
  cokernel.π_desc _ _ _

/-- A larger filtration step dies in the quotient by a smaller one. -/
@[reassoc]
lemma arrow_comp_π_eq_zero {b b' : ℤ} (h : b ≤ b') :
    (G.F b').arrow ≫ cokernel.π (G.F b).arrow = 0 := by
  rw [← Subobject.ofLE_arrow (G.antitone h), assoc, cokernel.condition, comp_zero]

/-- The short complex `Fᵇ ⟶ N ⟶ N / Fᵇ` of a filtered complex. -/
@[simps]
noncomputable def cokernelShortComplex (b : ℤ) : ShortComplex (CochainComplex C ℤ) :=
  ShortComplex.mk (G.F b).arrow (cokernel.π _) (cokernel.condition _)

lemma cokernelShortComplex_exact (b : ℤ) : (G.cokernelShortComplex b).Exact :=
  ShortComplex.exact_cokernel _

instance (b : ℤ) : Mono (G.cokernelShortComplex b).f :=
  inferInstanceAs (Mono (G.F b).arrow)

/-- The short complex `F^{b+1} ⟶ Fᵇ ⟶ grᵇ` of a filtered complex. -/
@[simps]
noncomputable def stepShortComplex (b : ℤ) : ShortComplex (CochainComplex C ℤ) :=
  ShortComplex.mk (Subobject.ofLE _ _ (G.F_succ_le b)) (G.gradedπ b) (cokernel.condition _)

lemma stepShortComplex_exact (b : ℤ) : (G.stepShortComplex b).Exact :=
  ShortComplex.exact_cokernel _

instance (b : ℤ) : Mono (G.stepShortComplex b).f :=
  inferInstanceAs (Mono (Subobject.ofLE _ _ _))

/-- The degree `n` part of `F^{b+1} ⟶ Fᵇ ⟶ grᵇ` splits when the graded projection splits in
degree `n`. -/
noncomputable def stepSplitting {b n : ℤ} (h : IsSplitEpi ((G.gradedπ b).f n)) :
    ((G.stepShortComplex b).map (HomologicalComplex.eval C _ n)).Splitting :=
  ShortComplex.Splitting.ofExactOfSection _
    ((G.stepShortComplex_exact b).map (HomologicalComplex.eval C _ n))
    h.exists_splitEpi.some.section_ h.exists_splitEpi.some.id
    (inferInstanceAs (Mono ((HomologicalComplex.eval C _ n).map _)))

/-- In degree `p`, the inclusion `FᵃM ⟶ M` vanishes for `a > d` if `F^{d+1}M = 0`. -/
lemma arrow_f_eq_zero_of_eq_bot {M : CochainComplex C ℤ} (F : DecreasingFiltration M) {d : ℤ}
    (hd : F.F (d + 1) = ⊥) {a : ℤ} (ha : d + 1 ≤ a) (p : ℤ) : (F.F a).arrow.f p = 0 := by
  have h : F.F a = ⊥ := le_bot_iff.1 (hd ▸ F.antitone ha)
  have hz : IsZero ((F.F a : CochainComplex C ℤ)) :=
    h ▸ (Subobject.botCoeIsoZero (B := M)).isZero_iff.2 (isZero_zero _)
  exact ((HomologicalComplex.eval C _ p).map_isZero hz).eq_of_src _ _

end Quotient

section Trivial

variable (A : CochainComplex C ℤ)

/-- The filtration of `A` concentrated in weight zero: `Fᵃ A = A` for `a ≤ 0` and `Fᵃ A = 0`
for `a > 0`. -/
noncomputable def trivial : DecreasingFiltration A where
  F a := if a ≤ 0 then ⊤ else ⊥
  F_succ_le a := by
    split_ifs <;> first | exact le_rfl | exact bot_le | omega

lemma trivial_F_of_le {a : ℤ} (h : a ≤ 0) : (trivial A).F a = ⊤ := by
  simp [trivial, h]

lemma trivial_F_of_pos {a : ℤ} (h : 0 < a) : (trivial A).F a = ⊥ := by
  simp [trivial, show ¬ a ≤ 0 by omega]

lemma isZero_trivial_gr {a : ℤ} (h : a ≠ 0) : IsZero ((trivial A).gr a) := by
  rcases lt_or_gt_of_ne h with h | h
  · exact (trivial A).isZero_gradedPiece_of_eq_top (trivial_F_of_le A (show a + 1 ≤ 0 by omega))
  · exact (trivial A).isZero_gradedPiece_of_eq_bot (trivial_F_of_pos A h)

lemma isIso_trivial_gradedπ {b : ℤ} (hb : b = 0) : IsIso ((trivial A).gradedπ b) := by
  subst hb
  have hz : IsZero (((trivial A).F (0 + 1) : CochainComplex C ℤ)) :=
    trivial_F_of_pos A (show (0 : ℤ) < 0 + 1 by omega) ▸
      (Subobject.botCoeIsoZero (B := A)).isZero_iff.2 (isZero_zero _)
  exact cokernel.π_of_zero (hz.eq_of_src _ _)

lemma isIso_trivial_arrow {b : ℤ} (hb : b = 0) : IsIso ((trivial A).F b).arrow :=
  (Subobject.isIso_arrow_iff_eq_top _).2 (trivial_F_of_le A hb.le)

/-- The graded piece in weight zero of the filtration concentrated in weight zero. -/
noncomputable def trivialGrIso {b : ℤ} (hb : b = 0) : (trivial A).gr b ≅ A :=
  haveI := isIso_trivial_gradedπ A hb
  haveI := isIso_trivial_arrow A hb
  (asIso ((trivial A).gradedπ b)).symm ≪≫ asIso ((trivial A).F b).arrow

@[reassoc (attr := simp)]
lemma gradedπ_trivialGrIso_hom {b : ℤ} (hb : b = 0) :
    (trivial A).gradedπ b ≫ (trivialGrIso A hb).hom = ((trivial A).F b).arrow := by
  simp [trivialGrIso]

lemma trivial_isSplitEpi_gradedπ (b n : ℤ) : IsSplitEpi (((trivial A).gradedπ b).f n) := by
  by_cases hb : b = 0
  · have := isIso_trivial_gradedπ A hb
    infer_instance
  · exact IsSplitEpi.mk' ⟨0, ((HomologicalComplex.eval C _ n).map_isZero
      (isZero_trivial_gr A hb)).eq_of_src _ _⟩

end Trivial

variable [MonoidalCategory C] [MonoidalClosed C] [MonoidalPreadditive C] [HasCountableProducts C]
  [∀ (X₁ X₂ : GradedObject ℤ C), X₁.HasTensor X₂]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ C), GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ C), GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃]
  [∀ (X₁ X₂ X₃ X₄ : GradedObject ℤ C), GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄]

section Filtration

variable {M N : CochainComplex C ℤ} (F : DecreasingFiltration M) (G : DecreasingFiltration N)

/-- The map `iHom(M, N) ⟶ ∏ₐ iHom(FᵃM, N / F^{a+r}N)` restricting to `FᵃM` and projecting to
`N / F^{a+r}N` on the factor `a`; its kernel is `Fʳ iHom(M, N)`. -/
noncomputable def internalHomFiltrationMap (r : ℤ) :
    internalHomObj M N ⟶ ∏ᶜ fun a : ℤ ↦
      internalHomObj (F.F a : CochainComplex C ℤ) (cokernel (G.F (a + r)).arrow) :=
  Pi.lift fun a ↦ internalHomPre (F.F a).arrow N ≫ internalHomPost _ (cokernel.π _)

@[reassoc (attr := simp)]
lemma internalHomFiltrationMap_π (r a : ℤ) :
    F.internalHomFiltrationMap G r ≫ Pi.π _ a =
      internalHomPre (F.F a).arrow N ≫ internalHomPost _ (cokernel.π _) :=
  Pi.lift_comp_π _ _

/-- The filtration `Fʳ iHom(M, N) = {v : v(FᵃM) ⊆ F^{a+r}N for every a}` of the internal hom
complex of two filtered complexes. -/
noncomputable def internalHom : DecreasingFiltration (internalHomObj M N) where
  F r := kernelSubobject (F.internalHomFiltrationMap G r)
  F_succ_le r := by
    have : F.internalHomFiltrationMap G r = F.internalHomFiltrationMap G (r + 1) ≫
        Limits.Pi.map fun a ↦
          internalHomPost _ (G.quotientMap (show a + r ≤ a + (r + 1) by omega)) :=
      Pi.hom_ext _ _ fun a ↦ by simp [← internalHomPost_comp]
    rw [this]
    exact kernelSubobject_comp_le _ _

lemma internalHom_F (r : ℤ) :
    (F.internalHom G).F r = kernelSubobject (F.internalHomFiltrationMap G r) :=
  rfl

/-- A map in `Fʳ iHom(M, N)` maps `FᵃM` into `F^{a+r}N`. -/
@[reassoc (attr := simp)]
lemma arrow_internalHom_comp_internalHomPre_comp_internalHomPost (r a : ℤ) :
    ((F.internalHom G).F r).arrow ≫ internalHomPre (F.F a).arrow N ≫
      internalHomPost _ (cokernel.π (G.F (a + r)).arrow) = 0 := by
  rw [← internalHomFiltrationMap_π, internalHom_F, kernelSubobject_arrow_comp_assoc, zero_comp]

/-- A map in `Fʳ iHom(M, N)` maps `FᵃM` into `FᵇN` when `b ≤ a + r`. -/
@[reassoc]
lemma arrow_internalHom_comp_internalHomPre_comp_internalHomPost' {r a b : ℤ} (h : b ≤ a + r) :
    ((F.internalHom G).F r).arrow ≫ internalHomPre (F.F a).arrow N ≫
      internalHomPost _ (cokernel.π (G.F b).arrow) = 0 := by
  rw [← G.π_quotientMap h, internalHomPost_comp, reassoc_of%
    (F.arrow_internalHom_comp_internalHomPre_comp_internalHomPost G r a), zero_comp]

/-- The restriction `Fʳ iHom(M, N) ⟶ iHom(FᵃM, F^{a+r}N)` of a map `v` with
`v(FᵃM) ⊆ F^{a+r}N`. -/
noncomputable def internalHomRestrict (r a : ℤ) :
    ((F.internalHom G).F r : CochainComplex C ℤ) ⟶
      internalHomObj (F.F a : CochainComplex C ℤ) (G.F (a + r) : CochainComplex C ℤ) :=
  liftInternalHomPost _ (G.cokernelShortComplex_exact (a + r))
    (((F.internalHom G).F r).arrow ≫ internalHomPre (F.F a).arrow N) (by simp)

@[reassoc (attr := simp)]
lemma internalHomRestrict_comp_internalHomPost (r a : ℤ) :
    F.internalHomRestrict G r a ≫ internalHomPost _ (G.F (a + r)).arrow =
      ((F.internalHom G).F r).arrow ≫ internalHomPre (F.F a).arrow N :=
  liftInternalHomPost_comp _ _ _ _

/-- When the graded projection `FᵃM ⟶ grᵃM` splits in each degree, the sequence
`iHom(grᵃM, Y) ⟶ iHom(FᵃM, Y) ⟶ iHom(F^{a+1}M, Y)` is short exact. -/
lemma shortExact_internalHomShortComplex_step {a : ℤ}
    (hF : ∀ n, IsSplitEpi ((F.gradedπ a).f n)) (Y : CochainComplex C ℤ) :
    (internalHomShortComplex Y (F.stepShortComplex a)).ShortExact :=
  shortExact_internalHomShortComplex Y _ fun n ↦ F.stepSplitting (hF n)

lemma mono_internalHomPre_gradedπ {a : ℤ} (hF : ∀ n, IsSplitEpi ((F.gradedπ a).f n))
    (Y : CochainComplex C ℤ) : Mono (internalHomPre (F.gradedπ a) Y) :=
  (F.shortExact_internalHomShortComplex_step hF Y).mono_f

lemma internalHomRestrict_comp_internalHomPost_comp_internalHomPre (r a : ℤ) :
    F.internalHomRestrict G r a ≫ internalHomPost _ (G.gradedπ (a + r)) ≫
      internalHomPre (Subobject.ofLE _ _ (F.F_succ_le a)) (G.gr (a + r)) = 0 := by
  rw [← cancel_mono (internalHomPost _ (G.gradedPieceToQuotient (a + r))), zero_comp, assoc,
    assoc, internalHomPre_comp_internalHomPost, ← internalHomPost_comp_assoc,
    gradedπ_gradedPieceToQuotient, internalHomPost_comp_assoc,
    internalHomRestrict_comp_internalHomPost_assoc, ← internalHomPre_comp_internalHomPost,
    ← internalHomPre_comp_assoc, Subobject.ofLE_arrow,
    F.arrow_internalHom_comp_internalHomPre_comp_internalHomPost' G (by omega)]

/-- The factor `Fʳ iHom(M, N) ⟶ iHom(grᵃM, gr^{a+r}N)` of the graded comparison: restrict to
`FᵃM`, project to `gr^{a+r}N`, and descend to `grᵃM`. -/
noncomputable def grInternalHomπ {a : ℤ} (hF : ∀ n, IsSplitEpi ((F.gradedπ a).f n)) (r : ℤ) :
    ((F.internalHom G).F r : CochainComplex C ℤ) ⟶ internalHomObj (F.gr a) (G.gr (a + r)) :=
  haveI := (F.shortExact_internalHomShortComplex_step hF (G.gr (a + r))).mono_f
  (F.shortExact_internalHomShortComplex_step hF (G.gr (a + r))).exact.lift
    (F.internalHomRestrict G r a ≫ internalHomPost _ (G.gradedπ (a + r)))
    (by simpa using F.internalHomRestrict_comp_internalHomPost_comp_internalHomPre G r a)

@[reassoc (attr := simp)]
lemma grInternalHomπ_comp_internalHomPre {a : ℤ} (hF : ∀ n, IsSplitEpi ((F.gradedπ a).f n))
    (r : ℤ) :
    F.grInternalHomπ G hF r ≫ internalHomPre (F.gradedπ a) _ =
      F.internalHomRestrict G r a ≫ internalHomPost _ (G.gradedπ (a + r)) :=
  haveI := (F.shortExact_internalHomShortComplex_step hF (G.gr (a + r))).mono_f
  (F.shortExact_internalHomShortComplex_step hF (G.gr (a + r))).exact.lift_f _ _

lemma ofLE_comp_grInternalHomπ {a : ℤ} (hF : ∀ n, IsSplitEpi ((F.gradedπ a).f n)) (r : ℤ) :
    Subobject.ofLE _ _ ((F.internalHom G).F_succ_le r) ≫ F.grInternalHomπ G hF r = 0 := by
  have := F.mono_internalHomPre_gradedπ hF (G.gr (a + r))
  rw [← cancel_mono (internalHomPre (F.gradedπ a) _), assoc, grInternalHomπ_comp_internalHomPre,
    ← cancel_mono (internalHomPost _ (G.gradedPieceToQuotient (a + r))), zero_comp, zero_comp,
    assoc, assoc, ← internalHomPost_comp, gradedπ_gradedPieceToQuotient, internalHomPost_comp,
    internalHomRestrict_comp_internalHomPost_assoc, Subobject.ofLE_arrow_assoc,
    F.arrow_internalHom_comp_internalHomPre_comp_internalHomPost' G (by omega)]

/-- The short complex `F^{r+1} iHom(M, N) ⟶ Fʳ iHom(M, N) ⟶ ∏ₐ iHom(grᵃM, gr^{a+r}N)`. -/
@[simps]
noncomputable def grInternalHomShortComplex (hF : ∀ a n, IsSplitEpi ((F.gradedπ a).f n))
    (r : ℤ) : ShortComplex (CochainComplex C ℤ) :=
  ShortComplex.mk (Subobject.ofLE _ _ ((F.internalHom G).F_succ_le r))
    (Pi.lift fun a ↦ F.grInternalHomπ G (hF a) r)
    (Pi.hom_ext _ _ fun a ↦ by
      rw [assoc, Pi.lift_comp_π, zero_comp]
      exact F.ofLE_comp_grInternalHomπ G (hF a) r)

/-- The canonical comparison `grʳ iHom(M, N) ⟶ ∏ₐ iHom(grᵃM, gr^{a+r}N)`, which restricts a
map `v` with `v(FᵃM) ⊆ F^{a+r}N` to `FᵃM` and projects it to `gr^{a+r}N`. -/
noncomputable def grInternalHomComparison (hF : ∀ a n, IsSplitEpi ((F.gradedπ a).f n))
    (r : ℤ) :
    (F.internalHom G).gr r ⟶ ∏ᶜ fun a : ℤ ↦ internalHomObj (F.gr a) (G.gr (a + r)) :=
  cokernel.desc _ (F.grInternalHomShortComplex G hF r).g (F.grInternalHomShortComplex G hF r).zero

/-- The components of the factor `Fʳ iHom(M, N) ⟶ iHom(grᵃM, gr^{a+r}N)`: on `[grᵃMᵖ, gr^{a+r}N^q]`
it is the restriction to `FᵃMᵖ`, followed by any projection `t : N^q ⟶ gr^{a+r}N^q` extending
the graded projection and any section `j` of the graded projection `FᵃMᵖ ⟶ grᵃMᵖ`. -/
lemma grInternalHomπ_f_π {a : ℤ} (hF : ∀ n, IsSplitEpi ((F.gradedπ a).f n)) (r n p q : ℤ)
    (h : p + n = q) (j : (F.gr a).X p ⟶ (F.F a : CochainComplex C ℤ).X p)
    (hj : j ≫ (F.gradedπ a).f p = 𝟙 _) (t : N.X q ⟶ (G.gr (a + r)).X q)
    (ht : (G.F (a + r)).arrow.f q ≫ t = (G.gradedπ (a + r)).f q) :
    (F.grInternalHomπ G hF r).f n ≫ internalHomπ _ _ n p q h =
      ((F.internalHom G).F r).arrow.f n ≫ internalHomπ M N n p q h ≫
        (pre ((F.F a).arrow.f p)).app _ ≫ (ihom _).map t ≫ (pre j).app _ := by
  have h₁ := congr_arg (fun φ ↦ φ.f n ≫ internalHomπ _ _ n p q h ≫ (pre j).app _)
    (F.grInternalHomπ_comp_internalHomPre G hF r)
  have h₂ := congr_arg (fun φ ↦ φ.f n ≫ internalHomπ _ _ n p q h ≫ (ihom _).map t ≫
    (pre j).app _) (F.internalHomRestrict_comp_internalHomPost G r a)
  simp only [HomologicalComplex.comp_f, assoc, internalHomPre_f_π_assoc,
    internalHomPost_f_π_assoc] at h₁ h₂
  rw [pre_app_comp_ihom_map_comp_pre_app] at h₂
  rw [← NatTrans.comp_app, ← pre_map, hj, pre_id, NatTrans.id_app, comp_id] at h₁
  rw [h₁, ← ht, Functor.map_comp, assoc, h₂, pre_app_comp_ihom_map_comp_pre_app]

/-- A degree `n` element of `Fʳ iHom(M, N)` maps `FᵃMᵖ` into `FᵇN^q` for `b ≤ a + r`. -/
@[reassoc]
lemma arrow_f_comp_internalHomπ_comp_pre_comp_map {r a b : ℤ} (hb : b ≤ a + r)
    (n p q : ℤ) (h : p + n = q) :
    ((F.internalHom G).F r).arrow.f n ≫ internalHomπ M N n p q h ≫
      (pre ((F.F a).arrow.f p)).app _ ≫ (ihom _).map ((cokernel.π (G.F b).arrow).f q) = 0 := by
  have := congr_arg (fun φ ↦ φ.f n ≫ internalHomπ _ _ n p q h)
    (F.arrow_internalHom_comp_internalHomPre_comp_internalHomPost' G hb)
  simpa only [HomologicalComplex.comp_f, assoc, internalHomPre_f_π_assoc, internalHomPost_f_π,
    HomologicalComplex.zero_f, zero_comp] using this

/-- A degree `n` element of `iHom(M, N)` which maps each `FᵃMᵖ` into `F^{a+r}N^q` lies in
`Fʳ iHom(M, N)`. -/
lemma exists_lift_arrow_f (r n : ℤ) {A : C} (x : A ⟶ (internalHomObj M N).X n)
    (hx : ∀ a p q (h : p + n = q), x ≫ internalHomπ M N n p q h ≫
      (pre ((F.F a).arrow.f p)).app _ ≫ (ihom _).map ((cokernel.π (G.F (a + r)).arrow).f q) = 0) :
    ∃ y : A ⟶ ((F.internalHom G).F r : CochainComplex C ℤ).X n,
      y ≫ ((F.internalHom G).F r).arrow.f n = x := by
  let φ := F.internalHomFiltrationMap G r
  have hS := (ShortComplex.exact_kernel φ).map (HomologicalComplex.eval C _ n)
  have : Mono ((ShortComplex.mk _ _ (kernel.condition φ)).map
      (HomologicalComplex.eval C _ n)).f :=
    inferInstanceAs (Mono ((HomologicalComplex.eval C _ n).map (kernel.ι φ)))
  obtain ⟨y, hy⟩ := hS.lift' x (by
    refine pi_X_hom_ext fun a ↦ internalHomObj_hom_ext fun p q h ↦ ?_
    simp only [ShortComplex.map_X₂, HomologicalComplex.eval_obj, ShortComplex.map_g,
      HomologicalComplex.eval_map, assoc, zero_comp, φ]
    have e := congr_arg (fun ψ ↦ ψ.f n ≫ internalHomπ _ _ n p q h)
      (F.internalHomFiltrationMap_π G r a)
    simp only [HomologicalComplex.comp_f, assoc, internalHomPre_f_π_assoc,
      internalHomPost_f_π] at e
    rw [e]
    exact hx a p q h)
  refine ⟨y ≫ (kernelSubobjectIso φ).inv.f n, ?_⟩
  have e : (kernelSubobjectIso φ).inv ≫ ((F.internalHom G).F r).arrow = kernel.ι φ :=
    kernelSubobject_arrow' φ
  rw [assoc, ← HomologicalComplex.comp_f, e]
  exact hy

/-- One step of the descending induction for the middle exactness of
`F^{r+1} ⟶ Fʳ ⟶ ∏ₐ iHom(grᵃM, gr^{a+r}N)` in degree `n`: if a degree `n` element `x` of
`Fʳ iHom(M, N)` has vanishing graded component `a` and maps `F^{a+1}Mᵖ` into `F^{a+r+2}N^q`,
then it maps `FᵃMᵖ` into `F^{a+r+1}N^q`. -/
lemma internalHom_step {a : ℤ} (hF : ∀ n, IsSplitEpi ((F.gradedπ a).f n))
    (hG : ∀ b n, IsSplitEpi ((G.gradedπ b).f n)) {cG : ℤ} (hcG : G.F cG = ⊤) (r n p q : ℤ)
    (h : p + n = q) {A : C} (x : A ⟶ ((F.internalHom G).F r : CochainComplex C ℤ).X n)
    (hx : x ≫ (F.grInternalHomπ G hF r).f n = 0)
    (hx' : x ≫ ((F.internalHom G).F r).arrow.f n ≫ internalHomπ M N n p q h ≫
      (pre ((F.F (a + 1)).arrow.f p)).app _ ≫
        (ihom _).map ((cokernel.π (G.F (a + r + 1)).arrow).f q) = 0) :
    x ≫ ((F.internalHom G).F r).arrow.f n ≫ internalHomπ M N n p q h ≫
      (pre ((F.F a).arrow.f p)).app _ ≫
        (ihom _).map ((cokernel.π (G.F (a + r + 1)).arrow).f q) = 0 := by
  obtain ⟨σr, σs, hσ, hσs⟩ : ∃ (σr : (F.F a : CochainComplex C ℤ).X p ⟶
      (F.F (a + 1) : CochainComplex C ℤ).X p)
      (σs : (F.gr a).X p ⟶ (F.F a : CochainComplex C ℤ).X p),
      σr ≫ (Subobject.ofLE _ _ (F.F_succ_le a)).f p + (F.gradedπ a).f p ≫ σs = 𝟙 _ ∧
        σs ≫ (F.gradedπ a).f p = 𝟙 _ :=
    ⟨(F.stepSplitting (hF p)).r, (F.stepSplitting (hF p)).s, (F.stepSplitting (hF p)).id,
      (F.stepSplitting (hF p)).s_g⟩
  obtain ⟨t, ht, -⟩ := G.exists_gradedProjection cG hcG hG (a + r) q
  -- the graded component of `x`, evaluated on the factor `(p, q)`
  have h₂ : x ≫ ((F.internalHom G).F r).arrow.f n ≫ internalHomπ M N n p q h ≫
      (pre ((F.F a).arrow.f p)).app _ ≫ (ihom _).map t ≫ (pre σs).app _ = 0 := by
    have := congr_arg (· ≫ internalHomπ _ _ n p q h) hx
    simp only [assoc, zero_comp] at this
    rwa [F.grInternalHomπ_f_π G hF r n p q h σs hσs t ht] at this
  -- `x` lies in `Fʳ`
  have h₁ : x ≫ ((F.internalHom G).F r).arrow.f n ≫ internalHomπ M N n p q h ≫
      (pre ((F.F a).arrow.f p)).app _ ≫
        (ihom _).map ((cokernel.π (G.F (a + r)).arrow).f q) = 0 := by
    rw [F.arrow_f_comp_internalHomπ_comp_pre_comp_map G le_rfl, comp_zero]
  obtain ⟨w, hw⟩ : ∃ w, w = x ≫ ((F.internalHom G).F r).arrow.f n ≫ internalHomπ M N n p q h ≫
    (pre ((F.F a).arrow.f p)).app (N.X q) := ⟨_, rfl⟩
  suffices hsuff : w ≫ (ihom _).map ((cokernel.π (G.F (a + r + 1)).arrow).f q) = 0 by
    rw [hw] at hsuff
    simpa only [assoc] using hsuff
  have hw' : x ≫ ((F.internalHom G).F r).arrow.f n ≫ internalHomπ M N n p q h ≫
      (pre ((F.F (a + 1)).arrow.f p)).app (N.X q) =
      w ≫ (pre ((Subobject.ofLE _ _ (F.F_succ_le a)).f p)).app _ := by
    rw [hw]
    simp only [assoc]
    rw [← NatTrans.comp_app, ← pre_map, ← HomologicalComplex.comp_f, Subobject.ofLE_arrow]
  -- the splitting `𝟙 = r ≫ ofLE + gradedπ ≫ s` of `FᵃMᵖ`
  have hid : w = w ≫ (pre ((Subobject.ofLE _ _ (F.F_succ_le a)).f p)).app _ ≫ (pre σr).app _ +
      w ≫ (pre σs).app _ ≫ (pre ((F.gradedπ a).f p)).app _ := by
    rw [← NatTrans.comp_app, ← NatTrans.comp_app, ← pre_map, ← pre_map, ← Preadditive.comp_add,
      ← pre_add_app]
    rw [hσ, pre_id, NatTrans.id_app, comp_id]
  have hx'' : w ≫ (pre ((Subobject.ofLE _ _ (F.F_succ_le a)).f p)).app _ ≫
      (ihom _).map ((cokernel.π (G.F (a + r + 1)).arrow).f q) = 0 := by
    rw [← assoc, ← hw']
    simpa only [assoc] using hx'
  have h₁' : w ≫ (ihom _).map ((cokernel.π (G.F (a + r)).arrow).f q) = 0 := by
    rw [hw]
    simpa only [assoc] using h₁
  have h₂' : w ≫ (ihom _).map t ≫ (pre σs).app _ = 0 := by
    rw [hw]
    simpa only [assoc] using h₂
  rw [hid, Preadditive.add_comp, assoc, assoc, assoc, assoc, pre_comm_ihom_map,
    pre_comm_ihom_map, reassoc_of% hx'', zero_comp, zero_add]
  -- the second summand: `w ≫ [s, -]` lands in `[grᵃMᵖ, F^{a+r+1}N^q]`
  let S₁ := (G.cokernelShortComplex (a + r)).map (HomologicalComplex.eval C _ q)
  let S₂ := (G.stepShortComplex (a + r)).map (HomologicalComplex.eval C _ q)
  have : Mono S₁.f := inferInstanceAs (Mono ((HomologicalComplex.eval C _ q).map _))
  have : Mono S₂.f := inferInstanceAs (Mono ((HomologicalComplex.eval C _ q).map _))
  have : Mono (S₁.map (ihom ((F.gr a).X p))).f := inferInstanceAs (Mono ((ihom _).map S₁.f))
  have : Mono (S₂.map (ihom ((F.gr a).X p))).f := inferInstanceAs (Mono ((ihom _).map S₂.f))
  obtain ⟨u, hu⟩ := (exact_map_ihom ((F.gr a).X p)
    ((G.cokernelShortComplex_exact (a + r)).map (HomologicalComplex.eval C _ q))).lift'
      (w ≫ (pre σs).app (N.X q)) (by
        change (w ≫ (pre σs).app (N.X q)) ≫
          (ihom _).map ((cokernel.π (G.F (a + r)).arrow).f q) = 0
        rw [assoc, pre_comm_ihom_map, reassoc_of% h₁', zero_comp])
  change u ≫ (ihom _).map ((G.F (a + r)).arrow.f q) = w ≫ (pre σs).app (N.X q) at hu
  obtain ⟨u', hu'⟩ := (exact_map_ihom ((F.gr a).X p)
    ((G.stepShortComplex_exact (a + r)).map (HomologicalComplex.eval C _ q))).lift' u (by
      change u ≫ (ihom _).map ((G.gradedπ (a + r)).f q) = 0
      have ht' : (G.F (a + r)).arrow.f q ≫ t = (G.gradedπ (a + r)).f q := ht
      rw [← ht', Functor.map_comp, reassoc_of% hu, pre_comm_ihom_map]
      simpa only [assoc] using h₂')
  change u' ≫ (ihom _).map ((Subobject.ofLE _ _ (G.F_succ_le (a + r))).f q) = u at hu'
  rw [← assoc, ← hu, ← hu']
  simp only [assoc]
  rw [← Functor.map_comp_assoc, ← Functor.map_comp_assoc, ← HomologicalComplex.comp_f,
    ← HomologicalComplex.comp_f]
  simp only [Subobject.ofLE_arrow, cokernel.condition, HomologicalComplex.zero_f,
    Functor.map_zero, zero_comp, comp_zero]
omit [MonoidalPreadditive C] [HasCountableProducts C]
  [∀ (X₁ X₂ : GradedObject ℤ C), X₁.HasTensor X₂]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ C), GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ C), GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃]
  [∀ (X₁ X₂ X₃ X₄ : GradedObject ℤ C), GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄] in
/-- If a map into `[X, N^q]` kills `N^q ⟶ (N / F^{b'}N)^q`, it kills `N^q ⟶ (N / FᵇN)^q` for
`b ≤ b'`. -/
lemma comp_ihom_map_π_f_eq_zero_of_le {A X : C} {b b' : ℤ} (hb : b ≤ b') (q : ℤ)
    (y : A ⟶ (ihom X).obj (N.X q))
    (hy : y ≫ (ihom X).map ((cokernel.π (G.F b').arrow).f q) = 0) :
    y ≫ (ihom X).map ((cokernel.π (G.F b).arrow).f q) = 0 := by
  rw [← G.π_quotientMap hb, HomologicalComplex.comp_f, Functor.map_comp, reassoc_of% hy,
    zero_comp]

/-- The middle exactness of `F^{r+1} ⟶ Fʳ ⟶ ∏ₐ iHom(grᵃM, gr^{a+r}N)` in degree `n`: a degree
`n` element of `Fʳ iHom(M, N)` whose graded components vanish lies in `F^{r+1} iHom(M, N)`. -/
lemma exists_lift_ofLE_f (hF : ∀ a n, IsSplitEpi ((F.gradedπ a).f n))
    (hG : ∀ b n, IsSplitEpi ((G.gradedπ b).f n)) {dF cG : ℤ} (hdF : F.F (dF + 1) = ⊥)
    (hcG : G.F cG = ⊤) (r n : ℤ) {A : C}
    (x : A ⟶ ((F.internalHom G).F r : CochainComplex C ℤ).X n)
    (hx : ∀ a, x ≫ (F.grInternalHomπ G (hF a) r).f n = 0) :
    ∃ y : A ⟶ ((F.internalHom G).F (r + 1) : CochainComplex C ℤ).X n,
      y ≫ (Subobject.ofLE _ _ ((F.internalHom G).F_succ_le r)).f n = x := by
  have key : ∀ p q (h : p + n = q) (k : ℕ) (a : ℤ), a = dF + 1 - k → ∀ b, b ≤ a + r + 1 →
      x ≫ ((F.internalHom G).F r).arrow.f n ≫ internalHomπ M N n p q h ≫
        (pre ((F.F a).arrow.f p)).app _ ≫ (ihom _).map ((cokernel.π (G.F b).arrow).f q) = 0 := by
    intro p q h k
    induction k with
    | zero =>
      intro a ha b _
      rw [F.arrow_f_eq_zero_of_eq_bot hdF (show dF + 1 ≤ a by omega), pre_zero_app, zero_comp,
        comp_zero, comp_zero, comp_zero]
    | succ k ih =>
      intro a ha b hb
      simp only [← assoc] at ih ⊢
      refine G.comp_ihom_map_π_f_eq_zero_of_le hb q _ ?_
      simp only [assoc]
      refine F.internalHom_step G (hF a) hG hcG r n p q h x (hx a) ?_
      have := ih (a + 1) (by push_cast at ha; omega) (a + r + 1) (by omega)
      simpa only [assoc] using this
  obtain ⟨y, hy⟩ := F.exists_lift_arrow_f G (r + 1) n
    (x ≫ ((F.internalHom G).F r).arrow.f n) fun a p q h ↦ by
      rcases le_or_gt a (dF + 1) with ha | ha
      · simpa only [assoc] using key p q h (dF + 1 - a).toNat a (by omega) _ (by omega)
      · rw [F.arrow_f_eq_zero_of_eq_bot hdF ha.le, pre_zero_app, zero_comp, comp_zero,
          comp_zero]
  refine ⟨y, ?_⟩
  have : Mono (((F.internalHom G).F r).arrow.f n) :=
    (HomologicalComplex.eval C _ n).map_mono _
  rw [← cancel_mono (((F.internalHom G).F r).arrow.f n), assoc, ← HomologicalComplex.comp_f,
    Subobject.ofLE_arrow, hy]

/-- The surjectivity of `Fʳ ⟶ ∏ₐ iHom(grᵃM, gr^{a+r}N)` in degree `n`: using degreewise
splittings of the filtrations, a family of maps `grᵃMᵖ ⟶ gr^{a+r}N^q` is the family of graded
components of `∑ₐ (Mᵖ ⟶ grᵃMᵖ ⟶ gr^{a+r}N^q ⟶ F^{a+r}N^q ⟶ N^q)`. -/
lemma exists_section_f (hF : ∀ a n, IsSplitEpi ((F.gradedπ a).f n))
    (hG : ∀ b n, IsSplitEpi ((G.gradedπ b).f n)) {cF dF cG : ℤ} (hcF : F.F cF = ⊤)
    (hdF : F.F (dF + 1) = ⊥) (hcG : G.F cG = ⊤) (r n : ℤ) :
    ∃ σ : (∏ᶜ fun a : ℤ ↦ internalHomObj (F.gr a) (G.gr (a + r))).X n ⟶
        ((F.internalHom G).F r : CochainComplex C ℤ).X n,
      ∀ a, σ ≫ (F.grInternalHomπ G (hF a) r).f n =
        (Pi.π (fun a : ℤ ↦ internalHomObj (F.gr a) (G.gr (a + r))) a).f n := by
  choose s hs₁ hs₂ using fun a p ↦ F.exists_gradedProjection cF hcF hF a p
  choose t ht₁ ht₂ using fun b q ↦ G.exists_gradedProjection cG hcG hG b q
  have hs₁' : ∀ a p, (F.F a).arrow.f p ≫ s a p = (F.gradedπ a).f p := hs₁
  have ht₁' : ∀ b q, (G.F b).arrow.f q ≫ t b q = (G.gradedπ b).f q := ht₁
  let k : ∀ b q, (G.gr b).X q ⟶ (G.F b : CochainComplex C ℤ).X q :=
    fun b q ↦ (hG b q).exists_splitEpi.some.section_
  have hk : ∀ b q, k b q ≫ (G.gradedπ b).f q = 𝟙 _ :=
    fun b q ↦ (hG b q).exists_splitEpi.some.id
  let j : ∀ a p, (F.gr a).X p ⟶ (F.F a : CochainComplex C ℤ).X p :=
    fun a p ↦ (hF a p).exists_splitEpi.some.section_
  have hj : ∀ a p, j a p ≫ (F.gradedπ a).f p = 𝟙 _ :=
    fun a p ↦ (hF a p).exists_splitEpi.some.id
  let φ : ∀ (a p q : ℤ) (_ : p + n = q),
      (∏ᶜ fun a : ℤ ↦ internalHomObj (F.gr a) (G.gr (a + r))).X n ⟶ (ihom (M.X p)).obj (N.X q) :=
    fun a p q h ↦ (Pi.π (fun a : ℤ ↦ internalHomObj (F.gr a) (G.gr (a + r))) a).f n ≫
      internalHomπ (F.gr a) (G.gr (a + r)) n p q h ≫
      (pre (s a p)).app _ ≫ (ihom _).map (k (a + r) q ≫ (G.F (a + r)).arrow.f q)
  let σ' : (∏ᶜ fun a : ℤ ↦ internalHomObj (F.gr a) (G.gr (a + r))).X n ⟶
      (internalHomObj M N).X n :=
    Pi.lift fun T : HomComplex.Triplet n ↦ ∑ a ∈ Finset.Icc cF dF, φ a T.p T.q T.hpq
  have hσ' : ∀ p q h, σ' ≫ internalHomπ M N n p q h = ∑ a ∈ Finset.Icc cF dF, φ a p q h :=
    fun p q h ↦ lift_internalHomπ _ _ _ _ _
  obtain ⟨σ, hσ⟩ := F.exists_lift_arrow_f G r n σ' fun a' p q h ↦ by
    rw [← assoc, hσ', Preadditive.sum_comp]
    refine Finset.sum_eq_zero fun a _ ↦ ?_
    simp only [φ, assoc, pre_app_comp_ihom_map_comp_pre_app_assoc]
    rcases lt_or_ge a a' with h' | h'
    · rw [hs₂ a p a' h', pre_zero_app, zero_comp, comp_zero, comp_zero]
    · rw [← Functor.map_comp, assoc, ← HomologicalComplex.comp_f,
        G.arrow_comp_π_eq_zero (show a' + r ≤ a + r by omega), HomologicalComplex.zero_f,
        comp_zero, Functor.map_zero, comp_zero, comp_zero, comp_zero]
  refine ⟨σ, fun a ↦ internalHomObj_hom_ext fun p q h ↦ ?_⟩
  by_cases ha : a ∈ Finset.Icc cF dF
  swap
  · refine ext_of_isZero_ihom ?_ _ _
    refine (HomologicalComplex.eval C _ p).map_isZero ?_
    simp only [Finset.mem_Icc, not_and_or, not_le] at ha
    rcases ha with h' | h'
    · exact F.isZero_gradedPiece_of_eq_top (top_le_iff.1 (hcF ▸ F.antitone (by omega)))
    · exact F.isZero_gradedPiece_of_eq_bot (le_bot_iff.1 (hdF ▸ F.antitone (by omega)))
  rw [assoc, F.grInternalHomπ_f_π G (hF a) r n p q h (j a p) (hj a p) (t (a + r) q)
    (ht₁' _ _), reassoc_of% hσ, reassoc_of% hσ', Preadditive.sum_comp,
    Finset.sum_eq_single_of_mem a ha]
  · simp only [φ, assoc, pre_app_comp_ihom_map_comp_pre_app_assoc, ← Functor.map_comp,
      pre_app_comp_ihom_map_comp_pre_app, hs₁', hj, ht₁', hk, pre_id, NatTrans.id_app,
      Functor.map_id, comp_id]
  · intro a'' _ hne
    simp only [φ, assoc, pre_app_comp_ihom_map_comp_pre_app_assoc, ← Functor.map_comp,
      pre_app_comp_ihom_map_comp_pre_app]
    rcases lt_or_gt_of_ne hne with h' | h'
    · rw [hs₂ a'' p a h', comp_zero, pre_zero_app, zero_comp, comp_zero, comp_zero]
    · rw [ht₂ (a + r) q (a'' + r) (by omega), comp_zero, Functor.map_zero, comp_zero,
        comp_zero, comp_zero]

@[reassoc (attr := simp)]
lemma grInternalHomShortComplex_g_f_π (hF : ∀ a n, IsSplitEpi ((F.gradedπ a).f n)) (r n a : ℤ) :
    (F.grInternalHomShortComplex G hF r).g.f n ≫
      (Pi.π (fun a : ℤ ↦ internalHomObj (F.gr a) (G.gr (a + r))) a).f n =
      (F.grInternalHomπ G (hF a) r).f n := by
  rw [← HomologicalComplex.comp_f, grInternalHomShortComplex_g, Pi.lift_comp_π]

@[reassoc (attr := simp)]
lemma gradedπ_grInternalHomComparison (hF : ∀ a n, IsSplitEpi ((F.gradedπ a).f n)) (r : ℤ) :
    (F.internalHom G).gradedπ r ≫ F.grInternalHomComparison G hF r =
      Pi.lift fun a ↦ F.grInternalHomπ G (hF a) r :=
  cokernel.π_desc _ _ _

/-- For finite filtrations which split in each cochain degree, the sequence
`0 ⟶ F^{r+1} iHom(M, N) ⟶ Fʳ iHom(M, N) ⟶ ∏ₐ iHom(grᵃM, gr^{a+r}N) ⟶ 0` is short exact. -/
lemma grInternalHomShortComplex_shortExact (hF : ∀ a n, IsSplitEpi ((F.gradedπ a).f n))
    (hG : ∀ b n, IsSplitEpi ((G.gradedπ b).f n)) {cF dF cG : ℤ} (hcF : F.F cF = ⊤)
    (hdF : F.F (dF + 1) = ⊥) (hcG : G.F cG = ⊤) (r : ℤ) :
    (F.grInternalHomShortComplex G hF r).ShortExact := by
  refine HomologicalComplex.shortExact_of_degreewise_shortExact _ fun n ↦ ?_
  obtain ⟨σ, hσ⟩ := F.exists_section_f G hF hG hcF hdF hcG r n
  have hid : σ ≫ ((F.grInternalHomShortComplex G hF r).map (HomologicalComplex.eval C _ n)).g =
      𝟙 _ :=
    pi_X_hom_ext fun a ↦ by
      change (σ ≫ (F.grInternalHomShortComplex G hF r).g.f n) ≫ _ = 𝟙 _ ≫ _
      rw [assoc, grInternalHomShortComplex_g_f_π, hσ, id_comp]
  have hepi : Epi ((F.grInternalHomShortComplex G hF r).map (HomologicalComplex.eval C _ n)).g :=
    haveI := IsSplitEpi.mk' (SplitEpi.mk σ hid)
    inferInstance
  have hmono : Mono ((F.grInternalHomShortComplex G hF r).map
      (HomologicalComplex.eval C _ n)).f :=
    (HomologicalComplex.eval C _ n).map_mono (Subobject.ofLE _ _ ((F.internalHom G).F_succ_le r))
  refine ShortComplex.ShortExact.mk' ?_ hmono hepi
  rw [ShortComplex.exact_iff_exact_up_to_refinements]
  intro A x hx
  obtain ⟨y, hy⟩ := F.exists_lift_ofLE_f G hF hG hdF hcG r n x fun a ↦ by
    have := congr_arg (· ≫ (Pi.π (fun a : ℤ ↦ internalHomObj (F.gr a) (G.gr (a + r))) a).f n) hx
    change (x ≫ (F.grInternalHomShortComplex G hF r).g.f n) ≫ _ = 0 ≫ _ at this
    rwa [assoc, grInternalHomShortComplex_g_f_π, zero_comp] at this
  exact ⟨A, 𝟙 A, inferInstance, y, by simpa using hy.symm⟩

/-- **Graded pieces of the filtered internal hom.** For finite filtrations of `M` and `N` which
split in each cochain degree, the canonical comparison
`grʳ iHom(M, N) ⟶ ∏ₐ iHom(grᵃM, gr^{a+r}N)` is an isomorphism. -/
theorem isIso_grInternalHomComparison (hF : ∀ a n, IsSplitEpi ((F.gradedπ a).f n))
    (hG : ∀ b n, IsSplitEpi ((G.gradedπ b).f n)) {cF dF cG : ℤ} (hcF : F.F cF = ⊤)
    (hdF : F.F (dF + 1) = ⊥) (hcG : G.F cG = ⊤) (r : ℤ) :
    IsIso (F.grInternalHomComparison G hF r) := by
  have hS := F.grInternalHomShortComplex_shortExact G hF hG hcF hdF hcG r
  let e := (cokernelIsCokernel (F.grInternalHomShortComplex G hF r).f).coconePointUniqueUpToIso
    hS.gIsCokernel
  have he : e.hom = F.grInternalHomComparison G hF r := by
    refine coequalizer.hom_ext ?_
    have := (cokernelIsCokernel _).comp_coconePointUniqueUpToIso_hom hS.gIsCokernel
      WalkingParallelPair.one
    simp only [Cofork.ofπ_ι_app] at this
    exact this.trans (cokernel.π_desc _ _ _).symm
  rw [← he]
  infer_instance

/-- **Graded pieces of the filtered internal hom.** For finite filtrations of `M` and `N` which
split in each cochain degree, `grʳ iHom(M, N) ≅ ∏ₐ iHom(grᵃM, gr^{a+r}N)`. -/
noncomputable def grInternalHomIso (hF : ∀ a n, IsSplitEpi ((F.gradedπ a).f n))
    (hG : ∀ b n, IsSplitEpi ((G.gradedπ b).f n)) {cF dF cG : ℤ} (hcF : F.F cF = ⊤)
    (hdF : F.F (dF + 1) = ⊥) (hcG : G.F cG = ⊤) (r : ℤ) :
    (F.internalHom G).gr r ≅ ∏ᶜ fun a : ℤ ↦ internalHomObj (F.gr a) (G.gr (a + r)) :=
  haveI := F.isIso_grInternalHomComparison G hF hG hcF hdF hcG r
  asIso (F.grInternalHomComparison G hF r)

end Filtration

section Dual

variable {K : CochainComplex C ℤ} (F : DecreasingFiltration K) (ω : CochainComplex C ℤ)

/-- Only the factor `a` of `∏_{a'} iHom(gr^{a'}K, gr^{a' - a}ω)` is nonzero. -/
lemma isIso_π_internalHomObj_trivial (a : ℤ) :
    IsIso (Pi.π (fun a' : ℤ ↦ internalHomObj (F.gr a') ((trivial ω).gr (a' + -a))) a) :=
  CategoryTheory.Limits.Pi.isIso_π_of_isZero _ a
    fun a' h ↦ isZero_internalHomObj _ (isZero_trivial_gr ω (by omega))

/-- **Graded pieces of the filtered dual.** For a finite filtration of `K` which splits in each
cochain degree and `ω` filtered in weight zero, the graded pieces of the filtered dual
`𝔻_F K = iHom_F(K, ω)` are `gr⁻ᵃ 𝔻_F K ≅ iHom(grᵃK, ω)`. -/
noncomputable def grInternalHomTrivialIso (hF : ∀ a n, IsSplitEpi ((F.gradedπ a).f n))
    {cF dF : ℤ} (hcF : F.F cF = ⊤) (hdF : F.F (dF + 1) = ⊥) (a : ℤ) :
    (F.internalHom (trivial ω)).gr (-a) ≅ internalHomObj (F.gr a) ω :=
  haveI := isIso_π_internalHomObj_trivial F ω a
  F.grInternalHomIso (trivial ω) hF (trivial_isSplitEpi_gradedπ ω) hcF hdF
      (trivial_F_of_le ω le_rfl) (-a) ≪≫
    asIso (Pi.π (fun a' : ℤ ↦ internalHomObj (F.gr a') ((trivial ω).gr (a' + -a))) a) ≪≫
    internalHomPostIso _ (trivialGrIso ω (add_neg_cancel a))

/-- The isomorphism `gr⁻ᵃ 𝔻_F K ≅ iHom(grᵃK, ω)` is induced by restricting a map in `F⁻ᵃ 𝔻_F K`
to `FᵃK`. -/
@[reassoc]
lemma gradedπ_grInternalHomTrivialIso_hom_comp_internalHomPre
    (hF : ∀ a n, IsSplitEpi ((F.gradedπ a).f n)) {cF dF : ℤ} (hcF : F.F cF = ⊤)
    (hdF : F.F (dF + 1) = ⊥) (a : ℤ) :
    (F.internalHom (trivial ω)).gradedπ (-a) ≫ (F.grInternalHomTrivialIso ω hF hcF hdF a).hom ≫
      internalHomPre (F.gradedπ a) ω =
      ((F.internalHom (trivial ω)).F (-a)).arrow ≫ internalHomPre (F.F a).arrow ω := by
  simp only [grInternalHomTrivialIso, grInternalHomIso, Iso.trans_hom, asIso_hom,
    internalHomPostIso_hom, assoc]
  rw [gradedπ_grInternalHomComparison_assoc, Pi.lift_comp_π_assoc,
    ← internalHomPre_comp_internalHomPost, grInternalHomπ_comp_internalHomPre_assoc,
    ← internalHomPost_comp, gradedπ_trivialGrIso_hom, internalHomRestrict_comp_internalHomPost]

/-- **The filtered evaluation.** Since `ω` is filtered in weight zero, the evaluation
`K ⊗ 𝔻_F K ⟶ ω` kills `FᵃK ⊗ Fᵇ 𝔻_F K` for `a + b > 0`, i.e. it is filtered for the
convolution filtration of `K ⊗ 𝔻_F K`. -/
lemma tensorHom_arrow_comp_counit_eq_zero {a b : ℤ} (hab : 0 < a + b) :
    ((F.F a).arrow ⊗ₘ ((F.internalHom (trivial ω)).F b).arrow) ≫
      (tensorHomAdjunction K).counit.app ω = 0 := by
  have h : ((F.internalHom (trivial ω)).F b).arrow ≫ internalHomPre (F.F a).arrow ω = 0 := by
    have hz : IsZero (((trivial ω).F (a + b) : CochainComplex C ℤ)) :=
      trivial_F_of_pos ω hab ▸ (Subobject.botCoeIsoZero (B := ω)).isZero_iff.2 (isZero_zero _)
    have : IsIso (cokernel.π ((trivial ω).F (a + b)).arrow) :=
      cokernel.π_of_zero (hz.eq_of_src _ _)
    rw [← cancel_mono (internalHomPost _ (cokernel.π ((trivial ω).F (a + b)).arrow)), assoc,
      arrow_internalHom_comp_internalHomPre_comp_internalHomPost, zero_comp]
  rw [tensorHom_def', assoc, ← whiskerLeft_internalHomPre_comp_counit,
    ← MonoidalCategory.whiskerLeft_comp_assoc, h, MonoidalPreadditive.whiskerLeft_zero, zero_comp]

/-- **The filtered evaluation on graded pieces.** On `FᵃK ⊗ F⁻ᵃ 𝔻_F K`, the filtered evaluation
`K ⊗ 𝔻_F K ⟶ ω` factors through the summand `grᵃK ⊗ gr⁻ᵃ 𝔻_F K` of `gr⁰(K ⊗ 𝔻_F K)`, and
under `gr⁻ᵃ 𝔻_F K ≅ iHom(grᵃK, ω)` it is the evaluation `grᵃK ⊗ iHom(grᵃK, ω) ⟶ ω`. -/
lemma tensorHom_gradedπ_comp_counit (hF : ∀ a n, IsSplitEpi ((F.gradedπ a).f n))
    {cF dF : ℤ} (hcF : F.F cF = ⊤) (hdF : F.F (dF + 1) = ⊥) (a : ℤ) :
    (F.gradedπ a ⊗ₘ ((F.internalHom (trivial ω)).gradedπ (-a) ≫
        (F.grInternalHomTrivialIso ω hF hcF hdF a).hom)) ≫
      (tensorHomAdjunction (F.gr a)).counit.app ω =
      ((F.F a).arrow ⊗ₘ ((F.internalHom (trivial ω)).F (-a)).arrow) ≫
        (tensorHomAdjunction K).counit.app ω := by
  rw [tensorHom_def', tensorHom_def', assoc, assoc, ← whiskerLeft_internalHomPre_comp_counit,
    ← whiskerLeft_internalHomPre_comp_counit, ← MonoidalCategory.whiskerLeft_comp_assoc,
    ← MonoidalCategory.whiskerLeft_comp_assoc, assoc,
    gradedπ_grInternalHomTrivialIso_hom_comp_internalHomPre]

end Dual

end CategoryTheory.DecreasingFiltration
