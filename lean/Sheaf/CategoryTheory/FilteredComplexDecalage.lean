/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group J4
-/
module

public import Sheaf.Algebra.Homology.FilteredComplexSubquotients
import all Sheaf.CategoryTheory.FilteredQuotientPageMaps

/-! # Canonical decalage of a filtered cochain complex

Source: Stacks Project, Tag 015X, Remark 13.26.15; Tag 012K.
(blueprint: lem-sp-filtered-complex-decalage).
-/

@[expose] public section
set_option autoImplicit false
universe u v
open CategoryTheory CategoryTheory.Limits
namespace CategoryTheory.DecreasingFiltration
variable {C : Type u} [Category.{v} C] [Abelian C]

private theorem complex_factor_of_degreewise
    {C : Type u} [Category.{v} C] [Abelian C]
    {K K' : CochainComplex C ℤ} (S : Subobject K) (T : Subobject K') (f : K ⟶ K')
    (h : ∀ n : ℤ, (imageSubobject (T.arrow.f n)).Factors (S.arrow.f n ≫ f.f n)) :
    ∃ k : (S : CochainComplex C ℤ) ⟶ (T : CochainComplex C ℤ),
      k ≫ T.arrow = S.arrow ≫ f := by
  have hh (n : ℤ) : ∃ k : (S : CochainComplex C ℤ).X n ⟶
      (T : CochainComplex C ℤ).X n, k ≫ T.arrow.f n = S.arrow.f n ≫ f.f n := by
    have hn := h n
    rw [imageSubobject_mono, Subobject.mk_factors_iff] at hn
    exact hn
  choose k hk using hh
  let g : (S : CochainComplex C ℤ) ⟶ (T : CochainComplex C ℤ) :=
    { f := k
      comm' := by
        intro i j hij
        apply (cancel_mono (T.arrow.f j)).1
        rw [Category.assoc, ← T.arrow.comm, ← Category.assoc, hk, Category.assoc,
          f.comm, ← Category.assoc, S.arrow.comm]
        simp only [Category.assoc, hk] }
  exact ⟨g, by ext n; exact hk n⟩

set_option backward.isDefEq.respectTransparency false in
/-- The unique decalage filtration, functorial for every filtered cochain map.
Source: Stacks Project, Tag 015X, Remark 13.26.15, and Tag 012K.
(blueprint: lem-sp-filtered-complex-decalage).

Proof. In degree n take the intersection of F^(a+n) with the inverse image of
F^(a+n+1) under the differential. Its differential lands in the next such
intersection: the first condition is the inverse-image condition in the
source, and the second follows from d squared equal to zero. The restricted
differentials therefore assemble into subcomplexes. Monotonicity of F and of
inverse image gives the decreasing transition maps. Their degreewise images
are precisely the prescribed intersections. A filtered cochain map preserves
the two intersected subobjects by its filtration equation and its chain-map
equation. Restricting it through the monic subcomplex inclusions gives the
required filtered map. Finally equal degreewise subobjects yield inclusions
in both directions between subcomplexes, by the same restriction argument;
antisymmetry and function extensionality prove uniqueness of the filtration.
No boundedness, finiteness or exactness hypothesis is used. -/
theorem exists_decalage {C : Type u} [Category.{v} C] [Abelian C]
    {K : CochainComplex C ℤ} (F : DecreasingFiltration K) :
    ∃! D : DecreasingFiltration K, (∀ a n : ℤ,
      D.complexStep a n = F.complexStep (a + n) n ⊓
        (Subobject.pullback (K.d n (n + 1))).obj
          (F.complexStep (a + n + 1) (n + 1))) ∧
      ∀ {K' : CochainComplex C ℤ} (F' D' : DecreasingFiltration K'),
        (∀ a n : ℤ, D'.complexStep a n = F'.complexStep (a + n) n ⊓
          (Subobject.pullback (K'.d n (n + 1))).obj
            (F'.complexStep (a + n + 1) (n + 1))) →
        ∀ t : (⟨K, F⟩ : FilteredObject (CochainComplex C ℤ)) ⟶ ⟨K', F'⟩,
          ∃ s : (⟨K, D⟩ : FilteredObject (CochainComplex C ℤ)) ⟶ ⟨K', D'⟩,
            s.hom = t.hom := by
  classical
  let S (a n : ℤ) : Subobject (K.X n) := F.complexStep (a + n) n ⊓
    (Subobject.pullback (K.d n (n + 1))).obj
      (F.complexStep (a + n + 1) (n + 1))
  have hstep (p q : ℤ) (hpq : p ≤ q) (n : ℤ) :
      F.complexStep q n ≤ F.complexStep p n := by
    dsimp only [complexStep]
    rw [imageSubobject_mono, imageSubobject_mono]
    apply Subobject.mk_le_mk_of_comm ((Subobject.ofLE (F.step q) (F.step p)
      (F.antitone_step hpq)).f n)
    exact congrArg (fun k ↦ k.f n) (Subobject.ofLE_arrow (F.antitone_step hpq))
  have hanti (n : ℤ) : Antitone (fun a ↦ S a n) := by
    intro a b hab
    apply inf_le_inf
    · exact hstep _ _ (by omega) n
    · exact (Subobject.pullback (K.d n (n + 1))).monotone (hstep _ _ (by omega) (n + 1))
  have hfact (a n : ℤ) : (S a (n + 1)).Factors ((S a n).arrow ≫ K.d n (n + 1)) := by
    apply (Subobject.inf_factors _).mpr
    constructor
    · have hh := (pullback_factors_iff _ _ _).mp
        (Subobject.factors_right_of_inf_factors (S a n).factors_self)
      simpa only [add_assoc] using hh
    · apply (pullback_factors_iff _ _ _).mpr
      simp only [Category.assoc, K.d_comp_d, comp_zero]
      exact Subobject.factors_zero
  let f (a n : ℤ) := (S a (n + 1)).factorThru ((S a n).arrow ≫ K.d n (n + 1)) (hfact a n)
  have hf (a n : ℤ) : f a n ≫ (S a (n + 1)).arrow = (S a n).arrow ≫ K.d n (n + 1) :=
    Subobject.factorThru_arrow _ _ _
  have hsq (a n : ℤ) : f a n ≫ f a (n + 1) = 0 := by
    apply (cancel_mono (S a ((n + 1) + 1)).arrow).1
    rw [Category.assoc, hf, ← Category.assoc, hf, Category.assoc,
      K.d_comp_d, comp_zero, zero_comp]
  let U := fun a ↦ CochainComplex.of (fun n ↦ (S a n : C)) (f a) (hsq a)
  let i : ∀ a, U a ⟶ K := fun a ↦ CochainComplex.ofHom
    (fun n ↦ (S a n).arrow) (by intro n; simpa [U] using (hf a n).symm)
  have hi : ∀ a n, (i a).f n = (S a n).arrow := fun _ _ ↦ rfl
  have hmono : ∀ a, Mono (i a) := fun a ↦
    HomologicalComplex.mono_of_mono_f _ (fun n ↦ by dsimp [i]; infer_instance)
  let : ∀ a, Mono (i a) := hmono
  have hu : Antitone (fun a ↦ Subobject.mk (i a)) := by
    intro a b hab
    let c : U b ⟶ U a := CochainComplex.ofHom
      (fun n ↦ Subobject.ofLE (S b n) (S a n) (hanti n hab)) (by
        intro n
        apply (cancel_mono (S a (n + 1)).arrow).1
        simp only [U, CochainComplex.of_d, Category.assoc, hf, Subobject.ofLE_arrow]
        rw [← Category.assoc, Subobject.ofLE_arrow])
    apply Subobject.mk_le_mk_of_comm c
    ext n
    exact Subobject.ofLE_arrow _
  let D : DecreasingFiltration K := ⟨fun a ↦ Subobject.mk (i a), fun a ↦ hu (by omega)⟩
  have hD (a n : ℤ) : D.complexStep a n = S a n := by
    let e := Subobject.underlyingIso (i a)
    have he : (D.step a).arrow = e.hom ≫ i a :=
      (Subobject.underlyingIso_hom_comp_eq_mk (i a)).symm
    dsimp only [complexStep]
    simp only [he, HomologicalComplex.comp_f]
    have : IsIso (e.hom.f n) := inferInstance
    rw [imageSubobject_iso_comp]
    simp only [hi, imageSubobject_mono, Subobject.mk_arrow]
  refine ⟨D, ⟨hD, ?_⟩, ?_⟩
  · intro K' F' D' hD' t
    refine ⟨⟨t.hom, ?_⟩, rfl⟩
    intro a
    apply complex_factor_of_degreewise
    intro n
    have hle : D.complexStep a n ≤
        (Subobject.pullback (t.hom.f n)).obj (D'.complexStep a n) := by
      rw [hD, hD']
      apply subobject_preserves_inf
      · exact filtered_step_preserved t (a + n) n
      · exact subobject_preserves_pullback _ _ _ _ (t.hom.comm n (n + 1)).symm
          _ _ (filtered_step_preserved t (a + n + 1) (n + 1))
    have hf := Subobject.factors_of_le _ hle
      (imageSubobject_factors_comp_self ((D.step a).arrow.f n) (𝟙 _))
    simp only [Category.id_comp] at hf
    exact (pullback_factors_iff _ _ _).mp hf
  · intro D' hD'
    have hle (D₁ D₂ : DecreasingFiltration K)
        (h : ∀ a n : ℤ, D₁.complexStep a n ≤ D₂.complexStep a n) (a : ℤ) :
        D₁.step a ≤ D₂.step a := by
      obtain ⟨k, hk⟩ := complex_factor_of_degreewise (D₁.step a) (D₂.step a) (𝟙 K) (by
        intro n
        change (D₂.complexStep a n).Factors ((D₁.step a).arrow.f n ≫ (𝟙 K : K ⟶ K).f n)
        simp only [HomologicalComplex.id_f, Category.comp_id]
        apply Subobject.factors_of_le _ (h a n)
        simpa only [complexStep, Category.id_comp] using
          imageSubobject_factors_comp_self ((D₁.step a).arrow.f n) (𝟙 _))
      exact Subobject.le_of_comm k (by simpa only [Category.comp_id] using hk)
    have heq (a n : ℤ) : D'.complexStep a n = D.complexStep a n :=
      (hD'.1 a n).trans (hD a n).symm
    have hobj (a : ℤ) : D'.step a = D.step a :=
      le_antisymm (hle D' D (fun a n ↦ (heq a n).le) a)
        (hle D D' (fun a n ↦ (heq a n).ge) a)
    have ext_filtration (E E' : DecreasingFiltration K)
        (h : ∀ a : ℤ, E.step a = E'.step a) : E = E' := by
      cases E
      cases E'
      congr 1
      funext a
      exact h a
    exact ext_filtration D' D hobj
/-- The canonical decalage, chosen from the proved unique characterization above.
(blueprint: lem-sp-filtered-complex-decalage). -/
noncomputable def decalage {K : CochainComplex C ℤ} (F : DecreasingFiltration K) :
    DecreasingFiltration K := (exists_decalage F).exists.choose

/-- The degreewise subobject formula characterizing decalage. -/
theorem decalage_complexStep {K : CochainComplex C ℤ} (F : DecreasingFiltration K)
    (a n : ℤ) :
    F.decalage.complexStep a n = F.complexStep (a + n) n ⊓
      (Subobject.pullback (K.d n (n + 1))).obj
        (F.complexStep (a + n + 1) (n + 1)) :=
  (exists_decalage F).exists.choose_spec.1 a n

/-- Decalage preserves each filtered map, with the same underlying cochain map. -/
theorem decalage_map_preserves {U V : FilteredObject (CochainComplex C ℤ)} (t : U ⟶ V)
    (a : ℤ) :
    ∃ k : (U.filtration.decalage.step a : CochainComplex C ℤ) ⟶
        (V.filtration.decalage.step a : CochainComplex C ℤ),
      k ≫ (V.filtration.decalage.step a).arrow =
        (U.filtration.decalage.step a).arrow ≫ t.hom := by
  obtain ⟨s, hs⟩ := (exists_decalage U.filtration).exists.choose_spec.2
    V.filtration V.filtration.decalage (decalage_complexStep V.filtration) t
  simpa only [hs, decalage] using s.preserves a

/-- The canonical decalage endofunctor on filtered cochain complexes.
The underlying complex and underlying maps are preserved.
(blueprint: lem-sp-filtered-complex-decalage). -/
noncomputable def decalageFunctor : FilteredObject (CochainComplex C ℤ) ⥤
    FilteredObject (CochainComplex C ℤ) where
  obj U := ⟨U.obj, U.filtration.decalage⟩
  map t := ⟨t.hom, decalage_map_preserves t⟩
  map_id U := by rfl
  map_comp t s := by rfl

end CategoryTheory.DecreasingFiltration
