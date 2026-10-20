/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group E1
-/
module

public import WeilConjectures.Algebra.Homology.FilteredComplexSubquotients
public import Sheaf.CategoryTheory.FilteredPageTwoModel
public import Mathlib.Algebra.Homology.Homotopy
import Sheaf.CategoryTheory.FiniteFiltrationInduction

/-!
# Filtered homotopies and spectral sequences

Source: Stacks Project, Homology, Lemma 012O and Definition 012U
(blueprint: lem-sp-filtered-homotopy-spectral-sequence).
-/

@[expose] public section

universe v u

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] [Abelian C]

private theorem quotient_homotopy
    {A₀ A B₀ B : CochainComplex C ℤ} (i : A₀ ⟶ A) (j : B₀ ⟶ B)
    {f g : A ⟶ B} (H : Homotopy f g)
    (f' g' : cokernel i ⟶ cokernel j)
    (hf : cokernel.π i ≫ f' = f ≫ cokernel.π j)
    (hg : cokernel.π i ≫ g' = g ≫ cokernel.π j)
    (hz : ∀ n m, i.f n ≫ H.hom n m ≫ (cokernel.π j).f m = 0) :
    Nonempty (Homotopy f' g') := by
  classical
  let d (n m : ℤ) : { l : (cokernel i).X n ⟶ (cokernel j).X m //
      (cokernel.π i).f n ≫ l = H.hom n m ≫ (cokernel.π j).f m } :=
    CokernelCofork.IsColimit.desc'
    (isColimitOfHasCokernelOfPreservesColimit
      (HomologicalComplex.eval C (ComplexShape.up ℤ) n) i)
    (H.hom n m ≫ (cokernel.π j).f m) (hz n m)
  have hd (n m : ℤ) : (cokernel.π i).f n ≫ (d n m).1 =
      H.hom n m ≫ (cokernel.π j).f m := (d n m).2
  refine ⟨{ hom := fun n m ↦ (d n m).1, zero := ?_, comm := ?_ }⟩
  · intro n m hnm
    apply (cancel_epi ((cokernel.π i).f n)).1
    simp only [hd, H.zero n m hnm, zero_comp, comp_zero]
  · intro n
    apply (cancel_epi ((cokernel.π i).f n)).1
    have hf' := congrArg (fun k ↦ HomologicalComplex.Hom.f k n) hf
    have hg' := congrArg (fun k ↦ HomologicalComplex.Hom.f k n) hg
    dsimp at hf' hg'
    change (cokernel.π i).f n ≫ f'.f n = (cokernel.π i).f n ≫
      ((cokernel i).d n ((ComplexShape.up ℤ).next n) ≫ (d ((ComplexShape.up ℤ).next n) n).1 +
        (d n ((ComplexShape.up ℤ).prev n)).1 ≫
          (cokernel j).d ((ComplexShape.up ℤ).prev n) n + g'.f n)
    have hh := H.comm n
    change f.f n = A.d n ((ComplexShape.up ℤ).next n) ≫ H.hom _ _ +
      H.hom _ _ ≫ B.d ((ComplexShape.up ℤ).prev n) n + g.f n at hh
    rw [Preadditive.comp_add, Preadditive.comp_add, hf', hg', hh,
      Preadditive.add_comp, Preadditive.add_comp]
    congr 2
    · simp only [Category.assoc, (cokernel.π i).comm_assoc, hd]
    · rw [Category.assoc, ← (cokernel.π j).comm]
      simp only [← Category.assoc, hd]

private theorem step_homotopy_components
    {K L : CochainComplex C ℤ}
    (F : DecreasingFiltration K) (G : DecreasingFiltration L)
    {a b : K ⟶ L} (H : Homotopy a b)
    (hshift : ∀ (p n : ℤ), ∃ ℓ :
      (F.complexStep p n : C) ⟶ (G.complexStep (p - 1) (n - 1) : C),
      ℓ ≫ (G.complexStep (p - 1) (n - 1)).arrow =
        (F.complexStep p n).arrow ≫ H.hom n (n - 1)) :
    ∀ p, ∃ h : ∀ n m, (F.step p : CochainComplex C ℤ).X n ⟶
        (G.step (p - 1) : CochainComplex C ℤ).X m,
      (∀ n m, ¬ (ComplexShape.up ℤ).Rel m n → h n m = 0) ∧
      ∀ n m, h n m ≫ (G.step (p - 1)).arrow.f m =
        (F.step p).arrow.f n ≫ H.hom n m := by
  classical
  intro p
  have lift (n : ℤ) : ∃ h : (F.step p : CochainComplex C ℤ).X n ⟶
      (G.step (p - 1) : CochainComplex C ℤ).X (n - 1),
      h ≫ (G.step (p - 1)).arrow.f (n - 1) =
        (F.step p).arrow.f n ≫ H.hom n (n - 1) := by
    obtain ⟨ℓ, hℓ⟩ := hshift p n
    refine ⟨factorThruImageSubobject ((F.step p).arrow.f n) ≫ ℓ ≫
      (imageSubobjectIso ((G.step (p - 1)).arrow.f (n - 1))).hom ≫
        (imageMonoIsoSource ((G.step (p - 1)).arrow.f (n - 1))).hom, ?_⟩
    simp only [Category.assoc, imageMonoIsoSource_hom_self, imageSubobject_arrow]
    change factorThruImageSubobject ((F.step p).arrow.f n) ≫
      ℓ ≫ (G.complexStep (p - 1) (n - 1)).arrow = _
    rw [hℓ, ← Category.assoc]
    simp only [DecreasingFiltration.complexStep, imageSubobject_arrow_comp]
  let h (n m : ℤ) : (F.step p : CochainComplex C ℤ).X n ⟶
      (G.step (p - 1) : CochainComplex C ℤ).X m := by
    by_cases he : m = n - 1
    · subst m
      exact (lift n).choose
    · exact 0
  refine ⟨h, ?_, ?_⟩
  · intro n m hnm
    have he : m ≠ n - 1 := by
      intro he
      apply hnm
      simp only [ComplexShape.up_Rel]
      omega
    simp [h, he]
  · intro n m
    by_cases he : m = n - 1
    · subst m
      simpa only [h, dif_pos] using (lift n).choose_spec
    · have hnm : ¬ (ComplexShape.up ℤ).Rel m n := by
        simp only [ComplexShape.up_Rel]
        omega
      simp [h, he, H.zero n m hnm]

private theorem lift_homotopy
    {A B K L : CochainComplex C ℤ} (i : A ⟶ K) (j : B ⟶ L) [Mono j]
    {a b : K ⟶ L} (H : Homotopy a b) {f g : A ⟶ B}
    (hf : f ≫ j = i ≫ a) (hg : g ≫ j = i ≫ b)
    (h : ∀ n m, A.X n ⟶ B.X m)
    (hz : ∀ n m, ¬ (ComplexShape.up ℤ).Rel m n → h n m = 0)
    (hh : ∀ n m, h n m ≫ j.f m = i.f n ≫ H.hom n m) :
    ∃ Hs : Homotopy f g, Hs.hom = h := by
  refine ⟨{ hom := h, zero := hz, comm := ?_ }, rfl⟩
  intro n
  apply (cancel_mono (j.f n)).1
  have hf' := congrArg (fun k ↦ HomologicalComplex.Hom.f k n) hf
  have hg' := congrArg (fun k ↦ HomologicalComplex.Hom.f k n) hg
  dsimp at hf' hg'
  change f.f n ≫ j.f n =
    (A.d n ((ComplexShape.up ℤ).next n) ≫ h _ _ +
      h _ _ ≫ B.d ((ComplexShape.up ℤ).prev n) n + g.f n) ≫ j.f n
  have hc := H.comm n
  change a.f n = K.d n ((ComplexShape.up ℤ).next n) ≫ H.hom _ _ +
    H.hom _ _ ≫ L.d ((ComplexShape.up ℤ).prev n) n + b.f n at hc
  rw [hf', hc, Preadditive.comp_add, Preadditive.comp_add,
    Preadditive.add_comp, Preadditive.add_comp, hg']
  congr 2
  · rw [Category.assoc, hh]
    simp only [← Category.assoc, i.comm]
  · rw [Category.assoc, ← j.comm]
    simp only [← Category.assoc, hh]

-- A supplied page model makes boundedness unnecessary for the page-map calculation.
-- Keep the boundedness binders for compatibility with the original statement.
set_option linter.unusedVariables false in
/-- The page-map part of filtered homotopy invariance.

The filtration-shifting homotopy calculation is performed on the `Z_r/B_r`
representatives supplied by the bounded filtered-complex spectral-sequence
construction.  For `r ≥ 2`, the homotopy term lies in the boundary filtration,
so the induced page maps coincide.
Source: Stacks Project, Homology, Lemma 012O.
(blueprint: lem-sp-filtered-homotopy-spectral-sequence-page-map) -/
theorem filteredHomotopy_page_map_eq
    (K L : CochainComplex C ℤ)
    (F : DecreasingFiltration K) (G : DecreasingFiltration L)
    (hKF : ∀ n : ℤ, ∃ pmin : ℤ, ∃ pmax : ℤ,
      F.complexStep pmin n = ⊤ ∧ F.complexStep pmax n = ⊥)
    (hLG : ∀ n : ℤ, ∃ pmin : ℤ, ∃ pmax : ℤ,
      G.complexStep pmin n = ⊤ ∧ G.complexStep pmax n = ⊥)
    (a b : FilteredObject.Hom ⟨K, F⟩ ⟨L, G⟩)
    (H : Homotopy a.hom b.hom)
    (hshift : ∀ (p n : ℤ), ∃ ℓ :
      (F.complexStep p n : C) ⟶ (G.complexStep (p - 1) (n - 1) : C),
      ℓ ≫ (G.complexStep (p - 1) (n - 1)).arrow =
        (F.complexStep p n).arrow ≫ H.hom n (n - 1)) :
    ∀ (M : FilteredPageTwoModel C), M.S.map a = M.S.map b := by
  classical
  intro M
  apply SpectralSequence.hom_ext
  intro r hr
  apply HomologicalComplex.hom_ext
  rintro ⟨p, q⟩
  obtain ⟨sa, aa, ba, hsa, haa, hba, hsqa, hpagea⟩ := M.naturality a p q r hr
  obtain ⟨sb, ab, bb, hsb, hab, hbb, hsqb, hpageb⟩ := M.naturality b p q r hr
  let inc (x y : ℤ) (hyx : y ≤ x) :=
    Subobject.ofLE (G.step x) (G.step y) (G.antitone_step hyx)
  have inc_fac (x y : ℤ) (hyx : y ≤ x) (n : ℤ) :
      (inc x y hyx).f n ≫ (G.step y).arrow.f n = (G.step x).arrow.f n := by
    rw [← HomologicalComplex.comp_f]
    exact congrArg (fun k ↦ HomologicalComplex.Hom.f k n) (Subobject.ofLE_arrow _)
  let lo := p - r + 1
  let fa := sa p ≫ inc p lo (by dsimp [lo]; omega)
  let fb := sb p ≫ inc p lo (by dsimp [lo]; omega)
  obtain ⟨h, hz, hfac⟩ := step_homotopy_components F G H hshift p
  let hc (n m : ℤ) := h n m ≫ (inc (p - 1) lo (by dsimp [lo]; omega)).f m
  have hcfac (n m : ℤ) : hc n m ≫ (G.step lo).arrow.f m =
      (F.step p).arrow.f n ≫ H.hom n m := by
    dsimp [hc]
    rw [Category.assoc, inc_fac (p - 1) lo (by dsimp [lo]; omega) m, hfac]
  obtain ⟨Hs, hHs⟩ := lift_homotopy (F.step p).arrow (G.step lo).arrow H
    (f := fa) (g := fb)
    (by dsimp [fa, inc]; rw [Category.assoc, Subobject.ofLE_arrow]; exact hsa p)
    (by dsimp [fb, inc]; rw [Category.assoc, Subobject.ofLE_arrow]; exact hsb p)
    hc (by intro n m hnm; dsimp [hc]; rw [hz n m hnm, zero_comp]) hcfac
  let i := Subobject.ofLE (F.step (p + r)) (F.step p) (F.antitone_step (by omega))
  let j := inc (p + 1) lo (by dsimp [lo]; omega)
  have hfa : F.complexQuotientπ p (p + r) (by omega) ≫
      (M.φ ⟨K, F⟩ p r hr ≫ ba) = fa ≫ G.complexQuotientπ lo (p + 1) (by
        dsimp [lo]; omega) := by
    rw [← Category.assoc, M.comm_φ ⟨K, F⟩ p r hr, Category.assoc, hba, ← Category.assoc]
    congr 1
    apply (cancel_mono (G.step lo).arrow).1
    dsimp only [fa, inc, lo]
    simp only [Category.assoc, Subobject.ofLE_arrow, hsa (p - r + 1),
      Subobject.ofLE_arrow_assoc, hsa p]
  have hfb : F.complexQuotientπ p (p + r) (by omega) ≫
      (M.φ ⟨K, F⟩ p r hr ≫ bb) = fb ≫ G.complexQuotientπ lo (p + 1) (by
        dsimp [lo]; omega) := by
    rw [← Category.assoc, M.comm_φ ⟨K, F⟩ p r hr, Category.assoc, hbb, ← Category.assoc]
    congr 1
    apply (cancel_mono (G.step lo).arrow).1
    dsimp only [fb, inc, lo]
    simp only [Category.assoc, Subobject.ofLE_arrow, hsb (p - r + 1),
      Subobject.ofLE_arrow_assoc, hsb p]
  have hkill (n m : ℤ) : i.f n ≫ Hs.hom n m ≫ (cokernel.π j).f m = 0 := by
    obtain ⟨hhi, hzhi, hhi_fac⟩ := step_homotopy_components F G H hshift (p + r)
    let k := inc (p + r - 1) lo (by dsimp [lo]; omega)
    have he : i.f n ≫ Hs.hom n m = hhi n m ≫ k.f m := by
      apply (cancel_mono ((G.step lo).arrow.f m)).1
      rw [hHs]
      rw [Category.assoc, hcfac, ← Category.assoc]
      have hi : i ≫ (F.step p).arrow = (F.step (p + r)).arrow :=
        Subobject.ofLE_arrow _
      rw [← HomologicalComplex.comp_f, hi]
      dsimp [k]
      rw [Category.assoc, inc_fac (p + r - 1) lo (by dsimp [lo]; omega) m, hhi_fac]
    have hk : k = inc (p + r - 1) (p + 1) (by omega) ≫ j := by
      dsimp [k, j, inc]
      rw [Subobject.ofLE_comp_ofLE]
    rw [← Category.assoc, he, hk, HomologicalComplex.comp_f]
    simp only [Category.assoc, ← HomologicalComplex.comp_f, cokernel.condition,
      HomologicalComplex.zero_f, comp_zero]
  -- The homotopy carries F^(p+r) into G^(p+r-1), which G^(p+1) kills.
  obtain ⟨Hq⟩ := quotient_homotopy i j Hs
    (M.φ ⟨K, F⟩ p r hr ≫ ba) (M.φ ⟨K, F⟩ p r hr ≫ bb) hfa hfb hkill
  -- Homotopy invariance descends to the homology image defining the page.
  have he := Hq.homologyMap_eq (p + q)
  rw [HomologicalComplex.homologyMap_comp, HomologicalComplex.homologyMap_comp] at he
  apply (cancel_mono ((M.pageIso ⟨L, G⟩ p q r hr).hom ≫
    image.ι (HomologicalComplex.homologyMap (M.φ ⟨L, G⟩ p r hr) (p + q)))).1
  rw [hpagea, hpageb]
  apply congrArg (fun k ↦ (M.pageIso ⟨K, F⟩ p q r hr).hom ≫ k)
  apply (cancel_epi (factorThruImage
    (HomologicalComplex.homologyMap (M.φ ⟨K, F⟩ p r hr) (p + q)))).1
  simpa only [← Category.assoc, image.fac] using he

/-- A homotopic filtered map induces a common filtered map on cohomology.

The common underlying map is the homology map of either chain map, using
`Homotopy.homologyMap_eq`.  The image descriptions of the two filtrations
then provide the required lifts on every filtration step.
Source: Stacks Project, Homology, Lemma 012O.
(blueprint: lem-sp-filtered-homotopy-spectral-sequence-filtered-abutment-map) -/
theorem exists_filteredHomology_map
    (K L : CochainComplex C ℤ)
    (F : DecreasingFiltration K) (G : DecreasingFiltration L)
    (a b : FilteredObject.Hom ⟨K, F⟩ ⟨L, G⟩)
    (H : Homotopy a.hom b.hom)
    (n : ℤ) (AF : DecreasingFiltration (K.homology n))
    (BF : DecreasingFiltration (L.homology n))
    (hAF : ∀ p : ℤ, AF.step p = imageSubobject
      (HomologicalComplex.homologyMap (F.step p).arrow n))
    (hBF : ∀ p : ℤ, BF.step p = imageSubobject
      (HomologicalComplex.homologyMap (G.step p).arrow n)) :
    ∃ t : FilteredObject.Hom ⟨K.homology n, AF⟩
        ⟨L.homology n, BF⟩,
      t.hom = HomologicalComplex.homologyMap a.hom n ∧
      t.hom = HomologicalComplex.homologyMap b.hom n ∧
      ∀ p : ℤ, ∃ lift : (AF.step p : C) ⟶ (BF.step p : C),
        lift ≫ (BF.step p).arrow = (AF.step p).arrow ≫ t.hom := by
  let f : K.homology n ⟶ L.homology n :=
    HomologicalComplex.homologyMap a.hom n
  let t : FilteredObject.Hom
      ⟨K.homology n, AF⟩ ⟨L.homology n, BF⟩ :=
    ⟨f, by
      intro p
      change ∃ lift : (AF.step p : C) ⟶ (BF.step p : C),
        lift ≫ (BF.step p).arrow = (AF.step p).arrow ≫ f
      rw [hAF p, hBF p]
      obtain ⟨s, hs⟩ := a.preserves p
      let m := HomologicalComplex.homologyMap s n
      let fi := HomologicalComplex.homologyMap (F.step p).arrow n
      let gi := HomologicalComplex.homologyMap (G.step p).arrow n
      have hm : m ≫ gi = fi ≫ f := by
        have hs' := congrArg (fun k => HomologicalComplex.homologyMap k n) hs
        simpa only [HomologicalComplex.homologyMap_comp] using hs'
      let sq : Arrow.mk fi ⟶ Arrow.mk gi := Arrow.homMk m f hm
      exact ⟨imageSubobjectMap sq, by
        exact imageSubobjectMap_arrow sq⟩⟩
  refine ⟨t, rfl, ?_, ?_⟩
  · exact H.homologyMap_eq n
  · intro p
    obtain ⟨lift, hlift⟩ := t.preserves p
    exact ⟨lift, hlift⟩

/-- A filtered chain homotopy lowers the filtration by one, so the maps it
induces on every page of a filtered-complex spectral sequence agree from the
second page onward.  The boundedness hypotheses are degreewise, as in the
filtered-complex construction.

Source: Stacks Project, Homology, Lemma 012O and Definition 012U
(blueprint: lem-sp-filtered-homotopy-spectral-sequence).

Proof.
1. Degreewise boundedness gives the filtered-complex spectral sequences and
   identifies their abutment filtrations with the images of cohomology of the steps.
2. Represent an `E_r` class by `x` in `F^p K^n` with `dx` in `F^(p+r) K^(n+1)`.
   The homotopy equation gives `(a-b)x = d(hx) + h(dx)`. Here `hx` is in
   `G^(p-1)`, hence in `G^(p-r+1)` for `r ≥ 2`, while `h(dx)` is in
   `G^(p+r-1)`, hence in `G^(p+1)`. Thus the difference lies in the boundary
   subobject plus the next filtration step and is zero on `E_r`. The page model's
   naturality identifies these maps with its spectral-sequence morphisms.
3. The homotopy makes the total cohomology maps equal. Each filtered chain map
   preserves the image filtration on cohomology. Their common cohomology map
   therefore gives one common filtered map `t`. Restrict it to step `p` and
   pass to the cokernel of step `p+1` to obtain one common graded map `g`.
   The displayed quotient-projection equation uniquely specifies this map.

The filtrations `AF` and `BF` below are pinned to the cohomology images; they
are arbitrary presentations of the abutment filtrations, not extra assumptions.
The common maps `t` and `g` express equality of the two induced maps on the
filtered abutment and its graded pieces. -/
theorem filteredHomotopy_spectralSequence_map_eq
    (K L : CochainComplex C ℤ)
    (F : DecreasingFiltration K) (G : DecreasingFiltration L)
    (hKF : ∀ n : ℤ, ∃ pmin : ℤ, ∃ pmax : ℤ,
      F.complexStep pmin n = ⊤ ∧ F.complexStep pmax n = ⊥)
    (hLG : ∀ n : ℤ, ∃ pmin : ℤ, ∃ pmax : ℤ,
      G.complexStep pmin n = ⊤ ∧ G.complexStep pmax n = ⊥)
    (a b : FilteredObject.Hom ⟨K, F⟩ ⟨L, G⟩)
    (H : Homotopy a.hom b.hom)
    (hshift : ∀ (p n : ℤ), ∃ ℓ :
      (F.complexStep p n : C) ⟶ (G.complexStep (p - 1) (n - 1) : C),
      ℓ ≫ (G.complexStep (p - 1) (n - 1)).arrow =
        (F.complexStep p n).arrow ≫ H.hom n (n - 1)) :
    (∀ (M : FilteredPageTwoModel C), M.S.map a = M.S.map b) ∧
    (∀ (n : ℤ) (AF : DecreasingFiltration (K.homology n))
      (BF : DecreasingFiltration (L.homology n)),
      (∀ p : ℤ, AF.step p = imageSubobject
        (HomologicalComplex.homologyMap (F.step p).arrow n)) →
      (∀ p : ℤ, BF.step p = imageSubobject
        (HomologicalComplex.homologyMap (G.step p).arrow n)) →
      ∃ t : FilteredObject.Hom ⟨K.homology n, AF⟩ ⟨L.homology n, BF⟩,
        t.hom = HomologicalComplex.homologyMap a.hom n ∧
        t.hom = HomologicalComplex.homologyMap b.hom n ∧
        ∀ p : ℤ, ∃ g : AF.gradedPiece p ⟶ BF.gradedPiece p,
          cokernel.π (Subobject.ofLE (AF.step (p + 1)) (AF.step p)
            (AF.antitone_step (by omega))) ≫ g =
          Classical.choose (t.preserves p) ≫
            cokernel.π (Subobject.ofLE (BF.step (p + 1)) (BF.step p)
              (BF.antitone_step (by omega)))) := by
  refine ⟨filteredHomotopy_page_map_eq K L F G hKF hLG a b H hshift, ?_⟩
  intro n AF BF hAF hBF
  obtain ⟨t, htA, htB, htpres⟩ :=
    exists_filteredHomology_map K L F G a b H n AF BF hAF hBF
  refine ⟨t, htA, htB, ?_⟩
  intro p
  obtain ⟨g, hg⟩ := FilteredObject.exists_gradedMap_steps _ _ t p
  exact ⟨g, hg⟩

end CategoryTheory
