/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group E1
-/
module

public import Sheaf.CategoryTheory.Filtration
public import Sheaf.Algebra.Homology.FilteredComplexSubquotients
public import Sheaf.CategoryTheory.FilteredPageTwoModel
public import Mathlib.Algebra.Homology.Homotopy
import Sheaf.CategoryTheory.FiniteFiltrationInduction
import Sheaf.CategoryTheory.FilteredCohomologyImage
import Sheaf.CategoryTheory.BoundedFilteredComplexSpectralSequence

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
    (a b : FilteredObject.HomPreservingSteps ⟨K, F⟩ ⟨L, G⟩)
    (H : Homotopy a.hom b.hom)
    (hshift : ∀ (p n : ℤ), ∃ ℓ :
      (F.complexStep p n : C) ⟶ (G.complexStep (p - 1) (n - 1) : C),
      ℓ ≫ (G.complexStep (p - 1) (n - 1)).arrow =
        (F.complexStep p n).arrow ≫ H.hom n (n - 1)) :
    ∀ (M : FilteredPageTwoModel C), M.S.map a = M.S.map b := by
  sorry

/-- A homotopic filtered map induces a common filtered map on cohomology.

The common underlying map is the homology map of either chain map, using
`Homotopy.homologyMap_eq`.  The image descriptions of the two filtrations
then provide the required lifts on every filtration step.
Source: Stacks Project, Homology, Lemma 012O.
(blueprint: lem-sp-filtered-homotopy-spectral-sequence-filtered-abutment-map) -/
theorem exists_filteredHomology_map
    (K L : CochainComplex C ℤ)
    (F : DecreasingFiltration K) (G : DecreasingFiltration L)
    (a b : FilteredObject.HomPreservingSteps ⟨K, F⟩ ⟨L, G⟩)
    (H : Homotopy a.hom b.hom)
    (n : ℤ) (AF : DecreasingFiltration (K.homology n))
    (BF : DecreasingFiltration (L.homology n))
    (hAF : ∀ p : ℤ, AF.step p = imageSubobject
      (HomologicalComplex.homologyMap (F.step p).arrow n))
    (hBF : ∀ p : ℤ, BF.step p = imageSubobject
      (HomologicalComplex.homologyMap (G.step p).arrow n)) :
    ∃ t : FilteredObject.HomPreservingSteps ⟨K.homology n, AF⟩
        ⟨L.homology n, BF⟩,
      t.hom = HomologicalComplex.homologyMap a.hom n ∧
      t.hom = HomologicalComplex.homologyMap b.hom n ∧
      ∀ p : ℤ, ∃ lift : (AF.step p : C) ⟶ (BF.step p : C),
        lift ≫ (BF.step p).arrow = (AF.step p).arrow ≫ t.hom := by
  have eAF : AF = DecreasingFiltration.cohomologyImage F n := by
    cases AF with
    | mk AF hAFstr =>
      congr
      funext p
      exact hAF p
  have eBF : BF = DecreasingFiltration.cohomologyImage G n := by
    cases BF with
    | mk BF hBFstr =>
      congr
      funext p
      exact hBF p
  subst AF
  subst BF
  let f : K.homology n ⟶ L.homology n :=
    HomologicalComplex.homologyMap a.hom n
  let t : FilteredObject.HomPreservingSteps
      ⟨K.homology n, DecreasingFiltration.cohomologyImage F n⟩
      ⟨L.homology n, DecreasingFiltration.cohomologyImage G n⟩ :=
    ⟨f, by
      intro p
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
    (a b : FilteredObject.HomPreservingSteps ⟨K, F⟩ ⟨L, G⟩)
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
      ∃ t : FilteredObject.HomPreservingSteps ⟨K.homology n, AF⟩ ⟨L.homology n, BF⟩,
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
