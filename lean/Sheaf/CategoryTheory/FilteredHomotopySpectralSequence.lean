/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group E1
-/
import Sheaf.CategoryTheory.Filtration
import Sheaf.Algebra.Homology.FilteredComplexSubquotients
import Sheaf.CategoryTheory.FilteredPageTwoModel
import Mathlib.Algebra.Homology.Homotopy

/-!
# Filtered homotopies and spectral sequences

Source: Stacks Project, Homology, Lemma 012O and Definition 012U
(blueprint: lem-sp-filtered-homotopy-spectral-sequence).
-/

universe v u

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] [Abelian C]

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
  sorry

end CategoryTheory
