/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q13
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Colimits
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Algebra.Homology.SpectralSequence.Basic
public import Mathlib.Algebra.Homology.TotalComplex
public import Mathlib.Data.Int.Interval
public import WeilConjectures.Algebra.Homology.FilteredComplexSubquotients
public import WeilConjectures.CategoryTheory.ExactCoupleConvergence
import WeilConjectures.Algebra.Homology.ExactCouple.DoubleComplex
import WeilConjectures.CategoryTheory.Abelian.Filtration
import WeilConjectures.Mathlib.Algebra.Homology.TotalComplex
import WeilConjectures.CategoryTheory.DoubleComplexTotal

/-!
# The column-cone spectral sequence of a bounded-below total map

Source: Stacks Project, Homology, Tags 0130 and 0132, lemma-first-quadrant-ss;
Derived Categories, Tag 014E, definition-cone
(blueprint: lem-trf-bounded-below-cech-cone-comparison).

The auxiliary constructions below name the ordinary total-map cone and its finite
column sums. The theorem specifies the filtration by those sums, its first page,
its exact-couple convergence, stabilization, and the truncated vanishing consequence.
-/

@[expose] public section

universe u v

open CategoryTheory CategoryTheory.Limits

namespace HomologicalComplex₂

variable {R : Type u} [CommRing R]
variable {A B : HomologicalComplex₂ (ModuleCat.{v} R)
  (ComplexShape.up ℤ) (ComplexShape.up ℤ)}

/-- The ordinary cone of the canonical total map, with total differential
`d_h + (-1)^q d_v`. Source: Stacks Tags 012Z and 014E
(blueprint: lem-trf-bounded-below-cech-cone-comparison). -/
noncomputable def cechTotalMapCone (f : A ⟶ B) : CochainComplex (ModuleCat.{v} R) ℤ :=
  CochainComplex.mappingCone (total.map f (ComplexShape.up ℤ))

/-- The column tail in degree `n` of the total-map cone. Under the support assumptions,
only `p ≤ q ≤ n-a+1` can contribute. The sign on the source summand in the signed
cone-total identification does not change its image subobject.
Source: Stacks Tags 012Z, 0132 and 014E
(blueprint: lem-trf-bounded-below-cech-cone-comparison). -/
noncomputable def cechTotalMapConeStep (f : A ⟶ B) (a p n : ℤ) :
    Subobject ((cechTotalMapCone f).X n) :=
  (Finset.Icc p (n - a + 1)).sup (fun q ↦
    imageSubobject (B.ιTotalOrZero (ComplexShape.up ℤ) q (n - q) n ≫
      (CochainComplex.mappingCone.inr (total.map f (ComplexShape.up ℤ))).f n) ⊔
    imageSubobject (A.ιTotalOrZero (ComplexShape.up ℤ) q (n + 1 - q) (n + 1) ≫
      (CochainComplex.mappingCone.inl (total.map f (ComplexShape.up ℤ))).v
        (n + 1) n (by omega)))

/-- The column-cone spectral sequence converges, stabilizes, and detects vanishing
through any fixed degree. The filtration `F` is specified degreewise, and `G` is its
cohomology image filtration. Coordinates `(P,Q)=(2q+j,-q)` put its exact couple into
the convention of `def-sp-convergence`; derived couple `s` is filtered page `s+1`.

Source: Stacks Project, Homology, Tags 0130 and 0132 (finite diagonals), and Derived
Categories, Tag 014E (blueprint: lem-trf-bounded-below-cech-cone-comparison).

Proof (postponed in stage 2).
1. Form the commuting bicomplex D with D^(q,j)=B^(q,j) ⊕ A^(q,j+1), vertical
   differential (b,x) ↦ (d_B b + f x,-d_A x), and horizontal differential
   (b,x) ↦ (d_B b,d_A x). The chain-map equations and commutation of the original
   differentials give both square-zero equations and commutation. Its support is
   q ≥ 0, j ≥ a-1, so its diagonals are finite (def-sp-double-complex-total).
2. On each summand use (b,x) ↦ (b,(-1)^q x). This is its own inverse. Computing
   both differentials gives the three source components (-1)^q f x,
   (-1)^(q+1) d_h x and -d_v x on both sides. It identifies Tot D with the
   ordinary cone of Tot f and carries the column filtration to the displayed
   finite sums (def-weil-abstract-derived-category).
3. Relabel j=k+(a-1), without a cochain-shift sign. Apply the first-quadrant
   theorem thm-sp-double-complex-spectral-sequences. The first page is H^j(C_q).
   The filtration-step long exact sequences give the exact couple, reindexed by
   (P,Q)=(2q+j,-q); its alpha maps are inclusions and its initial gamma maps are
   graded projections. Its alpha-colimit is total-cone cohomology with the displayed
   cocone. Finite image filtrations and stationary cycles give ConvergesTo in the
   sense of def-sp-convergence, and every bidegree stabilizes. The finite support
   ensures the same conclusion below a-1, where the total terms vanish.
4. If the column cohomology vanishes through r, all entries on every diagonal
   n ≤ r vanish on page one, since j=n-q ≤ r for q ≥ 0. The homology page rule
   propagates zero to later pages. Convergence identifies the stable entries with
   the graded pieces of G. Every such piece is zero; consecutive steps of the
   finite filtration are equal, so its whole-object end equals its zero end.
   This proves vanishing of total-cone cohomology through r (def-sp-filtration). -/
theorem boundedBelow_cech_cone_comparison
    (f : A ⟶ B) (a : ℤ)
    (hA : ∀ q j : ℤ, q < 0 ∨ j < a → IsZero ((A.X q).X j))
    (hB : ∀ q j : ℤ, q < 0 ∨ j < a → IsZero ((B.X q).X j)) :
    (∃ (F : DecreasingFiltration (cechTotalMapCone f))
      (E : CohomologicalSpectralSequence (ModuleCat.{v} R) 1)
      (e₁ : ∀ q j : ℤ,
        (E.page 1).X (q, j) ≅ (F.gradedPiece q).homology (q + j))
      (G : ∀ n : ℤ, DecreasingFiltration ((cechTotalMapCone f).homology n))
      (X : BigradedExactCouple (ModuleCat.{v} R) 0) (L : X.LimitSubobjects)
      (H : ∀ n : ℤ, X.AlphaColimit n)
      (eH : ∀ n : ℤ, (H n).obj ≅ (cechTotalMapCone f).homology n)
      (eD : ∀ P Q : ℤ,
        X.D P Q ≅ (F.step (-Q) : CochainComplex (ModuleCat.{v} R) ℤ).homology (P + Q))
      (eC : ∀ (s : ℕ) (q j : ℤ),
        (X.pageCouple s).E (2 * q + j) (-q) ≅ (E.page (s + 1) (by omega)).X (q, j)),
      (∀ p n : ℤ, F.complexStep p n = cechTotalMapConeStep f a p n) ∧
      (∀ q j : ℤ, Nonempty ((E.page 1).X (q, j) ≅
        (CochainComplex.mappingCone (f.f q)).homology j)) ∧
      (∀ n p : ℤ, (G n).step p =
        imageSubobject (HomologicalComplex.homologyMap (F.step p).arrow n)) ∧
      (∀ n : ℤ, (G n).IsFinite) ∧
      (∀ n P : ℤ, (H n).ι P ≫ (eH n).hom =
        (eD P (n - P)).hom ≫ eqToHom (by
          rw [show -(n - P) = P - n by omega, show P + (n - P) = n by omega]) ≫
          HomologicalComplex.homologyMap (F.step (P - n)).arrow n) ∧
      (∀ P Q : ℤ, X.alpha P Q ≫ (eD (P - 1) (Q + 1)).hom =
        (eD P Q).hom ≫ HomologicalComplex.homologyMap
          (Subobject.ofLE (F.step (-Q)) (F.step (-(Q + 1)))
            (F.antitone_step (by omega))) (P + Q) ≫
          eqToHom (by rw [show P - 1 + (Q + 1) = P + Q by omega])) ∧
      (∀ P Q : ℤ, X.initialG P Q ≫ eqToHom (by congr 1 <;> omega) ≫
          (eC 0 (-Q) (P + 2 * Q)).hom ≫ (e₁ (-Q) (P + 2 * Q)).hom ≫
          eqToHom (by rw [show -Q + (P + 2 * Q) = P + Q by omega]; rfl) =
        (eD P Q).hom ≫ HomologicalComplex.homologyMap
          (F.complexQuotientπ (-Q) (-Q + 1) (by omega)) (P + Q)) ∧
      (∀ (s : ℕ) (q j : ℤ), (eC s q j).hom ≫
          (E.page (s + 1) (by omega)).d (q, j) (q + (s + 1), j - (s + 1) + 1) =
        (X.pageCouple s).d (2 * q + j) (-q) ≫
          eqToHom (by congr 1 <;> omega) ≫
          (eC s (q + (s + 1)) (j - (s + 1) + 1)).hom) ∧
      X.ConvergesTo L H ∧
      (∀ q j : ℤ, Nonempty
        (X.pageInfinity L (2 * q + j) (-q) ≅ (G (q + j)).gradedPiece q)) ∧
      (∀ q j : ℤ, ∃ (N : ℤ) (hN : 1 ≤ N), ∀ (s : ℤ) (hs : N ≤ s),
        (E.page s (by omega)).d (q, j) (q + s, j - s + 1) = 0 ∧
        (E.page s (by omega)).d (q - s, j + s - 1) (q, j) = 0 ∧
        Nonempty ((E.page s (by omega)).X (q, j) ≅
          (E.page N hN).X (q, j)) ∧
        Nonempty ((E.page s (by omega)).X (q, j) ≅ (G (q + j)).gradedPiece q))) ∧
    ∀ r : ℤ,
      (∀ q : ℤ, 0 ≤ q → ∀ j : ℤ, j ≤ r →
        IsZero ((CochainComplex.mappingCone (f.f q)).homology j)) →
      ∀ n : ℤ, n ≤ r → IsZero ((cechTotalMapCone f).homology n) := by
  sorry

end HomologicalComplex₂
