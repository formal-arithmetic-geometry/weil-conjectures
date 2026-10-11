/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F1
-/
import Sheaf.CategoryTheory.CartanEilenbergExists
import Mathlib.Algebra.Homology.Homotopy

/-! # Vertical null-homotopy of a Cartan--Eilenberg defect

Source: Stacks Project, Tag 015I, compatibility of the boundary/cycle exact sequences;
Weibel, Homological Algebra, Lemma 5.7.10
(blueprint: lem-sp-ce-vertical-nullhomotopy).

We use the bicomplex convention of `exists_cartanEilenberg_resolution`: horizontal
integer degrees and nonnegative vertical degrees. The three row augmentations are
induced by the same bicomplex augmentation. Exactness of these augmented rows is
expressed by quasi-isomorphisms from complexes concentrated in vertical degree zero.
The canonical cycle-column-boundary sequences are short exact in any abelian category.
-/

universe u v

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

/-- A bicomplex map zero on its augmentation admits a horizontal-compatible vertical
null-homotopy. Source: Stacks Project, Tag 015I, and Weibel, Homological Algebra,
Lemma 5.7.10 (blueprint: lem-sp-ce-vertical-nullhomotopy).

Proof:
1. The double-complex map R induces maps on boundary, cycle, and horizontal-homology
   rows, all zero on their augmentations. These maps respect both canonical short
   exact sequences B → Z → H and Z → I → B in the abelian category.
2. Apply lem-weil-pbc-acyclic-map-to-injective-nullhomotopy to each exact augmented
   source row and injective target row, adjoining the augmentation in degree -1.
   This gives the three row null-homotopies, zero in vertical degree zero.
3. Induct on horizontal degree p, starting with the zero boundary at p = 0.
   Maintain that the cycle homotopy restricts to the boundary homotopy. Apply
   lem-sp-ce-compatible-homotopy-assembly first to B → Z → H to obtain the cycle
   homotopy extending the prescribed boundary homotopy, then to Z → I → B to obtain
   the column homotopy s and the next boundary homotopy. The source column is exact
   as an extension of exact rows; the target column is injective since the target
   sequence splits degreewise. Both applications respect the augmentations and
   give s = 0 in vertical degree zero. Factor d_h through I → B → Z → I.
   The maintained restriction and quotient identities then give s d_h = d_h s.
   Extend by zero in negative horizontal degrees.

`Homotopy.comm` says R = d_v s + s d_v. Its shape condition gives `s.hom 0 q = 0`
for every natural q, representing the zero component into vertical degree -1.
-/
theorem cartanEilenberg_vertical_nullhomotopy
    (A : Type u) [Category.{v} A] [Abelian A]
    (K L : CochainComplex A ℤ)
    (I J : HomologicalComplex₂ A (ComplexShape.up ℤ) (ComplexShape.up ℕ))
    (eI : ((CochainComplex.single₀ A).mapHomologicalComplex (ComplexShape.up ℤ)).obj K
      ⟶ I)
    (eJ : ((CochainComplex.single₀ A).mapHomologicalComplex (ComplexShape.up ℤ)).obj L
      ⟶ J)
    (hI : ∀ p : ℤ, p < 0 → IsZero (I.X p))
    (hJ : ∀ p : ℤ, p < 0 → IsZero (J.X p))
    (hsource : ∀ p : ℤ,
      QuasiIso (HomologicalComplex.cyclesMap eI p) ∧
      QuasiIso (image.map (Arrow.homMk' (eI.f (p - 1)) (eI.f p) (eI.comm (p - 1) p))) ∧
      QuasiIso (HomologicalComplex.homologyMap eI p))
    (htarget : ∀ p : ℤ,
      QuasiIso (HomologicalComplex.cyclesMap eJ p) ∧
      QuasiIso (image.map (Arrow.homMk' (eJ.f (p - 1)) (eJ.f p) (eJ.comm (p - 1) p))) ∧
      QuasiIso (HomologicalComplex.homologyMap eJ p))
    (hinjective : ∀ (p : ℤ) (q : ℕ),
      Injective ((J.cycles p).X q) ∧
      Injective ((image (J.d (p - 1) p)).X q) ∧
      Injective ((J.homology p).X q))
    (R : I ⟶ J) (hR : eI ≫ R = 0) :
    (∀ p : ℤ,
      Nonempty (Homotopy (HomologicalComplex.cyclesMap R p) 0) ∧
      Nonempty (Homotopy
        (image.map (Arrow.homMk' (R.f (p - 1)) (R.f p) (R.comm (p - 1) p))) 0) ∧
      Nonempty (Homotopy (HomologicalComplex.homologyMap R p) 0)) ∧
    ∃ s : ∀ p : ℤ, Homotopy (R.f p) 0,
      (∀ (p : ℤ) (q : ℕ), (s p).hom 0 q = 0) ∧
      (∀ (p p' : ℤ) (q q' : ℕ),
        (s p).hom q q' ≫ (J.d p p').f q' =
          (I.d p p').f q ≫ (s p').hom q q') := by
  sorry

end CategoryTheory
