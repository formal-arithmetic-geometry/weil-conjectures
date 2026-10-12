/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group C1
-/
module

public import Sheaf.CategoryTheory.HalfPlaneConvergence
import Sheaf.CategoryTheory.DerivedCoupleFunctoriality
import Sheaf.CategoryTheory.ExactCouple
import Sheaf.CategoryTheory.ExactCoupleConvergence
import Sheaf.CategoryTheory.Filtration
import Sheaf.CategoryTheory.HalfPlaneGradedCanonical

/-!
# Morphisms of exact couples and their abutments

Source: blueprint, sec-abelian-varieties/sk-prop-av-pqf-finite,
lemma lem-sp-couple-morphism; Stacks Project, Tags 011R, 011T and 012F
(blueprint: lem-sp-couple-morphism).

The index `r` of `pageCouple` denotes the actual page `r + 2`. Compatibility with
page cohomology is expressed using its kernel inclusion and quotient projection.
All induced maps are characterized by their defining commutative squares.
-/

@[expose] public section

universe u v

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.BigradedExactCouple

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- A bidegree-preserving pair commuting with the three exact-couple maps induces
compatible maps of all pages. For half-plane couples its map on `D^{0,n}` preserves
the canonical image filtration, and its graded map corresponds to the infinite-page map.

Proof, Step 1: By lem-sp-derived-couple-functoriality (Stacks Tags 011R and 011T),
the maps restrict to the derived D images and to differential kernels and induce maps
on their quotients. Iterate this construction: the page-zero map is `tE`, each page map
commutes with the differential, and the next map is induced on page cohomology.
The initial map consequently preserves all finite cycles and boundaries, and hence
induces the quotient map on the limiting cycles modulo limiting boundaries.
Step 2: By thm-sp-half-plane-convergence the diagonal colimit is canonically `D^{0,n}`.
Commutation with every power of alpha makes the diagonal colimit map equal to `tD 0 n`
and sends each image filtration step into the corresponding target step
(def-sp-exact-couple, def-sp-filtration).
Step 3: Restrict to filtration steps and pass to successive quotients to obtain the
graded map. By lem-sp-half-plane-graded-canonical the comparison isomorphisms commute
with the canonical maps from D given by g and the diagonal cocone. Both resulting
squares are natural in the couple map. The canonical maps onto the graded pieces are
epimorphic, so the graded map corresponds to the infinite-page map under these
isomorphisms (def-sp-convergence and thm-sp-half-plane-convergence).
Source: blueprint lem-sp-couple-morphism, Proof; Stacks Tags 011R, 011T and 012F
(blueprint: lem-sp-couple-morphism). -/
theorem coupleMorphism
    (X Y : BigradedExactCouple C 0)
    (tD : ∀ p q : ℤ, X.D p q ⟶ Y.D p q)
    (tE : ∀ p q : ℤ, X.E p q ⟶ Y.E p q)
    (hα : ∀ p q : ℤ, X.alpha p q ≫ tD (p - 1) (q + 1) =
      tD p q ≫ Y.alpha p q)
    (hf : ∀ p q : ℤ, X.f p q ≫ tD (p + 2) (q - 1) = tE p q ≫ Y.f p q)
    (hg : ∀ p q : ℤ, X.initialG p q ≫ tE p q = tD p q ≫ Y.initialG p q) :
    ∃ t : ∀ (r : ℕ) (p q : ℤ), (X.pageCouple r).E p q ⟶ (Y.pageCouple r).E p q,
      (∀ p q : ℤ, t 0 p q = tE p q) ∧
      (∀ (r : ℕ) (p q : ℤ),
        (X.pageCouple r).d p q ≫ t r (p + 2 + r) (q - 1 - r) =
          t r p q ≫ (Y.pageCouple r).d p q) ∧
      (∀ (r : ℕ) (p q : ℤ),
        ∃ k : kernel ((X.pageCouple r).d p q) ⟶
          kernel ((Y.pageCouple r).d p q),
          k ≫ kernel.ι ((Y.pageCouple r).d p q) =
            kernel.ι ((X.pageCouple r).d p q) ≫ t r p q ∧
          (X.pageCouple r).derivedEProjection p q ≫ t (r + 1) p q =
            k ≫ (Y.pageCouple r).derivedEProjection p q) ∧
      (∀ a b : ℤ,
        (∀ p q : ℤ, q < a → IsZero (X.D p q)) →
        (∀ p q : ℤ, (p < 0 ∨ q < a) → IsZero (X.E p q)) →
        (∀ p q : ℤ, q < b → IsZero (Y.D p q)) →
        (∀ p q : ℤ, (p < 0 ∨ q < b) → IsZero (Y.E p q)) →
        ∃ L : LimitSubobjects X, ∃ M : LimitSubobjects Y,
        ∃ A : ∀ n : ℤ, AlphaColimit X n, ∃ B : ∀ n : ℤ, AlphaColimit Y n,
        ∃ hA : ∀ n : ℤ, (A n).obj = X.D 0 n,
        ∃ hB : ∀ n : ℤ, (B n).obj = Y.D 0 n,
          (∀ n : ℤ, (A n).ι 0 ≫ eqToHom (hA n) =
            eqToHom (by congr 1; omega)) ∧
          (∀ n : ℤ, (B n).ι 0 ≫ eqToHom (hB n) =
            eqToHom (by congr 1; omega)) ∧
          ∃ f : ∀ n : ℤ, FilteredObject.Hom
            (⟨(A n).obj, X.imageFiltration n (A n)⟩ : FilteredObject C)
            (⟨(B n).obj, Y.imageFiltration n (B n)⟩ : FilteredObject C),
            (∀ n : ℤ, (f n).hom =
              eqToHom (hA n) ≫ tD 0 n ≫ eqToHom (hB n).symm) ∧
            (∀ n p : ℤ, (A n).ι p ≫ (f n).hom = tD p (n - p) ≫ (B n).ι p) ∧
            ∃ z : ∀ p q : ℤ, (L.Z p q : C) ⟶ (M.Z p q : C),
            ∃ tInf : ∀ p q : ℤ, X.pageInfinity L p q ⟶ Y.pageInfinity M p q,
            ∃ gr : ∀ p q : ℤ,
              (X.imageFiltration (p + q) (A (p + q))).gradedPiece p ⟶
                (Y.imageFiltration (p + q) (B (p + q))).gradedPiece p,
            ∃ e : ∀ p q : ℤ, X.pageInfinity L p q ≅
              (X.imageFiltration (p + q) (A (p + q))).gradedPiece p,
            ∃ e' : ∀ p q : ℤ, Y.pageInfinity M p q ≅
              (Y.imageFiltration (p + q) (B (p + q))).gradedPiece p,
              (∀ p q : ℤ, z p q ≫ (M.Z p q).arrow = (L.Z p q).arrow ≫ tE p q) ∧
              (∀ p q : ℤ,
                cokernel.π (Subobject.ofLE (L.B p q) (L.Z p q)
                  (limitBoundary_le_cycle X L p q)) ≫ tInf p q =
                z p q ≫ cokernel.π (Subobject.ofLE (M.B p q) (M.Z p q)
                  (limitBoundary_le_cycle Y M p q))) ∧
              (∀ p q : ℤ, X.toGradedPiece A p q ≫ gr p q =
                tD p q ≫ Y.toGradedPiece B p q) ∧
              (∀ p q : ℤ, X.toPageInfinity L p q ≫ (e p q).hom =
                X.toGradedPiece A p q) ∧
              (∀ p q : ℤ, Y.toPageInfinity M p q ≫ (e' p q).hom =
                Y.toGradedPiece B p q) ∧
              (∀ p q : ℤ, (e p q).hom ≫ gr p q = tInf p q ≫ (e' p q).hom)) := by
  sorry

end CategoryTheory.BigradedExactCouple
