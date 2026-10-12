/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group E2
-/
module

public import Sheaf.Algebra.Homology.FilteredComplexSubquotients
public import Sheaf.CategoryTheory.ExactCoupleConvergence
public import Mathlib.Algebra.Homology.HomologySequence
public import Mathlib.Algebra.Homology.SpectralSequence.Basic
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
import Sheaf.Algebra.Homology.FilteredComplexZBDescription
import Sheaf.CategoryTheory.ExactCouple
import Sheaf.CategoryTheory.ExactCoupleMorphism
import Sheaf.CategoryTheory.SpectralSequencePageInduction

/-!
# Pages for the canonical quotient transitions of a bounded filtered complex

This module states the remaining construction after the quotient-transition maps have
been constructed by the cokernel universal property.
-/

@[expose] public section

universe u v

open CategoryTheory.Limits

namespace CategoryTheory

/-- Construction of the pages and comparisons for supplied canonical quotient transitions.
Source: Stacks Project, Homology, Section 12.24, Lemmas 12.24.2--12.24.4 and 12.24.11;
blueprint thm-sp-spectral-object-yields, proof steps 1--6
(blueprint: thm-sp-spectral-object-yields-canonical-pages).

Proof: Form the long exact cohomology sequences of the filtration-step short exact
sequences. Their maps form the exact couple with coordinates `(P,Q)=(2p+q,-p)`;
the derived couple numbered `s` gives filtered page `s+1`. The connecting map for the
three successive filtration steps gives the displayed first differential. Derived-couple
homology supplies the spectral-sequence structure maps, and filtered morphisms induce
couple morphisms and compatible page morphisms, respecting identities and composition.
For the image comparisons, apply the filtered-complex cycle/boundary calculation: a
representative is a cycle modulo `F^(p+r)`, and its target class is zero exactly when it
is a differential from `F^(p-r+1)` plus a term of `F^(p+1)`. This identifies the kernel
with the displayed boundaries and supplies the stated representative equation. The
canonical quotient transition in that calculation equals the supplied `φ`, because
`hφ` specifies its composite with an epimorphic cokernel projection. Choose `eI` by
this representative comparison, rather than as an arbitrary isomorphism. At `r=1`
the transition is the identity; the image factorization of the identity supplies the
comparison with `e₁`. All representative maps commute with filtered morphisms, giving
the two naturality identities and the three quotient squares.
Put `G^p H^n = image(H^n(F^p K) → H^n(K))`. Finite filtration gives top and bottom
steps of `G` and hence separation. The same finite tails make the alpha system
constant with value `H^n(K)` for sufficiently small filtration index, giving `A` and
`aH` with the stated cocone equation. Its index `P` equals filtered index `P-n`.
The cycle tail is represented by `ker d ∩ F^p`, and the boundary tail by
`im d ∩ F^p`, each modulo `F^(p+1)`. Their quotient is the graded piece of `G`;
these tails supply `L` and the convergence conditions. The couple's structure maps
are the filtration inclusions and quotient projections, so the displayed alpha,
initial-gamma and page-differential equations hold with these choices.
Finally choose a common tail bound for cycles, boundaries and adjacent bidegrees;
the resulting differentials vanish and the homology structure maps identify the
stationary pages. Under the extra support assumptions the first page vanishes
outside the first quadrant. Homology preserves this support on each later page.
For `r > max(p,q)+1`, the target of the outgoing differential has negative second
coordinate, and the source of the incoming differential has negative first coordinate.
Both differentials are zero, so iteration of the page homology isomorphisms gives
the final comparison with every later page. -/
theorem boundedFilteredComplex_canonicalPages
    (C : Type u) [Category.{v} C] [Abelian C]
    (φ : ∀ (U : ObjectProperty.FullSubcategory
          (fun W : FilteredObject (CochainComplex C ℤ) ↦ W.filtration.IsFinite))
          (p r : ℤ) (hr : 1 ≤ r),
        U.obj.filtration.complexQuotient p (p + r) (by omega) ⟶
        U.obj.filtration.complexQuotient (p - r + 1) (p + 1) (by omega))
    (hφ : ∀ (U : ObjectProperty.FullSubcategory
          (fun W : FilteredObject (CochainComplex C ℤ) ↦ W.filtration.IsFinite))
          (p r : ℤ) (hr : 1 ≤ r),
        U.obj.filtration.complexQuotientπ p (p + r) (by omega) ≫ φ U p r hr =
          Subobject.ofLE (U.obj.filtration.step p)
            (U.obj.filtration.step (p - r + 1))
            (U.obj.filtration.antitone_step (by omega)) ≫
              U.obj.filtration.complexQuotientπ (p - r + 1) (p + 1) (by omega)) :
    ∃ (S : ObjectProperty.FullSubcategory
          (fun U : FilteredObject (CochainComplex C ℤ) ↦ U.filtration.IsFinite) ⥤
        CohomologicalSpectralSequence C 1)
      (e₁ : ∀ (U : ObjectProperty.FullSubcategory
          (fun W : FilteredObject (CochainComplex C ℤ) ↦ W.filtration.IsFinite))
          (p q : ℤ),
        ((S.obj U).page 1).X (p, q) ≅
        (U.obj.filtration.gradedPiece p).homology (p + q))
      (eI : ∀ (U : ObjectProperty.FullSubcategory
          (fun W : FilteredObject (CochainComplex C ℤ) ↦ W.filtration.IsFinite))
          (p q r : ℤ) (hr : 1 ≤ r),
        ((S.obj U).page r hr).X (p, q) ≅
          image (HomologicalComplex.homologyMap (φ U p r hr) (p + q))),
      (∀ (U : ObjectProperty.FullSubcategory
          (fun W : FilteredObject (CochainComplex C ℤ) ↦ W.filtration.IsFinite))
          (p q : ℤ),
        (eI U p q 1 (by omega)).hom ≫
            image.ι (HomologicalComplex.homologyMap (φ U p 1 (by omega)) (p + q)) =
          (e₁ U p q).hom ≫
            HomologicalComplex.homologyMap (φ U p 1 (by omega)) (p + q)) ∧
      (∀ (U V : ObjectProperty.FullSubcategory
          (fun W : FilteredObject (CochainComplex C ℤ) ↦ W.filtration.IsFinite))
          (t : U ⟶ V) (p q r : ℤ) (hr : 1 ≤ r),
        ∃ (s : ∀ a : ℤ, (U.obj.filtration.step a : CochainComplex C ℤ) ⟶
            (V.obj.filtration.step a : CochainComplex C ℤ))
          (a : U.obj.filtration.complexQuotient p (p + r) (by omega) ⟶
            V.obj.filtration.complexQuotient p (p + r) (by omega))
          (b : U.obj.filtration.complexQuotient (p - r + 1) (p + 1) (by omega) ⟶
            V.obj.filtration.complexQuotient (p - r + 1) (p + 1) (by omega))
          (g : U.obj.filtration.gradedPiece p ⟶ V.obj.filtration.gradedPiece p),
          (∀ i : ℤ, s i ≫ (V.obj.filtration.step i).arrow =
            (U.obj.filtration.step i).arrow ≫ t.hom.hom) ∧
          U.obj.filtration.complexQuotientπ p (p + r) (by omega) ≫ a =
            s p ≫ V.obj.filtration.complexQuotientπ p (p + r) (by omega) ∧
          U.obj.filtration.complexQuotientπ (p - r + 1) (p + 1) (by omega) ≫ b =
            s (p - r + 1) ≫
              V.obj.filtration.complexQuotientπ (p - r + 1) (p + 1) (by omega) ∧
          U.obj.filtration.complexQuotientπ p (p + 1) (by omega) ≫ g =
            s p ≫ V.obj.filtration.complexQuotientπ p (p + 1) (by omega) ∧
          ((S.map t).hom 1).f (p, q) ≫ (e₁ V p q).hom =
            (e₁ U p q).hom ≫ HomologicalComplex.homologyMap g (p + q) ∧
          ((S.map t).hom r hr).f (p, q) ≫ (eI V p q r hr).hom ≫
              image.ι (HomologicalComplex.homologyMap (φ V p r hr) (p + q)) =
            (eI U p q r hr).hom ≫
              image.ι (HomologicalComplex.homologyMap (φ U p r hr) (p + q)) ≫
                HomologicalComplex.homologyMap b (p + q)) ∧
      ∀ U : ObjectProperty.FullSubcategory
          (fun W : FilteredObject (CochainComplex C ℤ) ↦ W.filtration.IsFinite),
        (∀ p q : ℤ,
          ∃ (i : U.obj.filtration.gradedPiece (p + 1) ⟶
              U.obj.filtration.complexQuotient p (p + 2) (by omega))
            (j : U.obj.filtration.complexQuotient p (p + 2) (by omega) ⟶
              U.obj.filtration.gradedPiece p)
            (hij : i ≫ j = 0) (hS : (ShortComplex.mk i j hij).ShortExact),
            U.obj.filtration.complexQuotientπ (p + 1) (p + 1 + 1) (by omega) ≫ i =
              Subobject.ofLE (U.obj.filtration.step (p + 1))
                (U.obj.filtration.step p) (U.obj.filtration.antitone_step (by omega)) ≫
                  U.obj.filtration.complexQuotientπ p (p + 2) (by omega) ∧
            U.obj.filtration.complexQuotientπ p (p + 2) (by omega) ≫ j =
              U.obj.filtration.complexQuotientπ p (p + 1) (by omega) ∧
            ((S.obj U).page 1).d (p, q) (p + 1, q) ≫ (e₁ U (p + 1) q).hom =
              (e₁ U p q).hom ≫
                hS.δ (p + q) (p + 1 + q) (by simp [ComplexShape.up]; omega)) ∧
        (∀ (p q r : ℤ) (hr : 1 ≤ r),
          ∃ (hBZ : U.obj.filtration.complexBoundaries p (p + q) r ≤
              U.obj.filtration.complexCycles p (p + q) r)
            (eZ : ((S.obj U).page r hr).X (p, q) ≅ cokernel (Subobject.ofLE _ _ hBZ))
            (z : (U.obj.filtration.complexCycleRepresentatives p (p + q) r : C) ⟶
              (U.obj.filtration.complexCycles p (p + q) r : C))
            (g : (U.obj.filtration.complexCycleRepresentatives p (p + q) r : C) ⟶
              (U.obj.filtration.complexQuotient p (p + r) (by omega)).cycles (p + q)),
            z ≫ (U.obj.filtration.complexCycles p (p + q) r).arrow =
              (U.obj.filtration.complexCycleRepresentatives p (p + q) r).arrow ≫
                (U.obj.filtration.complexQuotientπ p (p + 1) (by omega)).f (p + q) ∧
            g ≫ (U.obj.filtration.complexQuotient p (p + r) (by omega)).iCycles (p + q) =
              (U.obj.filtration.complexCycleRepresentatives p (p + q) r).arrow ≫
                (U.obj.filtration.complexQuotientπ p (p + r) (by omega)).f (p + q) ∧
            z ≫ cokernel.π (Subobject.ofLE _ _ hBZ) ≫ eZ.inv ≫
                (eI U p q r hr).hom ≫
                image.ι (HomologicalComplex.homologyMap (φ U p r hr) (p + q)) =
              g ≫ (U.obj.filtration.complexQuotient p (p + r) (by omega)).homologyπ
                (p + q) ≫ HomologicalComplex.homologyMap (φ U p r hr) (p + q)) ∧
        (∃ (G : ∀ n : ℤ, DecreasingFiltration (U.obj.obj.homology n))
          (X : BigradedExactCouple C 0) (L : X.LimitSubobjects)
          (A : ∀ n : ℤ, X.AlphaColimit n)
          (aH : ∀ n : ℤ, (A n).obj ≅ U.obj.obj.homology n)
          (eD : ∀ P Q : ℤ, X.D P Q ≅
            (U.obj.filtration.step (-Q) : CochainComplex C ℤ).homology (P + Q))
          (eC : ∀ (s : ℕ) (p q : ℤ),
            (X.pageCouple s).E (2 * p + q) (-p) ≅
              ((S.obj U).page (s + 1) (by omega)).X (p, q)),
          (∀ n p : ℤ, (G n).step p =
            imageSubobject (HomologicalComplex.homologyMap
              (U.obj.filtration.step p).arrow n)) ∧
          (∀ n : ℤ, (G n).IsFinite ∧ (G n).IsSeparated) ∧
          (∀ n P : ℤ,
            (A n).ι P ≫ (aH n).hom =
              (eD P (n - P)).hom ≫ eqToHom (by
                rw [show -(n - P) = P - n by omega, show P + (n - P) = n by omega]) ≫
                HomologicalComplex.homologyMap
                  (U.obj.filtration.step (P - n)).arrow n) ∧
          (∀ P Q : ℤ,
            X.alpha P Q ≫ (eD (P - 1) (Q + 1)).hom =
              (eD P Q).hom ≫ HomologicalComplex.homologyMap
                (Subobject.ofLE (U.obj.filtration.step (-Q))
                  (U.obj.filtration.step (-(Q + 1)))
                  (U.obj.filtration.antitone_step (by omega))) (P + Q) ≫
                eqToHom (by rw [show P - 1 + (Q + 1) = P + Q by omega])) ∧
          (∀ P Q : ℤ,
            X.initialG P Q ≫ eqToHom (by congr 1 <;> omega) ≫
                (eC 0 (-Q) (P + 2 * Q)).hom ≫ (e₁ U (-Q) (P + 2 * Q)).hom ≫
                eqToHom (by
                  rw [show -Q + (P + 2 * Q) = P + Q by omega]
                  rfl) =
              (eD P Q).hom ≫ HomologicalComplex.homologyMap
                (U.obj.filtration.complexQuotientπ (-Q) (-Q + 1) (by omega)) (P + Q)) ∧
          (∀ (s : ℕ) (p q : ℤ),
            (eC s p q).hom ≫
                ((S.obj U).page (s + 1) (by omega)).d (p, q)
                  (p + (s + 1), q - (s + 1) + 1) =
              (X.pageCouple s).d (2 * p + q) (-p) ≫
                eqToHom (by congr 1 <;> omega) ≫
                  (eC s (p + (s + 1)) (q - (s + 1) + 1)).hom) ∧
          X.ConvergesTo L A ∧
          (∀ p q : ℤ, Nonempty
            (X.pageInfinity L (2 * p + q) (-p) ≅ (G (p + q)).gradedPiece p))) ∧
        (∀ p q : ℤ, ∃ (R : ℤ) (hR : 1 ≤ R), ∀ (r : ℤ) (hr : R ≤ r),
          U.obj.filtration.complexCycles p (p + q) r =
            U.obj.filtration.complexCycles p (p + q) R ∧
          U.obj.filtration.complexBoundaries p (p + q) r =
            U.obj.filtration.complexBoundaries p (p + q) R ∧
          ((S.obj U).page r (by omega)).d (p, q) (p + r, q - r + 1) = 0 ∧
          ((S.obj U).page r (by omega)).d (p - r, q + r - 1) (p, q) = 0 ∧
          Nonempty (((S.obj U).page r (by omega)).X (p, q) ≅
            ((S.obj U).page R hR).X (p, q))) ∧
        ((∀ p : ℤ, p ≤ 0 → U.obj.filtration.step p = ⊤) →
          (∀ p i : ℤ, (i < p ∨ p + 1 < i) →
            IsZero ((U.obj.filtration.gradedPiece p).homology i)) →
          (∀ (p q r : ℤ) (hr : 1 ≤ r), (p < 0 ∨ q < 0) →
            IsZero (((S.obj U).page r hr).X (p, q))) ∧
          ∀ (p q r t : ℤ) (hr : 1 ≤ r) (ht : r ≤ t), max p q + 1 < r →
            ((S.obj U).page r hr).d (p, q) (p + r, q - r + 1) = 0 ∧
            ((S.obj U).page r hr).d (p - r, q + r - 1) (p, q) = 0 ∧
            Nonempty (((S.obj U).page r hr).X (p, q) ≅
              ((S.obj U).page t (by omega)).X (p, q))) := by
  sorry

end CategoryTheory
