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

/-!
# Functorial pages of a finite filtered complex

Source: Stacks Project, Homology, Section 12.24, Lemmas 12.24.2--12.24.4.
(blueprint: lem-sp-bounded-filtered-page-construction).
-/

@[expose] public section

universe u v
open CategoryTheory.Limits
namespace CategoryTheory

/-- Construct the functorial pages, their representative comparisons, and their exact couple.
Source: Stacks Project, Homology, Lemmas 12.24.2--12.24.4; blueprint
thm-sp-spectral-object-yields, steps 1--4
(blueprint: lem-sp-bounded-filtered-page-construction).

Proof: For every filtration step take the short exact sequence with its successive quotient.
The homology long exact sequences form an exact couple with D(P,Q)=H^(P+Q)(F^(-Q)).
Its alpha is induced by inclusion and its gamma by quotient projection. Reindex E by
(P,Q)=(2p+q,-p); deriving the couple gives the pages with differentials of degree (r,1-r).
The connecting map for three successive steps gives the asserted first differential.
A filtered map restricts to each step and descends uniquely through each quotient.
These restrictions commute with inclusions, quotient projections, and connecting maps;
the resulting couple morphisms induce page maps commuting with page homology.
Uniqueness of restriction and cokernel descent gives identity and composition, hence S.
For the page comparison use representatives x in F^p with dx in F^(p+r). Such x gives
a cycle in the source quotient. Its image cohomology class in the target quotient vanishes
exactly when x=dy+f with y in F^(p-r+1) and f in F^(p+1). Thus the kernel of this
representative map is precisely the boundary subobject. Its cokernel descent gives eZ
and eI with the displayed equation. This description commutes with all filtered maps.
The supplied phi equals the descended map, since its composite with the epimorphic
source projection is prescribed. At r=1 phi is the identity on the graded piece, so eI
agrees with e1 followed by H(phi) and the image inclusion. All choices here are
quotients or objects specified up to unique compatible isomorphism. No abutment or
eventual stabilization is asserted in this construction. -/
theorem boundedFilteredComplex_pageConstruction
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
        (∃ (X : BigradedExactCouple C 0)
          (eD : ∀ P Q : ℤ, X.D P Q ≅
            (U.obj.filtration.step (-Q) : CochainComplex C ℤ).homology (P + Q))
          (eC : ∀ (s : ℕ) (p q : ℤ),
            (X.pageCouple s).E (2 * p + q) (-p) ≅
              ((S.obj U).page (s + 1) (by omega)).X (p, q)) ,
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
                  (eC s (p + (s + 1)) (q - (s + 1) + 1)).hom)) := by sorry

end CategoryTheory
