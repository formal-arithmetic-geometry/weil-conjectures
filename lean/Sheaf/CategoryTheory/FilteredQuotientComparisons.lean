/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group G3
-/
module

public import Sheaf.Algebra.Homology.FilteredComplexSubquotients
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
import Sheaf.Algebra.Homology.FilteredComplexQuotientImageComparison
import Sheaf.Algebra.Homology.FilteredComplexFirstPageCyclesBoundaries
import Sheaf.CategoryTheory.FilteredComplexBoundariesLECycles
import Sheaf.CategoryTheory.Filtration

/-!
# Natural comparisons for concrete cycle-boundary quotients

Source: Stacks Project, Homology, Tag 012K, cycle-boundary formulas
(blueprint: lem-sp-filtered-quotient-comparisons).
-/

@[expose] public section

universe u v
open CategoryTheory.Limits
namespace CategoryTheory

/-- Construct quotient comparisons and their naturality without choosing spectral pages.
Source: Stacks Project, Homology, Tag 012K, displayed cycle-boundary formulas
(blueprint: lem-sp-filtered-quotient-comparisons).

Proof: Boundaries are cycles since d squared is zero. Apply the quotient-image
comparison to each filtration and (p,p+q,r). Its quotient morphism equals the
supplied phi: cancel the epic source cokernel projection in their defining squares.
The cycle lift and the projection to Z are uniquely determined by their composites
with the monic cycle inclusions. The latter projection is epic because Z is exactly
the image of representatives in the graded piece; adding F^(p+1) before projecting
has no effect. At r=1 the representatives project to the graded cycles, and the
boundary quotient is their homology. This gives eH and its representative equation.
The comparison eQ is the isomorphism induced by the common kernel of the epic
representative maps to Z/B and to image H(phi). Thus on page one eQ followed by the
image inclusion is eH followed by H(phi).
For a filtered map, choose its uniquely determined step restrictions and descend
through the three cokernels to a,b,g. The differential square sends representatives
to representatives and boundaries to boundaries. Restrict g to Z, obtaining kz,
and descend through B to obtain k, with the displayed two defining equations.
Repeat on page one for kz1,k1. Homology naturality, checked after the epic cycle
representative projection, gives the eH square for any k1 with these equations.
The defining quotient equations and source epimorphism imply phi_U b = a phi_V.
Compose the representative equations with H(b); use that equality and homology
naturality of a to obtain the same representative map on both sides of the eQ
square. Cancel the epic representative projection onto Z/B. This gives eQ
naturality, The representatives used in this check are those of the quotient-image lemma.
All choices are quotients and maps uniquely specified by these squares. -/
theorem filteredQuotient_comparisons
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
    ∃ hBZ : ∀ (U : ObjectProperty.FullSubcategory
          (fun W : FilteredObject (CochainComplex C ℤ) ↦ W.filtration.IsFinite))
      (p q r : ℤ) (hr : 1 ≤ r),
      U.obj.filtration.complexBoundaries p (p + q) r ≤
        U.obj.filtration.complexCycles p (p + q) r,
    ∃ eH : ∀ (U : ObjectProperty.FullSubcategory
          (fun W : FilteredObject (CochainComplex C ℤ) ↦ W.filtration.IsFinite)) (p q : ℤ),
      cokernel (Subobject.ofLE _ _ (hBZ U p q 1 (by omega))) ≅
        (U.obj.filtration.gradedPiece p).homology (p + q),
    ∃ (eQ : ∀ (U : ObjectProperty.FullSubcategory
          (fun W : FilteredObject (CochainComplex C ℤ) ↦ W.filtration.IsFinite))
        (p q r : ℤ) (hr : 1 ≤ r),
      cokernel (Subobject.ofLE _ _ (hBZ U p q r hr)) ≅
        image (HomologicalComplex.homologyMap (φ U p r hr) (p + q))),
      (∀ (U : ObjectProperty.FullSubcategory
          (fun W : FilteredObject (CochainComplex C ℤ) ↦ W.filtration.IsFinite)) (p q : ℤ),
      ∃ (z : (U.obj.filtration.complexCycleRepresentatives p (p + q) 1 : C) ⟶
          (U.obj.filtration.complexCycles p (p + q) 1 : C))
        (g : (U.obj.filtration.complexCycleRepresentatives p (p + q) 1 : C) ⟶
          (U.obj.filtration.gradedPiece p).cycles (p + q)),
        z ≫ (U.obj.filtration.complexCycles p (p + q) 1).arrow =
          (U.obj.filtration.complexCycleRepresentatives p (p + q) 1).arrow ≫
            (U.obj.filtration.complexQuotientπ p (p + 1) (by omega)).f (p + q) ∧
        g ≫ (U.obj.filtration.gradedPiece p).iCycles (p + q) =
          (U.obj.filtration.complexCycleRepresentatives p (p + q) 1).arrow ≫
            (U.obj.filtration.complexQuotientπ p (p + 1) (by omega)).f (p + q) ∧
        Epi z ∧
        z ≫ cokernel.π (Subobject.ofLE _ _ (hBZ U p q 1 (by omega))) ≫
            (eH U p q).hom =
          g ≫ (U.obj.filtration.gradedPiece p).homologyπ (p + q)) ∧
      (∀ (U : ObjectProperty.FullSubcategory
          (fun W : FilteredObject (CochainComplex C ℤ) ↦ W.filtration.IsFinite))
          (p q : ℤ),
        (eQ U p q 1 (by omega)).hom ≫
            image.ι (HomologicalComplex.homologyMap (φ U p 1 (by omega)) (p + q)) =
          (eH U p q).hom ≫
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
          (g : U.obj.filtration.gradedPiece p ⟶ V.obj.filtration.gradedPiece p)
          (kz : (U.obj.filtration.complexCycles p (p + q) r : C) ⟶
            (V.obj.filtration.complexCycles p (p + q) r : C))
          (k : cokernel (Subobject.ofLE _ _ (hBZ U p q r hr)) ⟶
            cokernel (Subobject.ofLE _ _ (hBZ V p q r hr))),
          (∀ i : ℤ, s i ≫ (V.obj.filtration.step i).arrow =
            (U.obj.filtration.step i).arrow ≫ t.hom.hom) ∧
          U.obj.filtration.complexQuotientπ p (p + r) (by omega) ≫ a =
            s p ≫ V.obj.filtration.complexQuotientπ p (p + r) (by omega) ∧
          U.obj.filtration.complexQuotientπ (p - r + 1) (p + 1) (by omega) ≫ b =
            s (p - r + 1) ≫
              V.obj.filtration.complexQuotientπ (p - r + 1) (p + 1) (by omega) ∧
          U.obj.filtration.complexQuotientπ p (p + 1) (by omega) ≫ g =
            s p ≫ V.obj.filtration.complexQuotientπ p (p + 1) (by omega) ∧
          kz ≫ (V.obj.filtration.complexCycles p (p + q) r).arrow =
            (U.obj.filtration.complexCycles p (p + q) r).arrow ≫ g.f (p + q) ∧
          cokernel.π (Subobject.ofLE _ _ (hBZ U p q r hr)) ≫ k =
            kz ≫ cokernel.π (Subobject.ofLE _ _ (hBZ V p q r hr)) ∧
          (∃ (kz₁ : (U.obj.filtration.complexCycles p (p + q) 1 : C) ⟶
              (V.obj.filtration.complexCycles p (p + q) 1 : C))
            (k₁ : cokernel (Subobject.ofLE _ _ (hBZ U p q 1 (by omega))) ⟶
              cokernel (Subobject.ofLE _ _ (hBZ V p q 1 (by omega)))),
            kz₁ ≫ (V.obj.filtration.complexCycles p (p + q) 1).arrow =
              (U.obj.filtration.complexCycles p (p + q) 1).arrow ≫ g.f (p + q) ∧
            cokernel.π (Subobject.ofLE _ _ (hBZ U p q 1 (by omega))) ≫ k₁ =
              kz₁ ≫ cokernel.π (Subobject.ofLE _ _ (hBZ V p q 1 (by omega)))) ∧
          (∀ k₁ : cokernel (Subobject.ofLE _ _ (hBZ U p q 1 (by omega))) ⟶
              cokernel (Subobject.ofLE _ _ (hBZ V p q 1 (by omega))),
            (∃ kz₁ : (U.obj.filtration.complexCycles p (p + q) 1 : C) ⟶
                (V.obj.filtration.complexCycles p (p + q) 1 : C),
              kz₁ ≫ (V.obj.filtration.complexCycles p (p + q) 1).arrow =
                (U.obj.filtration.complexCycles p (p + q) 1).arrow ≫ g.f (p + q) ∧
              cokernel.π (Subobject.ofLE _ _ (hBZ U p q 1 (by omega))) ≫ k₁ =
                kz₁ ≫ cokernel.π (Subobject.ofLE _ _ (hBZ V p q 1 (by omega)))) →
            k₁ ≫ (eH V p q).hom =
              (eH U p q).hom ≫ HomologicalComplex.homologyMap g (p + q)) ∧
          k ≫ (eQ V p q r hr).hom ≫
              image.ι (HomologicalComplex.homologyMap (φ V p r hr) (p + q)) =
            (eQ U p q r hr).hom ≫
              image.ι (HomologicalComplex.homologyMap (φ U p r hr) (p + q)) ≫
                HomologicalComplex.homologyMap b (p + q)) := by sorry

end CategoryTheory
