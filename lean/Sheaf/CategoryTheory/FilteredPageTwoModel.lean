/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group E1
-/
module

public import Sheaf.Algebra.Homology.FilteredComplexSubquotients
public import Mathlib.Algebra.Homology.SpectralSequence.Basic

/-! # The functorial second page of a filtered complex

Source: Stacks Project, Homology, Tag 012K, quotient-complex image description;
Derived Categories, Tag 015K (blueprint: def-sp-filtered-page-two-model).
-/

@[expose] public section

universe uM vM

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

variable (C : Type uM) [Category.{vM} C] [Abelian C]

/-- A functorial realization of the filtered-complex spectral sequence from page two.
Its pages and their maps are fixed by the image of the cohomology map
`Fᵖ/Fᵖ⁺ʳ → Fᵖ⁻ʳ⁺¹/Fᵖ⁺¹`. The projection equations specify the quotient maps;
the naturality equation specifies the page maps, rather than arbitrary
isomorphisms of objects. The differential sends a cycle representative to its
complex differential, and higher page maps are spectral-sequence morphisms.
Source: Stacks, Tags 012K and 015K (blueprint: def-sp-filtered-page-two-model). -/
structure FilteredPageTwoModel where
  S : FilteredObject (CochainComplex C ℤ) ⥤ E₂CohomologicalSpectralSequence C
  φ : ∀ (U : FilteredObject (CochainComplex C ℤ)) (p r : ℤ) (hr : 2 ≤ r),
    U.filtration.complexQuotient p (p + r) (by omega) ⟶
      U.filtration.complexQuotient (p - r + 1) (p + 1) (by omega)
  comm_φ : ∀ (U : FilteredObject (CochainComplex C ℤ)) (p r : ℤ) (hr : 2 ≤ r),
    U.filtration.complexQuotientπ p (p + r) (by omega) ≫ φ U p r hr =
      Subobject.ofLE (U.filtration.step p) (U.filtration.step (p - r + 1))
        (U.filtration.antitone_step (by omega)) ≫
          U.filtration.complexQuotientπ (p - r + 1) (p + 1) (by omega)
  pageIso : ∀ (U : FilteredObject (CochainComplex C ℤ)) (p q r : ℤ) (hr : 2 ≤ r),
    ((S.obj U).page r hr).X (p, q) ≅ image (HomologicalComplex.homologyMap (φ U p r hr) (p + q))
  differential : ∀ (U : FilteredObject (CochainComplex C ℤ))
    (p q r : ℤ) (hr : 2 ≤ r),
    let R := U.filtration.complexCycleRepresentatives p (p + q) r
    let Q := U.filtration.complexQuotient (p - r + 1) (p + 1) (by omega)
    let Q' := U.filtration.complexQuotient (p + r - r + 1) (p + r + 1) (by omega)
    let n' := p + r + (q + 1 - r)
    ∃ (g : (R : C) ⟶ Q.cycles (p + q))
      (z : (R : C) ⟶ image (HomologicalComplex.homologyMap (φ U p r hr) (p + q)))
      (y : (R : C) ⟶ (U.filtration.step (p + r) : CochainComplex C ℤ).X n')
      (h : (R : C) ⟶ Q'.cycles n'),
      g ≫ Q.iCycles (p + q) = R.arrow ≫
        (Subobject.ofLE (U.filtration.step p) (U.filtration.step (p - r + 1))
          (U.filtration.antitone_step (by omega))).f (p + q) ≫
        (U.filtration.complexQuotientπ (p - r + 1) (p + 1) (by omega)).f (p + q) ∧
      z ≫ image.ι (HomologicalComplex.homologyMap (φ U p r hr) (p + q)) =
        g ≫ Q.homologyπ (p + q) ∧
      y ≫ (U.filtration.step (p + r)).arrow.f n' =
        R.arrow ≫ (U.filtration.step p).arrow.f (p + q) ≫ U.obj.d (p + q) n' ∧
      h ≫ Q'.iCycles n' = y ≫
        (Subobject.ofLE (U.filtration.step (p + r)) (U.filtration.step (p + r - r + 1))
          (U.filtration.antitone_step (by omega))).f n' ≫
        (U.filtration.complexQuotientπ (p + r - r + 1) (p + r + 1) (by omega)).f n' ∧
      z ≫ (pageIso U p q r hr).inv ≫
        ((S.obj U).page r hr).d (p, q) (p + r, q + 1 - r) ≫
        (pageIso U (p + r) (q + 1 - r) r hr).hom ≫
        image.ι (HomologicalComplex.homologyMap (φ U (p + r) r hr) n') =
          h ≫ Q'.homologyπ n'
  naturality : ∀ {U V : FilteredObject (CochainComplex C ℤ)} (t : U ⟶ V) (p q r : ℤ) (hr : 2 ≤ r),
    ∃ (s : ∀ a : ℤ, (U.filtration.step a : CochainComplex C ℤ) ⟶
        (V.filtration.step a : CochainComplex C ℤ))
      (a : U.filtration.complexQuotient p (p + r) (by omega) ⟶
        V.filtration.complexQuotient p (p + r) (by omega))
      (b : U.filtration.complexQuotient (p - r + 1) (p + 1) (by omega) ⟶
        V.filtration.complexQuotient (p - r + 1) (p + 1) (by omega)),
      (∀ i : ℤ, s i ≫ (V.filtration.step i).arrow =
        (U.filtration.step i).arrow ≫ t.hom) ∧
      U.filtration.complexQuotientπ p (p + r) (by omega) ≫ a =
        s p ≫ V.filtration.complexQuotientπ p (p + r) (by omega) ∧
      U.filtration.complexQuotientπ (p - r + 1) (p + 1) (by omega) ≫ b =
        s (p - r + 1) ≫ V.filtration.complexQuotientπ (p - r + 1) (p + 1) (by omega) ∧
      HomologicalComplex.homologyMap (φ U p r hr) (p + q) ≫
          HomologicalComplex.homologyMap b (p + q) =
        HomologicalComplex.homologyMap a (p + q) ≫
          HomologicalComplex.homologyMap (φ V p r hr) (p + q) ∧
      ((S.map t).hom r hr).f (p, q) ≫ (pageIso V p q r hr).hom ≫
          image.ι (HomologicalComplex.homologyMap (φ V p r hr) (p + q)) =
        (pageIso U p q r hr).hom ≫
          image.ι (HomologicalComplex.homologyMap (φ U p r hr) (p + q)) ≫
            HomologicalComplex.homologyMap b (p + q)

end CategoryTheory
