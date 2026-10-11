/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group U1
-/
import Sheaf.CategoryTheory.FlatFilteredScalarExtension
import Sheaf.CategoryTheory.FilteredPageTwoModel

/-! # Flat comparison of filtered cochain complexes

Source: Stacks Project, Homology, Tag 0BDU and the filtered-complex functoriality lemma;
Cohomology of Schemes, Tag 02KH (blueprint: lem-pc-flat-filtered-complex-comparison).
-/

universe u v w

namespace CategoryTheory

open Limits

/-- Flat tensor identifies all filtered pages, with their differentials, and an
isomorphism on the induced second-page maps implies an isomorphism on cohomology.
The spectral sequences are any functorial filtered-complex models from page two
(def-sp-filtered-page-two-model); their pages are images of quotient cohomology maps.
The step and quotient-complex isomorphisms are fixed by their inclusion and projection
equations; each page isomorphism is fixed by the image description of the pages,
through canonical flat cohomology base change of the quotient complexes. The graded
quotient isomorphisms also supply the first-page identification.
Source: Stacks Project, Homology, Tag 0BDU and
lemma-spectral-sequence-filtered-complex-functorial; Cohomology of Schemes, Tag 02KH
(blueprint: lem-pc-flat-filtered-complex-comparison).

Proof (stage 2: postponed).
1. Tensoring with the flat module B preserves all filtration inclusions and finite
   filtrations (lem-weil-pbc-flat-tensor-exact). Right exactness identifies quotient
   complexes after tensor extension. Flat cohomology base change identifies the first
   pages, naturally with their boundary differentials (lem-pc-flat-tensor-complex-cohom
   and thm-sp-spectral-object-yields). For an unbounded complex, use the three-term
   stupid truncation around each degree: it has the same cohomology in that degree.
2. Induct on pages: the next page is the cohomology of the preceding page complex.
   Exact tensor commutes with that cohomology, and with the images of the quotient
   cohomology maps, giving the compatible page isomorphisms.
   Functoriality gives the page maps of the filtered comparison. Isomorphisms at E2
   propagate to every later page by lem-sp-page-induction and hence to the stabilized
   E-infinity page (def-sp-convergence).
3. Convergence identifies E-infinity with the graded pieces of the finite induced
   cohomology filtrations (thm-sp-spectral-object-yields). The cohomology map induces
   these graded maps; lem-sp-finite-filtration-induction makes it an isomorphism.
   Compose with canonical flat cohomology base change to obtain the displayed map. -/
theorem flatFilteredComplex_comparison
    (A : Type u) (B : Type v) [CommRing A] [CommRing B]
    (φ : A →+* B) (hφ : φ.Flat)
    (C : FilteredObject (CochainComplex (ModuleCat.{max u v w} A) ℤ))
    (D : FilteredObject (CochainComplex (ModuleCat.{max u v w} B) ℤ))
    (hCfin : C.filtration.IsFinite) (hDfin : D.filtration.IsFinite)
    (hC : ∃ N : ℤ, ∀ i : ℤ, i < N → IsZero (C.obj.X i))
    (hD : ∃ N : ℤ, ∀ i : ℤ, i < N → IsZero (D.obj.X i))
    (f : ModuleCat.filteredScalarObject.{u, v, w} φ C ⟶ D)
    (MA : FilteredPageTwoModel (ModuleCat.{max u v w} A))
    (MB : FilteredPageTwoModel (ModuleCat.{max u v w} B)) :
    ∃ (s : ∀ p : ℤ,
        (ModuleCat.filteredScalarComplex.{u, v, w} φ (.up ℤ)).obj
            (C.filtration.step p : CochainComplex (ModuleCat.{max u v w} A) ℤ) ≅
          ((ModuleCat.filteredScalarObject.{u, v, w} φ C).filtration.step p :
            CochainComplex (ModuleCat.{max u v w} B) ℤ))
      (g : ∀ (a b : ℤ) (hab : a ≤ b),
        (ModuleCat.filteredScalarComplex.{u, v, w} φ (.up ℤ)).obj
            (C.filtration.complexQuotient a b hab) ≅
          (ModuleCat.filteredScalarObject.{u, v, w} φ C).filtration.complexQuotient a b hab)
      (e : ∀ (r : ℤ) (hr : 2 ≤ r),
        (ModuleCat.filteredScalarComplex.{u, v, w} φ
            (ComplexShape.up' (⟨r, 1 - r⟩ : ℤ × ℤ))).obj ((MA.S.obj C).page r hr) ≅
          (MB.S.obj (ModuleCat.filteredScalarObject.{u, v, w} φ C)).page r hr),
      (∀ p : ℤ, (s p).hom ≫
          ((ModuleCat.filteredScalarObject.{u, v, w} φ C).filtration.step p).arrow =
        (ModuleCat.filteredScalarComplex.{u, v, w} φ (.up ℤ)).map
          (C.filtration.step p).arrow) ∧
      (∀ (a b : ℤ) (hab : a ≤ b), (ModuleCat.filteredScalarComplex.{u, v, w} φ (.up ℤ)).map
          (C.filtration.complexQuotientπ a b hab) ≫ (g a b hab).hom =
        (s a).hom ≫
          (ModuleCat.filteredScalarObject.{u, v, w} φ C).filtration.complexQuotientπ
            a b hab) ∧
      (∀ (r : ℤ) (hr : 2 ≤ r) (p q : ℤ), (e r hr).hom.f (p, q) ≫
          (MB.pageIso (ModuleCat.filteredScalarObject.{u, v, w} φ C) p q r hr).hom ≫
          image.ι (HomologicalComplex.homologyMap
            (MB.φ (ModuleCat.filteredScalarObject.{u, v, w} φ C) p r hr) (p + q)) =
        (ModuleCat.filteredScalarFunctor.{u, v, w} φ).map
            ((MA.pageIso C p q r hr).hom ≫
              image.ι (HomologicalComplex.homologyMap (MA.φ C p r hr) (p + q))) ≫
          (ModuleCat.flatFilteredHomologyIso.{u, v, w} φ hφ
            (C.filtration.complexQuotient (p - r + 1) (p + 1) (by omega)) (p + q)).hom ≫
          HomologicalComplex.homologyMap (g (p - r + 1) (p + 1) (by omega)).hom (p + q)) ∧
      ((∀ p q : ℤ, IsIso ((e 2 le_rfl).hom.f (p, q) ≫ ((MB.S.map f).hom 2).f (p, q))) →
        ∀ n : ℤ, IsIso
          ((ModuleCat.flatFilteredHomologyIso.{u, v, w} φ hφ C.obj n).hom ≫
            HomologicalComplex.homologyMap f.hom n)) := by
  sorry

end CategoryTheory
