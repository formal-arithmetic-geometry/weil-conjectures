/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Z2
-/
module

public import Sheaf.AlgebraicGeometry.AlternatingCechTotalComplex
public import Sheaf.AlgebraicGeometry.Coherent
public import Sheaf.AlgebraicGeometry.DerivedCategory
public import Sheaf.Topology.RingedSpaceModuleCohomology
import Sheaf.AlgebraicGeometry.AffineQCohDerivedEquivalence
import Sheaf.Paper.QCohAcyclicDerivedSectionsComparison
import Sheaf.CategoryTheory.RingedSiteKInjectiveResolutions
import Sheaf.AlgebraicGeometry.RingedSpaceDerivedDirectImage
import Sheaf.Algebra.Homology.KInjectiveRestrictOpen
import Sheaf.CategoryTheory.BoundedFilteredComplexSpectralSequence
import Sheaf.CategoryTheory.SpectralSequencePageInduction
import Sheaf.CategoryTheory.FiniteFiltrationInduction
import Sheaf.AlgebraicGeometry.ModuleInjectiveOpenCoverCechAcyclic
import Sheaf.AlgebraicGeometry.AlternatingCechComputes

/-! # Alternating Čech cochains compute derived sections of quasi-coherent complexes

Source: Stacks, Cohomology, Lemma 08C2 and lemma-alternating-cech-complex-complex;
Cohomology of Schemes, Lemma 01XB; Perfect, Lemma 08D2
(blueprint: lem-sc-qcoh-complex-alternating-cech-derived-sections).
-/

@[expose] public section

universe u w v

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

/-- The canonical comparison exists, every comparison is invertible, and comparisons are
natural among complexes of quasi-coherent modules. No boundedness of F or G is assumed.
Source: Stacks, Cohomology, lemma-alternating-cech-complex-complex, Lemma 08C2;
Cohomology of Schemes, Lemma 01XB; Perfect, Lemma 08D2
(blueprint: lem-sc-qcoh-complex-alternating-cech-derived-sections).

Proof:
1. Insertion of a cover index contracts the augmented alternating Čech complex locally.
   The finite cover bounds the Čech direction, even for an unbounded coefficient complex.
2. Each nonempty intersection is affine. The affine quasi-coherent derived equivalence
   (lem-pc-affine-qcoh-derived-equivalence) and acyclic section comparison
   (lem-sc-qcoh-acyclic-derived-sections-comparison) identify its termwise sections with
   derived sections, naturally in the complex and restriction maps.
3. Take a functorial K-injective resolution with injective terms
   (prop-pur-kinjective-resolutions-exist). K-injective restriction to opens
   (lem-sc-derived-k-injective-restrict-open) and the derived-functor computation
   (def-pc-ringed-spaces-derived-direct-image) show that the maps of intersection section
   complexes are quasi-isomorphisms. Filter the Čech totals by Čech degree. Their finite
   graded pieces are shifted products of these quasi-isomorphisms. Spectral comparison
   (thm-sp-spectral-object-yields, lem-sp-page-induction) and finite filtration induction
   (lem-sp-finite-filtration-induction) show the induced map of totals is a quasi-isomorphism.
4. For the injective-term resolution, injective Čech acyclicity
   (lem-weil-pbc-module-injective-open-cover-cech-acyclic) and alternating comparison
   (lem-pc-alternating-cech-computes) make the augmented section rows exact. The finite
   staircase chase makes the cone of the section-to-total augmentation acyclic.
   Invert this augmentation in the derived category and compose with the map of totals.
5. Resolution comparisons between K-injectives are unique up to homotopy
   (lem-weil-pbc-kinjective-hom-derived, lem-sc-kinjective-quasi-iso-comparison). Additive
   Čech totalization preserves homotopies; this gives the equation defining every
   comparison, its resolution independence, and the naturality square. In particular,
   compare any K-injective resolution with the injective-term resolution from step 3.
   Their comparison is a homotopy equivalence, so sections and Čech totalization carry
   it to isomorphisms after localization. Naturality transports the canonical equation
   to every K-injective resolution, without requiring its terms to be injective. The same
   construction gives zero total and derived sections for the empty cover or zero complex.
-/
theorem qcoh_complex_alternating_cech_derived_sections
    (X : Scheme.{u}) (r : ℕ) (U : Fin r → X.Opens) (hU : iSup U = ⊤)
    (hAffine : ∀ (p : ℕ) (t : Fin (p + 1) → Fin r), IsAffineOpen (⨅ k, U (t k)))
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [HasDerivedCategory.{v}
      (ModuleCat.{u} ((moduleRings X.toRingedSpace).obj.obj (op ⊤)))]
    (F : CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ)
    (hF : ∀ n : ℤ, (F.X n).IsQuasicoherent) :
    (∃ β : DerivedCategory.Q.obj ((alternatingCechTotalFunctor U).obj F) ⟶
      (RingedSpace.globalSectionsFunctor X.toRingedSpace).rightDerivedFunctor.obj
        (DerivedCategory.Q.obj F), IsAlternatingCechDerivedComparison U F β) ∧
    (∀ β : DerivedCategory.Q.obj ((alternatingCechTotalFunctor U).obj F) ⟶
      (RingedSpace.globalSectionsFunctor X.toRingedSpace).rightDerivedFunctor.obj
        (DerivedCategory.Q.obj F), IsAlternatingCechDerivedComparison U F β → IsIso β) ∧
    (∀ (G : CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ)
      (_hG : ∀ n : ℤ, (G.X n).IsQuasicoherent) (g : F ⟶ G)
      (βF : DerivedCategory.Q.obj ((alternatingCechTotalFunctor U).obj F) ⟶
        (RingedSpace.globalSectionsFunctor X.toRingedSpace).rightDerivedFunctor.obj
          (DerivedCategory.Q.obj F))
      (βG : DerivedCategory.Q.obj ((alternatingCechTotalFunctor U).obj G) ⟶
        (RingedSpace.globalSectionsFunctor X.toRingedSpace).rightDerivedFunctor.obj
          (DerivedCategory.Q.obj G)),
      IsAlternatingCechDerivedComparison U F βF →
      IsAlternatingCechDerivedComparison U G βG →
      DerivedCategory.Q.map ((alternatingCechTotalFunctor U).map g) ≫ βG =
        βF ≫ (RingedSpace.globalSectionsFunctor X.toRingedSpace).rightDerivedFunctor.map
          (DerivedCategory.Q.map g)) := by
  sorry

end AlgebraicGeometry
