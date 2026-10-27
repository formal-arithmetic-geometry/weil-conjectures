/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q123
-/
module

public import WeilConjectures.AlgebraicGeometry.DerivedCategory
public import WeilConjectures.AlgebraicGeometry.PerfectComplex
public import Mathlib.AlgebraicGeometry.AffineScheme
import WeilConjectures.AlgebraicGeometry.DerivedStructureSheafHomHypercohomology
import Sheaf.Paper.QCohAcyclicDerivedSectionsComparison
import WeilConjectures.AlgebraicGeometry.Cohomology.FiniteFibre
import Mathlib.Algebra.Homology.DerivedCategory.TStructure
import WeilConjectures.AlgebraicGeometry.UnboundedDerivedFunctorCohomologicalBound
import Mathlib.CategoryTheory.Triangulated.TStructure.Basic
import Mathlib.CategoryTheory.Triangulated.Pretriangulated
import Mathlib.RingTheory.Spectrum.Prime.Topology
import WeilConjectures.AlgebraicGeometry.KoszulOpenSystem
import WeilConjectures.AlgebraicGeometry.KoszulOpenHomRestrictionEventuallyZero
import WeilConjectures.AlgebraicGeometry.AffinePerfectOpenRepresentCohomology
import WeilConjectures.AlgebraicGeometry.AffineKoszulGeometricProperties
import WeilConjectures.AlgebraicGeometry.KoszulComplex
import WeilConjectures.AlgebraicGeometry.AffineQCohDerivedEquivalence

/-! # Lifting a class from a supported perfect object on an affine scheme

Source: Stacks Project, Derived Categories of Schemes, Tag 08E3,
`lemma-represent-cohomology-class-on-closed`, using the given finite affine cover
for the cohomological bound (blueprint: lem-sfb-affine-supported-class-lift).

Sections below are ordinary global sections of the degree-zero cohomology sheaf.
The derived object need only have quasi-coherent cohomology.
-/

@[expose] public section

set_option autoImplicit false

universe u w

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- Every degree-zero cohomology section lifts from a perfect object supported on
the closed complement, with no positive cohomology. The assumed vanishing interval
uses the number of affines in the given cover, independently of the number of
principal opens chosen for the Koszul construction.

Source: Stacks Project, Derived Categories of Schemes, Tag 08E3,
`lemma-represent-cohomology-class-on-closed`
(blueprint: lem-sfb-affine-supported-class-lift).

Proof:
1. Write Y = Spec A. The natural identifications in
   lem-pc-derived-structure-sheaf-hom-hypercohomology and
   lem-sc-qcoh-acyclic-derived-sections-comparison identify Hom(O_Y,L) with
   Gamma(Y,H^0(L)) on an affine scheme. Apply the latter to the identity morphism,
   whose direct image is exact. Let psi : O_Y -> E correspond to c.
2. Restrict E to U = Y minus T. Its indicated cohomology sheaves vanish by
   pqf-lem-sheaf-zero-stalks and exactness of open restriction. If s = 0, U is empty
   and Hom(O_U,E|U) = 0. Otherwise the truncation triangle from
   def-sbc-standard-tstructure-derived-category has negative part in degrees <= -s
   and positive part in degrees >= 1. Global sections commute with countable
   products, and lem-sfb-affine-open-finite-cover-cohomology-bound gives vanishing
   of higher module cohomology in degrees >= s. Apply
   lem-pc-unbounded-derived-functor-cohomological-bound to the negative part, with
   N = s and b = -s. Its degree-zero derived sections vanish. The structure-sheaf
   Hom identification, orthogonality of def-weil-t-structure for the positive
   part, and lem-weil-pbc-hom-into-triangle-exact give Hom(O_U,E|U) = 0.
   Thus psi restricts to zero on U.
3. The finite affine cover makes U quasi-compact, by
   lem-weil-pbc-spec-basic-opens-unit-ideal-quasi-compact. The basis of principal
   opens from lem-weil-pbc-spec-localization-away-basic-open therefore supplies
   finitely many f_i with U the union of D(f_i). For empty U use the empty tuple.
   Take the tails I_e, augmentations u_e, full Koszul objects K_e and inclusions
   v_e : O_Y -> K_e of def-sc-koszul-open-system, for positive exponents e.
4. The composite I_1 -> O_Y -> E restricts to zero. By
   lem-sc-koszul-open-hom-restriction-eventually-zero it vanishes after a later
   power transition. Compatibility with augmentations in
   lem-sc-affine-perfect-open-represent-cohomology gives u_e followed by psi = 0.
5. Apply lem-weil-pbc-hom-out-of-triangle-exact to the distinguished triangle
   I_e -> O_Y -> K_e -> I_e[1] from
   lem-sc-affine-perfect-open-represent-cohomology. Obtain a : K_e -> E with
   v_e followed by a = psi.
6. By lem-pc-affine-koszul-geometric-properties, K_e is perfect and has zero
   cohomology stalks wherever some f_i^e is invertible, hence on U. The cochain
   grading of def-weil-pbc-koszul-complex is nonpositive, so its positive
   cohomology is zero. Its termwise associated-sheaf construction and
   lem-pc-affine-qcoh-derived-equivalence put it in D_QCoh(O_Y).
7. Let b be the section corresponding to v_e under the natural identification
   of step 1. Naturality gives Gamma(Y,H^0(a))(b) = c. This uses only
   quasi-coherence of the cohomology of E, with no pseudo-coherence hypothesis. -/
theorem affine_supported_class_lift (Y : Scheme.{u}) [IsAffine Y]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    [∀ V : Y.Opens,
      HasDerivedCategory.{w} (SheafOfModules.{u} ((moduleRings Y.toRingedSpace).over V))]
    (T : Set Y) (hT : IsClosed T) (s : ℕ) (V : Fin s → Y.Opens)
    (hV : ∀ i : Fin s, IsAffineOpen (V i))
    (hcover : (⋃ i : Fin s, (V i : Set Y)) = Tᶜ)
    (E : schemeDerivedQCohCategory Y)
    (hE : ∀ (j : ℤ), -(s : ℤ) + 1 ≤ j → j ≤ 0 → ∀ y : Y, y ∉ T →
      Subsingleton (↑(TopCat.Presheaf.stalk ((DerivedCategory.homologyFunctor
        (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) j).obj E.obj).val.presheaf y)))
    (c : ((DerivedCategory.homologyFunctor
      (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) 0).obj E.obj).val.obj
        (Opposite.op ⊤)) :
    ∃ K : schemeDerivedQCohCategory Y, Scheme.IsPerfect Y K.obj ∧
      ∃ a : K.obj ⟶ E.obj,
        ∃ b : ((DerivedCategory.homologyFunctor
          (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) 0).obj K.obj).val.obj
            (Opposite.op ⊤),
          ((DerivedCategory.homologyFunctor
            (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) 0).map a).val.app
              (Opposite.op ⊤) b = c ∧
          (∀ i : ℤ, 0 < i → IsZero ((DerivedCategory.homologyFunctor
            (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) i).obj K.obj)) ∧
          ∀ (i : ℤ) (y : Y), y ∉ T →
            Subsingleton (↑(TopCat.Presheaf.stalk ((DerivedCategory.homologyFunctor
              (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) i).obj K.obj).val.presheaf
                y)) := by
  sorry

end AlgebraicGeometry
