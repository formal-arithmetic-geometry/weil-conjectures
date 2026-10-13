/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group C4
-/
module

public import Sheaf.Paper.EtaleCEStationaryPageNaturality
import Sheaf.CategoryTheory.CartanEilenbergExists
import Sheaf.CategoryTheory.HypercohomologyFirstPage
import Sheaf.CategoryTheory.FilteredComplexPageHomology
import Sheaf.AlgebraicGeometry.EtaleSheafHExtDerivedComparison

/-! # Coherent quotient pages with descent of supplied comparisons

Source: Stacks Project, Derived Categories, Tags 015J and 015K; Homology, Tag 012K.
(blueprint: lem-weil-pbc-ce-quotient-page-descent).
-/

@[expose] public section

universe uNatural

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Etale

set_option maxHeartbeats 1000000 in
-- Elaborate the dependent CE totals and representative equations together.
/-- Choose quotient-page presentations on which a supplied filtered augmented
bicomplex comparison descends. No bicomplex comparison or total lift is asserted.
Source: Stacks Project, Tag 015J, first-page computation; Tag 015K; Homology,
Tag 012K, lemma-spectral-sequence-filtered-complex and lemma-functorial.
(blueprint: lem-weil-pbc-ce-quotient-page-descent).

Proof. Shift each bounded-below complex to nonnegative degrees, apply CE existence
and shift back. Use its flipped sections total and complex-degree filtration. Construct
positive pages from the actual cycle/boundary cokernels with the uniquely specified
representative differential. Use the quotient-of-quotients homology comparison, fixed
on cycle representatives, for the successor-page isomorphisms; do not choose arbitrary
homology isomorphisms. Adjoin the graded page zero. The finite-diagonal row comparison,
multiplied by (-1)^(pq), identifies page one with ordinary sheaf cohomology. Retain the
CE total augmentation, K-injective comparison and transported homology-image filtration
from the first hypercohomology construction to fill every field of D.
Given φ,u and their summand equation, the assumed filtration restrictions carry each
r-cycle to an r-cycle and each r-boundary to an r-boundary. Descend the resulting
maps through the boundary cokernels. The chain-map equation for the total map proves
commutation with the representative differential. The successor homology comparison
is fixed on representatives, so these page maps commute with it and define N.
The cokernel descent equation is precisely EtaleCEPageMapOnRepresentatives.
On page one the summand equation gives the Γ-image of φ in each resolution row,
preceded by the sections pullback unit. The augmentation equation hφ identifies this
with the usual resolution computation of cohomologyMap followed by Sheaf.H.map.
The identical factors (-1)^(pq) in source and target commute with the additive row
map and cancel, proving the stated first-page equation. All these constructions use
finite limits and cokernels in each bidegree, so zero rows and empty schemes require
no exceptions. -/
theorem exists_etaleCE_quotient_page_descent :
    ∃ (P : ∀ (X : Scheme.{uNatural})
        (K : CochainComplex.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{uNatural + 1})),
        EtaleTermwiseHypercohomology X K)
      (e : ∀ (X : Scheme.{uNatural})
        (K : CochainComplex.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{uNatural + 1})),
        EtaleCEQuotientRealization (P X K)),
      ∀ {X Y : Scheme.{uNatural}} (f : Y ⟶ X)
    (K : CochainComplex.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{uNatural + 1}))
    (L : CochainComplex.Plus (Sheaf Y.smallEtaleTopology AddCommGrpCat.{uNatural + 1}))
    (v : ((upperStar AddCommGrpCat.{uNatural + 1} f).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj K.obj ⟶ L.obj),
      let D := P X K
      let D' := P Y L
      ∀ (φ : (((upperStar AddCommGrpCat.{uNatural + 1} f).mapHomologicalComplex
      (ComplexShape.up ℕ)).mapHomologicalComplex (ComplexShape.up ℤ)).obj D.I ⟶ D'.I)
    (hφ : ∀ q : ℤ,
      (upperStar AddCommGrpCat.{uNatural + 1} f).map
          ((HomologicalComplex.singleObjXSelf (ComplexShape.up ℕ) 0 (K.obj.X q)).inv ≫
            (D.a.f q).f 0) ≫ (φ.f q).f 0 =
        v.f q ≫
          (HomologicalComplex.singleObjXSelf (ComplexShape.up ℕ) 0 (L.obj.X q)).inv ≫
            (D'.a.f q).f 0)
    (u : ((upperStar AddCommGrpCat.{uNatural + 1} f).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj D.sheafTotal ⟶ D'.sheafTotal)
    (hu : ∀ (m : ℕ) (q n : ℤ) (h : (m : ℤ) + q = n),
        (upperStar AddCommGrpCat.{uNatural + 1} f).map
            ((HomologicalComplex.extendXIso
              (((𝟭 (Sheaf X.smallEtaleTopology AddCommGrpCat.{uNatural + 1})).mapHomologicalComplex
                (ComplexShape.up ℕ)).obj (D.I.X q))
              ComplexShape.embeddingUpNat (i := m) (i' := (m : ℤ)) rfl).inv ≫
                (((CartanEilenbergPresentation.mappedFunctor
                  (𝟭 (Sheaf X.smallEtaleTopology AddCommGrpCat.{uNatural + 1}))).obj
                    D.I).flip).ιTotal (ComplexShape.up ℤ) (m : ℤ) q n h) ≫ u.f n =
          (φ.f q).f m ≫
            (HomologicalComplex.extendXIso
              (((𝟭 (Sheaf Y.smallEtaleTopology AddCommGrpCat.{uNatural + 1})).mapHomologicalComplex
                (ComplexShape.up ℕ)).obj (D'.I.X q))
              ComplexShape.embeddingUpNat (i := m) (i' := (m : ℤ)) rfl).inv ≫
                (((CartanEilenbergPresentation.mappedFunctor
                  (𝟭 (Sheaf Y.smallEtaleTopology AddCommGrpCat.{uNatural + 1}))).obj
                    D'.I).flip).ιTotal (ComplexShape.up ℤ) (m : ℤ) q n h),
      let b := D.totalSectionsIso.hom ≫ ceSectionsLift f u ≫ D'.totalSectionsIso.inv
      (∀ q : ℤ, ∃ s : (D.L.step q : CochainComplex AddCommGrpCat.{uNatural + 1} ℤ) ⟶
          (D'.L.step q : CochainComplex AddCommGrpCat.{uNatural + 1} ℤ),
        s ≫ (D'.L.step q).arrow = (D.L.step q).arrow ≫ b) →
      ∃ N : D.sequence ⟶ D'.sequence,
        (∀ (p : ℕ) (q : ℤ),
        (N.hom 1).f (q, (p : ℤ)) ≫ (D'.firstPageIso p q).hom =
          (D.firstPageIso p q).hom ≫
            AddCommGrpCat.ofHom ((Sheaf.H.map (v.f q) p).comp
              (cohomologyMap f (K.obj.X q) p))) ∧
        EtaleCEPageMapOnRepresentatives D D' (e X K) (e Y L) b N := by sorry

end AlgebraicGeometry.Etale
