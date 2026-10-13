/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group M2
-/
module

public import Sheaf.Paper.EtaleCEStationaryPageNaturality
public import Sheaf.CategoryTheory.FilteredComplexQuotientCoherence
import Sheaf.CategoryTheory.CartanEilenbergExists
import Sheaf.CategoryTheory.HypercohomologyFirstPage
import Sheaf.CategoryTheory.FilteredComplexPageHomology
import Sheaf.AlgebraicGeometry.EtaleSheafHExtDerivedComparison
import Sheaf.CategoryTheory.FilteredComplexPageDifferential
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.TopologicalInvariance

/-! # Coherent quotient presentations and comparison of supplied first-page maps

Source: Stacks Project, Derived Categories, Tags 015J and 015K; Homology, Tag 012K.
(blueprint: lem-weil-pbc-ce-coherent-quotient-presentations).
-/

@[expose] public section

universe uNatural

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Etale

set_option maxHeartbeats 1000000 in
-- Elaborate the simultaneous dependent CE families and summand equations together.
/-- Construct compatible pages and compute the first page of an already supplied map.
No spectral-sequence map, bicomplex comparison or total lift is constructed here.
Source: Stacks Project, Tags 015J, 015K and 012K.
(blueprint: lem-weil-pbc-ce-coherent-quotient-presentations).

Proof. Shift K by its lower bound, choose a Cartan--Eilenberg resolution in
nonnegative degrees and shift back. Use global sections of its extended flipped
total with the complex-degree filtration. Construct positive page objects as the
actual boundary cokernels, with the unique representative differential. In the
successor calculation, use the cokernel map from successor cycles to the homology
of the current page: the quotient-of-quotients universal property gives its
isomorphism with the next page and fixes its value on representatives. Adjoin the
graded complex as page zero. The row calculation gives the first-page isomorphism;
multiply it in bidegree (q,p) by (-1)^(pq). The CE augmentation, K-injective total
comparison and transported image filtration give the remaining presentation fields,
as in exists_hypercohomology_firstPage. Choose these proof witnesses simultaneously
for all X,K. Differential compatibility and the representative-fixed successor
comparison give the displayed coherence assertion.
For the last clause only a single first-page component map m is supplied.
Identify the concrete first quotient with the homology of the sections resolution
row. The summand equation for u identifies its map on a row cocycle with global
sections of phi, preceded by the sections pullback unit. The augmentation equation
hphi says that this row map lies over v.f q. Computing Ext sheaf cohomology on these
injective resolutions therefore identifies this map with cohomologyMap followed by
Sheaf.H.map. The map m has this action on cycle representatives by its hypothesis;
cancel the epimorphic cycle-to-page projection to obtain the first-page equation.
The identical source and target sign factors commute with the additive row map.
Zero rows, zero complexes and empty schemes satisfy the same finite cokernel and
resolution formulas; neither nonzero objects nor projective test objects are needed.
This is construction and a comparison calculation, not existence of a descended map. -/
theorem exists_etaleCE_coherent_quotient_presentations :
    ∃ (P : ∀ (X : Scheme.{uNatural})
        (K : CochainComplex.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{uNatural + 1})),
        EtaleTermwiseHypercohomology X K)
      (e : ∀ (X : Scheme.{uNatural})
        (K : CochainComplex.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{uNatural + 1})),
        EtaleCEQuotientRealization (P X K)),
      (∀ (X : Scheme.{uNatural})
        (K : CochainComplex.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{uNatural + 1})),
        FilteredComplexQuotientCoherence (P X K).sectionsTotal (P X K).L
          (P X K).sequence (e X K)) ∧
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
      ∀ (p : ℕ) (q : ℤ)
        (m : (D.sequence.page 1).X (q, (p : ℤ)) ⟶
          (D'.sequence.page 1).X (q, (p : ℤ))),
        (∀ (A : AddCommGrpCat.{uNatural + 1})
          (x : A ⟶ (D.L.step q : CochainComplex AddCommGrpCat.{uNatural + 1} ℤ).X
            (q + (p : ℤ)))
          (y : A ⟶ (D'.L.step q : CochainComplex AddCommGrpCat.{uNatural + 1} ℤ).X
            (q + (p : ℤ)))
          (z : A ⟶ (D.L.complexCycles q (q + (p : ℤ)) 1 : AddCommGrpCat.{uNatural + 1}))
          (z' : A ⟶ (D'.L.complexCycles q (q + (p : ℤ)) 1 : AddCommGrpCat.{uNatural + 1})),
          x ≫ (D.L.step q).arrow.f (q + (p : ℤ)) ≫ b.f (q + (p : ℤ)) =
            y ≫ (D'.L.step q).arrow.f (q + (p : ℤ)) →
          z ≫ (D.L.complexCycles q (q + (p : ℤ)) 1).arrow =
            x ≫ (D.L.complexQuotientπ q (q + 1) (by omega)).f (q + (p : ℤ)) →
          z' ≫ (D'.L.complexCycles q (q + (p : ℤ)) 1).arrow =
            y ≫ (D'.L.complexQuotientπ q (q + 1) (by omega)).f (q + (p : ℤ)) →
          z ≫ filteredComplexPageπ D.sectionsTotal D.L 1 (q, (p : ℤ)) ≫
              (e X K q (p : ℤ) 1 (by decide)).inv ≫ m =
            z' ≫ filteredComplexPageπ D'.sectionsTotal D'.L 1 (q, (p : ℤ)) ≫
              (e Y L q (p : ℤ) 1 (by decide)).inv) →
        m ≫ (D'.firstPageIso p q).hom =
          (D.firstPageIso p q).hom ≫
            AddCommGrpCat.ofHom ((Sheaf.H.map (v.f q) p).comp
              (cohomologyMap f (K.obj.X q) p)) := by sorry

end AlgebraicGeometry.Etale
