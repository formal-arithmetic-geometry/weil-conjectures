/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group M3
-/
module

public import Sheaf.Paper.EtaleCETotalSections

public import Sheaf.Paper.EtaleCEStationaryPageNaturality

import Sheaf.CategoryTheory.CartanEilenbergFunctorial
import Sheaf.CategoryTheory.BoundedFilteredComplexSpectralSequence
import Sheaf.Algebra.Homology.FilteredComplexZBDescription
import Sheaf.AlgebraicGeometry.EtaleSheafHExtDerivedComparison
import Sheaf.CategoryTheory.CartanEilenbergExists

/-! # Coherent first pages and augmented filtered CE lifts

Source: Stacks Project, Derived Categories, Tags 015J and 015K; Homology, Tag 012K.
(blueprint: lem-weil-pbc-ce-coherent-first-page-lifts).
-/

@[expose] public section

universe uNatural

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Etale

set_option maxHeartbeats 1000000 in
-- Elaborate the dependent simultaneous page and presentation families.
/-- Simultaneously construct the first-page data and lifts on actual cycle quotients.
This assertion has no stationary bounds, abutment-step maps or e-infinity comparison.
Source: Stacks Project, Tags 015J, 015K and 012K.
(blueprint: lem-weil-pbc-ce-coherent-first-page-lifts).

Proof. Shift each bounded-below complex to nonnegative degrees, apply CE existence,
and shift back. Extend and flip the chosen bicomplex and filter its sections total
by complex degree. The filtration is uniformly top below the complex's lower bound
and degreewise bottom above the total degree. Construct its pages as the actual
cycle/boundary cokernels. For the differential and successor-page comparison, use
a common finite crop containing all degrees involved; the representative equations
identify the constructions when the crop increases. Equivalently, the concrete
quotient-page differential is uniquely fixed by its equation on representatives.
Thus all presentations use compatible page-homology isomorphisms. The row cohomology
comparisons, multiplied in bidegree (q,p) by (-1)^(pq), give the unsigned horizontal
differential. Use the natural sheaf-H comparison to obtain ordinaryComparison.
The CE total augmentation and its K-injective comparison give the remaining fields
of D, exactly as in the existing first hypercohomology theorem; transport the
homology-image filtration by its canonical comparison. Do not choose D.E from an
unrelated objectwise existence witness.
For f,v apply augmented CE comparison to the chosen two bicomplexes. Extend, flip
and totalize its bidegree-preserving lift to get u. Its degree-zero augmentation
formula proves the strict square on each total summand and hence in every degree.
Conjugating the sections lift by the finite-diagonal comparisons gives b. Because
the lift preserves complex degree, b restricts to every step. Its maps on graded
cycles preserve boundaries and hence descend to the chosen quotient pages; common
crops and their representative equations make these maps commute with page homology.
They give M and the displayed representative equation. On the first page the same
row map computes cohomologyMap followed by Sheaf.H.map(v.f q). The equal source and
target sign corrections cancel, proving the first-page formula. All constructions
use finite diagrams and apply unchanged to zero complexes and empty schemes. -/
theorem exists_etaleCE_coherent_first_page_lifts :
    ∃ (D : ∀ (X : Scheme.{uNatural})
        (K : CochainComplex.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{uNatural + 1})),
        EtaleTermwiseHypercohomology X K)
      (M : ∀ {X Y : Scheme.{uNatural}} (f : Y ⟶ X)
        (K : CochainComplex.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{uNatural + 1}))
        (L : CochainComplex.Plus (Sheaf Y.smallEtaleTopology AddCommGrpCat.{uNatural + 1}))
        (v : ((upperStar AddCommGrpCat.{uNatural + 1} f).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj K.obj ⟶ L.obj),
        (D X K).sequence ⟶ (D Y L).sequence)
      (e : ∀ (X : Scheme.{uNatural})
        (K : CochainComplex.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{uNatural + 1})),
        EtaleCEQuotientRealization (D X K)),
      (∀ {X Y : Scheme.{uNatural}} (f : Y ⟶ X)
        (K : CochainComplex.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{uNatural + 1}))
        (L : CochainComplex.Plus (Sheaf Y.smallEtaleTopology AddCommGrpCat.{uNatural + 1}))
        (v : ((upperStar AddCommGrpCat.{uNatural + 1} f).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj K.obj ⟶ L.obj) (p : ℕ) (q : ℤ),
        ((M f K L v).hom 1).f (q, (p : ℤ)) ≫ ((D Y L).firstPageIso p q).hom =
          ((D X K).firstPageIso p q).hom ≫
            AddCommGrpCat.ofHom ((Sheaf.H.map (v.f q) p).comp
              (cohomologyMap f (K.obj.X q) p))) ∧
      (∀ {X Y : Scheme.{uNatural}} (f : Y ⟶ X)
        (K : CochainComplex.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{uNatural + 1}))
        (L : CochainComplex.Plus (Sheaf Y.smallEtaleTopology AddCommGrpCat.{uNatural + 1}))
        (v : ((upperStar AddCommGrpCat.{uNatural + 1} f).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj K.obj ⟶ L.obj),
        ∃ u : ((upperStar AddCommGrpCat.{uNatural + 1} f).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj (D X K).sheafTotal ⟶ (D Y L).sheafTotal,
          ((upperStar AddCommGrpCat.{uNatural + 1} f).mapHomologicalComplex
            (ComplexShape.up ℤ)).map (D X K).aug ≫ u = v ≫ (D Y L).aug ∧
          let b := (D X K).totalSectionsIso.hom ≫ ceSectionsLift f u ≫
            (D Y L).totalSectionsIso.inv
          (∀ q : ℤ, ∃ s : ((D X K).L.step q : CochainComplex AddCommGrpCat.{uNatural + 1} ℤ) ⟶
              ((D Y L).L.step q : CochainComplex AddCommGrpCat.{uNatural + 1} ℤ),
            s ≫ ((D Y L).L.step q).arrow = ((D X K).L.step q).arrow ≫ b) ∧
          EtaleCEPageMapOnRepresentatives (D X K) (D Y L) (e X K) (e Y L)
            b (M f K L v)) := by sorry

end AlgebraicGeometry.Etale
