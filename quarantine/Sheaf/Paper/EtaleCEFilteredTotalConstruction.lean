/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group M3
-/
module

public import Sheaf.Paper.EtaleCETotalSections

import Sheaf.Paper.EtaleCECoherentFirstPageLifts
import Sheaf.Paper.EtaleCEStationaryPageNaturality

/-! # Coherent filtered maps between CE totals

Source: Stacks Project, Tags 015J, 015K and 012K.
(blueprint: lem-weil-pbc-ce-filtered-total-construction).
-/

@[expose] public section

universe uNatural

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Etale

set_option linter.unusedVariables false in
set_option maxHeartbeats 1000000 in
-- Elaborate the dependent simultaneous presentation and stationary-page families.
/-- Construct the spectral-sequence maps directly on the CE totals, before composing
with the target K-injective comparison. Source: Stacks Project, Tags 015J and 015K;
Homology, Tag 012K, the cycle/boundary description and convergence.
(blueprint: lem-weil-pbc-ce-filtered-total-construction).

Proof: Shift each bounded-below complex to nonnegative degrees, choose a CE resolution,
and shift back. Choose its signed first spectral sequence and natural ordinary-cohomology
row comparison using the hypercohomology first-page and sheaf-H comparison theorems.
For coherence, construct the sequence from the complex-degree filtration. This filtration
is degreewise finite, but not uniformly finite. Crop it above c, apply the bounded filtered
construction, and compare the cycle and boundary representatives in degrees n-1,n,n+1
with c > n+1. These representatives are unchanged by increasing c. Their canonical maps
identify the page objects and page-homology comparisons on overlaps. Use a common crop
for source and target of a differential, and for source and target of a filtered map.
Glue through these identifications. This provides one sequence per presentation and
compatible page maps, rather than choosing unrelated witnesses of the objectwise theorem.
Exact inverse image and augmented CE comparison provide a bicomplex lift of v; extend,
flip and totalize to obtain u. On the degree-zero resolution summands the augmentation
identity of the bicomplex lift gives the strict displayed equality, by joint epimorphy
of the total inclusions. Apply the sections unit to u. The finite-diagonal comparisons
identify this with a map of global-sections CE totals. Since the bicomplex lift preserves
complex degree, this total map preserves every filtration step. The canonical page maps
give M, and the natural row comparison computes its first page as H(v) after pullback;
the source and target sign corrections are identical. Restrict homology of the total
map to the images of filtration-step homology. Transport these image maps by c_X,c_Y;
this yields t and ht. In degrees n-1,n,n+1, choose a bound past both filtration tails.
The cycle/boundary quotients are stationary after this bound. Their canonical maps to
successive image-filtration quotients provide eInf, with bounds depending only on the
presentation and bidegree. Naturality on cycle and boundary representatives identifies
the page map with the map on successive image quotients, hence with cokernel.map.
The latter square's proof is irrelevant. All comparisons include zero complexes, empty
schemes and empty diagonals; no arbitrary K-injective lift is chosen. -/
theorem exists_etaleHypercohomology_ce_filtered_totals :
    ∃ (D : ∀ (X : Scheme.{uNatural})
        (K : CochainComplex.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{uNatural + 1})),
        EtaleTermwiseHypercohomology X K)
      (M : ∀ {X Y : Scheme.{uNatural}} (f : Y ⟶ X)
        (K : CochainComplex.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{uNatural + 1}))
        (L : CochainComplex.Plus (Sheaf Y.smallEtaleTopology AddCommGrpCat.{uNatural + 1}))
        (v : ((upperStar AddCommGrpCat.{uNatural + 1} f).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj K.obj ⟶ L.obj),
        (D X K).sequence ⟶ (D Y L).sequence)
      (R : ∀ (X : Scheme.{uNatural})
        (K : CochainComplex.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{uNatural + 1}))
        (q n : ℤ), ℤ)
      (eInf : ∀ (X : Scheme.{uNatural})
        (K : CochainComplex.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{uNatural + 1}))
        (q n r : ℤ) (hr : 1 ≤ r) (hR : R X K q n ≤ r),
        ((D X K).sequence.page r hr).X (q, n - q) ≅ ((D X K).H n).gradedPiece q),
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
          ∀ n : ℤ,
            ∃ (t : ∀ q : ℤ, (((D X K).H n).step q : AddCommGrpCat.{uNatural + 1}) ⟶
            (((D Y L).H n).step q : AddCommGrpCat.{uNatural + 1}))
          (ht : ∀ q : ℤ, t q ≫ (((D Y L).H n).step q).arrow =
            (((D X K).H n).step q).arrow ≫
              (((D X K).c n).inv ≫
                HomologicalComplex.homologyMap
                  ((D X K).totalSectionsIso.hom ≫ ceSectionsLift f u ≫
                    (D Y L).totalSectionsIso.inv) n ≫ ((D Y L).c n).hom)),
          ∀ (hc : ∀ q : ℤ,
            Subobject.ofLE (((D X K).H n).step (q + 1)) (((D X K).H n).step q)
                (((D X K).H n).antitone_step (Int.le_add_one (le_refl q))) ≫ t q =
              t (q + 1) ≫
                Subobject.ofLE (((D Y L).H n).step (q + 1)) (((D Y L).H n).step q)
                  (((D Y L).H n).antitone_step (Int.le_add_one (le_refl q)))),
          ∀ (q r : ℤ) (hr : 1 ≤ r) (hX : R X K q n ≤ r) (hY : R Y L q n ≤ r),
            ((M f K L v).hom r hr).f (q, n - q) ≫ (eInf Y L q n r hr hY).hom =
              (eInf X K q n r hr hX).hom ≫
                cokernel.map
                  (Subobject.ofLE (((D X K).H n).step (q + 1)) (((D X K).H n).step q)
                    (((D X K).H n).antitone_step (Int.le_add_one (le_refl q))))
                  (Subobject.ofLE (((D Y L).H n).step (q + 1)) (((D Y L).H n).step q)
                    (((D Y L).H n).antitone_step (Int.le_add_one (le_refl q))))
                  (t (q + 1)) (t q) (hc q)) := by
  obtain ⟨D, M, e, hE, hLift⟩ := exists_etaleCE_coherent_first_page_lifts
  obtain ⟨R, eInf, hStable⟩ := exists_etaleCE_stationary_page_comparisons D e
  refine ⟨D, M, R, eInf, hE, ?_⟩
  intro X Y f K L v
  obtain ⟨u, hu, hPres, hRep⟩ := hLift f K L v
  refine ⟨u, hu, ?_⟩
  exact hStable K L
    ((D X K).totalSectionsIso.hom ≫ ceSectionsLift f u ≫ (D Y L).totalSectionsIso.inv)
    (M f K L v) hPres hRep

end AlgebraicGeometry.Etale
