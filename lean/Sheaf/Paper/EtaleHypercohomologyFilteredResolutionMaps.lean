/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group B2
-/
module

public import Sheaf.Paper.EtaleTermwiseHypercohomology

import Sheaf.AlgebraicGeometry.EtaleInverseImageExact
import Sheaf.CategoryTheory.BoundedFilteredComplexSpectralSequence
import Sheaf.CategoryTheory.CartanEilenbergFunctorial
import Sheaf.CategoryTheory.CartanEilenbergExists
import Sheaf.CategoryTheory.KInjectiveComputes
import Sheaf.AlgebraicGeometry.EtaleSheafHExtDerivedComparison
import Sheaf.AlgebraicGeometry.EtaleCohomologyPullbackFunctorial

/-! # Filtered resolution construction of étale hypercohomology pullback

Source: Stacks Project, Tags 015J, 015K and 0EZM.
(blueprint: lem-weil-pbc-filtered-resolution-pullback).
-/

@[expose] public section

universe uNatural

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Etale

set_option maxHeartbeats 1000000 in
-- Elaborating resolution and spectral-page comparison families together.
/-- Construct filtered pullback spectral-sequence maps with their concrete
K-injective cohomology comparison; no derived unit--Leray identification is claimed.
Source: Stacks Project, Tags 015J and 015K, and Tag 0EZM.
(blueprint: lem-weil-pbc-filtered-resolution-pullback).

Proof: For every bounded-below complex choose a bounded-below CE resolution.
Use the second-degree filtration after extension and index flip, and the
canonical filtered-complex spectral-sequence functor to choose all presentations.
Apply exact inverse image and CE comparison to each v, then apply the
termwise global-sections unit. These bicomplex maps preserve the complex-degree
filtration, so the filtered-complex functor supplies M. For any given lift j over v with hj
and any supplied chain map w with the stated degreewise components, the comparison
of the total CE map with j is a homotopy over the augmentations, so their
cohomology maps agree. Transport the image filtration along the canonical total
comparison to obtain t and ht. The parent derives hc by monicity of filtration inclusions.
For E₁, compute the map on each injective row as cohomologyMap followed by
Sheaf.H.map of v; the signed row identifications commute because the indices
are unchanged. Finally finite convergence makes the cycles and boundaries
stationary in each bidegree. Choose the least common stationary bound for the
presentation in that bidegree; the canonical quotient-to-image identifications
supply eInf. Their naturality for filtered maps identifies stable-page maps
with cokernel.map of t, giving the last equation. All choices are of witnesses
in this existence theorem; no definition chooses an undetermined object. -/
theorem exists_etaleHypercohomology_filtered_resolution_maps :
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
          (ComplexShape.up ℤ)).obj K.obj ⟶ L.obj) (n : ℤ),
        ∀ (j : ((upperStar AddCommGrpCat.{uNatural + 1} f).mapHomologicalComplex
              (ComplexShape.up ℤ)).obj (D X K).ρ.complex ⟶ (D Y L).ρ.complex)
          (hj : Nonempty (Homotopy
            (((upperStar AddCommGrpCat.{uNatural + 1} f).mapHomologicalComplex
              (ComplexShape.up ℤ)).map (D X K).ρ.map ≫ j) (v ≫ (D Y L).ρ.map))),
        ∀ (w : ((Sheaf.Γ X.smallEtaleTopology AddCommGrpCat.{uNatural + 1}).mapHomologicalComplex
              (ComplexShape.up ℤ)).obj (D X K).ρ.complex ⟶
            ((Sheaf.Γ Y.smallEtaleTopology AddCommGrpCat.{uNatural + 1}).mapHomologicalComplex
              (ComplexShape.up ℤ)).obj (D Y L).ρ.complex)
          (hw : ∀ i : ℤ, w.f i =
            globalSectionsUpperStarMap AddCommGrpCat.{uNatural + 1} f ((D X K).ρ.complex.X i) ≫
              (Sheaf.Γ Y.smallEtaleTopology AddCommGrpCat.{uNatural + 1}).map (j.f i)),
        ∃ (t : ∀ q : ℤ, (((D X K).H n).step q : AddCommGrpCat.{uNatural + 1}) ⟶
            (((D Y L).H n).step q : AddCommGrpCat.{uNatural + 1}))
          (ht : ∀ q : ℤ, t q ≫ (((D Y L).H n).step q).arrow =
            (((D X K).H n).step q).arrow ≫
            ((@resolutionEtaleCohomologyIso.{uNatural} X K.obj (D X K).ρ.complex
              (D X K).ρ.map (D X K).ρ.quasiIso (D X K).ρ.isKInjective n).inv ≫
            HomologicalComplex.homologyMap w n ≫
            (@resolutionEtaleCohomologyIso.{uNatural} Y L.obj (D Y L).ρ.complex
              (D Y L).ρ.map (D Y L).ρ.quasiIso (D Y L).ρ.isKInjective n).hom)),
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
  sorry

end AlgebraicGeometry.Etale
