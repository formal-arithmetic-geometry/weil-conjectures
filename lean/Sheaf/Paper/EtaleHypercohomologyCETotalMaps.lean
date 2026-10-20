/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group K2
-/
module

public import Sheaf.Paper.EtaleTermwiseHypercohomology
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.TopologicalInvariance

import Sheaf.Paper.EtaleCEFilteredTotalConstruction

/-! # Coherent filtered Cartan--Eilenberg total maps

Source: Stacks Project, derived.tex, Tags 015J and 015K.
(blueprint: lem-weil-pbc-ce-total-filtered-maps).
-/

@[expose] public section

universe uNatural

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Etale

set_option linter.unusedVariables false in
set_option maxHeartbeats 1000000 in
-- Elaborate the simultaneous presentation, total-map and stabilization witnesses.
/-- Choose the filtered CE spectral sequences and their maps on CE totals. The abutment
here uses the CE total source, rather than any supplied lift between the chosen resolutions.
Source: Stacks Project, derived.tex, Tag 015J (lemma-two-ss-complex-functor) and
Tag 015K (remark-functorial-ss).
(blueprint: lem-weil-pbc-ce-total-filtered-maps).

Proof: Use exists_etaleHypercohomology_ce_filtered_totals to construct the coherent
filtered spectral data and a map u between the CE sheaf totals, with its strict
augmentation square and stationary-page equation on the cohomology of CE totals.
Compose u with the target presentation's comparison to obtain g. Its augmentation
square, followed by the target's over_K homotopy, gives the required homotopy.
Define s degreewise from the global-sections unit and g; naturality of the unit
makes s a chain map. The proved finite-diagonal comparison totalSectionsIso supplies
e and its summand formula. On every nonnegative diagonal summand, this formula and
w_formula show that the target comparison followed by global sections is w; negative
resolution summands are zero. Hence the map of global-sections CE totals followed
by w_Y equals e.hom followed by s. Applying homologyMap_comp and c_formula identifies
the CE abutment map with the required resolutionEtaleCohomologyIso composite.
Keep the filtration-step maps supplied by the filtered-total construction, rewrite
ht by this equality, and retain its stationary-page equation. The latter does not
depend on the proof of ht.
Zero complexes, empty schemes and empty diagonal sums are included in these constructions.
No choice of an arbitrary resolution lift is used in this statement. -/
theorem exists_etaleHypercohomology_ce_total_maps :
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
        let A := (((CartanEilenbergPresentation.mappedFunctor
          (𝟭 (Sheaf X.smallEtaleTopology AddCommGrpCat.{uNatural + 1}))).obj
            (D X K).I).flip).total (ComplexShape.up ℤ)
        let B := (((CartanEilenbergPresentation.mappedFunctor
          (Sheaf.Γ X.smallEtaleTopology AddCommGrpCat.{uNatural + 1})).obj
            (D X K).I).flip).total (ComplexShape.up ℤ)
        ∃ (g : ((upperStar AddCommGrpCat.{uNatural + 1} f).mapHomologicalComplex
              (ComplexShape.up ℤ)).obj A ⟶ (D Y L).ρ.complex)
          (s : ((Sheaf.Γ X.smallEtaleTopology AddCommGrpCat.{uNatural + 1}).mapHomologicalComplex
              (ComplexShape.up ℤ)).obj A ⟶
            ((Sheaf.Γ Y.smallEtaleTopology AddCommGrpCat.{uNatural + 1}).mapHomologicalComplex
              (ComplexShape.up ℤ)).obj (D Y L).ρ.complex)
          (e : B ≅ ((Sheaf.Γ X.smallEtaleTopology AddCommGrpCat.{uNatural + 1})
              |>.mapHomologicalComplex (ComplexShape.up ℤ)).obj A),
          Nonempty (Homotopy
            (((upperStar AddCommGrpCat.{uNatural + 1} f).mapHomologicalComplex
              (ComplexShape.up ℤ)).map (D X K).aug ≫ g) (v ≫ (D Y L).ρ.map)) ∧
          (∀ i : ℤ, s.f i =
            globalSectionsUpperStarMap AddCommGrpCat.{uNatural + 1} f (A.X i) ≫
              (Sheaf.Γ Y.smallEtaleTopology AddCommGrpCat.{uNatural + 1}).map (g.f i)) ∧
          (∀ (m : ℕ) (k n : ℤ) (h : (m : ℤ) + k = n),
            (((CartanEilenbergPresentation.mappedFunctor
              (Sheaf.Γ X.smallEtaleTopology AddCommGrpCat.{uNatural + 1})).obj
                (D X K).I).flip).ιTotal (ComplexShape.up ℤ) (m : ℤ) k n h ≫ e.hom.f n =
              (HomologicalComplex.extendXIso
                (((Sheaf.Γ X.smallEtaleTopology AddCommGrpCat.{uNatural + 1})
                  |>.mapHomologicalComplex (ComplexShape.up ℕ)).obj ((D X K).I.X k))
                ComplexShape.embeddingUpNat (i := m) (i' := (m : ℤ)) rfl).hom ≫
              (Sheaf.Γ X.smallEtaleTopology AddCommGrpCat.{uNatural + 1}).map
                ((HomologicalComplex.extendXIso
                  (((𝟭 (Sheaf X.smallEtaleTopology AddCommGrpCat.{uNatural + 1}))
                    |>.mapHomologicalComplex (ComplexShape.up ℕ)).obj ((D X K).I.X k))
                  ComplexShape.embeddingUpNat (i := m) (i' := (m : ℤ)) rfl).inv ≫
                (((CartanEilenbergPresentation.mappedFunctor
                  (𝟭 (Sheaf X.smallEtaleTopology AddCommGrpCat.{uNatural + 1}))).obj
                    (D X K).I).flip).ιTotal (ComplexShape.up ℤ) (m : ℤ) k n h)) ∧
          ∀ n : ℤ,
            ∃ (t : ∀ q : ℤ, (((D X K).H n).step q : AddCommGrpCat.{uNatural + 1}) ⟶
            (((D Y L).H n).step q : AddCommGrpCat.{uNatural + 1}))
          (ht : ∀ q : ℤ, t q ≫ (((D Y L).H n).step q).arrow =
            (((D X K).H n).step q).arrow ≫
            (((D X K).c n).inv ≫
              HomologicalComplex.homologyMap (e.hom ≫ s) n ≫
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
  obtain ⟨D, M, R, eInf, hE, hT⟩ := exists_etaleHypercohomology_ce_filtered_totals
  refine ⟨D, M, R, eInf, hE, ?_⟩
  intro X Y f K L v
  obtain ⟨u, hu, hstable⟩ := hT f K L v
  let g := u ≫ (D Y L).comparison
  let s := ceSectionsLift f g
  let e := (D X K).totalSectionsIso
  refine ⟨g, s, e, ?_, ?_, (D X K).totalSectionsIso_formula, ?_⟩
  · obtain ⟨h⟩ := (D Y L).over_K
    exact ⟨by simpa only [g, ← Category.assoc, hu] using h.compLeft v⟩
  · intro i
    rfl
  · intro n
    obtain ⟨t, ht, hpage⟩ := hstable n
    have htotal :
        ((D X K).totalSectionsIso.hom ≫ ceSectionsLift f u ≫
          (D Y L).totalSectionsIso.inv) ≫ (D Y L).w = e.hom ≫ s := by
      rw [← (D Y L).totalSectionsIso_comparison]
      simp only [Category.assoc, Iso.inv_hom_id_assoc]
      rw [← ceSectionsLift_comp]
    have habut :
        HomologicalComplex.homologyMap
          ((D X K).totalSectionsIso.hom ≫ ceSectionsLift f u ≫
            (D Y L).totalSectionsIso.inv) n ≫ ((D Y L).c n).hom =
        HomologicalComplex.homologyMap (e.hom ≫ s) n ≫
          (@resolutionEtaleCohomologyIso.{uNatural} Y L.obj (D Y L).ρ.complex
            (D Y L).ρ.map (D Y L).ρ.quasiIso (D Y L).ρ.isKInjective n).hom := by
      rw [(D Y L).c_formula]
      rw [← Category.assoc, ← HomologicalComplex.homologyMap_comp, htotal]
    refine ⟨t, ?_, hpage⟩
    intro q
    rw [ht q, ← Category.assoc, habut]
    simp only [Category.assoc]

end AlgebraicGeometry.Etale
