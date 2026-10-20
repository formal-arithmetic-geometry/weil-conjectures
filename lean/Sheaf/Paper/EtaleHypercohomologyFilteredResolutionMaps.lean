/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group B2
-/
module

public import Sheaf.Paper.EtaleTermwiseHypercohomology

import Sheaf.Paper.EtaleHypercohomologyCETotalMaps
import Sheaf.Algebra.Homology.KInjectiveComparisonPrinciple
import Sheaf.CategoryTheory.CartanEilenbergAugmentationQuasiIso

/-! # Filtered resolution construction of étale hypercohomology pullback

Source: Stacks Project, Tags 015J, 015K and 0EZM.
(blueprint: lem-weil-pbc-filtered-resolution-pullback).
-/

@[expose] public section

universe uNatural

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Etale

set_option backward.isDefEq.respectTransparency false in
private theorem sections_naturality {A : Type (uNatural + 2)}
    [Category.{uNatural + 1} A]
    [Abelian A] [IsGrothendieckAbelian.{uNatural + 1} A] [HasSmallSiteSheafify A]
    {X Y : Scheme.{uNatural}} (f : Y ⟶ X)
    {F G : Sheaf X.smallEtaleTopology A} (g : F ⟶ G) :
    (Sheaf.Γ X.smallEtaleTopology A).map g ≫
      globalSectionsUpperStarMap A f G =
    globalSectionsUpperStarMap A f F ≫
      (Sheaf.Γ Y.smallEtaleTopology A).map
        ((upperStar A f).map g) := by
  unfold globalSectionsUpperStarMap
  rw [Category.assoc, Category.assoc,
    (Sheaf.ΓNatIsoSheafSections X.smallEtaleTopology A
      terminalIsTerminal).hom.naturality_assoc g]
  have hn := (upperStarLowerStarAdjunction A f).unit.naturality g
  simp only [Functor.id_map] at hn
  rw [← Functor.map_comp_assoc, hn, Functor.map_comp]
  simp only [Category.assoc]
  rw [← (Sheaf.ΓNatIsoSheafSections Y.smallEtaleTopology A
      terminalIsTerminal).inv.naturality]
  congr 1
  congr 1
  have hu := ((upperStar A f).map g).hom.naturality
    (PreservesTerminal.iso (Scheme.Hom.Etale f)).inv.op
  simp only [Functor.comp_map, Functor.flip_obj_map, ObjectProperty.ι_map]
  erw [lowerStar_map_hom_app]
  simpa only [Category.assoc] using! congrArg (fun a ↦ a ≫
    (Sheaf.ΓNatIsoSheafSections Y.smallEtaleTopology A
      terminalIsTerminal).inv.app ((upperStar A f).obj G)) hu.symm


private noncomputable def sectionsUnit {X Y : Scheme.{uNatural}} (f : Y ⟶ X)
    (A : CochainComplex (Sheaf X.smallEtaleTopology AddCommGrpCat.{uNatural + 1}) ℤ) :
    ((Sheaf.Γ X.smallEtaleTopology AddCommGrpCat.{uNatural + 1}).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj A ⟶
    ((Sheaf.Γ Y.smallEtaleTopology AddCommGrpCat.{uNatural + 1}).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj
      (((upperStar AddCommGrpCat.{uNatural + 1} f).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj A) where
  f i := globalSectionsUpperStarMap AddCommGrpCat.{uNatural + 1} f (A.X i)
  comm' i k _ := (sections_naturality f (A.d i k)).symm

private theorem sectionsUnit_naturality {X Y : Scheme.{uNatural}} (f : Y ⟶ X)
    {A B : CochainComplex (Sheaf X.smallEtaleTopology AddCommGrpCat.{uNatural + 1}) ℤ}
    (a : A ⟶ B) :
    ((Sheaf.Γ X.smallEtaleTopology AddCommGrpCat.{uNatural + 1}).mapHomologicalComplex
        (ComplexShape.up ℤ)).map a ≫ sectionsUnit f B =
      sectionsUnit f A ≫
        ((Sheaf.Γ Y.smallEtaleTopology AddCommGrpCat.{uNatural + 1}).mapHomologicalComplex
          (ComplexShape.up ℤ)).map
          (((upperStar AddCommGrpCat.{uNatural + 1} f).mapHomologicalComplex
            (ComplexShape.up ℤ)).map a) := by
  apply HomologicalComplex.hom_f_injective
  funext i
  exact sections_naturality f (a.f i)

set_option backward.isDefEq.respectTransparency false in
set_option linter.unusedVariables false in
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
  classical
  obtain ⟨D, M, R, eInf, hE, hA⟩ := exists_etaleHypercohomology_ce_total_maps
  refine ⟨D, M, R, eInf, hE, ?_⟩
  intro X Y f K L v n j hj w hw
  obtain ⟨g, s, e, hg, hs, he, hfil⟩ := hA f K L v
  let F := (upperStar AddCommGrpCat.{uNatural + 1} f).mapHomologicalComplex
    (ComplexShape.up ℤ)
  let ΓY := (Sheaf.Γ Y.smallEtaleTopology AddCommGrpCat.{uNatural + 1}).mapHomologicalComplex
    (ComplexShape.up ℤ)
  let A := (((CartanEilenbergPresentation.mappedFunctor
    (𝟭 (Sheaf X.smallEtaleTopology AddCommGrpCat.{uNatural + 1}))).obj
      (D X K).I).flip).total (ComplexShape.up ℤ)
  let Q := HomotopyCategory.quotient
    (Sheaf Y.smallEtaleTopology AddCommGrpCat.{uNatural + 1}) (ComplexShape.up ℤ)
  let : QuasiIso (D X K).aug := Functor.cartanEilenberg_augmentation_quasiIso
    K.obj (D X K).I (D X K).a (D X K).below (D X K).rows
    (D X K).aug (D X K).aug_formula
  let := (D Y L).ρ.isKInjective
  -- Check the finite-diagonal comparison against the presentation's actual section map.
  have hew : (D X K).w = e.hom ≫
      ((Sheaf.Γ X.smallEtaleTopology AddCommGrpCat.{uNatural + 1}).mapHomologicalComplex
        (ComplexShape.up ℤ)).map (D X K).comparison := by
    apply HomologicalComplex.hom_f_injective
    funext n
    apply HomologicalComplex₂.total.hom_ext (ComplexShape.up ℤ)
    intro r k hrk
    dsimp only
    by_cases hr : 0 ≤ r
    · obtain ⟨m, rfl⟩ : ∃ m : ℕ, r = (m : ℤ) := ⟨r.toNat, (Int.toNat_of_nonneg hr).symm⟩
      rw [HomologicalComplex.comp_f, ← Category.assoc, he m k n hrk,
        Category.assoc, Functor.mapHomologicalComplex_map_f, ← Functor.map_comp]
      exact (D X K).w_formula m k n hrk
    · have hz : IsZero
          ((((CartanEilenbergPresentation.mappedFunctor
            (Sheaf.Γ X.smallEtaleTopology AddCommGrpCat.{uNatural + 1})).obj
              (D X K).I).flip).X r |>.X k) := by
        exact HomologicalComplex.isZero_extend_X _ ComplexShape.embeddingUpNat r
          (fun m hm ↦ by change (m : ℤ) = r at hm; omega)
      exact hz.eq_of_src _ _
  -- Both maps out of the CE total extend the same augmented map. Cancel that augmentation.
  have hcomp : Nonempty (Homotopy (F.map (D X K).aug ≫
      (F.map (D X K).comparison ≫ j)) (v ≫ (D Y L).ρ.map)) := by
    have h := ((upperStar AddCommGrpCat.{uNatural + 1} f).mapHomotopy
      (D X K).over_K.some).compRight j
    have h' := h.trans hj.some
    rw [Functor.map_comp] at h'
    exact ⟨by simpa only [Category.assoc] using h'⟩
  have heq : Q.map g = Q.map (F.map (D X K).comparison ≫ j) := by
    apply (CochainComplex.IsKInjective.precomp_bijective_of_quasiIso
      (F.map (D X K).aug) (D Y L).ρ.complex).injective
    have h₁ := HomotopyCategory.eq_of_homotopy _ _ hg.some
    have h₂ := HomotopyCategory.eq_of_homotopy _ _ hcomp.some
    simpa only [Functor.map_comp] using h₁.trans h₂.symm
  have h := HomotopyCategory.homotopyOfEq _ _ heq
  -- Apply Γ to the homotopy and precompose by the sectionwise inverse-image unit.
  have hs' : s = sectionsUnit f A ≫ ΓY.map g := by
    apply HomologicalComplex.hom_f_injective
    funext i
    exact hs i
  have hw' : w = sectionsUnit f (D X K).ρ.complex ≫ ΓY.map j := by
    apply HomologicalComplex.hom_f_injective
    funext i
    exact hw i
  have hΓ : HomologicalComplex.homologyMap (e.hom ≫ s) n =
      HomologicalComplex.homologyMap ((D X K).w ≫ w) n := by
    rw [hs']
    have hΓh := (Sheaf.Γ Y.smallEtaleTopology AddCommGrpCat.{uNatural + 1}).mapHomotopy h
    have hh := (hΓh.compLeft (e.hom ≫ sectionsUnit f A)).homologyMap_eq n
    simp only [Category.assoc] at hh
    rw [hh, hew, hw']
    simp only [ΓY, Functor.map_comp, Category.assoc]
    rw [← Category.assoc (sectionsUnit f A), ← sectionsUnit_naturality f]
    simp only [Category.assoc]
  -- The canonical c_X is the cohomology map of D.w followed by the resolution comparison.
  have hconj : ((D X K).c n).inv ≫ HomologicalComplex.homologyMap (e.hom ≫ s) n ≫
      (@resolutionEtaleCohomologyIso.{uNatural} Y L.obj (D Y L).ρ.complex
        (D Y L).ρ.map (D Y L).ρ.quasiIso (D Y L).ρ.isKInjective n).hom =
      (@resolutionEtaleCohomologyIso.{uNatural} X K.obj (D X K).ρ.complex
        (D X K).ρ.map (D X K).ρ.quasiIso (D X K).ρ.isKInjective n).inv ≫
        HomologicalComplex.homologyMap w n ≫
        (@resolutionEtaleCohomologyIso.{uNatural} Y L.obj (D Y L).ρ.complex
          (D Y L).ρ.map (D Y L).ρ.quasiIso (D Y L).ρ.isKInjective n).hom := by
    rw [hΓ, HomologicalComplex.homologyMap_comp]
    have hc : ((D X K).c n).inv ≫ HomologicalComplex.homologyMap (D X K).w n =
        (@resolutionEtaleCohomologyIso.{uNatural} X K.obj (D X K).ρ.complex
          (D X K).ρ.map (D X K).ρ.quasiIso (D X K).ρ.isKInjective n).inv := by
      apply (cancel_mono
        (@resolutionEtaleCohomologyIso.{uNatural} X K.obj (D X K).ρ.complex
          (D X K).ρ.map (D X K).ρ.quasiIso (D X K).ρ.isKInjective n).hom).1
      rw [Category.assoc, ← (D X K).c_formula n, Iso.inv_hom_id, Iso.inv_hom_id]
    simp only [← Category.assoc, hc]
  obtain ⟨t, ht, hstable⟩ := hfil n
  refine ⟨t, ?_, hstable⟩
  intro q
  rw [← hconj]
  exact ht q

end AlgebraicGeometry.Etale
