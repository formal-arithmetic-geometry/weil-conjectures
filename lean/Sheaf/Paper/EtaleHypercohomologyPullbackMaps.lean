/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group S1
-/
module

public import Sheaf.Paper.EtaleTermwiseHypercohomology
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.TopologicalInvariance
public import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStar

import Sheaf.Paper.EtaleHypercohomologyFilteredResolutionMaps
import Sheaf.Paper.EtaleKInjectivePullbackAbutment
import Sheaf.Algebra.Homology.KInjectiveComparisonPrinciple

/-! # Construction and abutment comparison for termwise hypercohomology pullback

Source: Stacks Project, Tags 015J, 015K and 0EZM.
(blueprint: lem-weil-pbc-hypercohomology-pullback-maps).
-/

@[expose] public section

universe uNatural

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Etale

set_option backward.isDefEq.respectTransparency false in
private theorem sections_naturality {X Y : Scheme.{uNatural}} (f : Y ⟶ X)
    {A B : Sheaf X.smallEtaleTopology AddCommGrpCat.{uNatural + 1}} (g : A ⟶ B) :
    (Sheaf.Γ X.smallEtaleTopology AddCommGrpCat.{uNatural + 1}).map g ≫
      globalSectionsUpperStarMap AddCommGrpCat.{uNatural + 1} f B =
    globalSectionsUpperStarMap AddCommGrpCat.{uNatural + 1} f A ≫
      (Sheaf.Γ Y.smallEtaleTopology AddCommGrpCat.{uNatural + 1}).map
        ((upperStar AddCommGrpCat.{uNatural + 1} f).map g) := by
  unfold globalSectionsUpperStarMap
  rw [Category.assoc, Category.assoc,
    (Sheaf.ΓNatIsoSheafSections X.smallEtaleTopology AddCommGrpCat.{uNatural + 1}
      terminalIsTerminal).hom.naturality_assoc g]
  have hn := (upperStarLowerStarAdjunction AddCommGrpCat.{uNatural + 1} f).unit.naturality g
  simp only [Functor.id_map] at hn
  rw [← Functor.map_comp_assoc, hn, Functor.map_comp]
  simp only [Category.assoc]
  rw [← (Sheaf.ΓNatIsoSheafSections Y.smallEtaleTopology AddCommGrpCat.{uNatural + 1}
      terminalIsTerminal).inv.naturality]
  congr 1
  congr 1
  have hu := ((upperStar AddCommGrpCat.{uNatural + 1} f).map g).hom.naturality
    (PreservesTerminal.iso (Scheme.Hom.Etale f)).inv.op
  simp only [Functor.comp_map, Functor.flip_obj_map, ObjectProperty.ι_map]
  erw [lowerStar_map_hom_app]
  simpa only [Category.assoc] using! congrArg (fun a ↦ a ≫
    (Sheaf.ΓNatIsoSheafSections Y.smallEtaleTopology AddCommGrpCat.{uNatural + 1}
      terminalIsTerminal).inv.app ((upperStar AddCommGrpCat.{uNatural + 1} f).obj B)) hu.symm

set_option backward.isDefEq.respectTransparency false in
set_option linter.unusedVariables false in
set_option maxHeartbeats 1000000 in
-- Elaborating the dependent presentation families and compatibility equations.
/-- Construction and abutment comparison for termwise hypercohomology pullback.
Source: Stacks Project, Tags 015J, 015K and 0EZM.
(blueprint: lem-weil-pbc-hypercohomology-pullback-maps).

Proof: Choose bounded-below Cartan--Eilenberg resolutions for each complex and use
thm-sp-if-e1 to obtain their termwise presentations. For a pair (f,v), exactness
of f⁻¹ and lem-weil-pbc-cartesian-eilenberg-functorial provide a bicomplex lift.
Apply global sections to the inverse-image unit and then to this lift. Both maps
preserve the complex-degree filtration. The filtered-complex spectral-sequence
construction gives M. On each row the injective resolution is K-injective;
factoring the row lift through a K-injective resolution computes cohomologyMap
followed by Sheaf.H.map v. The signed E₁ identifications commute with this row
map, giving the displayed first-page equation. The total is a K-injective
resolution, and comparison maps over the augmentation are unique up to
homotopy. Hence its global-section cohomology map is the unit--Leray--v map,
which equals P by hP. Restricting the filtered total map gives maps on image
filtrations. Their inclusions commute by monicity. Functorial convergence
identifies stable pages with cokernels of successive filtration inclusions;
choose uniform stabilization bounds for each presentation and bidegree, and
transport these identifications through the canonical resolution comparison.
The resulting graded maps are cokernel.map of the filtration maps, yielding
the last equation. No identity or composition assertion is used here. -/
theorem exists_etaleHypercohomology_pullback_maps
    (P : ∀ {X Y : Scheme.{uNatural}} (f : Y ⟶ X)
      (K : CochainComplex (Sheaf X.smallEtaleTopology AddCommGrpCat.{uNatural + 1}) ℤ)
      (L : CochainComplex (Sheaf Y.smallEtaleTopology AddCommGrpCat.{uNatural + 1}) ℤ)
      (_ : ((upperStar AddCommGrpCat.{uNatural + 1} f).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj K ⟶ L) (n : ℤ),
      (cohomology AddCommGrpCat.{uNatural + 1} X n).obj (DerivedCategory.Q.obj K) ⟶
        (cohomology AddCommGrpCat.{uNatural + 1} Y n).obj (DerivedCategory.Q.obj L))
    (hP : ∀ {X Y : Scheme.{uNatural}} (f : Y ⟶ X)
      (K : CochainComplex (Sheaf X.smallEtaleTopology AddCommGrpCat.{uNatural + 1}) ℤ)
      (L : CochainComplex (Sheaf Y.smallEtaleTopology AddCommGrpCat.{uNatural + 1}) ℤ)
      (v : ((upperStar AddCommGrpCat.{uNatural + 1} f).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj K ⟶ L) (n : ℤ),
      P f K L v n = (DerivedCategory.homologyFunctor AddCommGrpCat.{uNatural + 1} n).map
        ((rightDerivedGlobalSections AddCommGrpCat.{uNatural + 1} X).map
            ((mapDerivedUpperStarLowerStarAdjunction AddCommGrpCat.{uNatural + 1} f).unit.app
              (DerivedCategory.Q.obj K)) ≫
          (rightDerivedLowerStarCompRightDerivedGlobalSectionsIso
            AddCommGrpCat.{uNatural + 1} f).hom.app
              ((upperStar AddCommGrpCat.{uNatural + 1} f).mapDerivedCategory.obj
                (DerivedCategory.Q.obj K)) ≫
          (rightDerivedGlobalSections AddCommGrpCat.{uNatural + 1} Y).map
            ((upperStar AddCommGrpCat.{uNatural + 1} f).mapDerivedCategoryFactors.hom.app K ≫
              DerivedCategory.Q.map v))) :
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
        ∃ (t : ∀ q : ℤ, (((D X K).H n).step q : AddCommGrpCat.{uNatural + 1}) ⟶
            (((D Y L).H n).step q : AddCommGrpCat.{uNatural + 1}))
          (ht : ∀ q : ℤ, t q ≫ (((D Y L).H n).step q).arrow =
            (((D X K).H n).step q).arrow ≫ P f K.obj L.obj v n)
          (hc : ∀ q : ℤ,
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
  obtain ⟨D, M, R, eInf, hE, hA⟩ :=
    exists_etaleHypercohomology_filtered_resolution_maps
  refine ⟨D, M, R, eInf, hE, ?_⟩
  intro X Y f K L v n
  let := (D X K).ρ.quasiIso
  let := (D Y L).ρ.isKInjective
  let F := (upperStar AddCommGrpCat.{uNatural + 1} f).mapHomologicalComplex
    (ComplexShape.up ℤ)
  let Q := HomotopyCategory.quotient
    (Sheaf Y.smallEtaleTopology AddCommGrpCat.{uNatural + 1}) (ComplexShape.up ℤ)
  have hbij := CochainComplex.IsKInjective.precomp_bijective_of_quasiIso
    (F.map (D X K).ρ.map) (D Y L).ρ.complex
  obtain ⟨a, ha⟩ := hbij.surjective (Q.map (v ≫ (D Y L).ρ.map))
  obtain ⟨j, rfl⟩ := Q.map_surjective a
  have hj : Nonempty (Homotopy (F.map (D X K).ρ.map ≫ j)
      (v ≫ (D Y L).ρ.map)) := by
    refine ⟨HomotopyCategory.homotopyOfEq _ _ ?_⟩
    simpa only [Functor.map_comp] using ha
  let w : ((Sheaf.Γ X.smallEtaleTopology AddCommGrpCat.{uNatural + 1}).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj (D X K).ρ.complex ⟶
      ((Sheaf.Γ Y.smallEtaleTopology AddCommGrpCat.{uNatural + 1}).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj (D Y L).ρ.complex :=
    { f := fun i ↦ globalSectionsUpperStarMap AddCommGrpCat.{uNatural + 1} f
          ((D X K).ρ.complex.X i) ≫
        (Sheaf.Γ Y.smallEtaleTopology AddCommGrpCat.{uNatural + 1}).map (j.f i)
      comm' := by
        intro i k hik
        change (_ ≫ _) ≫
            (Sheaf.Γ Y.smallEtaleTopology AddCommGrpCat.{uNatural + 1}).map
              ((D Y L).ρ.complex.d i k) =
          (Sheaf.Γ X.smallEtaleTopology AddCommGrpCat.{uNatural + 1}).map
            ((D X K).ρ.complex.d i k) ≫ _
        rw [Category.assoc, ← Functor.map_comp, j.comm i k, Functor.map_comp]
        simp only [F, Functor.mapHomologicalComplex_obj_d]
        rw [← Category.assoc, ← sections_naturality f, Category.assoc] }
  have hw : ∀ i : ℤ, w.f i =
      globalSectionsUpperStarMap AddCommGrpCat.{uNatural + 1} f ((D X K).ρ.complex.X i) ≫
        (Sheaf.Γ Y.smallEtaleTopology AddCommGrpCat.{uNatural + 1}).map (j.f i) :=
    fun _ ↦ rfl
  obtain ⟨t, ht, hstable⟩ := hA f K L v n j hj w hw
  have hmap := etaleKInjective_pullback_abutment f K.obj L.obj v
    (D X K).ρ (D Y L).ρ j hj w hw n
  have hPmap := hP f K.obj L.obj v n
  have ht' : ∀ q : ℤ, t q ≫ (((D Y L).H n).step q).arrow =
      (((D X K).H n).step q).arrow ≫ P f K.obj L.obj v n := by
    intro q
    rw [hPmap, ← hmap]
    exact ht q
  have hc : ∀ q : ℤ,
      Subobject.ofLE (((D X K).H n).step (q + 1)) (((D X K).H n).step q)
          (((D X K).H n).antitone_step (Int.le_add_one (le_refl q))) ≫ t q =
        t (q + 1) ≫
          Subobject.ofLE (((D Y L).H n).step (q + 1)) (((D Y L).H n).step q)
            (((D Y L).H n).antitone_step (Int.le_add_one (le_refl q))) := by
    intro q
    apply (cancel_mono (((D Y L).H n).step q).arrow).1
    rw [Category.assoc, ht', Category.assoc, Subobject.ofLE_arrow, ht',
      ← Category.assoc, Subobject.ofLE_arrow]
  exact ⟨t, ht', hc, hstable hc⟩

end AlgebraicGeometry.Etale
