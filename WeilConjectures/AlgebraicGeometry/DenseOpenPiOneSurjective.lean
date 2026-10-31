/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.FundamentalGroup.DenseOpenNormal
public import WeilConjectures.EtaleCohomology.Purity.RealSheaves.Construction
public import WeilConjectures.WeilSheaf.DenseOpen
public import WeilConjectures.AlgebraicGeometry.RealSheavesSetup
public import WeilConjectures.AlgebraicGeometry.IsConstructibleEtaleModuleSheaf

import WeilConjectures.ConstructibleSheaf.NormalOpenLowerStar
import WeilConjectures.ConstructibleSheaf.DenseOpenUnitNormal
import WeilConjectures.AlgebraicGeometry.ConstructibleEtaleModuleSheafComparison
import WeilConjectures.AlgebraicGeometry.GeometricallyConnectedAlgebraicClosure
import WeilConjectures.AlgebraicGeometry.NormalStalkFlatDescent

/-! # Fundamental groups of a dense open surject

Source: Stacks Project, Fundamental Groups of Schemes, Tag 0BQI; blueprint, dense-open lemma
(blueprint: lem-wf-dense-open-pi1-surjective).

## Main statements

* `AlgebraicGeometry.Scheme.FiniteEtale.denseOpenPiOneSurjective` records the five
  clauses of the dense-open lemma: geometric and Weil-group surjectivity, extension
  of lisse sheaves, restriction on curves, and constructibility of the middle extension.
-/

@[expose] public section
set_option autoImplicit false

universe u v

open CategoryTheory CategoryTheory.Limits CategoryTheory.PreGaloisCategory
open AlgebraicGeometry
open AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.FiniteEtale

namespace AlgebraicGeometry.Scheme.FiniteEtale

private theorem curve_geometry (D : RealSheaves.Setup.{u, v}) (X : Scheme.{u})
    [X.Over (Spec (.of D.k₀))] (hX : D.IsCurve X) :
    GeometricallyConnected (X ↘ Spec (.of D.k₀)) ∧
      SmoothOfRelativeDimension 1 (X ↘ Spec (.of D.k₀)) ∧
      IsNoetherian X ∧ IsIntegral X := by
  have : IsAlgClosed D.k := IsAlgClosure.isAlgClosed D.k₀
  have : Smooth (X ↘ Spec (.of D.k₀)) := hX.2.2.1
  have : LocallyOfFiniteType (X ↘ Spec (.of D.k₀)) := hX.2.2.2.1
  have : QuasiCompact (X ↘ Spec (.of D.k₀)) := hX.2.2.2.2.1
  have : GeometricallyConnected (X ↘ Spec (.of D.k₀)) :=
    (geometricallyConnected_iff_connectedSpace_of_isAlgClosed (Ω := D.k) X).mpr
      hX.2.2.2.2.2.2
  have : ConnectedSpace X := GeometricallyConnected.connectedSpace_of_subsingleton
    (X ↘ Spec (.of D.k₀))
  have := LocallyOfFiniteType.isLocallyNoetherian (X ↘ Spec (.of D.k₀))
  have := QuasiCompact.compactSpace_of_compactSpace (X ↘ Spec (.of D.k₀))
  have := IsRegular.of_smooth (X ↘ Spec (.of D.k₀))
  have := IsRegular.isIntegral X
  have hp := hX.2.2.2.2.2.1 Set.univ
    (by simp only [irreducibleComponents_eq_singleton, Set.mem_singleton_iff])
  have hdim : topologicalKrullDim X = (1 : WithBot ℕ∞) :=
    ((Homeomorph.Set.univ X).isHomeomorph.topologicalKrullDim_eq _).symm.trans hp
  exact ⟨inferInstance,
    (smoothOfRelativeDimension_iff_topologicalKrullDim_eq _ 1).mpr hdim, {}, inferInstance⟩

/-- The fundamental group, Weil-group, lisse-extension, curve-restriction and
constructibility assertions for a dense open of a connected normal Noetherian scheme.

Source: Stacks Project, Fundamental Groups of Schemes, Tag 0BQI
(lemma-irreducible-geometrically-unibranch); blueprint
`lem-wf-dense-open-pi1-surjective`, clauses (1)--(5)
(blueprint: lem-wf-dense-open-pi1-surjective).
Proof:
Step 0: the geometric point makes V' nonempty. A connected locally Noetherian
scheme with domain stalks is irreducible (`irreducibleSpace_of_isDomain_stalk`),
so the nonempty open V' is connected (`connectedSpace_of_isOpenImmersion`).
Step (1): the surjectivity of the fundamental-group map and the connectedness of
pulled-back connected finite etale covers are the proved source theorems
`fundamentalGroupMap_surjective_of_isIntegrallyClosed_stalk` (Galois category
`lem-fet-galois-category`, transitivity `lem-galois-transitive`, proper open
subgroup `lem-wf-profinite-closed-subgroup-intersection-open`) and
`isConnected_pullback_of_isIntegrallyClosed_stalk`.
Step (2): the field projection is flat and surjective; the geometric open map is an
open immersion by cancellation of the two pullback squares, nonempty by
surjectivity and connected as an open of the irreducible geometric scheme.
`lem-weil-geometrically-connected-algebraic-closure` gives geometric connectedness
of both arithmetic schemes, and `lem-wf-normal-stalk-flat-descent` descends normal
local domains to the arithmetic scheme. Then
`WeilGroup.restrictionHom_surjective_of_isIntegrallyClosed_stalk` gives
surjectivity (`def-wf-weil-group`, `lem-wf-weil-group-exact-sequence`); degree and
first-coordinate compatibility are definitional, and
`WeilGroup.map_ker_weilGroupDeg_restrictionHom` identifies the degree kernels.
Step (3): the finite-level unit is
`Etale.isIso_unit_upperStarLowerStarAdjunction_of_isIntegrallyClosed_stalk`; the
adic unit is
`IsAdicLisseSheaf.isIso_adicUpperStarLowerStarAdjunction_unit_app_of_isIntegrallyClosed`.
Step (4): `curve_geometry` derives from `d-real-setup` geometric connectedness,
smooth relative dimension one, Noetherianity and integrality (smooth implies regular,
`lem-sc-smooth-regular`). A nonempty open of the irreducible curve is dense. Apply
`WeilSheaf.upperStar_map_bijective_of_isLisse` and
`WeilSheaf.IsIrreducibleLisse.upperStar_of_isDominant`; on the geometric curves,
build the open-immersion base-change square and apply
`ProEtale.IsAdicLisseSheaf.adicUpperStar_map_bijective` and
`ProEtale.IsIrreducibleAdicLocalSystem.adicUpperStar`.
Step (5): the smooth curve is regular, so its etale open has normal local domains;
apply `lem-fin-normal-open-lisse-image` and convert the constructibility predicate by
`lem-weil-pbc-constructible-etale-module-sheaf-comparison`.
-/
theorem denseOpenPiOneSurjective
    {V V' : Scheme.{u}} (j : V' ⟶ V) [IsOpenImmersion j]
    [ConnectedSpace V] [IsNoetherian V]
    (hV : ∀ x : V, IsDomain (V.presheaf.stalk x) ∧
      IsIntegrallyClosed (V.presheaf.stalk x)) (hj : Dense (Set.range j.base))
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (s : Spec (.of Ω) ⟶ V') :
    ConnectedSpace V' ∧ ∀ [ConnectedSpace V']
    (G' G : Type u) [Group G'] [Group G]
    [TopologicalSpace G'] [TopologicalSpace G]
    [IsTopologicalGroup G'] [IsTopologicalGroup G]
    [CompactSpace G'] [CompactSpace G]
    [∀ P, MulAction G' ((fiber s).obj P)]
    [∀ P, MulAction G ((fiber (s ≫ j)).obj P)]
    [IsFundamentalGroup (fiber s) G']
    [IsFundamentalGroup (fiber (s ≫ j)) G],
    Function.Surjective (fundamentalGroupMap (pullbackFiberIso j s) G' G) ∧
      (∀ P : V.FiniteEtale, PreGaloisCategory.IsConnected P →
        PreGaloisCategory.IsConnected ((FiniteEtale.pullback j).obj P)) ∧
      (∀ {Λ : Type (u + 1)} [CommRing Λ] [Finite Λ]
        (N : Sheaf V.smallEtaleTopology (ModuleCat.{u + 1} Λ))
        [Scheme.IsFiniteLocallyConstantSheaf N],
        IsIso ((Etale.upperStarLowerStarAdjunction
          (ModuleCat.{u + 1} Λ) j).unit.app N)) ∧
      (∀ (l : ℕ) [Fact l.Prime] (N : ProEtale.AdicSheaf l V),
        ProEtale.IsAdicLisseSheaf N →
        IsIso ((ProEtale.adicUpperStarLowerStarAdjunction l j).unit.app N)) ∧
      (∀ (D : RealSheaves.Setup.{u, v}) {X U : Scheme.{u}}
        [X.Over (Spec (.of D.k₀))] [U.Over (Spec (.of D.k₀))]
        [IsSeparated (X ↘ Spec (.of D.k₀))]
        [LocallyOfFiniteType (X ↘ Spec (.of D.k₀))]
        [QuasiCompact (X ↘ Spec (.of D.k₀))]
        (i : U ⟶ X) [IsOpenImmersion i] [i.IsOver (Spec (.of D.k₀))]
        (_hi : Dense (Set.range i.base))
        (_hc : ConnectedSpace (D.geometricCurve X))
        (_hn : ∀ x : D.geometricCurve X,
          IsDomain ((D.geometricCurve X).presheaf.stalk x) ∧
            IsIntegrallyClosed ((D.geometricCurve X).presheaf.stalk x)),
        GeometricallyConnected (X ↘ Spec (.of D.k₀)) ∧
        GeometricallyConnected (U ↘ Spec (.of D.k₀)) ∧
        ∀ [GeometricallyConnected (X ↘ Spec (.of D.k₀))]
          [GeometricallyConnected (U ↘ Spec (.of D.k₀))]
          [ConnectedSpace X] [ConnectedSpace U]
          (sU : Spec (.of (AlgebraicClosure D.k₀)) ⟶ U)
          (sX : Spec (.of (AlgebraicClosure D.k₀)) ⟶ X)
          (σ : fiber (sU ≫ i) ≅ fiber sX)
          (H₁ H₂ : Type u) [Group H₁] [Group H₂]
          [TopologicalSpace H₁] [TopologicalSpace H₂]
          [IsTopologicalGroup H₁] [IsTopologicalGroup H₂]
          [CompactSpace H₁] [CompactSpace H₂]
          [∀ P, MulAction H₁ ((fiber sU).obj P)]
          [∀ P, MulAction H₂ ((fiber sX).obj P)]
          [IsFundamentalGroup (fiber sU) H₁]
          [IsFundamentalGroup (fiber sX) H₂],
          Function.Surjective (WeilGroup.restrictionHom i (comp_over i _) σ H₁ H₂) ∧
          (∀ w : weilGroup (U ↘ Spec (.of D.k₀)) sU H₁,
            weilGroupDeg (X ↘ Spec (.of D.k₀)) sX H₂
                (WeilGroup.restrictionHom i (comp_over i _) σ H₁ H₂ w) =
              weilGroupDeg (U ↘ Spec (.of D.k₀)) sU H₁ w) ∧
          (∀ w : weilGroup (U ↘ Spec (.of D.k₀)) sU H₁,
            ((WeilGroup.restrictionHom i (comp_over i _) σ H₁ H₂ w :
                H₂ × Multiplicative ℤ).1) =
              WeilGroup.restrictionMap i σ H₁ H₂ (w : H₁ × Multiplicative ℤ).1) ∧
          (weilGroupDeg (U ↘ Spec (.of D.k₀)) sU H₁).ker.map
              (WeilGroup.restrictionHom i (comp_over i _) σ H₁ H₂) =
            (weilGroupDeg (X ↘ Spec (.of D.k₀)) sX H₂).ker) ∧
      (∀ (D : RealSheaves.Setup.{u, v}) {U X : Scheme.{u}}
        [U.Over (Spec (.of D.k₀))] [X.Over (Spec (.of D.k₀))]
        (_hX : D.IsCurve X) (k : U ⟶ X) [IsOpenImmersion k]
        [k.IsOver (Spec (.of D.k₀))] (_hU : Nonempty U),
        (∀ (A N : WeilSheaf D.k₀ D.l X), A.IsLisse → N.IsLisse →
          Function.Bijective ((WeilSheaf.upperStar k).map :
            (A ⟶ N) → ((WeilSheaf.upperStar k).obj A ⟶
              (WeilSheaf.upperStar k).obj N))) ∧
        (∀ (N : WeilSheaf D.k₀ D.l X), N.IsIrreducibleLisse →
          ((WeilSheaf.upperStar k).obj N).IsIrreducibleLisse) ∧
        (∀ (A N : ProEtale.AdicSheaf D.l (D.geometricCurve X)),
          ProEtale.IsAdicLisseSheaf A → ProEtale.IsAdicLisseSheaf N →
          Function.Bijective
            ((ProEtale.adicUpperStar D.l
                (pullback.map (U ↘ Spec (.of D.k₀))
                  (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))
                  (X ↘ Spec (.of D.k₀))
                  (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))
                  k (𝟙 _) (𝟙 _)
                  ((Category.comp_id _).trans (comp_over k _).symm)
                  ((Category.comp_id _).trans (Category.id_comp _).symm))).map :
              (A ⟶ N) → _)) ∧
        (∀ (N : ProEtale.AdicSheaf D.l (D.geometricCurve X)),
          ProEtale.IsIrreducibleAdicLocalSystem N →
          ProEtale.IsIrreducibleAdicLocalSystem
            ((ProEtale.adicUpperStar D.l
                (pullback.map (U ↘ Spec (.of D.k₀))
                  (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))
                  (X ↘ Spec (.of D.k₀))
                  (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))
                  k (𝟙 _) (𝟙 _)
                  ((Category.comp_id _).trans (comp_over k _).symm)
                  ((Category.comp_id _).trans (Category.id_comp _).symm))).obj N))) ∧
      (∀ (D : RealSheaves.Setup.{u, v}) {C₀ U₀ : Scheme.{u}}
        [C₀.Over (Spec (.of D.k₀))] [U₀.Over (Spec (.of D.k₀))]
        (_hC : D.IsCurve C₀) (i : U₀ ⟶ C₀) [IsOpenImmersion i]
        [i.IsOver (Spec (.of D.k₀))] (_hU : Nonempty U₀)
        {Λ : Type (u + 1)} [CommRing Λ] [Finite Λ]
        (F : Sheaf U₀.smallEtaleTopology (ModuleCat.{u + 1} Λ))
        [Scheme.IsFiniteLocallyConstantSheaf F],
        Scheme.IsConstructibleEtaleModuleSheaf
          ((Etale.lowerStar (ModuleCat.{u + 1} Λ) i).obj F)) := by
  have : Nonempty V' := ⟨s default⟩
  have : IrreducibleSpace V := irreducibleSpace_of_isDomain_stalk V fun x ↦ (hV x).1
  have hconn := connectedSpace_of_isOpenImmersion j
  refine ⟨hconn, ?_⟩
  intro _ G' G _ _ _ _ _ _ _ _ _ _ _ _
  refine ⟨fundamentalGroupMap_surjective_of_isIntegrallyClosed_stalk
    j (pullbackFiberIso j s) G' G hV, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro P hP
    let := hP
    exact isConnected_pullback_of_isIntegrallyClosed_stalk j hV P
  · intro Λ _ _ N _
    exact Etale.isIso_unit_upperStarLowerStarAdjunction_of_isIntegrallyClosed_stalk hV j hj N
  · intro l _ N hN
    exact hN.isIso_adicUpperStarLowerStarAdjunction_unit_app_of_isIntegrallyClosed hV j hj
  · intro D X U _ _ _ _ _ i _ _ hi hc hn
    have : IsAlgClosed D.k := IsAlgClosure.isAlgClosed D.k₀
    let g := Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k))
    let p := X ↘ Spec (.of D.k₀)
    let q := U ↘ Spec (.of D.k₀)
    have : Surjective g := ⟨fun x ↦ ⟨default, Subsingleton.elim _ _⟩⟩
    have : ConnectedSpace (D.geometricCurve X) := hc
    have : GeometricallyConnected p :=
      (geometricallyConnected_iff_connectedSpace_of_isAlgClosed (Ω := D.k) X).mpr hc
    have : ConnectedSpace X := GeometricallyConnected.connectedSpace_of_subsingleton p
    have : Nonempty U := Set.range_nonempty_iff_nonempty.mp (hi.nonempty_iff.mpr inferInstance)
    have : Nonempty (D.geometricCurve U) :=
      (pullback.fst q g).surjective.nonempty
    have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian p
    have : IsLocallyNoetherian (D.geometricCurve X) :=
      LocallyOfFiniteType.isLocallyNoetherian (pullback.snd p g)
    have : IrreducibleSpace (D.geometricCurve X) :=
      irreducibleSpace_of_isDomain_stalk _ fun x ↦ (hn x).1
    let ib := pullback.map q g p g i (𝟙 _) (𝟙 _)
      ((Category.comp_id _).trans (comp_over i _).symm)
      ((Category.comp_id _).trans (Category.id_comp _).symm)
    have hb : IsPullback (pullback.fst q g) ib i (pullback.fst p g) := by
      apply IsPullback.of_bot ?_ (by simp [ib]) (IsPullback.of_hasPullback p g)
      have he : ib ≫ pullback.snd p g = pullback.snd q g := by simp [ib]
      rw [he]
      simpa only [p, comp_over] using IsPullback.of_hasPullback q g
    have : IsOpenImmersion ib := MorphismProperty.of_isPullback hb inferInstance
    have : ConnectedSpace (D.geometricCurve U) := connectedSpace_of_isOpenImmersion ib
    have : GeometricallyConnected q :=
      (geometricallyConnected_iff_connectedSpace_of_isAlgClosed (Ω := D.k) U).mpr inferInstance
    refine ⟨inferInstance, inferInstance, ?_⟩
    intro _ _ _ _ sU sX σ H₁ H₂ _ _ _ _ _ _ _ _ _ _ _ _
    have hnormal := normal_stalks_of_flat_surjective (pullback.fst p g) hn
    have hsurj := WeilGroup.restrictionHom_surjective_of_isIntegrallyClosed_stalk
      i (comp_over i _) σ H₁ H₂ hnormal
    exact ⟨hsurj, fun _ ↦ rfl, fun _ ↦ rfl,
      WeilGroup.map_ker_weilGroupDeg_restrictionHom i (comp_over i _) σ H₁ H₂ hsurj⟩
  · intro D U X _ _ hX k _ _ hU
    obtain ⟨hg, hs, hn, hi⟩ := curve_geometry D X hX
    let := hg
    let := hs
    let := hn
    let := hi
    let := hU
    have : Smooth (X ↘ Spec (.of D.k₀)) := hX.2.2.1
    have : LocallyOfFiniteType (X ↘ Spec (.of D.k₀)) := hX.2.2.2.1
    have : QuasiCompact (X ↘ Spec (.of D.k₀)) := hX.2.2.2.2.1
    have : IsDominant k := ⟨k.isOpenEmbedding.isOpenMap.denseRange_of_isPreirreducibleSpace k⟩
    let kb := pullback.map (U ↘ Spec (.of D.k₀))
      (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))
      (X ↘ Spec (.of D.k₀))
      (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))
      k (𝟙 _) (𝟙 _)
      ((Category.comp_id _).trans (comp_over k _).symm)
      ((Category.comp_id _).trans (Category.id_comp _).symm)
    have : ConnectedSpace (D.geometricCurve X) := hX.2.2.2.2.2.2
    have := IsRegular.of_smooth (pullback.snd (X ↘ Spec (.of D.k₀))
      (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k))))
    have := LocallyOfFiniteType.isLocallyNoetherian (pullback.snd (X ↘ Spec (.of D.k₀))
      (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k))))
    have := QuasiCompact.compactSpace_of_compactSpace (pullback.snd
      (X ↘ Spec (.of D.k₀)) (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k))))
    have hb : IsPullback (pullback.fst (U ↘ Spec (.of D.k₀))
        (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))) kb k
        (pullback.fst (X ↘ Spec (.of D.k₀))
          (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))) := by
      apply IsPullback.of_bot ?_ (by simp [kb]) (IsPullback.of_hasPullback _ _)
      have he : kb ≫ pullback.snd (X ↘ Spec (.of D.k₀))
          (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k))) =
          pullback.snd (U ↘ Spec (.of D.k₀))
            (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k))) := by simp [kb]
      rw [he]
      simpa only [comp_over] using IsPullback.of_hasPullback (U ↘ Spec (.of D.k₀))
        (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))
    have : IsOpenImmersion kb := MorphismProperty.of_isPullback hb inferInstance
    have : Surjective (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k))) :=
      ⟨fun x ↦ ⟨default, Subsingleton.elim _ _⟩⟩
    have : Nonempty (D.geometricCurve U) := (pullback.fst (U ↘ Spec (.of D.k₀))
      (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))).surjective.nonempty
    have : IrreducibleSpace (D.geometricCurve X) := IsRegular.irreducibleSpace _
    have hd : Dense (Set.range kb) :=
      kb.isOpenEmbedding.isOpenMap.denseRange_of_isPreirreducibleSpace kb
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro A N _ hN
      exact WeilSheaf.upperStar_map_bijective_of_isLisse k k.denseRange A hN
    · intro N hN
      exact hN.upperStar_of_isDominant k
    · intro A N _ hN
      exact hN.adicUpperStar_map_bijective (fun _ ↦ inferInstance) kb hd A
    · intro N hN
      exact hN.adicUpperStar kb hd
  · intro D C U _ _ hC i _ _ hU Λ _ _ F _
    obtain ⟨hg, hs, hn, hi⟩ := curve_geometry D C hC
    let := hg
    let := hs
    let := hn
    let := hi
    let := hU
    have : Smooth (C ↘ Spec (.of D.k₀)) := hC.2.2.1
    have : LocallyOfFiniteType (C ↘ Spec (.of D.k₀)) := hC.2.2.2.1
    have := IsRegular.of_smooth (C ↘ Spec (.of D.k₀))
    have hnormal := Scheme.isDomain_and_isIntegrallyClosed_stalk_of_etale_of_isDomain i
      (fun x ↦ ⟨inferInstance, IsRegular.isIntegrallyClosed_stalk x⟩)
    exact (Scheme.isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf _).mpr
      (Etale.isConstructibleSheaf_lowerStar_of_isFiniteLocallyConstantSheaf
        (C ↘ Spec (.of D.k₀)) i (fun x ↦ (hnormal x).2) F)

end AlgebraicGeometry.Scheme.FiniteEtale
