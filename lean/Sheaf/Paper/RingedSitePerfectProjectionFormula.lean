/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NI
-/
module

public import Sheaf.CategoryTheory.RingedToposMorphism
public import Sheaf.Paper.ProjectionMateExact
public import Sheaf.Paper.StrictPerfectCoefficientPackageOfUniverses
public import Sheaf.Paper.RingedExchangeTensorCoherence
import Sheaf.Paper.ProjectionMateSlicePresentation
import Sheaf.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses
import WeilConjectures.Mathlib.CategoryTheory.Triangulated.Generators
import Sheaf.CategoryTheory.DerivedCategory.BoundedComplexTriangulatedDevissage
import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology
import Mathlib.CategoryTheory.Sites.LocalProperties

/-!
# Perfect projection formula on small ringed sites

Source: Stacks Project, Cohomology on Sites, Tag 0944, lemma-projection-formula and
its preceding projection morphism (blueprint: lem-sbc-ringed-site-perfect-projection-formula).
-/

@[expose] public section

universe u w

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits

namespace SheafOfModules

private theorem map_to_kInjective
    {A : Type*} [Category A] [Abelian A] [HasDerivedCategory A]
    (K I : CochainComplex A ℤ) [I.IsKInjective]
    (f : DerivedCategory.Q.obj K ⟶ DerivedCategory.Q.obj I) :
    ∃ g : K ⟶ I, DerivedCategory.Q.map g = f := by
  obtain ⟨g, hg⟩ := (CochainComplex.IsKInjective.Qh_map_bijective
    ((HomotopyCategory.quotient A (.up ℤ)).obj K) I).surjective
    ((DerivedCategory.quotientCompQhIso A).hom.app K ≫ f ≫
      (DerivedCategory.quotientCompQhIso A).inv.app I)
  obtain ⟨g, rfl⟩ := (HomotopyCategory.quotient A (.up ℤ)).map_surjective g
  refine ⟨g, ?_⟩
  apply (cancel_epi ((DerivedCategory.quotientCompQhIso A).hom.app K)).mp
  rw [← DerivedCategory.quotientCompQhIso_hom_naturality, hg]
  simp only [Category.assoc, Iso.inv_hom_id_app, Category.comp_id]

private theorem quasiIso_local
    (Y : RingedTensorCorner.{u, w}) {ι : Type*} (V : ι → Y.site)
    (hV : Y.topology.CoversTop V) {K L : CochainComplex Y.mateModules ℤ} (f : K ⟶ L)
    (hf : ∀ i, QuasiIso (((localizedSystemRestriction.{u, u, u} Y.ring
      (V i)).mapHomologicalComplex (.up ℤ)).map f)) : QuasiIso f := by
  rw [quasiIso_iff]
  intro n
  rw [quasiIsoAt_iff, ShortComplex.quasiIso_iff]
  let R := (sheafCompose Y.topology (forget₂ CommRingCat.{u} RingCat.{u})).obj Y.ring
  let H := HomologicalComplex.shortComplexFunctor Y.mateModules (.up ℤ) n
  have : IsIso ((SheafOfModules.toSheaf R).map (ShortComplex.homologyMap (H.map f))) := by
    apply Sheaf.isIso_of_coversTop hV
    intro i
    let G := localizedSystemRestriction.{u, u, u} Y.ring (V i)
    have : QuasiIso ((G.mapHomologicalComplex (.up ℤ)).map f) := hf i
    have hsc : ShortComplex.QuasiIso (G.mapShortComplex.map (H.map f)) :=
      (quasiIsoAt_iff ((G.mapHomologicalComplex (.up ℤ)).map f) n).mp inferInstance
    have hn := ShortComplex.mapHomologyIso_hom_naturality (H.map f) G
    have : IsIso (((H.obj K).mapHomologyIso G).hom ≫
        G.map (ShortComplex.homologyMap (H.map f))) := by
      rw [← hn]
      exact IsIso.comp_isIso' hsc.isIso' ((H.obj L).mapHomologyIso G).isIso_hom
    have : IsIso (G.map (ShortComplex.homologyMap (H.map f))) :=
      IsIso.of_isIso_comp_left ((H.obj K).mapHomologyIso G).hom _
    change IsIso ((SheafOfModules.toSheaf (R.over (V i))).map
      (G.map (ShortComplex.homologyMap (H.map f))))
    infer_instance
  exact isIso_of_reflects_iso _ (SheafOfModules.toSheaf R)

private theorem derived_iso_local
    (Y : RingedTensorCorner.{u, w})
    [∀ U : Y.site, HasDerivedCategory.{u + 1} (projectionSliceModules Y U)]
    {ι : Type*} (V : ι → Y.site) (hV : Y.topology.CoversTop V)
    {P Q : Y.mateDerived} (f : P ⟶ Q)
    (hf : ∀ i, IsIso ((projectionSliceRestriction Y (V i)).map f)) : IsIso f := by
  classical
  obtain ⟨K, ⟨p⟩⟩ := Functor.EssSurj.mem_essImage (DerivedCategory.Q (C := Y.mateModules)) P
  obtain ⟨L, ⟨q⟩⟩ := Functor.EssSurj.mem_essImage (DerivedCategory.Q (C := Y.mateModules)) Q
  obtain ⟨I₀, η₀, hI₀⟩ :=
    (grothendieckAbelian_and_functorial_kInjective_resolutionsOfUniverses.{u, u, u}
      Y.topology Y.ring).2.2
  have : QuasiIso (η₀.app L) := (hI₀ L).1
  have : (I₀.obj L).IsKInjective := (hI₀ L).2.1
  let q' := q.symm ≪≫ asIso (DerivedCategory.Q.map (η₀.app L))
  obtain ⟨g, hg⟩ := map_to_kInjective K (I₀.obj L) (p.hom ≫ f ≫ q'.hom)
  have hlocal (i : ι) : QuasiIso
      (((localizedSystemRestriction.{u, u, u} Y.ring (V i)).mapHomologicalComplex
        (.up ℤ)).map g) := by
    let R := projectionSliceRestriction Y (V i)
    let e := (localizedSystemRestriction.{u, u, u} Y.ring (V i)).mapDerivedCategoryFactors
    have : IsIso (R.map (DerivedCategory.Q.map g)) := by
      rw [hg, Functor.map_comp, Functor.map_comp]
      have := hf i
      infer_instance
    have : IsIso (DerivedCategory.Q.map
        (((localizedSystemRestriction.{u, u, u} Y.ring (V i)).mapHomologicalComplex
          (.up ℤ)).map g)) := by
      have hi : IsIso (e.hom.app K ≫ DerivedCategory.Q.map
          (((localizedSystemRestriction.{u, u, u} Y.ring (V i)).mapHomologicalComplex
            (.up ℤ)).map g)) := by
        change IsIso (e.hom.app K ≫
          ((localizedSystemRestriction.{u, u, u} Y.ring (V i)).mapHomologicalComplex
            (.up ℤ) ⋙ DerivedCategory.Q).map g)
        rw [← e.hom.naturality g]
        change IsIso (R.map (DerivedCategory.Q.map g) ≫ e.hom.app (I₀.obj L))
        infer_instance
      exact IsIso.of_isIso_comp_left (e.hom.app K) _
    exact (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).mp inferInstance
  have : QuasiIso g := quasiIso_local Y V hV g hlocal
  have : IsIso (p.hom ≫ f ≫ q'.hom) := hg ▸ inferInstanceAs (IsIso (DerivedCategory.Q.map g))
  have : IsIso (f ≫ q'.hom) := IsIso.of_isIso_comp_left p.hom _
  exact IsIso.of_isIso_comp_right _ q'.hom

private theorem projection_unit_iso
    {Y X : RingedTensorCorner.{u, w}} (e : RingedTensorEdge Y X)
    (a : RingedTensorModel Y) (b : RingedTensorModel X) (E : X.mateDerived) :
    IsIso (e.projection a b E Y.mateUnit) := by
  obtain ⟨sY, sX, sL, sR, _, _, _, _, _, _, _, _, _, _, unitL, unitY,
    unitX, _, _, _, alpha, halpha, _, _, _, hunit⟩ := ringedProjectionMateExact e a b
  let c := e.right.map (X.tensor.map (Prod.mkHom (𝟙 E) unitL.hom) ≫ (unitX E).hom)
  have hc : IsIso c := by
    dsimp [c]
    have : IsIso (X.tensor.map (Prod.mkHom (𝟙 E) unitL.hom)) :=
      (X.tensor.mapIso ((Iso.refl E).prod unitL)).isIso_hom
    infer_instance
  have h : IsIso ((alpha E).app Y.mateUnit ≫ c) := by
    change IsIso ((alpha E).app Y.mateUnit ≫ e.right.map _)
    rw [hunit E]
    infer_instance
  have h : IsIso ((alpha E).app Y.mateUnit) := IsIso.of_isIso_comp_right _ c
  rw [halpha] at h
  simpa [derivedProjectionFormulaMate, Adjunction.rightAdjointProjectionMap,
    RingedTensorEdge.projection] using h

private noncomputable def restriction_unit_iso
    (Y : RingedTensorCorner.{u, w}) (U : Y.site)
    [HasDerivedCategory.{u + 1} (projectionSliceModules Y U)] :
    (projectionSliceRestriction Y U).obj Y.mateUnit ≅
      (DerivedCategory.singleFunctor (projectionSliceModules Y U) 0).obj
        (SheafOfModules.unit _) := by
  let G := localizedSystemRestriction.{u, u, u} Y.ring U
  let r : G.obj (SheafOfModules.unit _) ≅ SheafOfModules.unit _ :=
    (SheafOfModules.fullyFaithfulForget _).preimageIso
      (PresheafOfModules.isoMk (fun _ ↦ Iso.refl _) (by intro A B f; ext; rfl))
  exact (G.mapDerivedCategorySingleFunctor 0).app (SheafOfModules.unit _) ≪≫
    (DerivedCategory.singleFunctor (projectionSliceModules Y U) 0).mapIso r

private theorem strictPerfect_iso
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (R : Sheaf J CommRingCat.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u}
      ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R))]
    (F G : DerivedCategory (SheafOfModules.{u}
      ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R)) ⥤
      DerivedCategory (SheafOfModules.{u}
        ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R)))
    [F.CommShift ℤ] [G.CommShift ℤ] [F.IsTriangulated] [G.IsTriangulated]
    (τ : F ⟶ G) [NatTrans.CommShift τ ℤ]
    (hunit : IsIso (τ.app ((DerivedCategory.singleFunctor _ 0).obj
      (SheafOfModules.unit _))))
    (K : CochainComplex (SheafOfModules.{u}
      ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R)) ℤ) (a b : ℤ)
    (hb : ∀ n : ℤ, n < a ∨ b < n → IsZero (K.X n))
    (pkg : StrictPerfectCoefficientPackageOnSite _ K) :
    IsIso (τ.app (DerivedCategory.Q.obj K)) := by
  let S := τ.isoLocus
  apply CategoryTheory.bounded_complex_mem_triangulated S K a b hb
  intro n _ _
  let H := DerivedCategory.singleFunctor (SheafOfModules.{u}
    ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R)) 0
  have hbase : S (H.obj (SheafOfModules.unit _)) := by
    exact hunit
  have hfree : S (H.obj (∏ᶜ fun _ : Fin (pkg.N n) ↦ SheafOfModules.unit _)) := by
    exact S.prop_of_isLimit
      (isLimitOfPreserves H (limit.isLimit (Discrete.functor
        (fun _ : Fin (pkg.N n) ↦ SheafOfModules.unit
          ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R))))) (fun _ ↦ hbase)
  exact S.prop_of_retract
    ((show Retract (K.X n) (∏ᶜ fun _ : Fin (pkg.N n) ↦ SheafOfModules.unit _) from
      ⟨pkg.i n, pkg.p n, pkg.splitting n⟩).map H) hfree

/-- The canonical counit projection mate is invertible for every locally perfect coefficient.
The corners and edge are the recorded small-site presentation of the ringed topoi, their
ordinary unbounded derived module categories, and derived adjunction. The tensor models
identify their tensor bifunctors with direct-sum total tensor on flat K-flat representatives.
Perfectness uses covering sieves and bounded degreewise finite-free retracts, with bounds
and ranks allowed to vary over the covering objects. The source object is unbounded.

Source: Stacks Project, Cohomology on Sites, Tag 0944, lemma-projection-formula;
the projection morphism immediately preceding it
(blueprint: lem-sbc-ringed-site-perfect-projection-formula).

Proof:
1. The unit equation in `ringedProjectionMateExact` makes the mate at the coefficient
   ring invertible, by cancellation of its tensor-unit identifications.
2. `projectionMateSlicePresentation` identifies restriction of the actual mate with a
   shift-compatible natural transformation between exact functors on the ordinary slice.
   Exact restriction preserves the degree-zero coefficient ring, so the local mate is
   invertible on that ring.
3. The isomorphism locus of this natural transformation is triangulated and stable under
   retracts. It contains finite products of the ring, including the empty product, and
   hence every term of a strictly perfect representative. The proved bounded-complex
   triangulated devissage puts the whole representative in this locus.
4. Apply this on each arrow of every covering sieve witnessing perfectness, using each
   representative's own bounds and ranks. Their domains cover every site object.
   To detect a derived isomorphism, replace its target by a K-injective complex and lift
   the arrow to a chain map. Exact restriction commutes with short-complex homology;
   the local homology isomorphisms are detected by the covering family, so the chain
   map is a quasi-isomorphism. The original derived mate is therefore invertible. -/
theorem ringedSitePerfectProjectionFormula
    {Y X : RingedTensorCorner.{u, w}} (e : RingedTensorEdge Y X)
    (a : RingedTensorModel Y) (b : RingedTensorModel X)
    (E : X.mateDerived) (P : Y.mateDerived)
    (hP : IsPerfectOnRingedSiteOfUniverses.{u, u, u, w} Y.ring P) :
    IsIso (e.projection a b E P) := by
  classical
  obtain ⟨sliceDerived⟩ : Nonempty
      (∀ U : Y.site, HasDerivedCategory.{u + 1} (projectionSliceModules Y U)) :=
    ⟨fun _ ↦ HasDerivedCategory.standard _⟩
  let : ∀ U : Y.site, HasDerivedCategory.{u + 1} (projectionSliceModules Y U) :=
    sliceDerived
  obtain ⟨K, hK, ⟨p⟩⟩ := hP
  let S (V : Y.site) := (hK V).choose
  have hS (V : Y.site) := (hK V).choose_spec
  let I := Σ V : Y.site, Σ U : Y.site, {f : U ⟶ V // S V f}
  let V (i : I) : Y.site := i.2.1
  have hV : Y.topology.CoversTop V := by
    intro W
    apply Y.topology.superset_covering _ (hS W).1
    intro U f hf
    exact ⟨⟨W, U, f, hf⟩, ⟨𝟙 U⟩⟩
  apply derived_iso_local Y V hV
  intro i
  obtain ⟨T, ht, ⟨pkg⟩, q, hq⟩ := (hS i.1).2 i.2.1 i.2.2.1 i.2.2.2
  obtain ⟨lo, hi, hb⟩ := ht
  have := hq
  let R := projectionSliceRestriction Y (V i)
  let model : R.obj P ≅ DerivedCategory.Q.obj T :=
    R.mapIso p ≪≫
      (localizedSystemRestriction.{u, u, u} Y.ring (V i)).mapDerivedCategoryFactors.app K ≪≫
        (asIso (DerivedCategory.Q.map q)).symm
  obtain ⟨d⟩ := projectionMateSlicePresentation e a b E (V i)
  let := d.sourceShift
  let := d.targetShift
  have := d.sourceExact
  have := d.targetExact
  have := d.shiftCompatible
  have := projection_unit_iso e a b E
  have : IsIso (d.mate.app (R.obj Y.mateUnit)) := by
    have : IsIso (d.sourceComparison.hom.app Y.mateUnit ≫
        d.mate.app (R.obj Y.mateUnit)) := by
      rw [← d.equation Y.mateUnit]
      infer_instance
    exact IsIso.of_isIso_comp_left (d.sourceComparison.hom.app Y.mateUnit) _
  have hu : IsIso (d.mate.app ((DerivedCategory.singleFunctor
      (projectionSliceModules Y (V i)) 0).obj (SheafOfModules.unit _))) :=
    (NatTrans.isIso_app_iff_of_iso d.mate (restriction_unit_iso Y (V i))).mp inferInstance
  let : HasDerivedCategory.{u + 1}
      (SheafOfModules.{u} ((sheafCompose (Y.topology.over (V i))
        (forget₂ CommRingCat.{u} RingCat.{u})).obj (Y.ring.over (V i)))) :=
    sliceDerived (V i)
  have htau := strictPerfect_iso.{u, u + 1} (Y.ring.over (V i)) d.source d.target d.mate
    hu T lo hi hb pkg
  have : IsIso (d.mate.app (R.obj P)) :=
    (NatTrans.isIso_app_iff_of_iso d.mate model).mpr htau
  have : IsIso (R.map (e.projection a b E P) ≫ d.targetComparison.hom.app P) := by
    rw [d.equation P]
    infer_instance
  exact IsIso.of_isIso_comp_right _ (d.targetComparison.hom.app P)

end SheafOfModules
