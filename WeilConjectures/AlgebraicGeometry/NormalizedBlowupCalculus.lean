/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.NormalizedBlowup
public import WeilConjectures.AlgebraicGeometry.IsRegularScheme
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Invertible
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import WeilConjectures.AlgebraicGeometry.NormalizedBlowupFinality
import Mathlib.Algebra.Field.ULift
import WeilConjectures.AlgebraicGeometry.Regular
import WeilConjectures.Blowup.InvertibleCenter
import WeilConjectures.Mathlib.AlgebraicGeometry.Geometrically.Reduced
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
import WeilConjectures.Mathlib.AlgebraicGeometry.Normalization
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.RingTheory.LocalProperties.Reduced
import WeilConjectures.Blowup.Proper
import WeilConjectures.Blowup.Complement
import WeilConjectures.Blowup.Density
import WeilConjectures.Blowup.FlatBaseChange
import WeilConjectures.Blowup.Affine.ChartAlgebra
import WeilConjectures.AlgebraicGeometry.ReducedAlgebraicNormalizationFieldChange
import WeilConjectures.AlgebraicGeometry.ComponentwiseNormalizationSmoothPullback
import WeilConjectures.AlgebraicGeometry.IntegralNormalGenericRecognition
import WeilConjectures.Mathlib.Topology.Sober

/-!
# Normalized blowups and smooth comparison

Source: Illusie--Laszlo--Orgogozo, Travaux de Gabber, Expose VIII, sections 2.2.1--2.2.4
and 2.2.7--2.2.9; Stacks Project, Tags 035S and 035Q
(blueprint: lem-trf-normalized-blowup-calculus).

The comparison with a fibre product is expressed by its pullback square. Thus the map to
that fibre product is the canonical comparison, with both projections prescribed.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.IdealSheafData

private theorem normal_self_normalization (X : Scheme.{u}) [IsLocallyNoetherian X]
    (hn : ∀ x : X, IsDomain (X.presheaf.stalk x) ∧
      IsIntegrallyClosed (X.presheaf.stalk x)) : IsIso X.fromReducedNormalization := by
  obtain ⟨e, he, _⟩ := Scheme.existsUnique_iso_reducedNormalization_of_integral_normal_generic
    (𝟙 X) hn (by exact Set.bijOn_id _) (by intro x hx; infer_instance)
  have : IsIso (e.hom ≫ X.fromReducedNormalization) := he.symm ▸ inferInstance
  exact IsIso.of_isIso_comp_left e.hom _

private theorem generic_mapsTo_of_generalizing {X Y : Scheme.{u}} (f : X ⟶ Y)
    (hf : GeneralizingMap f) : Set.MapsTo f (genericPoints X) (genericPoints Y) := by
  intro x hx
  rw [mem_genericPoints_iff_forall_specializes] at hx ⊢
  intro y hy
  obtain ⟨z, hz, hzf⟩ := hf hy
  simpa [hx z hz] using hzf.symm

private theorem generic_of_injective {X Y : Scheme.{u}} (f : X ⟶ Y)
    (hf : Function.Injective f) {x : X} (hx : f x ∈ genericPoints Y) :
    x ∈ genericPoints X := by
  rw [mem_genericPoints_iff_forall_specializes] at hx ⊢
  intro y hy
  exact hf (hx (f y) (hy.map f.continuous))

private theorem reduced_affine_blowup (A : Type u) [CommRing A] [_root_.IsReduced A]
    (I : Ideal A) : IsReduced (AffineBlowup I) := by
  let C := Scheme.Cover.mkOfCovers (P := @IsOpenImmersion) (X := AffineBlowup I) I
    (fun a ↦ Spec (.of (HomogeneousLocalization.Away (reesGrading I) (reesX I a a.2))))
    (fun a ↦ AffineBlowup.chart I (reesX I a a.2) (reesX_mem I a a.2))
    (fun x ↦ by
      have hx : x ∈ ⨆ a : I, Proj.basicOpen (reesGrading I) (reesX I a a.2) := by
        rw [AffineBlowup.iSup_basicOpen_reesX_eq_top]; trivial
      obtain ⟨a, ha⟩ := TopologicalSpace.Opens.mem_iSup.mp hx
      rw [← AffineBlowup.opensRange_chart I _ (reesX_mem I a a.2)] at ha
      obtain ⟨y, hy⟩ := ha
      exact ⟨a, y, hy⟩)
  have (a : I) : IsReduced (C.X a) := by
    let e := AffineBlowup.homogeneousAwayEquivChart I a.2
    have : _root_.IsReduced (Localization.Away (a : A)) := inferInstance
    have : _root_.IsReduced (AffineBlowup.chartRing I a) :=
      isReduced_of_injective (AffineBlowup.chartRing I a).val
        Subtype.val_injective
    have : _root_.IsReduced
        (HomogeneousLocalization.Away (reesGrading I) (reesX I a a.2)) :=
      isReduced_of_injective e.toRingHom e.injective
    exact (affine_isReduced_iff _).mpr inferInstance
  exact IsReduced.of_openCover _ C

private theorem reduced_blowup {X : Scheme.{u}} [IsReduced X] (I : X.IdealSheafData) :
    IsReduced I.blowup := by
  let C := Scheme.Cover.mkOfCovers (P := @IsOpenImmersion) (X := I.blowup) X.affineOpens
    (fun U ↦ AffineBlowup (I.ideal U)) I.blowupι (fun x ↦ by
      have hx : x ∈ ⨆ U : X.affineOpens, (I.blowupι U).opensRange := by
        rw [I.iSup_opensRange_blowupι_eq_top]; trivial
      obtain ⟨U, y, hy⟩ := TopologicalSpace.Opens.mem_iSup.mp hx
      exact ⟨U, y, hy⟩)
  have (U : X.affineOpens) : IsReduced (C.X U) :=
    reduced_affine_blowup Γ(X, U.1) (I.ideal U)
  exact IsReduced.of_openCover _ C

private theorem dense_open_contains_generic (X : Scheme.{u}) [IsNoetherian X]
    (V : X.Opens) (hV : Dense (V : Set X)) : genericPoints X ⊆ (V : Set X) := by
  intro x hx
  let Z : irreducibleComponents X := ⟨closure {x}, hx⟩
  obtain ⟨y, hyZ, hyV⟩ := AlgebraicGeometry.component_meets_dense_open X
    finite_irreducibleComponents_of_isNoetherian V hV Z
  exact ((isGenericPoint_closure : IsGenericPoint x (closure {x})).mem_open_set_iff
    V.isOpen).mpr ⟨y, hyZ, hyV⟩

private theorem generic_mapsTo_of_dense_iso_open {X Y : Scheme.{u}}
    [IsNoetherian X] (f : X ⟶ Y) (V : Y.Opens)
    (hd : Dense (f ⁻¹ᵁ V : Set X)) [IsIso (f ∣_ V)] :
    Set.MapsTo f (genericPoints X) (genericPoints Y) := by
  intro x hx
  have hmem := dense_open_contains_generic X (f ⁻¹ᵁ V) hd hx
  let y : (f ⁻¹ᵁ V).toScheme := ⟨x, hmem⟩
  have hy : y ∈ genericPoints (f ⁻¹ᵁ V).toScheme :=
    generic_of_injective _ (f ⁻¹ᵁ V).ι.isOpenEmbedding.injective hx
  have hz := generic_mapsTo_of_generalizing (f ∣_ V)
    (f ∣_ V).isOpenEmbedding.generalizingMap hy
  have hw := generic_mapsTo_of_generalizing V.ι V.ι.isOpenEmbedding.generalizingMap hz
  have he := congrArg (fun g : (f ⁻¹ᵁ V).toScheme ⟶ Y ↦ g y)
    (morphismRestrict_ι f V)
  exact he ▸ hw

private theorem dense_preimage_of_generic_mapsTo {X Y : Scheme.{u}}
    (f : X ⟶ Y) (hf : Set.MapsTo f (genericPoints X) (genericPoints Y))
    [IsNoetherian Y] (V : Y.Opens) (hd : Dense (V : Set Y)) :
    Dense (f ⁻¹ᵁ V : Set X) := by
  rw [dense_iff_inter_open]
  intro W hW hne
  obtain ⟨x, hx⟩ := hne
  let Z := irreducibleComponent x
  have hZ := irreducibleComponent_mem_irreducibleComponents x
  have hxZ : x ∈ Z := mem_irreducibleComponent
  let η := hZ.1.genericPoint
  have hη : IsGenericPoint η Z :=
    hZ.1.isGenericPoint_genericPoint (isClosed_of_mem_irreducibleComponents _ hZ)
  have hgen : η ∈ genericPoints X := by
    change closure {η} ∈ irreducibleComponents X
    rw [hη]
    exact hZ
  have hηW : η ∈ W := (hη.mem_open_set_iff hW).mpr ⟨x, hxZ, hx⟩
  exact ⟨η, hηW, dense_open_contains_generic Y V hd (hf hgen)⟩

private theorem top_invertible (X : Scheme.{u}) :
    (⊤ : X.IdealSheafData).IsInvertible := by
  intro x
  obtain ⟨U, hU, hxU, -⟩ := exists_isAffineOpen_mem_and_subset (U := ⊤) (x := x) trivial
  let U : X.affineOpens := ⟨U, hU⟩
  refine ⟨U, hxU, 1, ?_, ?_⟩
  · exact one_mem _
  · simp

private theorem normalization_generic {k : Type u} [Field k]
    (X : Scheme.{u}) (q : X ⟶ Spec (.of k)) [IsReduced X]
    [LocallyOfFiniteType q] [QuasiCompact q] :
    Set.MapsTo X.fromReducedNormalization
      (genericPoints X.reducedNormalization) (genericPoints X) := by
  have : IsFinite X.fromReducedNormalization := AlgebraicGeometry.finite_normalization X q
  have : LocallyOfFiniteType (X.fromReducedNormalization ≫ q) := inferInstance
  have : QuasiCompact (X.fromReducedNormalization ≫ q) := inferInstance
  have : IsLocallyNoetherian X.reducedNormalization :=
    LocallyOfFiniteType.isLocallyNoetherian (X.fromReducedNormalization ≫ q)
  have : CompactSpace X.reducedNormalization :=
    QuasiCompact.compactSpace_of_compactSpace (X.fromReducedNormalization ≫ q)
  have : IsNoetherian X.reducedNormalization := ⟨⟩
  obtain ⟨V, _, hd, hi⟩ := (reduced_algebraic_normalization_field_change X q).2.2.1
  exact generic_mapsTo_of_dense_iso_open X.fromReducedNormalization V
    (AlgebraicGeometry.dense_preimage_normalization X q V hd)

private theorem unit_normalization_iso (S : Scheme.{u}) [IsLocallyNoetherian S] :
    ∃ e : (⊤ : S.IdealSheafData).normalizedBlowup ≅ S.reducedNormalization,
      e.hom ≫ S.fromReducedNormalization = (⊤ : S.IdealSheafData).normalizedBlowupMap := by
  let I : S.IdealSheafData := ⊤
  have : IsIso I.blowupMap := I.isIso_blowupMap_of_isInvertible (top_invertible S)
  have : IsLocallyNoetherian I.blowup :=
    LocallyOfFiniteType.isLocallyNoetherian I.blowupMap
  obtain ⟨e, he, _⟩ := Scheme.reducedNormalization_smooth_pullback I.blowupMap
  let d := e ≪≫ asIso (pullback.snd I.blowupMap S.fromReducedNormalization)
  refine ⟨d, ?_⟩
  change e.hom ≫ pullback.snd _ _ ≫ S.fromReducedNormalization = _
  rw [← pullback.condition, ← Category.assoc, he]
  rfl

private theorem normalization_finality (S : Scheme.{u})
    (q : S ⟶ Spec (.of (ULift.{u} ℚ))) [IsReduced S]
    [LocallyOfFiniteType q] [QuasiCompact q]
    (Y : Scheme.{u}) (f : Y ⟶ S)
    (hn : ∀ y : Y, IsDomain (Y.presheaf.stalk y) ∧
      IsIntegrallyClosed (Y.presheaf.stalk y))
    (hg : Set.MapsTo f (genericPoints Y) (genericPoints S)) :
    ∃! n : Y ⟶ S.reducedNormalization, n ≫ S.fromReducedNormalization = f := by
  have : IsLocallyNoetherian S := LocallyOfFiniteType.isLocallyNoetherian q
  obtain ⟨e, he⟩ := unit_normalization_iso S
  have hfg (U : S.affineOpens) : ((⊤ : S.IdealSheafData).ideal U).FG := by
    simp only [ideal_top]; exact Ideal.fg_top _
  have hd : Dense ((⊤ : S.IdealSheafData).support.compl : Set S) := by
    simp
  have ht : ((⊤ : S.IdealSheafData).comap f).IsInvertible := by
    rw [comap_top]; exact top_invertible Y
  obtain ⟨l, hl, hu⟩ := (normalizedBlowup_finality S q ⊤ hfg hd).2.2.2 Y f hn hg ht
  refine ⟨l ≫ e.hom, by dsimp; rw [Category.assoc, he, hl], ?_⟩
  intro n hnf
  have hni : (n ≫ e.inv) ≫ (⊤ : S.IdealSheafData).normalizedBlowupMap = f := by
    rw [← he, Category.assoc, e.inv_hom_id_assoc, hnf]
  have h := congrArg (fun a ↦ a ≫ e.hom) (hu (n ≫ e.inv) hni)
  simpa only [Category.assoc, e.inv_hom_id, Category.comp_id] using h

private theorem smooth_normalization_square {X Y : Scheme.{u}}
    (f : X ⟶ Y) [IsLocallyNoetherian X] [IsLocallyNoetherian Y] [Smooth f] :
    ∃ n : X.reducedNormalization ⟶ Y.reducedNormalization,
      IsPullback n X.fromReducedNormalization Y.fromReducedNormalization f := by
  obtain ⟨e, he, _⟩ := Scheme.reducedNormalization_smooth_pullback f
  refine ⟨e.hom ≫ pullback.snd _ _, ?_⟩
  apply IsPullback.flip
  exact (IsPullback.of_hasPullback f Y.fromReducedNormalization).of_iso'
    e (Iso.refl _) (Iso.refl _) (Iso.refl _)
    (by simpa using he) (by simp) (by simp) (by simp)

private theorem smooth_blowup_square {S T : Scheme.{u}} (J : S.IdealSheafData)
    (h : T ⟶ S) [Flat h] :
    ∃ k : (J.comap h).blowup ⟶ J.blowup,
      IsPullback k (J.comap h).blowupMap J.blowupMap h := by
  let e := J.blowupFlatBaseChangeIso h
  refine ⟨e.hom ≫ pullback.fst _ _, ?_⟩
  exact (IsPullback.of_hasPullback J.blowupMap h).of_iso'
    e (Iso.refl _) (Iso.refl _) (Iso.refl _)
    (by simp) (by simp [e])
    (by simp) (by simp)

private theorem smooth_normalized_blowup_square {S T : Scheme.{u}}
    [IsLocallyNoetherian S] [IsLocallyNoetherian T]
    (J : S.IdealSheafData) (h : T ⟶ S) [Smooth h] :
    ∃ b : (J.comap h).normalizedBlowup ⟶ J.normalizedBlowup,
      IsPullback b (J.comap h).normalizedBlowupMap J.normalizedBlowupMap h := by
  obtain ⟨k, hk⟩ := smooth_blowup_square J h
  have : Smooth k := MorphismProperty.of_isPullback hk.flip inferInstance
  have : IsLocallyNoetherian J.blowup :=
    LocallyOfFiniteType.isLocallyNoetherian J.blowupMap
  have : IsLocallyNoetherian (J.comap h).blowup :=
    LocallyOfFiniteType.isLocallyNoetherian (J.comap h).blowupMap
  obtain ⟨b, hb⟩ := smooth_normalization_square k
  exact ⟨b, hb.paste_vert hk⟩

private theorem normal_of_open {X Y : Scheme.{u}} (f : Y ⟶ X) [IsOpenImmersion f]
    (hn : ∀ x : X, IsDomain (X.presheaf.stalk x) ∧
      IsIntegrallyClosed (X.presheaf.stalk x)) (y : Y) :
    IsDomain (Y.presheaf.stalk y) ∧ IsIntegrallyClosed (Y.presheaf.stalk y) := by
  let e := (asIso (f.stalkMap y)).commRingCatIsoToRingEquiv
  have := (hn (f y)).1
  have := (hn (f y)).2
  exact ⟨e.symm.toMulEquiv.isDomain, IsIntegrallyClosed.of_equiv e⟩

private theorem mapsTo_comp {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (hf : Set.MapsTo f (genericPoints X) (genericPoints Y))
    (hg : Set.MapsTo g (genericPoints Y) (genericPoints Z)) :
    Set.MapsTo (f ≫ g) (genericPoints X) (genericPoints Z) :=
  fun _ hx ↦ hg (hf hx)

private theorem generic_factor_of_dense_iso {X Y S : Scheme.{u}} [IsNoetherian S]
    (p : Y ⟶ S) (f : X ⟶ S) (a : X ⟶ Y) (ha : a ≫ p = f)
    (hf : Set.MapsTo f (genericPoints X) (genericPoints S))
    (V : S.Opens) (hd : Dense (V : Set S)) [IsIso (p ∣_ V)] :
    Set.MapsTo a (genericPoints X) (genericPoints Y) := by
  intro x hx
  have hmem : p (a x) ∈ V := by
    rw [← Scheme.Hom.comp_apply, ha]
    exact dense_open_contains_generic S V hd (hf hx)
  let y : (p ⁻¹ᵁ V).toScheme := ⟨a x, hmem⟩
  have hy : y ∈ genericPoints (p ⁻¹ᵁ V).toScheme := by
    apply generic_of_injective (p ∣_ V) (p ∣_ V).isOpenEmbedding.injective
    apply generic_of_injective V.ι V.ι.isOpenEmbedding.injective
    have he := congrArg (fun g : (p ⁻¹ᵁ V).toScheme ⟶ S ↦ g y)
      (morphismRestrict_ι p V)
    rw [Scheme.Hom.comp_apply, Scheme.Hom.comp_apply] at he
    rw [he]
    change p (a x) ∈ genericPoints S
    rw [← Scheme.Hom.comp_apply, ha]
    exact hf hx
  exact generic_mapsTo_of_generalizing (p ⁻¹ᵁ V).ι
    (p ⁻¹ᵁ V).ι.isOpenEmbedding.generalizingMap hy

private theorem normalization_comparison (S : Scheme.{u})
    (q : S ⟶ Spec (.of (ULift.{u} ℚ))) [IsReduced S]
    [LocallyOfFiniteType q] [QuasiCompact q] (J : S.IdealSheafData)
    (hJ : ∀ U : S.affineOpens, (J.ideal U).FG)
    (hd : Dense (J.support.compl : Set S))
    (n : J.normalizedBlowup ⟶ S.reducedNormalization)
    (hn : n ≫ S.fromReducedNormalization = J.normalizedBlowupMap) :
    ∃! e : J.normalizedBlowup ≅ (J.comap S.fromReducedNormalization).normalizedBlowup,
      e.hom ≫ (J.comap S.fromReducedNormalization).normalizedBlowupMap = n := by
  have : IsLocallyNoetherian S := LocallyOfFiniteType.isLocallyNoetherian q
  have : CompactSpace S := QuasiCompact.compactSpace_of_compactSpace q
  have : IsNoetherian S := ⟨⟩
  have : IsFinite S.fromReducedNormalization := AlgebraicGeometry.finite_normalization S q
  have : LocallyOfFiniteType (S.fromReducedNormalization ≫ q) := inferInstance
  have : QuasiCompact (S.fromReducedNormalization ≫ q) := inferInstance
  have : IsLocallyNoetherian S.reducedNormalization :=
    LocallyOfFiniteType.isLocallyNoetherian (S.fromReducedNormalization ≫ q)
  have hnorm := AlgebraicGeometry.normal_normalization S
  have (x : S.reducedNormalization) : IsDomain (S.reducedNormalization.presheaf.stalk x) :=
    (hnorm x).1
  have : IsReduced S.reducedNormalization := isReduced_of_isReduced_stalk _
  let K := J.comap S.fromReducedNormalization
  have hK (U : S.reducedNormalization.affineOpens) : (K.ideal U).FG := by
    have := IsLocallyNoetherian.component_noetherian U
    exact IsNoetherian.noetherian _
  have hg := normalization_generic S q
  have hKd : Dense (K.support.compl : Set S.reducedNormalization) := by
    simpa [K, support_comap] using
      dense_preimage_of_generic_mapsTo S.fromReducedNormalization hg J.support.compl hd
  obtain ⟨hA, hgA, hiA, hfinalA⟩ := normalizedBlowup_finality S q J hJ hd
  obtain ⟨hB, hgB, hiB, hfinalB⟩ := normalizedBlowup_finality S.reducedNormalization
    (S.fromReducedNormalization ≫ q) K hK hKd
  obtain ⟨V, _, hV, hVi⟩ := (reduced_algebraic_normalization_field_change S q).2.2.1
  have hgn := generic_factor_of_dense_iso S.fromReducedNormalization
    J.normalizedBlowupMap n hn hgA V hV
  have hin : (K.comap n).IsInvertible := by
    dsimp only [K]
    rw [← comap_comp, hn]
    exact hiA
  obtain ⟨a, ha, hau⟩ := hfinalB _ n hA hgn hin
  have hgb := mapsTo_comp K.normalizedBlowupMap S.fromReducedNormalization hgB hg
  have hib : (J.comap (K.normalizedBlowupMap ≫ S.fromReducedNormalization)).IsInvertible := by
    simpa only [← comap_comp, K] using hiB
  obtain ⟨b, hb, hbu⟩ := hfinalA _
    (K.normalizedBlowupMap ≫ S.fromReducedNormalization) hB hgb hib
  have hbn : b ≫ n = K.normalizedBlowupMap := by
    obtain ⟨l, hl, hu⟩ := normalization_finality S q _
      (K.normalizedBlowupMap ≫ S.fromReducedNormalization) hB hgb
    apply (hu _ ?_).trans (hu _ rfl).symm
    rw [Category.assoc, hn, hb]
  have hab : a ≫ b = 𝟙 _ := by
    obtain ⟨l, hl, hu⟩ := hfinalA _ J.normalizedBlowupMap hA hgA hiA
    apply (hu _ ?_).trans (hu _ (by simp)).symm
    rw [Category.assoc, hb, ← Category.assoc, ha, hn]
  have hba : b ≫ a = 𝟙 _ := by
    obtain ⟨l, hl, hu⟩ := hfinalB _ K.normalizedBlowupMap hB hgB hiB
    apply (hu _ ?_).trans (hu _ (by simp)).symm
    rw [Category.assoc, ha, hbn]
  refine ⟨⟨a, b, hab, hba⟩, ha, ?_⟩
  intro e he
  exact Iso.ext (hau e.hom he)

private theorem blowup_birational (S : Scheme.{u})
    (q : S ⟶ Spec (.of (ULift.{u} ℚ))) [IsReduced S]
    [LocallyOfFiniteType q] [QuasiCompact q] (J : S.IdealSheafData)
    (hd : Dense (J.support.compl : Set S)) :
    ∃ V : S.Opens, Dense (V : Set S) ∧
      Dense (J.normalizedBlowupMap ⁻¹ᵁ V : Set J.normalizedBlowup) ∧
      IsIso (J.normalizedBlowupMap ∣_ V) := by
  have : IsLocallyNoetherian S := LocallyOfFiniteType.isLocallyNoetherian q
  have : CompactSpace S := QuasiCompact.compactSpace_of_compactSpace q
  have : IsNoetherian S := ⟨⟩
  have : IsProper J.blowupMap := inferInstance
  have : LocallyOfFiniteType (J.blowupMap ≫ q) := inferInstance
  have : QuasiCompact (J.blowupMap ≫ q) := inferInstance
  have : IsLocallyNoetherian J.blowup :=
    LocallyOfFiniteType.isLocallyNoetherian J.blowupMap
  have : IsReduced J.blowup := reduced_blowup J
  obtain ⟨N, hN, hNd, _⟩ := (reduced_algebraic_normalization_field_change S q).2.2.1
  let V : S.Opens := J.support.compl ⊓ N
  have hV : Dense (V : Set S) := hd.inter_of_isOpen_left hNd J.support.compl.isOpen
  have hi : IsIso (J.blowupMap ∣_ V) :=
    isIso_morphismRestrict_of_le J.blowupMap inf_le_left
      J.isIso_blowupMap_restrict_support_compl
  have hNV : ∀ y : V.toScheme, IsDomain (V.toScheme.presheaf.stalk y) ∧
      IsIntegrallyClosed (V.toScheme.presheaf.stalk y) := by
    intro y
    let e := (asIso (V.ι.stalkMap y)).commRingCatIsoToRingEquiv
    have hy := (hN (V.ι y)).mp y.2.2
    have := hy.1
    have := hy.2
    exact ⟨e.symm.toMulEquiv.isDomain, IsIntegrallyClosed.of_equiv e⟩
  let W := J.blowupMap ⁻¹ᵁ V
  have hNW := normal_of_open (J.blowupMap ∣_ V) hNV
  have : IsIso W.toScheme.fromReducedNormalization := normal_self_normalization W.toScheme hNW
  obtain ⟨e, he, _⟩ :=
    (reduced_algebraic_normalization_field_change J.blowup (J.blowupMap ≫ q)).2.2.2.1 W
  have : IsIso (J.blowup.fromReducedNormalization ∣_ W) := by
    have : IsIso (e.hom ≫ (J.blowup.fromReducedNormalization ∣_ W)) :=
      he.symm ▸ inferInstance
    exact IsIso.of_isIso_comp_left e.hom _
  have hp : IsIso (J.normalizedBlowupMap ∣_ V) := by
    change IsIso ((J.blowup.fromReducedNormalization ≫ J.blowupMap) ∣_ V)
    rw [morphismRestrict_comp]
    infer_instance
  have : CompactSpace J.blowup :=
    QuasiCompact.compactSpace_of_compactSpace (J.blowupMap ≫ q)
  have : IsNoetherian J.blowup := ⟨⟩
  have hdB : Dense (J.blowupMap ⁻¹ᵁ J.support.compl : Set J.blowup) := by
    have := J.isSchemeTheoreticallyDominant_blowupMap_preimage_compl_support
    have h := (J.blowupMap ⁻¹ᵁ J.support.compl).ι.denseRange
    simpa only [DenseRange, Scheme.Opens.range_ι] using h
  have : IsIso (J.blowupMap ∣_ J.support.compl) :=
    J.isIso_blowupMap_restrict_support_compl
  have hgB := generic_mapsTo_of_dense_iso_open J.blowupMap J.support.compl hdB
  have hW : Dense (W : Set J.blowup) :=
    dense_preimage_of_generic_mapsTo J.blowupMap hgB V hV
  exact ⟨V, hV, AlgebraicGeometry.dense_preimage_normalization J.blowup (J.blowupMap ≫ q) W hW, hp⟩

/-- Normalized blowup calculus for a reduced finite-type rational scheme. Coherence of the
quasi-coherent ideal is finite generation on affine opens, since the base is Noetherian.
Normality is the explicit condition that all stalks are integrally closed domains.
Birationality on components is expressed by a dense open isomorphism with dense inverse
image. Maximally dominating means `Set.MapsTo` on the sets `genericPoints`.

The two smooth comparison squares are pullbacks, equivalently their canonical comparison
maps to the displayed fibre products are isomorphisms. The last two clauses spell out
identity and composition compatibility; the equalities of extended centres are passed
explicitly, so that the maps being compared have literally the same source scheme.

Source: ILO, Expose VIII, 2.2.1--2.2.4, 2.2.7--2.2.9; Stacks Tags 035S and 035Q
(blueprint: lem-trf-normalized-blowup-calculus).

Proof plan:
1. Work on the finitely many reduced integral components. Normalize the ordinary blowup
on each component. Normalization is finite over a finite-type rational scheme (035S),
normal and surjective (035Q), and an isomorphism on a dense open. The centre avoids all
generic points, so blowing up retains them. This proves normality, reducedness, finite
type, surjectivity and componentwise birationality.
2. Principalization makes the extended ideal invertible. For a maximally dominating map
from a normal scheme, the ordinary blowup universal property gives a unique lift, and
normalization lifting factors it uniquely through the component normalizations. The
local lifts agree by uniqueness and glue. This proves finality and rigidity over S.
3. Lift the normalized blowup to S's normalization. Finality gives the map from the
normalized blowup over that normalization in the other direction. The two universal
properties show that the composites are identities, giving the isomorphism over S^nu.
No claim that integral closure commutes with adjoining chart fractions is used.
4. A smooth map is flat, locally finitely presented and has geometrically regular,
hence reduced, fibres (the smooth criterion and smooth-geometrically-reduced nodes).
Its source is reduced. ILO 2.2.9 identifies its normalization with the pullback of S^nu:
the comparison is integral and generically an isomorphism, and its target is normal,
being regular over a normal scheme. Ordinary blowups commute with flat base change;
apply the same normalization comparison to them. Smoothness follows by base change.
5. Flatness and openness of a flat locally finitely presented map imply that the inverse
image of the dense complement of the centre is dense. The uniquely characterized
comparison maps preserve identities and composition; extend the centres by comap_id
and comap_comp to compare the literal source objects.
6. Blowing up an invertible ideal, in particular the unit ideal, is an isomorphism.
Normalizing gives B_O(S) = S^nu. Normal schemes are their own normalization. Regular
schemes are normal by rem-pc-regular-normal, so their normalization maps are isomorphisms.
The empty scheme is covered by the empty component coproduct throughout. -/
theorem normalizedBlowup_calculus (S : Scheme.{u})
    (q : S ⟶ Spec (.of (ULift.{u} ℚ))) [IsReduced S]
    [LocallyOfFiniteType q] [QuasiCompact q] (J : S.IdealSheafData)
    (hJ : ∀ U : S.affineOpens, (J.ideal U).FG)
    (hcentre : Dense (J.support.compl : Set S)) :
    (∀ x : J.normalizedBlowup,
      IsDomain (J.normalizedBlowup.presheaf.stalk x) ∧
      IsIntegrallyClosed (J.normalizedBlowup.presheaf.stalk x)) ∧
    IsReduced J.normalizedBlowup ∧
    LocallyOfFiniteType (J.normalizedBlowupMap ≫ q) ∧
    QuasiCompact (J.normalizedBlowupMap ≫ q) ∧
    Surjective J.normalizedBlowupMap ∧
    Set.MapsTo J.normalizedBlowupMap (genericPoints J.normalizedBlowup) (genericPoints S) ∧
    (∃ U : S.Opens, Dense (U : Set S) ∧
      Dense (J.normalizedBlowupMap ⁻¹ᵁ U : Set J.normalizedBlowup) ∧
      IsIso (J.normalizedBlowupMap ∣_ U)) ∧
    (J.comap J.normalizedBlowupMap).IsInvertible ∧
    (∀ (Y : Scheme.{u}) (f : Y ⟶ S),
      (∀ y : Y, IsDomain (Y.presheaf.stalk y) ∧
        IsIntegrallyClosed (Y.presheaf.stalk y)) →
      Set.MapsTo f (genericPoints Y) (genericPoints S) → (J.comap f).IsInvertible →
      ∃! l : Y ⟶ J.normalizedBlowup, l ≫ J.normalizedBlowupMap = f) ∧
    (∀ e : J.normalizedBlowup ≅ J.normalizedBlowup,
      e.hom ≫ J.normalizedBlowupMap = J.normalizedBlowupMap → e = Iso.refl _) ∧
    (∃! n : J.normalizedBlowup ⟶ S.reducedNormalization,
      n ≫ S.fromReducedNormalization = J.normalizedBlowupMap) ∧
    (∀ n : J.normalizedBlowup ⟶ S.reducedNormalization,
      n ≫ S.fromReducedNormalization = J.normalizedBlowupMap →
      ∃! e : J.normalizedBlowup ≅ (J.comap S.fromReducedNormalization).normalizedBlowup,
        e.hom ≫ (J.comap S.fromReducedNormalization).normalizedBlowupMap = n) ∧
    (∀ (T : Scheme.{u}) (h : T ⟶ S) [Smooth h]
      [LocallyOfFiniteType (h ≫ q)] [QuasiCompact (h ≫ q)],
      IsReduced T ∧ Dense ((J.comap h).support.compl : Set T) ∧
      (∃! n : T.reducedNormalization ⟶ S.reducedNormalization,
        n ≫ S.fromReducedNormalization = T.fromReducedNormalization ≫ h) ∧
      (∀ n : T.reducedNormalization ⟶ S.reducedNormalization,
        n ≫ S.fromReducedNormalization = T.fromReducedNormalization ≫ h →
        IsPullback n T.fromReducedNormalization S.fromReducedNormalization h) ∧
      (∃! b : (J.comap h).normalizedBlowup ⟶ J.normalizedBlowup,
        b ≫ J.normalizedBlowupMap = (J.comap h).normalizedBlowupMap ≫ h) ∧
      (∀ b : (J.comap h).normalizedBlowup ⟶ J.normalizedBlowup,
        b ≫ J.normalizedBlowupMap = (J.comap h).normalizedBlowupMap ≫ h →
        IsPullback b (J.comap h).normalizedBlowupMap J.normalizedBlowupMap h ∧ Smooth b)) ∧
    (IsRegularScheme S → IsIso S.fromReducedNormalization) ∧
    (∃! e : (⊤ : S.IdealSheafData).normalizedBlowup ≅ S.reducedNormalization,
      e.hom ≫ S.fromReducedNormalization = (⊤ : S.IdealSheafData).normalizedBlowupMap) ∧
    ((∀ x : S, IsDomain (S.presheaf.stalk x) ∧
      IsIntegrallyClosed (S.presheaf.stalk x)) →
      IsIso S.fromReducedNormalization ∧ IsIso (⊤ : S.IdealSheafData).normalizedBlowupMap) ∧
    ((∀ n : S.reducedNormalization ⟶ S.reducedNormalization,
      n ≫ S.fromReducedNormalization = S.fromReducedNormalization → n = 𝟙 _) ∧
      (∀ (K : S.IdealSheafData) (hK : J.comap (𝟙 S) = K)
        (b : K.normalizedBlowup ⟶ J.normalizedBlowup),
        b ≫ J.normalizedBlowupMap = K.normalizedBlowupMap →
        b = eqToHom (congrArg normalizedBlowup (hK.symm.trans J.comap_id)))) ∧
    (∀ (T U : Scheme.{u}) (h : T ⟶ S) (g : U ⟶ T) [Smooth h] [Smooth g]
      [LocallyOfFiniteType (h ≫ q)] [QuasiCompact (h ≫ q)]
      [LocallyOfFiniteType (g ≫ h ≫ q)] [QuasiCompact (g ≫ h ≫ q)],
      (∀ (n₁ : T.reducedNormalization ⟶ S.reducedNormalization)
        (n₂ : U.reducedNormalization ⟶ T.reducedNormalization)
        (n₃ : U.reducedNormalization ⟶ S.reducedNormalization),
        n₁ ≫ S.fromReducedNormalization = T.fromReducedNormalization ≫ h →
        n₂ ≫ T.fromReducedNormalization = U.fromReducedNormalization ≫ g →
        n₃ ≫ S.fromReducedNormalization = U.fromReducedNormalization ≫ g ≫ h →
        n₂ ≫ n₁ = n₃) ∧
      (∀ (K : U.IdealSheafData) (hK : (J.comap h).comap g = K)
        (b₁ : (J.comap h).normalizedBlowup ⟶ J.normalizedBlowup)
        (b₂ : K.normalizedBlowup ⟶ (J.comap h).normalizedBlowup)
        (b₃ : (J.comap (g ≫ h)).normalizedBlowup ⟶ J.normalizedBlowup),
        b₁ ≫ J.normalizedBlowupMap = (J.comap h).normalizedBlowupMap ≫ h →
        b₂ ≫ (J.comap h).normalizedBlowupMap = K.normalizedBlowupMap ≫ g →
        b₃ ≫ J.normalizedBlowupMap = (J.comap (g ≫ h)).normalizedBlowupMap ≫ g ≫ h →
        b₂ ≫ b₁ = eqToHom
          (congrArg normalizedBlowup (hK.symm.trans (J.comap_comp g h).symm)) ≫ b₃)) := by
  have : IsLocallyNoetherian S := LocallyOfFiniteType.isLocallyNoetherian q
  have : CompactSpace S := QuasiCompact.compactSpace_of_compactSpace q
  have : IsNoetherian S := ⟨⟩
  have : IsProper J.blowupMap := inferInstance
  have : LocallyOfFiniteType (J.blowupMap ≫ q) := inferInstance
  have : QuasiCompact (J.blowupMap ≫ q) := inferInstance
  have : IsFinite J.blowup.fromReducedNormalization :=
    AlgebraicGeometry.finite_normalization J.blowup (J.blowupMap ≫ q)
  have hft : LocallyOfFiniteType (J.normalizedBlowupMap ≫ q) := by
    unfold normalizedBlowupMap
    infer_instance
  have hqc : QuasiCompact (J.normalizedBlowupMap ≫ q) := by
    unfold normalizedBlowupMap
    infer_instance
  obtain ⟨hn, hg, hi, hfinal⟩ := normalizedBlowup_finality S q J hJ hcentre
  have (x : J.normalizedBlowup) : IsDomain (J.normalizedBlowup.presheaf.stalk x) := (hn x).1
  have hred : IsReduced J.normalizedBlowup := isReduced_of_isReduced_stalk _
  have : IsReduced J.normalizedBlowup := hred
  have hbir := blowup_birational S q J hcentre
  have hsurj : Surjective J.normalizedBlowupMap := by
    have : IsFinite J.blowup.fromReducedNormalization :=
      AlgebraicGeometry.finite_normalization J.blowup (J.blowupMap ≫ q)
    have : IsProper J.normalizedBlowupMap := by
      unfold normalizedBlowupMap
      infer_instance
    have : IsDominant J.normalizedBlowupMap := by
      obtain ⟨V, hV, hd, hiV⟩ := hbir
      have : IsIso (J.normalizedBlowupMap ∣_ V) := hiV
      constructor
      apply hV.mono
      intro y hy
      let z : V.toScheme := ⟨y, hy⟩
      obtain ⟨x, hx⟩ := (J.normalizedBlowupMap ∣_ V).surjective z
      refine ⟨x.1, ?_⟩
      have he := congrArg (fun f : (J.normalizedBlowupMap ⁻¹ᵁ V).toScheme ⟶ S ↦ f x)
        (morphismRestrict_ι J.normalizedBlowupMap V)
      change V.ι ((J.normalizedBlowupMap ∣_ V) x) =
        J.normalizedBlowupMap x.1 at he
      exact he.symm.trans (congrArg (fun z : V.toScheme ↦ V.ι z) hx)
    infer_instance
  have hself (a b : J.normalizedBlowup ⟶ J.normalizedBlowup)
      (ha : a ≫ J.normalizedBlowupMap = J.normalizedBlowupMap)
      (hb : b ≫ J.normalizedBlowupMap = J.normalizedBlowupMap) : a = b := by
    obtain ⟨l, hl, hu⟩ := hfinal _ J.normalizedBlowupMap hn hg hi
    exact (hu a ha).trans (hu b hb).symm
  have hng := normalization_generic S q
  have hnn := AlgebraicGeometry.normal_normalization S
  have hnormal_id (n : S.reducedNormalization ⟶ S.reducedNormalization)
      (he : n ≫ S.fromReducedNormalization = S.fromReducedNormalization) : n = 𝟙 _ := by
    obtain ⟨l, hl, hu⟩ := normalization_finality S q _ S.fromReducedNormalization hnn hng
    exact (hu n he).trans (hu (𝟙 _) (by simp)).symm
  have hsmooth (T : Scheme.{u}) (h : T ⟶ S) [Smooth h]
      [LocallyOfFiniteType (h ≫ q)] [QuasiCompact (h ≫ q)] :
      IsReduced T ∧ Dense ((J.comap h).support.compl : Set T) ∧
      (∃! n : T.reducedNormalization ⟶ S.reducedNormalization,
        n ≫ S.fromReducedNormalization = T.fromReducedNormalization ≫ h) ∧
      (∀ n : T.reducedNormalization ⟶ S.reducedNormalization,
        n ≫ S.fromReducedNormalization = T.fromReducedNormalization ≫ h →
        IsPullback n T.fromReducedNormalization S.fromReducedNormalization h) ∧
      (∃! b : (J.comap h).normalizedBlowup ⟶ J.normalizedBlowup,
        b ≫ J.normalizedBlowupMap = (J.comap h).normalizedBlowupMap ≫ h) ∧
      (∀ b : (J.comap h).normalizedBlowup ⟶ J.normalizedBlowup,
        b ≫ J.normalizedBlowupMap = (J.comap h).normalizedBlowupMap ≫ h →
        IsPullback b (J.comap h).normalizedBlowupMap J.normalizedBlowupMap h ∧ Smooth b) := by
    have : IsLocallyNoetherian T := LocallyOfFiniteType.isLocallyNoetherian h
    have hrt : IsReduced T :=
      GeometricallyReduced.isReduced_of_flat_of_isLocallyNoetherian h
    have : IsReduced T := hrt
    have hdt : Dense ((J.comap h).support.compl : Set T) := by
      simpa [support_comap] using hcentre.preimage h.isOpenMap
    have hgt := generic_mapsTo_of_generalizing h (Flat.generalizingMap h)
    have hnt := AlgebraicGeometry.normal_normalization T
    have hngt := mapsTo_comp T.fromReducedNormalization h (normalization_generic T (h ≫ q)) hgt
    have hnf := normalization_finality S q _ (T.fromReducedNormalization ≫ h) hnt hngt
    have hnuniq (n₁ n₂ : T.reducedNormalization ⟶ S.reducedNormalization)
        (he₁ : n₁ ≫ S.fromReducedNormalization = T.fromReducedNormalization ≫ h)
        (he₂ : n₂ ≫ S.fromReducedNormalization = T.fromReducedNormalization ≫ h) : n₁ = n₂ :=
      (hnf.unique he₁ he₂)
    have hntsquare : ∀ n : T.reducedNormalization ⟶ S.reducedNormalization,
        n ≫ S.fromReducedNormalization = T.fromReducedNormalization ≫ h →
        IsPullback n T.fromReducedNormalization S.fromReducedNormalization h := by
      intro n hne
      obtain ⟨n₀, hn₀⟩ := smooth_normalization_square h
      exact hnuniq n n₀ hne hn₀.w ▸ hn₀
    have hK (U : T.affineOpens) : ((J.comap h).ideal U).FG := by
      have := IsLocallyNoetherian.component_noetherian U
      exact IsNoetherian.noetherian _
    obtain ⟨hnK, hgK, hiK, _⟩ := normalizedBlowup_finality T (h ≫ q) (J.comap h) hK hdt
    have hgc := mapsTo_comp (J.comap h).normalizedBlowupMap h hgK hgt
    have hic : (J.comap ((J.comap h).normalizedBlowupMap ≫ h)).IsInvertible := by
      rw [comap_comp]
      exact hiK
    have hbf := hfinal _ ((J.comap h).normalizedBlowupMap ≫ h) hnK hgc hic
    have hbsquare : ∀ b : (J.comap h).normalizedBlowup ⟶ J.normalizedBlowup,
        b ≫ J.normalizedBlowupMap = (J.comap h).normalizedBlowupMap ≫ h →
        IsPullback b (J.comap h).normalizedBlowupMap J.normalizedBlowupMap h ∧ Smooth b := by
      intro b hbe
      obtain ⟨b₀, hb₀⟩ := smooth_normalized_blowup_square J h
      have he : b = b₀ := hbf.unique hbe hb₀.w
      subst b
      exact ⟨hb₀, MorphismProperty.of_isPullback hb₀.flip inferInstance⟩
    exact ⟨hrt, hdt, hnf, hntsquare, hbf, hbsquare⟩
  have hunit : ∃! e : (⊤ : S.IdealSheafData).normalizedBlowup ≅ S.reducedNormalization,
      e.hom ≫ S.fromReducedNormalization = (⊤ : S.IdealSheafData).normalizedBlowupMap := by
    obtain ⟨e, he⟩ := unit_normalization_iso S
    have hfg (U : S.affineOpens) : ((⊤ : S.IdealSheafData).ideal U).FG := by
      simp only [ideal_top]
      exact Ideal.fg_top _
    have hd : Dense ((⊤ : S.IdealSheafData).support.compl : Set S) := by simp
    obtain ⟨hnO, hgO, _, _⟩ := normalizedBlowup_finality S q ⊤ hfg hd
    have hu := normalization_finality S q _ (⊤ : S.IdealSheafData).normalizedBlowupMap hnO hgO
    exact ⟨e, he, fun e' he' ↦ Iso.ext (hu.unique he' he)⟩
  refine ⟨hn, hred, hft, hqc, hsurj, hg, hbir, hi, hfinal, ?_,
    normalization_finality S q _ J.normalizedBlowupMap hn hg,
    normalization_comparison S q J hJ hcentre, hsmooth, ?_, hunit, ?_,
    ⟨hnormal_id, ?_⟩, ?_⟩
  · intro e he
    exact Iso.ext (hself e.hom (𝟙 _) he (by simp))
  · intro hreg
    have : IsRegular S := hreg.2
    exact normal_self_normalization S (fun x ↦
      ⟨inferInstance, IsRegular.isIntegrallyClosed_stalk x⟩)
  · intro hnorm
    have hiS : IsIso S.fromReducedNormalization := normal_self_normalization S hnorm
    obtain ⟨e, he, _⟩ := hunit
    have hmap : IsIso (⊤ : S.IdealSheafData).normalizedBlowupMap := by
      rw [← he]
      infer_instance
    exact ⟨hiS, hmap⟩
  · intro K hK b hb
    have hKJ : K = J := hK.symm.trans J.comap_id
    subst hKJ
    simpa using hself b (𝟙 _) hb (by simp)
  · intro T U h g _ _ _ _ _ _
    have hT := hsmooth T h
    have : IsReduced T := hT.1
    have : IsLocallyNoetherian T := LocallyOfFiniteType.isLocallyNoetherian h
    have : IsLocallyNoetherian U := LocallyOfFiniteType.isLocallyNoetherian g
    have : IsReduced U := GeometricallyReduced.isReduced_of_flat_of_isLocallyNoetherian g
    have hdt := hT.2.1
    have hdU : Dense ((J.comap (g ≫ h)).support.compl : Set U) := by
      rw [support_comap]
      exact hcentre.preimage (g ≫ h).isOpenMap
    have hgt := generic_mapsTo_of_generalizing h (Flat.generalizingMap h)
    have hgu := generic_mapsTo_of_generalizing g (Flat.generalizingMap g)
    constructor
    · intro n₁ n₂ n₃ he₁ he₂ he₃
      have hnu := mapsTo_comp U.fromReducedNormalization (g ≫ h)
        (normalization_generic U (g ≫ h ≫ q)) (mapsTo_comp g h hgu hgt)
      have hu := normalization_finality S q _ (U.fromReducedNormalization ≫ g ≫ h)
        (AlgebraicGeometry.normal_normalization U) hnu
      apply hu.unique ?_ he₃
      rw [Category.assoc, he₁, ← Category.assoc, he₂, Category.assoc]
    · intro K hK b₁ b₂ b₃ he₁ he₂ he₃
      have hKeq : K = J.comap (g ≫ h) :=
        hK.symm.trans (J.comap_comp g h).symm
      subst hKeq
      have hfg (V : U.affineOpens) : ((J.comap (g ≫ h)).ideal V).FG := by
        have := IsLocallyNoetherian.component_noetherian V
        exact IsNoetherian.noetherian _
      obtain ⟨hnU, hgU, hiU, _⟩ :=
        normalizedBlowup_finality U (g ≫ h ≫ q) (J.comap (g ≫ h)) hfg hdU
      have hgc := mapsTo_comp (J.comap (g ≫ h)).normalizedBlowupMap (g ≫ h) hgU
        (mapsTo_comp g h hgu hgt)
      have hic : (J.comap ((J.comap (g ≫ h)).normalizedBlowupMap ≫ g ≫ h)).IsInvertible := by
        rw [J.comap_comp (J.comap (g ≫ h)).normalizedBlowupMap (g ≫ h)]
        exact hiU
      have hu := hfinal _ ((J.comap (g ≫ h)).normalizedBlowupMap ≫ g ≫ h) hnU hgc hic
      have he : b₂ ≫ b₁ = b₃ := by
        apply hu.unique ?_ he₃
        rw [Category.assoc, he₁, ← Category.assoc, he₂, Category.assoc]
      simpa using he


end AlgebraicGeometry.Scheme.IdealSheafData
