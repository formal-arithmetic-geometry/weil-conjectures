/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Reduction.ReductionExceptionalObjects
import all WeilConjectures.AlgebraicGeometry.Reduction.ReductionDirectImage
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.HomComparison
import WeilConjectures.SixFunctors.Etale.Derived.Stability.UpperShriek
import Mathlib.CategoryTheory.Adjunction.Restrict
import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekIndependenceUnbounded

/-! # Realization of a finite-coefficient exceptional adjunction -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genInjectivity false
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genCtorIdx false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
namespace CategoryTheory

end CategoryTheory

namespace AlgebraicGeometry.ProEtale

private def realizationAdjunction
    {C D E F : Type*} [Category C] [Category D] [Category E] [Category F]
    (e : E ≌ C) (d : F ≌ D) (L : C ⥤ D) (U : E ⥤ F) (V : F ⥤ E)
    (a : U ⊣ V) (t : e.functor ⋙ L ≅ U ⋙ d.functor) :
    L ⊣ d.inverse ⋙ V ⋙ e.functor :=
  ((e.symm.toAdjunction.comp a).comp d.toAdjunction).ofNatIsoLeft
    (Functor.isoWhiskerLeft e.inverse t.symm ≪≫ e.invFunIdAssoc L)

private theorem realizationAdjunction_counit
    {C D E F : Type*} [Category C] [Category D] [Category E] [Category F]
    (e : E ≌ C) (d : F ≌ D) (L : C ⥤ D) (U : E ⥤ F) (V : F ⥤ E)
    (a : U ⊣ V) (t : e.functor ⋙ L ≅ U ⋙ d.functor) (K : D) :
    (realizationAdjunction e d L U V a t).counit.app K =
      t.hom.app (V.obj (d.inverse.obj K)) ≫
        d.functor.map (a.counit.app (d.inverse.obj K)) ≫ d.counit.app K := by
  dsimp only [realizationAdjunction, Adjunction.ofNatIsoLeft,
    NatTrans.comp_app, Functor.whiskerLeft_app, Iso.trans_inv, NatTrans.comp_app,
    Functor.isoWhiskerLeft_inv, Functor.whiskerLeft_app]
  rw [Equivalence.invFunIdAssoc_inv_app, Adjunction.comp_counit_app,
    Adjunction.comp_counit_app]
  simp only [Equivalence.toAdjunction_counit, Functor.map_comp, Category.assoc]
  change L.map (e.counitInv.app (e.functor.obj (V.obj (d.inverse.obj K)))) ≫
    t.hom.app (e.inverse.obj (e.functor.obj (V.obj (d.inverse.obj K)))) ≫
    (U ⋙ d.functor).map (e.unitInv.app (V.obj (d.inverse.obj K))) ≫ _ = _
  rw [← t.hom.naturality_assoc]
  simp only [Functor.comp_map, ← Category.assoc]
  rw [← L.map_comp, Equivalence.counitInv_functor_comp]
  simp only [Functor.map_id, Category.id_comp, Functor.id_obj]

private theorem realizationPreservesOfIso
    {C D : Type*} [Category C] [Category D]
    (P : ObjectProperty C) (Q : ObjectProperty D) [Q.IsClosedUnderIsomorphisms]
    {L L' : C ⥤ D} (i : L ≅ L')
    (h : ∀ M : P.FullSubcategory, Q (L'.obj M.obj)) :
    ∀ M : P.FullSubcategory, Q (L.obj M.obj) :=
  fun M ↦ Q.prop_of_iso (i.symm.app M.obj) (h M)

private theorem realizationForProperties
    {C D E F : Type*} [Category C] [Category D] [Category E] [Category F]
    (P : ObjectProperty C) (Q : ObjectProperty D)
    (R : ObjectProperty E) (S : ObjectProperty F)
    (siteX : C ⥤ E) (siteY : D ⥤ F)
    (hX : ∀ M : P.FullSubcategory, R (siteX.obj M.obj))
    (hY : ∀ M : Q.FullSubcategory, S (siteY.obj M.obj))
    (eInv : R.FullSubcategory ⥤ P.FullSubcategory)
    (eUnit : 𝟭 P.FullSubcategory ≅ R.lift (P.ι ⋙ siteX) hX ⋙ eInv)
    (eCounit : eInv ⋙ R.lift (P.ι ⋙ siteX) hX ≅ 𝟭 R.FullSubcategory)
    (eTriangle : ∀ M, (R.lift (P.ι ⋙ siteX) hX).map (eUnit.hom.app M) ≫
      eCounit.hom.app ((R.lift (P.ι ⋙ siteX) hX).obj M) = 𝟙 _)
    (dInv : S.FullSubcategory ⥤ Q.FullSubcategory)
    (dUnit : 𝟭 Q.FullSubcategory ≅ S.lift (Q.ι ⋙ siteY) hY ⋙ dInv)
    (dCounit : dInv ⋙ S.lift (Q.ι ⋙ siteY) hY ≅ 𝟭 S.FullSubcategory)
    (dTriangle : ∀ M, (S.lift (Q.ι ⋙ siteY) hY).map (dUnit.hom.app M) ≫
      dCounit.hom.app ((S.lift (Q.ι ⋙ siteY) hY).obj M) = 𝟙 _)
    (L₀ : C ⥤ D) (R₀ : D ⥤ C) (a₀ : L₀ ⊣ R₀)
    (hL : ∀ M : P.FullSubcategory, Q (L₀.obj M.obj))
    (hR : ∀ K : Q.FullSubcategory, P (R₀.obj K.obj))
    (L₁ : E ⥤ F) (hF : ∀ M : R.FullSubcategory, S (L₁.obj M.obj))
    (Pplus : ObjectProperty C) (hPplus : P ≤ Pplus)
    (tplus : Pplus.ι ⋙ siteX ⋙ L₁ ≅ Pplus.ι ⋙ L₀ ⋙ siteY) :
    ∃ (G : S.FullSubcategory ⥤ R.FullSubcategory)
      (adj : S.lift (R.ι ⋙ L₁) hF ⊣ G)
      (origin : S.FullSubcategory ⥤ D)
      (_origin_ctf : ∀ K, Q (origin.obj K))
      (originIso : origin ⋙ siteY ≅ S.ι)
      (right_ctf : ∀ K, P (R₀.obj (origin.obj K)))
      (rightIso : G ⋙ R.ι ≅ origin ⋙ R₀ ⋙ siteX),
      ∀ K, L₁.map (rightIso.hom.app K) ≫
        tplus.hom.app ⟨R₀.obj (origin.obj K), hPplus _ (right_ctf K)⟩ ≫
        siteY.map (a₀.counit.app (origin.obj K)) ≫ originIso.hom.app K =
          (adj.counit.app K).hom := by
  let e : P.FullSubcategory ≌ R.FullSubcategory :=
    ⟨R.lift (P.ι ⋙ siteX) hX, eInv, eUnit, eCounit, eTriangle⟩
  let d : Q.FullSubcategory ≌ S.FullSubcategory :=
    ⟨S.lift (Q.ι ⋙ siteY) hY, dInv, dUnit, dCounit, dTriangle⟩
  let U := Q.lift (P.ι ⋙ L₀) hL
  let V := P.lift (Q.ι ⋙ R₀) hR
  let a : U ⊣ V := a₀.restrictFullyFaithful P.fullyFaithfulι Q.fullyFaithfulι
    (Iso.refl _) (Iso.refl _)
  let L := S.lift (R.ι ⋙ L₁) hF
  let t₀ : (P.ι ⋙ siteX) ⋙ L₁ ≅ (P.ι ⋙ L₀) ⋙ siteY :=
    Functor.isoWhiskerLeft (ObjectProperty.ιOfLE hPplus) tplus
  let t : e.functor ⋙ L ≅ U ⋙ d.functor :=
    (S.fullyFaithfulι.whiskeringRight _).preimageIso t₀
  let G := d.inverse ⋙ V ⋙ e.functor
  let adj : L ⊣ G := realizationAdjunction e d L U V a t
  let origin := d.inverse ⋙ Q.ι
  let originIso : origin ⋙ siteY ≅ S.ι :=
    Functor.isoWhiskerRight d.counitIso S.ι
  have right_ctf (K : S.FullSubcategory) : P (R₀.obj (origin.obj K)) :=
    hR (d.inverse.obj K)
  let rightIso : G ⋙ R.ι ≅ origin ⋙ R₀ ⋙ siteX := Iso.refl _
  refine ⟨G, adj, origin, fun K ↦ (d.inverse.obj K).property,
    originIso, right_ctf, rightIso, ?_⟩
  intro K
  have hc := realizationAdjunction_counit e d L U V a t K
  have hc' := congrArg (fun z ↦ z.hom) hc
  have ha := a₀.map_restrictFullyFaithful_counit_app
    (L := U) (R := V) P.fullyFaithfulι Q.fullyFaithfulι
    (Iso.refl _) (Iso.refl _) (d.inverse.obj K)
  have ha' : (a.counit.app (d.inverse.obj K)).hom =
      a₀.counit.app (origin.obj K) := by
    change (a.counit.app (d.inverse.obj K)).hom =
      (𝟙 _) ≫ L₀.map (𝟙 _) ≫ a₀.counit.app (origin.obj K) at ha
    simpa only [L₀.map_id, Category.id_comp] using ha
  have ht (M : P.FullSubcategory) : (t.hom.app M).hom = t₀.hom.app M :=
    congrArg (fun z ↦ z.app M) ((S.fullyFaithfulι.whiskeringRight P.FullSubcategory).map_preimage
        (X := e.functor ⋙ L) (Y := U ⋙ d.functor) t₀.hom)
  change (adj.counit.app K).hom = (t.hom.app (V.obj (d.inverse.obj K))).hom ≫
    siteY.map (a.counit.app (d.inverse.obj K)).hom ≫ originIso.hom.app K at hc'
  rw [ht, ha'] at hc'
  change L₁.map (𝟙 _) ≫ t₀.hom.app (V.obj (d.inverse.obj K)) ≫
    siteY.map (a₀.counit.app (origin.obj K)) ≫
    originIso.hom.app K = (adj.counit.app K).hom
  rw [L₁.map_id, Category.id_comp]
  exact hc'.symm

private theorem finiteCtf_iff_good (T : Scheme.{u}) (A : Type u)
    [CommRing A] [Finite A] (K : proEtaleDerivedCategory T A) :
    spFiniteConstructibleTor T A K ↔ ReductionGood T A K := by
  constructor
  · rintro ⟨⟨a, b, hab, hv⟩, hc, ht⟩
    refine ⟨(Set.finite_Icc a b).subset ?_, hc, ht⟩
    intro i hi
    exact ⟨le_of_not_gt (fun h ↦ hi (hv i (Or.inl h))),
      le_of_not_gt (fun h ↦ hi (hv i (Or.inr h)))⟩
  · rintro ⟨hb, hc, ht⟩
    obtain ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ := (bounded_iff_finite_support K).mpr hb
    refine ⟨⟨min a b, max a b, min_le_max, ?_⟩, hc, ht⟩
    intro i hi
    rcases hi with hi | hi
    · exact (DerivedCategory.isGE_iff K a).mp ha i (hi.trans_le (min_le_left _ _))
    · exact (DerivedCategory.isLE_iff K b).mp hb i ((le_max_right _ _).trans_lt hi)

private abbrev ordinaryCtf (A : Type u) [CommRing A] (T : Scheme.{u}) :=
  Etale.DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} (ULift.{u + 1} A)) T

private theorem site_ctf (T : Scheme.{u}) (A : Type u) [CommRing A] [Finite A]
    (K : Etale.DerivedCategoryModule (ULift.{u + 1} A) T) (hK : ordinaryCtf A T K) :
    spFiniteConstructibleTor T A ((reductionSite A T).obj K) := by
  apply (finiteCtf_iff_good T A _).mpr
  apply (reductionGood_realization_iff T A _).mpr
  exact DerivedCategory.constructibleFiniteTor_mapDerivedCategory (ULift.{u + 1} A) hK

private def siteCtf (T : Scheme.{u}) (A : Type u) [CommRing A] [Finite A] :
    (ordinaryCtf A T).FullSubcategory ⥤ spFiniteConstructibleTorCategory T A :=
  (spFiniteConstructibleTor T A).lift ((ordinaryCtf A T).ι ⋙ reductionSite A T)
    (fun K ↦ site_ctf T A K.obj K.property)

private theorem siteCtf_equivalence (T : Scheme.{u}) (A : Type u)
    [CommRing A] [Finite A] : (siteCtf T A).IsEquivalence := by
  let C := comparisonUpperStar (ModuleCat.{u + 1} (ULift.{u + 1} A)) T
  let E := sfIntrinsicDerivedEquivalence T A
  have hbij (K L : (ordinaryCtf A T).FullSubcategory) :
      Function.Bijective (fun a : K ⟶ L ↦ (siteCtf T A).map a) := by
    have h := bijective_comparisonUpperStar_mapDerivedCategory_map
      K.obj L.obj L.property.1.1.1
    constructor
    · intro f g he
      apply ObjectProperty.hom_ext
      apply h.injective
      exact E.functor.map_injective (congrArg (fun a ↦ a.hom) he)
    · intro f
      obtain ⟨g, hg⟩ := h.surjective (E.functor.preimage f.hom)
      refine ⟨ObjectProperty.homMk g, ObjectProperty.hom_ext _ ?_⟩
      change E.functor.map (C.mapDerivedCategory.map g) = f.hom
      change C.mapDerivedCategory.map g = E.functor.preimage f.hom at hg
      exact (congrArg E.functor.map hg).trans (E.functor.map_preimage f.hom)
  have : (siteCtf T A).Full := ⟨fun {K L} f ↦ (hbij K L).surjective f⟩
  have : (siteCtf T A).Faithful := ⟨fun {K L} f g h ↦ (hbij K L).injective h⟩
  have : (siteCtf T A).EssSurj := by
    constructor
    intro M
    let K := E.inverse.obj M.obj
    have hK := (reductionGood_realization_iff T A K).mp
      (reductionGood_iso (E.counitIso.app M.obj).symm
        ((finiteCtf_iff_good T A M.obj).mp M.property))
    obtain ⟨L, hL, ⟨e⟩⟩ := hK.1
    have ht := (DerivedCategory.constructibleFiniteTor
      (ModuleCat.{u + 1} (ULift.{u + 1} A)) T).prop_of_iso e.symm hK
    obtain ⟨a, b, hab⟩ := ht.2
    have hctf : ordinaryCtf A T L := ⟨hL, a, b,
      (DerivedCategory.torAmplitudeIn_mapDerivedCategory_iff a b L).mp hab⟩
    refine ⟨⟨L, hctf⟩, ⟨(spFiniteConstructibleTor T A).isoMk ?_⟩⟩
    exact E.functor.mapIso e ≪≫ E.counitIso.app M.obj
  exact {}

private def siteCtfEquivalence (T : Scheme.{u}) (A : Type u)
    [CommRing A] [Finite A] :
    (ordinaryCtf A T).FullSubcategory ≌ spFiniteConstructibleTorCategory T A :=
  have := siteCtf_equivalence T A
  (siteCtf T A).asEquivalence

private structure OrdinaryCtfData (A : Type u) [CommRing A] [Finite A]
    {X Z Y : Scheme.{u}} (j : X ⟶ Z) [IsOpenImmersion j] (p : Z ⟶ Y) [IsProper p] where
  right : Etale.DerivedCategoryModule (ULift.{u + 1} A) Y ⥤
    Etale.DerivedCategoryModule (ULift.{u + 1} A) X
  adjunction : Etale.rightDerivedLowerShriekOfCompactification
    (ModuleCat.{u + 1} (ULift.{u + 1} A))
    (⟨Z, p, j, rfl, inferInstance, inferInstance⟩ : Compactification (j ≫ p)) ⊣ right
  left_preserves : ∀ M : (ordinaryCtf A X).FullSubcategory,
    ordinaryCtf A Y ((Etale.rightDerivedLowerShriekOfCompactification
      (ModuleCat.{u + 1} (ULift.{u + 1} A))
      (⟨Z, p, j, rfl, inferInstance, inferInstance⟩ : Compactification (j ≫ p))).obj M.obj)
  right_preserves : ∀ K : (ordinaryCtf A Y).FullSubcategory,
    ordinaryCtf A X (right.obj K.obj)

@[irreducible] private def ordinaryAdjunction (A : Type u) [CommRing A] [Finite A]
    {X Z Y : Scheme.{u}} (j : X ⟶ Z) [IsOpenImmersion j] (p : Z ⟶ Y) [IsProper p]
    [HasCompactification (j ≫ p)] [QuasiCompact (j ≫ p)] :
    Etale.rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} (ULift.{u + 1} A))
      (⟨Z, p, j, rfl, inferInstance, inferInstance⟩ : Compactification (j ≫ p)) ⊣
        Etale.rightDerivedUpperShriek (ULift.{u + 1} A) (j ≫ p) :=
  (Etale.rightDerivedUpperShriekAdjunction (ULift.{u + 1} A) (j ≫ p)).ofNatIsoLeft
    (Etale.rightDerivedLowerShriekIso (ULift.{u + 1} A)
      (⟨Z, p, j, rfl, inferInstance, inferInstance⟩ : Compactification (j ≫ p))).symm

private theorem ordinaryLeftPreserves (A : Type u) [CommRing A] [Finite A]
    (k : Type u) [Field k] {X Z Y : Scheme.{u}} [IsNoetherian X]
    (s : Y ⟶ Spec (.of k)) [LocallyOfFiniteType s] [QuasiCompact s]
    [HasInvertibleExponent (ULift.{u + 1} A) Y]
    (j : X ⟶ Z) [IsOpenImmersion j] (p : Z ⟶ Y) [IsProper p]
    [HasCompactification (j ≫ p)] :
    ∀ M : (ordinaryCtf A X).FullSubcategory,
      ordinaryCtf A Y ((Etale.rightDerivedLowerShriekOfCompactification
        (ModuleCat.{u + 1} (ULift.{u + 1} A))
        (⟨Z, p, j, rfl, inferInstance, inferInstance⟩ : Compactification (j ≫ p))).obj M.obj) :=
  CategoryTheory.realizationPreservesOfIso (ordinaryCtf A X) (ordinaryCtf A Y)
    (Etale.rightDerivedLowerShriekIso (ULift.{u + 1} A)
      (⟨Z, p, j, rfl, inferInstance, inferInstance⟩ : Compactification (j ≫ p)))
    (fun M ↦ Etale.constructibleFiniteTor_rightDerivedLowerShriek
      (ULift.{u + 1} A) s (j ≫ p) M.property)

@[irreducible] private def ordinaryCtfData (A : Type u) [CommRing A] [Finite A]
    (k : Type u) [Field k] {X Z Y : Scheme.{u}} [IsNoetherian X]
    (s : Y ⟶ Spec (.of k)) [LocallyOfFiniteType s] [QuasiCompact s]
    [HasInvertibleExponent (ULift.{u + 1} A) Y]
    (j : X ⟶ Z) [IsOpenImmersion j] (p : Z ⟶ Y) [IsProper p] :
    OrdinaryCtfData A j p := by
  have : HasCompactification (j ≫ p) :=
    (⟨Z, p, j, rfl, inferInstance, inferInstance⟩ : Compactification (j ≫ p)).hasCompactification
  exact ⟨_, ordinaryAdjunction A j p, ordinaryLeftPreserves A k s j p,
    fun K ↦ Etale.constructibleFiniteTor_rightDerivedUpperShriek (ULift.{u + 1} A)
      s (j ≫ p) K.property⟩

private theorem realizationFromData (A : Type u) [CommRing A] [Finite A]
    {X Z Y : Scheme.{u}} (j : X ⟶ Z) [IsOpenImmersion j] (p : Z ⟶ Y) [IsProper p]
    (hF : ∀ M : spFiniteConstructibleTorCategory X A,
      spFiniteConstructibleTor Y A ((reductionCompactSupport A j p).obj M.obj))
    (D : OrdinaryCtfData A j p) :
    ∃ (G : spFiniteConstructibleTorCategory Y A ⥤ spFiniteConstructibleTorCategory X A)
      (adj : reductionCtfCompactSupport A j p hF ⊣ G),
      Nonempty (ReductionExceptionalRealization A j p hF G adj) := by
  -- Keep the comparison abstract when taking components of its large construction.
  obtain ⟨tCmp, hCmp⟩ : ∃ t, reductionSiteCompactSupportIso A j p = t := ⟨_, rfl⟩
  let P := ordinaryCtf A X
  let Q := ordinaryCtf A Y
  let e := siteCtfEquivalence X A
  let d := siteCtfEquivalence Y A
  let B := ModuleCat.{u + 1} (ULift.{u + 1} A)
  let L₀ := Etale.rightDerivedLowerShriekOfCompactification B
    (⟨Z, p, j, rfl, inferInstance, inferInstance⟩ : Compactification (j ≫ p))
  obtain ⟨G, adj, origin, origin_ctf, originIso, right_ctf, rightIso, hc⟩ :=
    CategoryTheory.realizationForProperties P Q
      (spFiniteConstructibleTor X A) (spFiniteConstructibleTor Y A)
      (reductionSite A X) (reductionSite A Y)
      (fun M ↦ site_ctf X A M.obj M.property)
      (fun M ↦ site_ctf Y A M.obj M.property)
      e.inverse e.unitIso e.counitIso e.functor_unitIso_comp
      d.inverse d.unitIso d.counitIso d.functor_unitIso_comp
      L₀ D.right D.adjunction D.left_preserves D.right_preserves
      (reductionCompactSupport A j p) hF DerivedCategory.TStructure.t.plus
      (fun _ h ↦ h.1.1.1) tCmp
  refine ⟨G, adj, ⟨⟨origin, origin_ctf, originIso, D.right, D.adjunction,
    fun K ↦ (right_ctf K).1.1.1, rightIso, ?_⟩⟩⟩
  intro K
  rw [hCmp]
  exact hc K

/-- The already proved intrinsic realization equivalence identifies precisely the
finite-ctf subcategories.  This public form combines the existing finite-support
and realization predicate comparisons without changing either predicate.
Source: blueprint `det-sp-reduction-exceptional`, Charts, finite coefficient domains. -/
theorem reductionCtf_realization_iff (T : Scheme.{u}) (A : Type u)
    [CommRing A] [Finite A]
    (K : DerivedCategory (Sheaf (ProEt.topology T)
      (ModuleCat.{u + 1} (ULift.{u + 1, u} A)))) :
    spFiniteConstructibleTor T A ((sfIntrinsicDerivedEquivalence T A).functor.obj K) ↔
      ProEtale.DerivedCategory.constructibleFiniteTor
        (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) T K :=
  (finiteCtf_iff_good T A _).trans (reductionGood_realization_iff T A K)

/-- The recorded intrinsic finite-ctf property is invariant under isomorphism.
Source: blueprint `det-sp-reduction-exceptional`, Charts, finite coefficient domains. -/
theorem reductionCtf_of_iso (T : Scheme.{u}) (A : Type u) [CommRing A] [Finite A]
    {K L : proEtaleDerivedCategory T A} (e : K ≅ L)
    (h : spFiniteConstructibleTor T A K) : spFiniteConstructibleTor T A L :=
  (finiteCtf_iff_good T A _).mpr
    (reductionGood_iso e ((finiteCtf_iff_good T A _).mp h))

/-- The canonical comparison on the ordinary-etale and intrinsic finite-ctf
categories, with the existing coefficient realization as underlying functor.
Source: blueprint `det-sp-reduction-exceptional`, Charts, finite coefficient domains. -/
def reductionSiteCtf (T : Scheme.{u}) (A : Type u) [CommRing A] [Finite A] :
    (Etale.DerivedCategory.constructibleFiniteTor
      (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) T).FullSubcategory ⥤
      spFiniteConstructibleTorCategory T A :=
  (spFiniteConstructibleTor T A).lift
    ((Etale.DerivedCategory.constructibleFiniteTor
      (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) T).ι ⋙ reductionSite A T)
    (fun K ↦ (reductionCtf_realization_iff T A _).mpr
      (DerivedCategory.constructibleFiniteTor_mapDerivedCategory
        (ULift.{u + 1, u} A) K.property))

end AlgebraicGeometry.ProEtale
