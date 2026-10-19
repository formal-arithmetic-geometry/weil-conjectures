/- Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE. -/
module

public import Sheaf.AlgebraicGeometry.SupportComparisonBoundaryMaps
public import Sheaf.AlgebraicGeometry.SupportComparisonSnakeModel
import Sheaf.CategoryTheory.DerivedInjectiveBoundary

/-! # A common injective model for support comparison

Source: Stacks Project, proetale.tex Tags 099V, 099W and 09B1;
etale-cohomology.tex Tag 09XP
(blueprint: lem-pur-support-comparison-injective-ladder).
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

namespace CategoryTheory.Functor
variable {B B' D : Type*} [Category* B] [Category* B'] [Category* D]
  [Abelian B] [Abelian B'] [Abelian D]
  [HasDerivedCategory B] [HasDerivedCategory B'] [HasDerivedCategory D]
  [EnoughInjectives B] [EnoughInjectives B']
  (G : B ⥤ D) (G' : B' ⥤ D) (β : B ⥤ B')
  [G.Additive] [G'.Additive] [β.Additive]
  [PreservesFiniteLimits β] [PreservesFiniteColimits β]
  (ε : G ⟶ β ⋙ G')

private noncomputable def normalizedBC : G.rightDerivedFunctorPlus ⟶
    β.mapDerivedCategoryPlus ⋙ G'.rightDerivedFunctorPlus :=
  (Functor.rightUnitor _).inv ≫
    (Functor.isoWhiskerLeft _ (Functor.mapDerivedCategoryPlusIdIso D)).inv ≫
    Functor.rightDerivedFunctorPlusBaseChange
      ((Functor.rightUnitor G).hom ≫ ε)

private theorem normalizedBC_fac (K : HomotopyCategory.Plus B) :
    G.rightDerivedFunctorPlusUnit.app K ≫ (normalizedBC G G' β ε).app
      (DerivedCategory.Plus.Qh.obj K) =
    DerivedCategory.Plus.Qh.map ((NatTrans.mapHomotopyCategoryPlus ε).app K) ≫
      DerivedCategory.Plus.Qh.map
        ((mapHomotopyCategoryPlusCompIso (Iso.refl (β ⋙ G'))).inv.app K) ≫
      G'.rightDerivedFunctorPlusUnit.app (β.mapHomotopyCategoryPlus.obj K) ≫
      G'.rightDerivedFunctorPlus.map (β.mapDerivedCategoryPlusFactorsh.inv.app K) := by
  have h := congr_app (rightDerivedFunctorPlusBaseChange_fac
    (G := G) (G' := G') (β := β) (γ := 𝟭 D)
    ((Functor.rightUnitor G).hom ≫ ε)) K
  simp only [NatTrans.comp_app, whiskerRight_app, whiskerLeft_app,
    associator_hom_app, Category.comp_id] at h
  dsimp only [normalizedBC, NatTrans.comp_app, rightUnitor_inv_app,
    isoWhiskerLeft_inv, whiskerLeft_app, Category.id_comp, Category.comp_id]
  simp only [Category.id_comp]
  have hn := (mapDerivedCategoryPlusIdIso D).inv.naturality
    (G.rightDerivedFunctorPlusUnit.app K)
  dsimp only [Functor.comp_map, Functor.comp_obj, Functor.id_map, Functor.id_obj] at hn
  rw [← Category.assoc]
  erw [hn]
  rw [Category.assoc, h]
  have hid : (NatTrans.mapHomologicalComplex (G.rightUnitor.hom) (.up ℤ)).app
      K.obj.as = 𝟙 _ := by
    ext n
    rfl
  simp only [comp_obj, rightDerivedFunctorPlusBaseChangeAux,
    NatTrans.mapHomotopyCategoryPlus, NatTrans.mapHomotopyCategory_comp,
    whiskerLeft_comp, NatTrans.comp_app, whiskerLeft_app,
    ← mapDerivedCategoryPlusIdIso_hom_app_factorsh, associator_inv_app,
    whiskerRight_app, mapHomotopyCategoryPlusCompIso_refl_hom_app, map_id,
    FullyFaithful.whiskeringRight_preimage_app, whiskeringRight_obj_obj,
    ObjectProperty.ι_obj, mapHomotopyCategory_obj, NatTrans.mapHomotopyCategory_app,
    hid, mapHomotopyCategoryPlusCompIso_refl_inv_app, associator_hom_app,
    Category.comp_id, Category.id_comp, Iso.inv_hom_id_app_assoc]
  erw [Category.id_comp]

private theorem normalizedBC_model
    (I : CochainComplex.Plus B) (L : CochainComplex.Plus B')
    [∀ n : ℤ, Injective (I.obj.X n)] [∀ n : ℤ, Injective (L.obj.X n)]
    (K : DerivedCategory.Plus B)
    (e : DerivedCategory.Plus.Q.obj I ≅ K)
    (e' : DerivedCategory.Plus.Q.obj L ≅ β.mapDerivedCategoryPlus.obj K)
    (b : β.mapCochainComplexPlus.obj I ⟶ L)
    (hb : DerivedCategory.Plus.Q.map b ≫ e'.hom =
      β.mapDerivedCategoryPlusFactorsh.inv.app ((HomotopyCategory.Plus.quotient B).obj I) ≫
        β.mapDerivedCategoryPlus.map e.hom) (q : ℤ) :
    HomologicalComplex.homologyMap
        ((NatTrans.mapHomologicalComplex ε (.up ℤ)).app I.obj ≫
          (G'.mapHomologicalComplex (.up ℤ)).map b.hom) q ≫
      (injectiveHomologyModelIso G' L (β.mapDerivedCategoryPlus.obj K) e' q).hom =
    (injectiveHomologyModelIso G I K e q).hom ≫
      (DerivedCategory.Plus.homologyFunctor D q).map ((normalizedBC G G' β ε).app K) := by
  let π := HomotopyCategory.Plus.quotient B
  let π' := HomotopyCategory.Plus.quotient B'
  let t : G.mapCochainComplexPlus.obj I ⟶ G'.mapCochainComplexPlus.obj L :=
    ObjectProperty.homMk
      ((NatTrans.mapHomologicalComplex ε (.up ℤ)).app I.obj ≫
        (G'.mapHomologicalComplex (.up ℤ)).map b.hom)
  have ht : DerivedCategory.Plus.Q.map t =
      DerivedCategory.Plus.Qh.map ((NatTrans.mapHomotopyCategoryPlus ε).app (π.obj I)) ≫
        DerivedCategory.Plus.Qh.map
          ((mapHomotopyCategoryPlusCompIso (Iso.refl (β ⋙ G'))).inv.app (π.obj I)) ≫
        DerivedCategory.Plus.Qh.map (G'.mapHomotopyCategoryPlus.map (π'.map b)) := by
    rw [mapHomotopyCategoryPlusCompIso_refl_inv_app, Functor.map_id, Category.id_comp,
      ← Functor.map_comp]
    apply DerivedCategory.Plus.Qh.congr_map
    apply ObjectProperty.hom_ext
    change (HomotopyCategory.quotient D (.up ℤ)).map (_ ≫ _) = _
    rw [Functor.map_comp]
    rfl
  have hu := G'.rightDerivedFunctorPlusUnit.naturality (π'.map b)
  have hn := (normalizedBC G G' β ε).naturality e.hom
  dsimp only [Functor.comp_map] at hu hn
  have hh : DerivedCategory.Plus.Q.map t ≫
      G'.rightDerivedFunctorPlusUnit.app (π'.obj L) ≫
        G'.rightDerivedFunctorPlus.map e'.hom =
    G.rightDerivedFunctorPlusUnit.app (π.obj I) ≫
      G.rightDerivedFunctorPlus.map e.hom ≫ (normalizedBC G G' β ε).app K := by
    rw [ht, Category.assoc, Category.assoc]
    erw [reassoc_of% hu]
    rw [← Functor.map_comp]
    erw [hb]
    rw [Functor.map_comp]
    rw [hn]
    have hf := normalizedBC_fac G G' β ε (π.obj I)
    convert! congrArg
      (fun z ↦ z ≫ G'.rightDerivedFunctorPlus.map (β.mapDerivedCategoryPlus.map e.hom))
      hf.symm using 1 <;> simp only [Category.assoc] <;> rfl
  have hq := DerivedCategory.Plus.homologyFunctorObjQIso_hom_naturality t q
  apply (cancel_epi (DerivedCategory.Plus.homologyFunctorObjQIso
    (G.mapCochainComplexPlus.obj I) q).hom).1
  dsimp only [injectiveHomologyModelIso, Iso.trans_hom, Iso.symm_hom,
    Functor.mapIso_hom, asIso_hom, Functor.comp_map]
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  erw [← reassoc_of% hq]
  simp only [Iso.hom_inv_id_assoc]
  simpa only [Functor.map_comp, Category.assoc] using
    congrArg (DerivedCategory.Plus.homologyFunctor D q).map hh

private theorem exists_injective_model (K : DerivedCategory.Plus B) :
    ∃ I : CochainComplex.Plus B, (∀ n : ℤ, Injective (I.obj.X n)) ∧
      Nonempty (DerivedCategory.Plus.Q.obj I ≅ K) := by
  let Q := (InjectiveObject.ι B).mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh
  let M := Q.objPreimage K
  obtain ⟨L, hL⟩ := HomotopyCategory.Plus.quotient_obj_surjective M
  let I := (InjectiveObject.ι B).mapCochainComplexPlus.obj L
  exact ⟨I, fun n ↦ inferInstanceAs (Injective (L.obj.X n).obj),
    ⟨Q.mapIso (eqToIso hL) ≪≫ Q.objObjPreimageIso K⟩⟩

omit [EnoughInjectives B] in
private theorem exists_model_map
    (I L : CochainComplex.Plus B) [∀ n : ℤ, Injective (L.obj.X n)]
    (K : DerivedCategory.Plus B) (e : DerivedCategory.Plus.Q.obj L ≅ K)
    (f : DerivedCategory.Plus.Q.obj I ⟶ K) :
    ∃ b : I ⟶ L, DerivedCategory.Plus.Q.map b ≫ e.hom = f := by
  have : L.obj.IsKInjective := by
    obtain ⟨n, hn⟩ := L.property
    exact CochainComplex.isKInjective_of_injective L.obj n
  obtain ⟨b, hb⟩ := (DerivedCategory.Plus.Qh_map_bijective_of_isKInjective
    ((HomotopyCategory.Plus.quotient B).obj I)
    ((HomotopyCategory.Plus.quotient B).obj L)
      (show L.obj.IsKInjective from inferInstance)).2 (f ≫ e.inv)
  obtain ⟨b, rfl⟩ := (HomotopyCategory.Plus.quotient B).map_surjective b
  refine ⟨b, ?_⟩
  change DerivedCategory.Plus.Qh.map ((HomotopyCategory.Plus.quotient B).map b) ≫ e.hom = _
  rw [hb]
  simp

end CategoryTheory.Functor

namespace AlgebraicGeometry

/-- The three canonical graded functors evaluated on one derived coefficient.
Source: Stacks Tag 09XP (blueprint: lem-pur-support-comparison-injective-ladder). -/
noncomputable def supportBoundaryHomologyRow
    {B : Type (u + 1)} [Category.{u} B]
    (J : GrothendieckTopology B) (A : Type (u + 1)) [CommRing A]
    {V W : B} (j : W ⟶ V)
    (δ : Sheaf.SupportSequenceBoundary J (ModuleCat.{u + 1} A) j ⊤)
    (K : DerivedCategory.Plus (Sheaf J (ModuleCat.{u + 1} A))) :
    SupportHomologyRow (ModuleCat.{u + 1} A) where
  obj₁ q := (Sheaf.supportHypercohomologyFunctor J (ModuleCat.{u + 1} A) j q).obj K
  obj₂ q := (Sheaf.sectionHypercohomologyFunctor J (ModuleCat.{u + 1} A) V q).obj K
  obj₃ q := (Sheaf.sectionHypercohomologyFunctor J (ModuleCat.{u + 1} A) W q).obj K
  f q := (Sheaf.supportHypercohomologyInclusion J (ModuleCat.{u + 1} A) j q).app K
  g q := (Sheaf.sectionHypercohomologyRestriction J (ModuleCat.{u + 1} A) j q).app K
  δ q := (δ q).app ⟨K, trivial⟩

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
private noncomputable def supportBoundary_rowModel
    {B : Type (u + 1)} [Category.{u} B]
    (J : GrothendieckTopology B) (A : Type (u + 1)) [CommRing A]
    {V W : B} (j : W ⟶ V)
    (δ : Sheaf.SupportSequenceBoundary J (ModuleCat.{u + 1} A) j ⊤)
    (hδ : supportBoundaryNormalization J A j δ)
    (I : CochainComplex.Plus (Sheaf J (ModuleCat.{u + 1} A)))
    [∀ n : ℤ, Injective (I.obj.X n)]
    (K : DerivedCategory.Plus (Sheaf J (ModuleCat.{u + 1} A)))
    (e : DerivedCategory.Plus.Q.obj I ≅ K) :
    SupportHomologyRowModel (supportBoundaryHomologyRow J A j δ K) := by
  let S := Sheaf.supportedSectionsFunctor J (ModuleCat.{u + 1} A) j
  let E : Sheaf J (ModuleCat.{u + 1} A) ⥤ ModuleCat.{u + 1} A :=
    sheafToPresheaf J (ModuleCat.{u + 1} A) ⋙ (evaluation _ _).obj (op V)
  let G : Sheaf J (ModuleCat.{u + 1} A) ⥤ ModuleCat.{u + 1} A :=
    sheafToPresheaf J (ModuleCat.{u + 1} A) ⋙ (evaluation _ _).obj (op W)
  let w := Classical.choose (hδ I)
  let hs := Classical.choose (Classical.choose_spec (hδ I))
  have hh := Classical.choose_spec (Classical.choose_spec (hδ I))
  let row := ShortComplex.mk _ _ w
  let eS := Functor.injectiveHomologyModelIso S I K e
  let eE := Functor.injectiveHomologyModelIso E I K e
  let eG := Functor.injectiveHomologyModelIso G I K e
  refine {
    S := row
    shortExact := hs
    e₁ := eS
    e₂ := eE
    e₃ := eG
    f_comm := ?_
    g_comm := ?_
    δ_comm := ?_ }
  · intro q
    exact Functor.injectiveHomologyModelIso_natTrans
      (Sheaf.supportedSectionsInclusion J (ModuleCat.{u + 1} A) j) I K e q
  · intro q
    exact Functor.injectiveHomologyModelIso_natTrans (S := E) (F := G)
      ((sheafSections J (ModuleCat.{u + 1} A)).map j.op) I K e q
  · intro q
    have h0 := hh q
    let P : ObjectProperty (DerivedCategory.Plus (Sheaf J (ModuleCat.{u + 1} A))) := ⊤
    have hn := (δ q).naturality (ObjectProperty.homMk e.hom :
      (⟨DerivedCategory.Plus.Q.obj I, trivial⟩ : P.FullSubcategory) ⟶ ⟨K, trivial⟩)
    dsimp only [Functor.comp_map, ObjectProperty.ι_map] at hn
    change (Sheaf.supportSequenceModelIso J (ModuleCat.{u + 1} A) G I
      (DerivedCategory.Plus.Q.obj I) (Iso.refl _) q).hom ≫
        (δ q).app ⟨DerivedCategory.Plus.Q.obj I, trivial⟩ ≫
          (Sheaf.supportSequenceModelIso J (ModuleCat.{u + 1} A) S I
            (DerivedCategory.Plus.Q.obj I) (Iso.refl _) (q + 1)).inv = _ at h0
    let E0 (H : Sheaf J (ModuleCat.{u + 1} A) ⥤ ModuleCat.{u + 1} A) [H.Additive]
        (r : ℤ) := Functor.injectiveHomologyModelIso H I
      (DerivedCategory.Plus.Q.obj I) (Iso.refl _) r
    have hiso (H : Sheaf J (ModuleCat.{u + 1} A) ⥤ ModuleCat.{u + 1} A) [H.Additive]
        (r : ℤ) :
        (Functor.injectiveHomologyModelIso H I K e r).hom =
          (E0 H r).hom ≫
            (H.rightDerivedFunctorPlus ⋙ DerivedCategory.Plus.homologyFunctor
              (ModuleCat.{u + 1} A) r).map e.hom := by
      simp only [E0, Functor.injectiveHomologyModelIso, Iso.trans_hom, Iso.symm_hom,
        Functor.mapIso_hom, asIso_hom, Iso.refl_hom, Functor.comp_map, Category.assoc]
      erw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id, Category.id_comp]
    have h0' : hs.δ q (q + 1) rfl ≫ (E0 S (q + 1)).hom =
        (E0 G q).hom ≫ (δ q).app ⟨DerivedCategory.Plus.Q.obj I, trivial⟩ := by
      change (E0 G q).hom ≫ (δ q).app ⟨DerivedCategory.Plus.Q.obj I, trivial⟩ ≫
        (E0 S (q + 1)).inv = hs.δ q (q + 1) rfl at h0
      rw [← h0]
      simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    change hs.δ q (q + 1) rfl ≫ (Functor.injectiveHomologyModelIso S I K e (q + 1)).hom =
      (Functor.injectiveHomologyModelIso G I K e q).hom ≫ (δ q).app ⟨K, trivial⟩
    rw [hiso, hiso]
    simp only [Category.assoc]
    change (G.rightDerivedFunctorPlus ⋙ DerivedCategory.Plus.homologyFunctor
        (ModuleCat.{u + 1} A) q).map e.hom ≫ (δ q).app ⟨K, trivial⟩ =
      (δ q).app ⟨DerivedCategory.Plus.Q.obj I, trivial⟩ ≫
        (S.rightDerivedFunctorPlus ⋙ DerivedCategory.Plus.homologyFunctor
          (ModuleCat.{u + 1} A) (q + 1)).map e.hom at hn
    rw [hn, ← Category.assoc, h0', Category.assoc]

/-- The three specified comparison maps have a common cochain realization on
normalized injective support sequences. The conclusion supplies cochain complexes,
short exactness, their morphism, and the nine transport equations; it asserts no
commutativity of a localization square.
Source: Stacks Project, proetale.tex Tags 099V, 099W, 09B1; etale-cohomology.tex
Tag 09XP; derived.tex Tags 0DVC and 09T5.
(blueprint: lem-pur-support-comparison-injective-ladder).

Proof: choose bounded-below injective representatives I of F and L of its
exact comparison inverse image. K-injectivity of L lifts the derived comparison
identification to a chain map from the inverse image of I to L. Apply the
ordinary comparison units on supported sections, global sections and open
sections, then compose with this chain map. Naturality of the kernel inclusion
and of restriction makes these three maps a morphism of short exact complexes.
The normalization hypotheses identify their snake boundaries with the supplied
boundaries. The canonical right-derived-unit homology isomorphisms provide all
three row identifications. Finally the right-derived base-change factorization
and naturality of its unit identify the three transported homology maps with
the specified comparison maps. This argument needs no preservation of
injectives by inverse image and no invertibility of the comparison unit. -/
theorem exists_supportComparison_injective_ladder
    (k : Type u) [Field k] [IsAlgClosed k]
    (A : Type (u + 1)) [CommRing A] [Finite A]
    (T : Scheme.{u}) [T.Over (Spec (.of k))]
    [LocallyOfFiniteType (T ↘ Spec (.of k))]
    [QuasiCompact (T ↘ Spec (.of k))]
    [IsSeparated (T ↘ Spec (.of k))]
    (C : Scheme.{u}) (i : C ⟶ T) [IsClosedImmersion i]
    (δₑ : Sheaf.SupportSequenceBoundary T.smallEtaleTopology
      (ModuleCat.{u + 1} A) (Etale.supportRestrictionArrow i) ⊤)
    (δₚ : Sheaf.SupportSequenceBoundary (Scheme.ProEt.topology T)
      (ModuleCat.{u + 1} A) (ProEtale.supportRestrictionArrow i) ⊤)
    (hₑ : supportBoundaryNormalization T.smallEtaleTopology A
      (Etale.supportRestrictionArrow i) δₑ)
    (hₚ : supportBoundaryNormalization (Scheme.ProEt.topology T) A
      (ProEtale.supportRestrictionArrow i) δₚ)
    (F : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) :
    Nonempty (SupportComparisonSnakeModel
      (supportBoundaryHomologyRow T.smallEtaleTopology A
        (Etale.supportRestrictionArrow i) δₑ
        ((DerivedCategory.Plus.singleFunctor
          (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) 0).obj F))
      (supportBoundaryHomologyRow (Scheme.ProEt.topology T) A
        (ProEtale.supportRestrictionArrow i) δₚ
        ((DerivedCategory.Plus.singleFunctor
          (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) 0 ⋙
          (ProEtale.comparisonUpperStar
            (ModuleCat.{u + 1} A) T).mapDerivedCategoryPlus).obj F))
      (fun q ↦ (ProEtale.supportComparisonHypercohomology A i q).app
        ((DerivedCategory.Plus.singleFunctor
          (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) 0).obj F))
      (fun q ↦ (ProEtale.finiteComparisonGlobalHypercohomology T A q).app
        ((DerivedCategory.Plus.singleFunctor
          (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) 0).obj F))
      (fun q ↦ (ProEtale.finiteComparisonSectionHypercohomology T A
        (Scheme.Etale.mk i.openComplement.ι) q).app
        ((DerivedCategory.Plus.singleFunctor
          (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) 0).obj F))) := by
  classical
  let β := ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) T
  let K := (DerivedCategory.Plus.singleFunctor
    (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) 0).obj F
  obtain ⟨I, hI, ⟨e⟩⟩ := Functor.exists_injective_model K
  let (n : ℤ) : Injective (I.obj.X n) := hI n
  obtain ⟨L, hL, ⟨e'⟩⟩ := Functor.exists_injective_model (β.mapDerivedCategoryPlus.obj K)
  let (n : ℤ) : Injective (L.obj.X n) := hL n
  obtain ⟨b, hb⟩ := Functor.exists_model_map (β.mapCochainComplexPlus.obj I) L
    (β.mapDerivedCategoryPlus.obj K) e'
    (β.mapDerivedCategoryPlusFactorsh.inv.app ((HomotopyCategory.Plus.quotient _).obj I) ≫
      β.mapDerivedCategoryPlus.map e.hom)
  let S := Sheaf.supportedSectionsFunctor T.smallEtaleTopology
    (ModuleCat.{u + 1} A) (Etale.supportRestrictionArrow i)
  let S' := Sheaf.supportedSectionsFunctor (Scheme.ProEt.topology T)
    (ModuleCat.{u + 1} A) (ProEtale.supportRestrictionArrow i)
  let E : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A) ⥤ ModuleCat.{u + 1} A :=
    sheafToPresheaf T.smallEtaleTopology (ModuleCat.{u + 1} A) ⋙
      (evaluation _ _).obj (op (Scheme.Etale.mk (𝟙 T)))
  let E' : Sheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} A) ⥤ ModuleCat.{u + 1} A :=
    sheafToPresheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} A) ⋙
      (evaluation _ _).obj (op (Scheme.ProEt.mk (𝟙 T)))
  let G : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A) ⥤ ModuleCat.{u + 1} A :=
    sheafToPresheaf T.smallEtaleTopology (ModuleCat.{u + 1} A) ⋙
      (evaluation _ _).obj (op (Scheme.Etale.mk i.openComplement.ι))
  let G' : Sheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} A) ⥤ ModuleCat.{u + 1} A :=
    sheafToPresheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} A) ⋙
      (evaluation _ _).obj (op (Scheme.ProEt.mk i.openComplement.ι))
  let εS : S ⟶ β ⋙ S' := ProEtale.supportComparisonUnit A i
  let εE : E ⟶ β ⋙ E' :=
    ProEtale.finiteComparisonSectionUnit T A (Scheme.Etale.mk (𝟙 T))
  let εG : G ⟶ β ⋙ G' :=
    ProEtale.finiteComparisonSectionUnit T A (Scheme.Etale.mk i.openComplement.ι)
  let R := supportBoundary_rowModel T.smallEtaleTopology A
    (Etale.supportRestrictionArrow i) δₑ hₑ I K e
  let R' := supportBoundary_rowModel (Scheme.ProEt.topology T) A
    (ProEtale.supportRestrictionArrow i) δₚ hₚ L (β.mapDerivedCategoryPlus.obj K) e'
  let tS := (NatTrans.mapHomologicalComplex εS (.up ℤ)).app I.obj ≫
    (S'.mapHomologicalComplex (.up ℤ)).map b.hom
  let tE := (NatTrans.mapHomologicalComplex εE (.up ℤ)).app I.obj ≫
    (E'.mapHomologicalComplex (.up ℤ)).map b.hom
  let tG := (NatTrans.mapHomologicalComplex εG (.up ℤ)).app I.obj ≫
    (G'.mapHomologicalComplex (.up ℤ)).map b.hom
  let φ : R.S ⟶ R'.S :=
    { τ₁ := tS
      τ₂ := tE
      τ₃ := tG
      comm₁₂ := by
        ext n : 1
        let ιₑ := Sheaf.supportedSectionsInclusion T.smallEtaleTopology
          (ModuleCat.{u + 1} A) (Etale.supportRestrictionArrow i)
        let ιₚ := Sheaf.supportedSectionsInclusion (Scheme.ProEt.topology T)
          (ModuleCat.{u + 1} A) (ProEtale.supportRestrictionArrow i)
        change (εS.app (I.obj.X n) ≫ S'.map (b.hom.f n)) ≫ ιₚ.app (L.obj.X n) =
          ιₑ.app (I.obj.X n) ≫ (εE.app (I.obj.X n) ≫ E'.map (b.hom.f n))
        have hn := ιₚ.naturality (b.hom.f n)
        change S'.map (b.hom.f n) ≫ ιₚ.app (L.obj.X n) =
          ιₚ.app (β.obj (I.obj.X n)) ≫ E'.map (b.hom.f n) at hn
        rw [Category.assoc, hn]
        have hu := (Classical.choose_spec
          (ProEtale.supportComparisonUnit_existsUnique A i)).1 (I.obj.X n)
        change εS.app (I.obj.X n) ≫ ιₚ.app (β.obj (I.obj.X n)) =
          ιₑ.app (I.obj.X n) ≫ εE.app (I.obj.X n) at hu
        simpa only [Category.assoc] using
          congrArg (fun z ↦ z ≫ E'.map (b.hom.f n)) hu
      comm₂₃ := by
        ext n : 1
        let πₑ : E ⟶ G :=
          (sheafSections T.smallEtaleTopology (ModuleCat.{u + 1} A)).map
            (Etale.supportRestrictionArrow i).op
        let πₚ : E' ⟶ G' :=
          (sheafSections (Scheme.ProEt.topology T) (ModuleCat.{u + 1} A)).map
            (ProEtale.supportRestrictionArrow i).op
        change (εE.app (I.obj.X n) ≫ E'.map (b.hom.f n)) ≫ πₚ.app (L.obj.X n) =
          πₑ.app (I.obj.X n) ≫ (εG.app (I.obj.X n) ≫ G'.map (b.hom.f n))
        have hn := πₚ.naturality (b.hom.f n)
        change E'.map (b.hom.f n) ≫ πₚ.app (L.obj.X n) =
          πₚ.app (β.obj (I.obj.X n)) ≫ G'.map (b.hom.f n) at hn
        rw [Category.assoc, hn]
        have hu := ((ProEtale.comparisonAdjunction (ModuleCat.{u + 1} A) T).unit.app
          (I.obj.X n)).hom.naturality (Etale.supportRestrictionArrow i).op
        change πₑ.app (I.obj.X n) ≫ εG.app (I.obj.X n) =
          εE.app (I.obj.X n) ≫ πₚ.app (β.obj (I.obj.X n)) at hu
        simpa only [Category.assoc] using
          congrArg (fun z ↦ z ≫ G'.map (b.hom.f n)) hu.symm }
  refine ⟨{ left := R, right := R', φ := φ, comm₁ := ?_, comm₂ := ?_, comm₃ := ?_ }⟩
  · intro q
    have hh := Functor.normalizedBC_model S S' β εS I L K e e' b hb q
    convert! hh using 1
  · intro q
    have hh := Functor.normalizedBC_model E E' β εE I L K e e' b hb q
    convert! hh using 1
  · intro q
    have hh := Functor.normalizedBC_model G G' β εG I L K e e' b hb q
    convert! hh using 1

end AlgebraicGeometry
