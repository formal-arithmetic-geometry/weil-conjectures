/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group V2
-/
module

public import Sheaf.Paper.RingedProjectionCoherenceData
import Sheaf.Algebra.Homology.WeilSiteDerivedTensorDescent
import Sheaf.Algebra.Homology.TensorColimitsIndependentCoefficients
import Sheaf.Paper.DerivedPullbackRepresentativeComputation
import Sheaf.Paper.KFlatRingedToposPullback

/-! # Normalized identity, composition and section pullback comparisons

Source: Stacks Project, Tags 06YS, 0D6D and 0FPI. The constructions use the flat K-flat
localization and the recorded ordinary module comparisons. No tensor compatibility
or adjunction compatibility is assumed.
-/

@[expose] public noncomputable section

set_option Elab.async false
set_option genSizeOf false
set_option genInjectivity false
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u w
open CategoryTheory CategoryTheory.Limits
namespace SheafOfModules.ProjectionCoherence

private theorem flat_localization (A : RingedTensorCorner.{u, w}) :
    let P : ObjectProperty (HomotopyCategory A.mateModules (ComplexShape.up ℤ)) :=
      fun K ↦ A.mateFlat K.as
    (P.ι ⋙ DerivedCategory.Qh).IsLocalization
      ((HomotopyCategory.quasiIso A.mateModules (ComplexShape.up ℤ)).inverseImage P.ι) := by
  obtain ⟨P, hP, ⟨F, hF, ⟨e⟩⟩, _⟩ :=
    wf_site_derived_tensor_descent.{u, u, w, u, u} A.topology A.ring
  have heq : P = (fun K ↦ A.mateFlat K.as) := by
    funext K
    exact propext (hP K)
  subst P
  let := hF
  exact Functor.IsLocalization.of_equivalence_target _ _ _ F.asEquivalence e

private theorem iso_descent
    {C D E : Type*} [Category C] [Category D] [Category E]
    (F : C ⥤ D) [F.Full] [F.EssSurj] (U V : D ⥤ E) (e : F ⋙ U ≅ F ⋙ V) :
    ∃ e' : U ≅ V, Functor.isoWhiskerLeft F e' = e := by
  let e' : U ≅ V := NatIso.ofComponents (fun X ↦
    U.mapIso (F.objObjPreimageIso X).symm ≪≫ e.app (F.objPreimage X) ≪≫
      V.mapIso (F.objObjPreimageIso X)) (by
    intro X Y f
    apply (cancel_epi (U.map (F.objObjPreimageIso X).hom)).1
    apply (cancel_mono (V.map (F.objObjPreimageIso Y).inv)).1
    have hn := e.hom.naturality (F.preimage
      ((F.objObjPreimageIso X).hom ≫ f ≫ (F.objObjPreimageIso Y).inv))
    dsimp only [Functor.comp_map] at hn
    rw [F.map_preimage] at hn
    simpa [Category.assoc] using hn
  )
  refine ⟨e', ?_⟩
  apply Iso.ext
  ext X
  apply (cancel_epi (U.map (F.objObjPreimageIso (F.obj X)).hom)).1
  have hn := e.hom.naturality
    (F.preimage (F.objObjPreimageIso (F.obj X)).hom)
  dsimp only [Functor.comp_map] at hn
  rw [F.map_preimage] at hn
  simpa [e', Category.assoc] using hn.symm


private def flatQuotient (A : RingedTensorCorner.{u, w}) :
    A.mateFlat.FullSubcategory ⥤
      ObjectProperty.FullSubcategory
        (fun K : HomotopyCategory A.mateModules (ComplexShape.up ℤ) ↦ A.mateFlat K.as) where
  obj K := ⟨(HomotopyCategory.quotient _ _).obj K.obj, K.property⟩
  map f := ObjectProperty.homMk ((HomotopyCategory.quotient _ _).map f.hom)

private instance flatQuotient_full (A : RingedTensorCorner.{u, w}) :
    (flatQuotient A).Full where
  map_surjective f := ⟨ObjectProperty.homMk f.hom.out, by
    apply ObjectProperty.hom_ext
    change (HomotopyCategory.quotient A.mateModules (ComplexShape.up ℤ)).map
      f.hom.out = f.hom
    exact HomotopyCategory.quotient_map_out f.hom⟩

private instance flatQuotient_essSurj (A : RingedTensorCorner.{u, w}) :
    (flatQuotient A).EssSurj where
  mem_essImage X := ⟨⟨X.obj.as, X.property⟩, ⟨Iso.refl _⟩⟩

set_option maxHeartbeats 800000 in
-- Descending through both a quotient and a localization needs extra elaboration fuel.
private theorem localization_iso_descent
    {C H D E : Type*} [Category C] [Category H] [Category D] [Category E]
    (F : C ⥤ H) [F.Full] [F.EssSurj]
    (L : H ⥤ D) (W : MorphismProperty H) [L.IsLocalization W]
    (K : C ⥤ D) (eK : F ⋙ L ≅ K)
    (U V : D ⥤ E) (e : K ⋙ U ≅ K ⋙ V) :
    ∃ t : U ≅ V, Functor.isoWhiskerLeft K t = e := by
  let ecomp : F ⋙ (L ⋙ U) ≅ F ⋙ (L ⋙ V) :=
    (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight eK U ≪≫ e ≪≫
      (Functor.isoWhiskerRight eK V).symm ≪≫ Functor.associator _ _ _
  obtain ⟨eh, heh⟩ := iso_descent F _ _ ecomp
  let t := Localization.liftNatIso L W _ _ U V eh
  refine ⟨t, ?_⟩
  apply Iso.ext
  ext X
  have hh := NatTrans.congr_app (congrArg Iso.hom heh) X
  have ht : t.hom.app (L.obj (F.obj X)) = eh.hom.app (F.obj X) := by
    change (Localization.liftNatTrans L W _ _ U V eh.hom).app (L.obj (F.obj X)) = _
    rw [Localization.liftNatTrans_app]
    simp
  have hn := t.hom.naturality (eK.hom.app X)
  dsimp only [Functor.comp_obj] at hn
  rw [ht] at hn
  have hh' : eh.hom.app (F.obj X) =
      U.map (eK.hom.app X) ≫ e.hom.app X ≫ V.map (eK.inv.app X) := by
    simpa [ecomp, Category.assoc] using hh
  rw [hh'] at hn
  simp only [Category.assoc, ← V.map_comp, Iso.inv_hom_id_app,
    CategoryTheory.Functor.map_id] at hn
  erw [Category.comp_id] at hn
  apply (cancel_epi (U.map (eK.hom.app X))).1
  simpa only [CategoryTheory.Category.comp_id, Functor.isoWhiskerLeft_hom,
    Functor.whiskerLeft_app] using hn

private theorem flat_iso_descent (A : RingedTensorCorner.{u, w})
    {E : Type*} [Category E] (U V : A.mateDerived ⥤ E)
    (e : (A.mateFlat.ι ⋙ DerivedCategory.Q) ⋙ U ≅
      (A.mateFlat.ι ⋙ DerivedCategory.Q) ⋙ V) :
    ∃ t : U ≅ V, Functor.isoWhiskerLeft (A.mateFlat.ι ⋙ DerivedCategory.Q) t = e := by
  let P : ObjectProperty (HomotopyCategory A.mateModules (ComplexShape.up ℤ)) :=
    fun K ↦ A.mateFlat K.as
  let F := flatQuotient A
  let L := P.ι ⋙ DerivedCategory.Qh
  let K := A.mateFlat.ι ⋙ DerivedCategory.Q
  let eK : F ⋙ L ≅ K := NatIso.ofComponents
    (fun X ↦ (DerivedCategory.quotientCompQhIso A.mateModules).app X.obj) (by
      intro X Y f
      exact (DerivedCategory.quotientCompQhIso A.mateModules).hom.naturality f.hom)
  let W := (HomotopyCategory.quasiIso A.mateModules (ComplexShape.up ℤ)).inverseImage P.ι
  let : L.IsLocalization W := flat_localization A
  exact localization_iso_descent F L W K eK U V e

private def complexEps {A B : RingedTensorCorner.{u, w}}
    (e : RingedTensorEdge A B) : DerivedCategory.Q ⋙ e.left ⟶
      e.pullback.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q where
  app P := derivedPullbackComplexComparison e.pullback e.left e.epsilon P
  naturality P Q f := by
    let t : DerivedCategory.Q ⋙ e.left ⟶
        e.pullback.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q :=
      Functor.whiskerRight (DerivedCategory.quotientCompQhIso A.mateModules).inv e.left ≫
        Functor.whiskerLeft (HomotopyCategory.quotient A.mateModules (.up ℤ)) e.epsilon ≫
        Functor.whiskerRight (e.pullback.mapHomotopyCategoryFactors (.up ℤ)).hom
          DerivedCategory.Qh ≫
        Functor.whiskerLeft (e.pullback.mapHomologicalComplex (.up ℤ))
          (DerivedCategory.quotientCompQhIso B.mateModules).hom
    exact t.naturality f

private theorem flat_preserved {A B : RingedTensorCorner.{u, w}}
    (e : RingedTensorEdge A B) (P : CochainComplex A.mateModules ℤ) (hp : A.mateFlat P) :
    B.mateFlat ((e.pullback.mapHomologicalComplex (.up ℤ)).obj P) := by
  let := monoidalCategory A.ring
  let := monoidalCategory B.ring
  have hf (n : ℤ) : IsFlatOnSite (J := A.topology) (R := A.ring) (P.X n) :=
    ObjectProperty.prop_of_iso (exactFunctor _ _)
      (siteSheafTensorRightIso A.ring _).symm (hp.2 n)
  obtain ⟨hk, ht⟩ := isKFlat_ringedToposPullback e.inverse e.direct e.adjunction
    e.algebraic e.ringMap e.pullback e.object_eq e.map_eq P
    ((CochainComplex.isKFlatIndependentCoefficients_iff_isKFlat P).2 hp.1) hf
  refine ⟨(CochainComplex.isKFlatIndependentCoefficients_iff_isKFlat _).1 hk, ?_⟩
  intro n
  exact ObjectProperty.prop_of_iso (exactFunctor _ _)
    (siteSheafTensorRightIso B.ring _) (ht n)

private theorem complexEps_isIso {A B : RingedTensorCorner.{u, w}}
    (e : RingedTensorEdge A B) (P : CochainComplex A.mateModules ℤ) (hp : A.mateFlat P) :
    IsIso ((complexEps e).app P) := by
  let := monoidalCategory A.ring
  have hf (n : ℤ) : IsFlatOnSite (J := A.topology) (R := A.ring) (P.X n) :=
    ObjectProperty.prop_of_iso (exactFunctor _ _)
      (siteSheafTensorRightIso A.ring _).symm (hp.2 n)
  exact (CanonicalTensorPullbackOfUniverses.derivedPullback_kflat_tensor_computation
    e.inverse e.direct e.adjunction e.algebraic e.ringMap e.pullback e.object_eq e.map_eq
    e.left e.epsilon e.isLeftDerived).1 P
      ((CochainComplex.isKFlatIndependentCoefficients_iff_isKFlat P).2 hp.1) hf

private def flatPull {A B : RingedTensorCorner.{u, w}} (e : RingedTensorEdge A B) :
    A.mateFlat.FullSubcategory ⥤ B.mateFlat.FullSubcategory where
  obj P := ⟨(e.pullback.mapHomologicalComplex (.up ℤ)).obj P.obj,
    flat_preserved e P.obj P.property⟩
  map f := ObjectProperty.homMk ((e.pullback.mapHomologicalComplex (.up ℤ)).map f.hom)
  map_id P := by
    apply ObjectProperty.hom_ext
    exact (e.pullback.mapHomologicalComplex (.up ℤ)).map_id P.obj
  map_comp f g := by
    apply ObjectProperty.hom_ext
    exact (e.pullback.mapHomologicalComplex (.up ℤ)).map_comp f.hom g.hom

private def flatEps {A B : RingedTensorCorner.{u, w}} (e : RingedTensorEdge A B) :
    (A.mateFlat.ι ⋙ DerivedCategory.Q) ⋙ e.left ≅
      flatPull e ⋙ B.mateFlat.ι ⋙ DerivedCategory.Q :=
  NatIso.ofComponents (fun (P : A.mateFlat.FullSubcategory) ↦
    @asIso _ _ _ _ ((complexEps e).app P.obj) (complexEps_isIso e P.obj P.property))
      (by intro P Q f; exact (complexEps e).naturality f.hom)


private theorem flatEps_hom_app {A B : RingedTensorCorner.{u, w}}
    (e : RingedTensorEdge A B) (P : A.mateFlat.FullSubcategory) :
    (flatEps e).hom.app P =
      derivedPullbackComplexComparison e.pullback e.left e.epsilon P.obj := rfl

private theorem flatPull_obj_obj {A B : RingedTensorCorner.{u, w}}
    (e : RingedTensorEdge A B) (P : A.mateFlat.FullSubcategory) :
    ((flatPull e).obj P).obj =
      (e.pullback.mapHomologicalComplex (.up ℤ)).obj P.obj := rfl

private theorem descended_comparison_normalization
    {C D E : Type*} [Category C] [Category D] [Category E]
    (K : C ⥤ D) (U V : D ⥤ E) (P Q : C ⥤ E)
    (r : K ⋙ U ≅ P) (s : K ⋙ V ≅ Q) (p : P ≅ Q)
    (t : U ≅ V) (ht : Functor.isoWhiskerLeft K t = r ≪≫ p ≪≫ s.symm) (X : C) :
    t.hom.app (K.obj X) ≫ s.hom.app X = r.hom.app X ≫ p.hom.app X := by
  have h := NatTrans.congr_app (congrArg Iso.hom ht) X
  change t.hom.app (K.obj X) = r.hom.app X ≫ p.hom.app X ≫ s.inv.app X at h
  rw [h, Category.assoc, Category.assoc, Iso.inv_hom_id_app, Category.comp_id]

private theorem composition_normalized {X Y Z : RingedTensorCorner.{u, w}}
    (f : RingedTensorEdge Y X) (g : RingedTensorEdge Z Y) (h : RingedTensorEdge Z X)
    (s : Composition f g h) :
    ∃ l : h.left ≅ g.left ⋙ f.left, s.Normalized l := by
  let KX := X.mateFlat.ι ⋙ DerivedCategory.Q
  let KY := Y.mateFlat.ι ⋙ DerivedCategory.Q
  let KZ := Z.mateFlat.ι ⋙ DerivedCategory.Q
  let c := (Functor.mapHomologicalComplexCompIso s.modules.symm (.up ℤ)).symm
  let m : flatPull h ⋙ KX ≅ flatPull g ⋙ flatPull f ⋙ KX :=
    Functor.isoWhiskerLeft Z.mateFlat.ι (Functor.isoWhiskerRight c DerivedCategory.Q)
  let path : KZ ⋙ (g.left ⋙ f.left) ≅ flatPull g ⋙ flatPull f ⋙ KX :=
    Functor.isoWhiskerRight (flatEps g) f.left ≪≫
      Functor.isoWhiskerLeft (flatPull g) (flatEps f)
  let e := flatEps h ≪≫ m ≪≫ path.symm
  obtain ⟨l, hl⟩ := flat_iso_descent Z h.left (g.left ⋙ f.left) e
  refine ⟨l, ?_⟩
  intro P hp
  have hc : c.hom.app P =
      (NatIso.mapHomologicalComplex s.modules (.up ℤ)).hom.app P := by
    ext n
    rfl
  have hh := descended_comparison_normalization KZ _ _ _ _
    (flatEps h) path m l hl ⟨P, hp⟩
  simpa only [path, m, KZ, KX, KY, Iso.trans_hom, Iso.symm_hom,
    NatTrans.comp_app, Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom,
    Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_hom_app, Functor.associator_inv_app,
    flatEps_hom_app, flatPull_obj_obj, ObjectProperty.ι_obj, Functor.comp_obj,
    Category.id_comp, Category.comp_id, Category.assoc, hc] using hh


private theorem section_normalized {X W : RingedTensorCorner.{u, w}}
    (i : RingedTensorEdge W X) (p : RingedTensorEdge X W) (s : Section i p) :
    ∃ l : p.left ⋙ i.left ≅ 𝟭 X.mateDerived, s.Normalized l := by
  let KX := X.mateFlat.ι ⋙ DerivedCategory.Q
  let KW := W.mateFlat.ι ⋙ DerivedCategory.Q
  let c := Functor.mapHomologicalComplexCompIso s.modules (.up ℤ) ≪≫
    Functor.mapHomologicalComplexIdIso X.mateModules (.up ℤ)
  let m : flatPull p ⋙ flatPull i ⋙ KX ≅ KX :=
    Functor.isoWhiskerLeft X.mateFlat.ι
      (Functor.isoWhiskerRight c DerivedCategory.Q)
  let path : KX ⋙ (p.left ⋙ i.left) ≅ flatPull p ⋙ flatPull i ⋙ KX :=
    Functor.isoWhiskerRight (flatEps p) i.left ≪≫
      Functor.isoWhiskerLeft (flatPull p) (flatEps i)
  let e : KX ⋙ (p.left ⋙ i.left) ≅ KX ⋙ 𝟭 X.mateDerived :=
    path ≪≫ m
  obtain ⟨l, hl⟩ := flat_iso_descent X (p.left ⋙ i.left) (𝟭 X.mateDerived) e
  refine ⟨l, ?_⟩
  intro P hp
  have hc : c.hom.app P =
      (NatIso.mapHomologicalComplex s.modules (.up ℤ)).hom.app P := by
    ext n
    rfl
  have hh := NatTrans.congr_app (congrArg Iso.hom hl) ⟨P, hp⟩
  simp only [e, path, m, KX, Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerLeft_hom,
    Functor.isoWhiskerRight_hom,
    Functor.whiskerLeft_app, Functor.whiskerRight_app,
    flatEps_hom_app, flatPull_obj_obj, ObjectProperty.ι_obj, Functor.comp_obj,
    Category.assoc, hc] at hh
  exact hh


private theorem identity_normalized {X : RingedTensorCorner.{u, w}}
    (h : RingedTensorEdge X X) (s : Identity h) :
    ∃ l : h.left ≅ 𝟭 X.mateDerived, s.Normalized l := by
  let KX := X.mateFlat.ι ⋙ DerivedCategory.Q
  let c := NatIso.mapHomologicalComplex s.modules (.up ℤ) ≪≫
    Functor.mapHomologicalComplexIdIso X.mateModules (.up ℤ)
  let m : flatPull h ⋙ KX ≅ KX :=
    Functor.isoWhiskerLeft X.mateFlat.ι
      (Functor.isoWhiskerRight c DerivedCategory.Q)
  let e : KX ⋙ h.left ≅ KX ⋙ 𝟭 X.mateDerived :=
    flatEps h ≪≫ m
  obtain ⟨l, hl⟩ := flat_iso_descent X h.left (𝟭 X.mateDerived) e
  refine ⟨l, ?_⟩
  intro P hp
  have hc : c.hom.app P =
      (NatIso.mapHomologicalComplex s.modules (.up ℤ)).hom.app P := by
    ext n
    rfl
  have hh := NatTrans.congr_app (congrArg Iso.hom hl) ⟨P, hp⟩
  simp only [e, m, KX, Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerLeft_hom,
    Functor.isoWhiskerRight_hom,
    Functor.whiskerLeft_app, Functor.whiskerRight_app,
    flatEps_hom_app, ObjectProperty.ι_obj, Functor.comp_obj,
    hc] at hh
  exact hh


set_option linter.checkUnivs false in
/-- The three derived comparisons with exactly their flat K-flat normalizations.
Source: Stacks 06YS, 0D6D and 0FPI
(blueprint: lem-sfb-ringed-projection-pullback-comparisons). -/
structure PullbackComparisons where
  identity : ∀ {X : RingedTensorCorner.{u, w}} (h : RingedTensorEdge X X) (s : Identity h),
    ∃ l : h.left ≅ 𝟭 X.mateDerived, s.Normalized l
  composition : ∀ {X Y Z : RingedTensorCorner.{u, w}}
    (f : RingedTensorEdge Y X) (g : RingedTensorEdge Z Y) (h : RingedTensorEdge Z X)
    (s : Composition f g h), ∃ l : h.left ≅ g.left ⋙ f.left, s.Normalized l
  sectionComparison : ∀ {X W : RingedTensorCorner.{u, w}}
    (i : RingedTensorEdge W X) (p : RingedTensorEdge X W) (s : Section i p),
    ∃ l : p.left ⋙ i.left ≅ 𝟭 X.mateDerived, s.Normalized l

set_option linter.checkUnivs false in
/-- Ordinary module comparisons induce normalized derived pullback comparisons.
Source: Stacks 06YS, 0D6D and 0FPI
(blueprint: lem-sfb-ringed-projection-pullback-comparisons).

Proof: the quotient from flat K-flat complexes to their homotopy subcategory is
full and essentially surjective. Tensor descent presents the derived category as
the localization of that subcategory. Descend natural isomorphisms first through
the quotient and then through this localization. Each edge's derived comparison
is a natural isomorphism on flat K-flat complexes, and pullback preserves this
class. For composition, conjugate the termwise ordinary module comparison by the
single-edge comparison and the composite of the other two comparison maps. For
identity use the identity termwise comparison; for section use the composite
comparison followed by the supplied ordinary contraction. The component equation
of localization descent and cancellation of the comparison isomorphisms give
exactly the three displayed Normalized predicates.
-/
theorem ringedProjectionPullbackComparisons : Nonempty (PullbackComparisons.{u, w}) := by
  exact ⟨{
    identity := identity_normalized
    composition := composition_normalized
    sectionComparison := section_normalized }⟩

end SheafOfModules.ProjectionCoherence
