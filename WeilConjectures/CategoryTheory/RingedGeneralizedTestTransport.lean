/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.RingedGeneralizedLocalizationTest
import WeilConjectures.CategoryTheory.RingedEquivalenceModuleHom
import WeilConjectures.CategoryTheory.ScalarLocalizationRegularColimit
import WeilConjectures.CategoryTheory.RingedSectionLocalization
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.RingTheory.Localization.Away.Basic
import WeilConjectures.Algebra.Homology.DerivedInternalHom
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
import Mathlib.CategoryTheory.Functor.OfSequence
import WeilConjectures.RingTheory.ModuleLocalizationFilteredColimit
import Mathlib.Algebra.Category.ModuleCat.Colimits
import Mathlib.Algebra.Module.LocalizedModule.Basic
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.CategoryTheory.Limits.ConcreteCategory.Basic
import Mathlib.Algebra.Module.LocalizedModule.IsLocalization
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Colimits
import WeilConjectures.CategoryTheory.RingedGeneralizedCompletenessCriterion
import all WeilConjectures.CategoryTheory.RingedEquivalenceSlices
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp

/-! # Generalized localization tests on a ringed site -/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite CategoryTheory.MonoidalCategory
namespace CategoryTheory
attribute [local instance] ringSections


private theorem sequence_colimit_transport
    {A B : Type*} [Category* A] [Category* B]
    (F : A ⥤ B) [PreservesColimitsOfShape ℕ F]
    {X : A} {Y : B} (f : X ⟶ X) (g : Y ⟶ Y)
    (i : F.obj X ≅ Y) (h : F.map f ≫ i.hom = i.hom ≫ g)
    (c : Cocone (Functor.ofSequence (X := fun _ : ℕ ↦ X) (fun _ ↦ f)))
    (d : Cocone (Functor.ofSequence (X := fun _ : ℕ ↦ Y) (fun _ ↦ g)))
    (hc : IsColimit c) (hd : IsColimit d) :
    ∃ q : F.obj c.pt ≅ d.pt,
      F.map (c.ι.app 0) ≫ q.hom = i.hom ≫ d.ι.app 0 := by
  let α : Functor.ofSequence (X := fun _ : ℕ ↦ X) (fun _ ↦ f) ⋙ F ⟶
      Functor.ofSequence (X := fun _ : ℕ ↦ Y) (fun _ ↦ g) :=
    NatTrans.ofSequence (fun _ ↦ i.hom) (by
      intro n
      dsimp only [Functor.comp_map]
      rw [Functor.ofSequence_map_homOfLE_succ, Functor.ofSequence_map_homOfLE_succ]
      exact h)
  have : IsIso α := by
    rw [NatTrans.isIso_iff_isIso_app]
    intro n
    change IsIso i.hom
    infer_instance
  exact ⟨(isColimitOfPreserves F hc).coconePointsIsoOfNatIso hd (asIso α),
    IsColimit.comp_coconePointsIsoOfNatIso_hom
      (isColimitOfPreserves F hc) hd (asIso α) 0⟩

private theorem localization_transport
    {C D : Type u} [SmallCategory C] [SmallCategory D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    {R : Sheaf J CommRingCat.{u}} {S : Sheaf K CommRingCat.{u}}
    (F : PresentationModules R ⥤ PresentationModules S)
    [PreservesColimitsOfShape ℕ F]
    (i : F.obj (SheafOfModules.unit (localCoefficientRings R)) ≅
      SheafOfModules.unit (localCoefficientRings S))
    (s : (R.obj ⋙ forget CommRingCat).sections)
    (t : (S.obj ⋙ forget CommRingCat).sections)
    (h : F.map (presentationScalar R s) ≫ i.hom = i.hom ≫ presentationScalar S t) :
    ∃ l : F.obj (ringedSectionLocalizationOfUniverses R s) ≅
        ringedSectionLocalizationOfUniverses S t,
      F.map (ringedSectionLocalizationUnit R s) ≫ l.hom =
        i.hom ≫ ringedSectionLocalizationUnitOfUniverses S t := by
  change ∃ l : F.obj (ringedSectionLocalization R s) ≅ ringedSectionLocalization S t,
    F.map (ringedSectionLocalizationUnit R s) ≫ l.hom =
      i.hom ≫ ringedSectionLocalizationUnit S t
  have scalar_eq {E : Type u} [SmallCategory E] {L : GrothendieckTopology E}
      (T : Sheaf L CommRingCat.{u}) (a : (T.obj ⋙ forget CommRingCat).sections) :
      presentationScalar T a = (SheafOfModules.unitHomEquiv _).symm
        ⟨a.val, a.property⟩ := by
    apply (SheafOfModules.unitHomEquiv _).injective
    rw [Equiv.apply_symm_apply]
    ext U
    change (a.val U : T.obj.obj U) * 1 = a.val U
    exact mul_one _
  obtain ⟨c, ⟨hc⟩, ec, hec⟩ := scalarLocalization_regularColimit R s
  obtain ⟨d, ⟨hd⟩, ed, hed⟩ := scalarLocalization_regularColimit S t
  rw [scalar_eq R s, scalar_eq S t] at h
  obtain ⟨q, hq⟩ := sequence_colimit_transport F _ _ i h c d hc hd
  refine ⟨(F.mapIso ec).symm ≪≫ q ≪≫ ed, ?_⟩
  have hc0 : F.map (ringedSectionLocalizationUnit R s) ≫ F.map ec.inv =
      F.map (c.ι.app 0) := by
    exact (F.map_comp _ _).symm.trans
      (congrArg F.map ((Iso.comp_inv_eq ec).mpr hec.symm))
  change F.map (ringedSectionLocalizationUnit R s) ≫
    ((F.map ec.inv ≫ q.hom) ≫ ed.hom) = _
  rw [← Category.assoc, ← Category.assoc, hc0, Category.assoc, reassoc_of% hq, hed]

private def generalizedTransportFunctorOfCore
    {C D : Type u} [SmallCategory C] [SmallCategory D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    {R : Sheaf J CommRingCat.{u}} {S : Sheaf K CommRingCat.{u}}
    {F : PresentationModules R ⥤ PresentationModules S}
    (T : RingedPresentationCore R S F) : RingedPresentationFunctor R S F where
  additive := T.additive
  finiteLimits := T.finiteLimits
  finiteColimits := T.finiteColimits
  termwise := by
    let := HasDerivedCategory.standard (PresentationModules R)
    let := HasDerivedCategory.standard (PresentationModules S)
    let := T.additive
    let := T.finiteLimits
    let := T.finiteColimits
    exact ⟨F.mapDerivedCategoryFactors⟩
  unit := T.unit
  kInjective := T.kInjective
  internalHom := T.internalHom
  localization := by
    let := T.sequentialColimits
    exact localization_transport F T.unit

private def presentationCoreOfEquivalence
    {C D : Type u} [SmallCategory C] [SmallCategory D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    {R : Sheaf J CommRingCat.{u}} {S : Sheaf K CommRingCat.{u}}
    (F : PresentationModules R ⥤ PresentationModules S) [F.IsEquivalence]
    (i : F.obj (SheafOfModules.unit (localCoefficientRings R)) ≅
      SheafOfModules.unit (localCoefficientRings S))
    (h : Nonempty (presentationRHom R ⋙
      presentationDerivedMap (R := R) (S := S) F (Functor.additive_of_preserves_binary_products _)
        (inferInstance) (inferInstance) ≅
      ((presentationDerivedMap (R := R) (S := S) F
          (Functor.additive_of_preserves_binary_products _) (inferInstance) (inferInstance)).op.prod
        (presentationDerivedMap (R := R) (S := S) F
          (Functor.additive_of_preserves_binary_products _) (inferInstance) (inferInstance))) ⋙
        presentationRHom S)) :
    RingedPresentationCore R S F := by
  letI ha : F.Additive := Functor.additive_of_preserves_binary_products F
  exact {
    additive := ha
    finiteLimits := inferInstance
    finiteColimits := inferInstance
    sequentialColimits := inferInstance
    unit := i
    kInjective := fun I hI ↦ by
      let := hI
      change CochainComplex.IsKInjective ((F.mapHomologicalComplex (.up ℤ)).obj I)
      infer_instance
    internalHom := h }

private def inverseHomComparison
    {A B : Type*} [Category A] [Category B] (E : A ≌ B)
    (H : Aᵒᵖ × A ⥤ A) (K : Bᵒᵖ × B ⥤ B)
    (a : H ⋙ E.functor ≅ (E.functor.op.prod E.functor) ⋙ K) :
    K ⋙ E.inverse ≅ (E.inverse.op.prod E.inverse) ⋙ H :=
  (Iso.isoCompInverse (H := E)
    (Functor.associator _ _ _ ≪≫
      Iso.inverseCompIso (G := E.op.prod E) a)).symm

private def generalizedTransportEquivalenceOfCore
    {C D : Type u} [SmallCategory C] [SmallCategory D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    {R : Sheaf J CommRingCat.{u}} {S : Sheaf K CommRingCat.{u}}
    (T : RingedPresentationEquivalenceCore R S) : RingedPresentationEquivalence R S where
  modules := T.modules
  forward := generalizedTransportFunctorOfCore
    (presentationCoreOfEquivalence (R := R) (S := S)
      T.modules.functor T.forwardUnit T.forwardHom)
  backward := by
    let := HasDerivedCategory.standard (PresentationModules R)
    let := HasDerivedCategory.standard (PresentationModules S)
    let := Functor.additive_of_preserves_binary_products T.modules.functor
    let := Functor.additive_of_preserves_binary_products T.modules.inverse
    exact generalizedTransportFunctorOfCore (presentationCoreOfEquivalence (R := S) (S := R)
      T.modules.inverse
      (T.modules.inverse.mapIso T.forwardUnit.symm ≪≫ T.modules.unitIso.symm.app _)
      (T.forwardHom.map (fun a ↦ inverseHomComparison T.modules.mapDerivedCategory _ _ a)))
  derivedUnit := by
    let := HasDerivedCategory.standard (PresentationModules R)
    let := HasDerivedCategory.standard (PresentationModules S)
    let := Functor.additive_of_preserves_binary_products T.modules.functor
    let := Functor.additive_of_preserves_binary_products T.modules.inverse
    exact ⟨T.modules.mapDerivedCategory.unitIso.symm⟩
  derivedCounit := by
    let := HasDerivedCategory.standard (PresentationModules R)
    let := HasDerivedCategory.standard (PresentationModules S)
    let := Functor.additive_of_preserves_binary_products T.modules.functor
    let := Functor.additive_of_preserves_binary_products T.modules.inverse
    exact ⟨T.modules.mapDerivedCategory.counitIso⟩


/-- Complete the ringed module equivalence core with the formal derived comparisons. -/
private theorem generalizedTransportAt
    {C D : Type u} [SmallCategory C] [SmallCategory D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    {R : Sheaf J CommRingCat.{u}} {S : Sheaf K CommRingCat.{u}}
    (e : RingedToposMorphism (localCoefficientRings R) (localCoefficientRings S))
    [e.inverse.IsEquivalence] [IsIso e.ringMap] : Nonempty (RingedPresentationAt e) := by
  obtain ⟨T, ⟨p⟩, a, ha⟩ := ringed_equivalence_module_hom e
  exact ⟨{ transport := generalizedTransportEquivalenceOfCore T
           pushforward := p
           underlying := a
           structural := ha }⟩

/-- Transport a single localization test after the scalar and object comparisons. -/
private theorem generalizedTransportLocalizationTest
    {C D : Type u} [SmallCategory C] [SmallCategory D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    {R : Sheaf J CommRingCat.{u}} {S : Sheaf K CommRingCat.{u}}
    {F : PresentationModules R ⥤ PresentationModules S}
    (T : RingedPresentationFunctor R S F)
    (s : (R.obj ⋙ forget CommRingCat).sections)
    (t : (S.obj ⋙ forget CommRingCat).sections)
    (h : F.map (presentationScalar R s) ≫ T.unit.hom =
      T.unit.hom ≫ presentationScalar S t)
    (X : PresentationDerived R) (Y : PresentationDerived S) (q : T.derived.obj X ≅ Y) :
    let := HasDerivedCategory.standard (PresentationModules R)
    let := HasDerivedCategory.standard (PresentationModules S)
    Nonempty (T.derived.obj ((presentationRHom R).obj
      (op ((DerivedCategory.singleFunctor _ 0).obj
        (ringedSectionLocalizationOfUniverses R s)), X)) ≅
      (presentationRHom S).obj (op ((DerivedCategory.singleFunctor _ 0).obj
        (ringedSectionLocalizationOfUniverses S t)), Y)) := by
  let := HasDerivedCategory.standard (PresentationModules R)
  let := HasDerivedCategory.standard (PresentationModules S)
  let := T.additive
  let := T.finiteLimits
  let := T.finiteColimits
  obtain ⟨l, _⟩ := T.localization s t h
  obtain ⟨a⟩ := T.internalHom
  let d := (F.mapDerivedCategorySingleFunctor 0).app
      (ringedSectionLocalizationOfUniverses R s) ≪≫
    (DerivedCategory.singleFunctor _ 0).mapIso l
  exact ⟨a.app _ ≪≫ (presentationRHom S).mapIso (d.symm.op.prod q)⟩


private def generalizedScalarOver
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (R : Sheaf J CommRingCat.{u}) (A : Sheaf J (Type u))
    (a : A ⟶ (presentationForget R).obj (SheafOfModules.unit (localCoefficientRings R))) :
    (productOver A).obj (ringSets (localCoefficientRings R)) ⟶
      (productOver A).obj (ringSets (localCoefficientRings R)) :=
  Over.homMk (⟨{
    app := fun U ↦ TypeCat.ofHom fun x ↦
      (x.1, @Mul.mul (R.obj.obj U) inferInstance (a.hom.app U x.1) x.2)
    naturality := by
      intro U V f
      ext x
      change (A.obj.map f x.1,
          @Mul.mul (R.obj.obj V) inferInstance
            (a.hom.app V (A.obj.map f x.1)) (R.obj.map f x.2)) =
        (A.obj.map f x.1, R.obj.map f
          (@Mul.mul (R.obj.obj U) inferInstance (a.hom.app U x.1) x.2))
      refine congrArg (fun z : R.obj.obj V ↦ (A.obj.map f x.1, z)) ?_
      exact (congrArg (fun z ↦ @Mul.mul (R.obj.obj V) inferInstance z (R.obj.map f x.2))
        (NatTrans.naturality_apply a.hom f x.1)).trans
          ((R.obj.map f).hom.map_mul _ _).symm }⟩) (by ext U x; rfl)

private theorem generalizedScalar_fibre
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (R : Sheaf J CommRingCat.{u}) (A : Sheaf J (Type u))
    (a : A ⟶ (presentationForget R).obj (SheafOfModules.unit (localCoefficientRings R)))
    (s : RingedSheafSliceAdjunctionData (localCoefficientRings R) A) :
    s.fibreEquivalence.inverse.map (generalizedScalarOver R A a) ≫
      (productFibreIso A s).hom.app (ringSets (localCoefficientRings R)) =
    (productFibreIso A s).hom.app (ringSets (localCoefficientRings R)) ≫
      (presentationForget (presentationElementRing R A)).map
        (presentationScalar (presentationElementRing R A)
          (presentationGeneralizedSection R A a)) := by
  apply (sheafToPresheaf (elementTopology A) (Type u)).map_injective
  simp only [Functor.map_comp, productFibreIso,
    Functor.fullyFaithfulCancelRight_hom_app, Functor.map_preimage,
    Iso.trans_hom, Functor.isoWhiskerLeft_hom,
    Functor.whiskerLeft_app, NatTrans.comp_app,
    NatIso.ofComponents_hom_app, Category.assoc]
  erw [s.fibre_iso.hom.naturality_assoc]
  ext U x
  let y := (s.fibre_iso.hom.app
    ((productOver A).obj (ringSets (localCoefficientRings R)))).app U x
  change @Mul.mul (R.obj.obj U.unop.unop.1) inferInstance
      (a.hom.app U.unop.unop.1 y.val.1) y.val.2 =
    @Mul.mul (R.obj.obj U.unop.unop.1) inferInstance
      (a.hom.app U.unop.unop.1 U.unop.unop.2) y.val.2
  exact congrArg (fun z ↦ @Mul.mul (R.obj.obj U.unop.unop.1) inferInstance
    (a.hom.app U.unop.unop.1 z) y.val.2) y.property

private theorem generalizedFibre_endomorphism
    {L O L' O' : Type*} [Category L] [Category O] [Category L'] [Category O']
    (E : L ≌ O) (E' : L' ≌ O') (P : O ⥤ O')
    {X : O} {Y : O'} {V : L} {W : L'}
    (f : X ⟶ X) (g : Y ⟶ Y) (l : V ⟶ V) (m : W ⟶ W)
    (p : E.inverse.obj X ≅ V) (q : E'.inverse.obj Y ≅ W)
    (z : P.obj X ⟶ Y)
    (hp : E.inverse.map f ≫ p.hom = p.hom ≫ l)
    (hq : E'.inverse.map g ≫ q.hom = q.hom ≫ m)
    (hz : P.map f ≫ z = z ≫ g) :
    let c := E.counitIso.symm.app X ≪≫ E.functor.mapIso p
    (E.functor ⋙ P ⋙ E'.inverse).map l ≫
      E'.inverse.map (P.map c.inv ≫ z) ≫ q.hom =
    E'.inverse.map (P.map c.inv ≫ z) ≫ q.hom ≫ m := by
  intro c
  have hc : f ≫ c.hom = c.hom ≫ E.functor.map l := by
    change f ≫ E.counitIso.inv.app X ≫ E.functor.map p.hom =
      (E.counitIso.inv.app X ≫ E.functor.map p.hom) ≫ E.functor.map l
    have hn := E.counitIso.inv.naturality f
    dsimp only [Functor.id_map, Functor.comp_map] at hn
    rw [reassoc_of% hn, ← E.functor.map_comp, hp,
      E.functor.map_comp, Category.assoc]
  have hc' : E.functor.map l ≫ c.inv = c.inv ≫ f := by
    calc
      _ = c.inv ≫ (c.hom ≫ E.functor.map l) ≫ c.inv := by simp
      _ = c.inv ≫ (f ≫ c.hom) ≫ c.inv := by rw [hc]
      _ = _ := by simp
  have ht : P.map (E.functor.map l) ≫ (P.map c.inv ≫ z) =
      (P.map c.inv ≫ z) ≫ g := by
    rw [← P.map_comp_assoc, hc', P.map_comp, Category.assoc, hz, Category.assoc]
  change E'.inverse.map (P.map (E.functor.map l)) ≫
    E'.inverse.map (P.map c.inv ≫ z) ≫ q.hom = _
  rw [← E'.inverse.map_comp_assoc, ht, E'.inverse.map_comp, Category.assoc, hq]

private theorem generalizedScalar_post
    {C D : Type u} [SmallCategory C] [SmallCategory D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    {R : Sheaf J CommRingCat.{u}} {S : Sheaf K CommRingCat.{u}}
    (e : RingedToposMorphism (localCoefficientRings R) (localCoefficientRings S))
    [e.inverse.IsEquivalence] (A : Sheaf K (Type u))
    (a : A ⟶ (presentationForget S).obj (SheafOfModules.unit (localCoefficientRings S))) :
    (Over.post e.inverse).map (generalizedScalarOver S A a) ≫
      (productPostIso e.inverse A).hom.app (ringSets (localCoefficientRings S)) ≫
        (productOver (e.inverse.obj A)).map e.ringMap =
    (productPostIso e.inverse A).hom.app (ringSets (localCoefficientRings S)) ≫
      (productOver (e.inverse.obj A)).map e.ringMap ≫
        generalizedScalarOver R (e.inverse.obj A) (e.inverse.map a ≫ e.ringMap) := by
  apply Over.OverMorphism.ext
  apply CartesianMonoidalCategory.hom_ext
  · simp only [Over.comp_left, Over.post_map, productPostIso,
      NatIso.ofComponents_hom_app, Over.isoMk_hom_left, productOver,
      Over.homMk_left, Category.assoc, CartesianMonoidalCategory.tensorHom_fst,
      Category.comp_id, CartesianMonoidalCategory.prodComparisonIso_hom,
      CartesianMonoidalCategory.prodComparison_fst]
    rw [← e.inverse.map_comp]
    rfl
  · simp only [Over.comp_left, Over.post_map, productPostIso,
      NatIso.ofComponents_hom_app, Over.isoMk_hom_left, productOver,
      Over.homMk_left, Category.assoc, CartesianMonoidalCategory.tensorHom_snd,
      ]
    ext U x
    change ((e.inverse.map ((generalizedScalarOver S A a).left) ≫
        e.inverse.map (CartesianMonoidalCategory.snd A (ringSets (localCoefficientRings S))) ≫
          e.ringMap).hom.app U x) =
      ((e.inverse.map (CartesianMonoidalCategory.fst A (ringSets (localCoefficientRings S))) ≫
        e.inverse.map a ≫ e.ringMap).hom.app U x) *
      ((e.inverse.map (CartesianMonoidalCategory.snd A (ringSets (localCoefficientRings S))) ≫
        e.ringMap).hom.app U x)
    rw [← e.inverse.map_comp_assoc, ← e.inverse.map_comp_assoc]
    exact e.ring_mul _ _ _ _ (fun _ _ ↦ rfl) U x

private theorem generalizedSlice_scalarSets
    {C D : Type u} [SmallCategory C] [SmallCategory D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    {R : Sheaf J CommRingCat.{u}} {S : Sheaf K CommRingCat.{u}}
    (e : RingedToposMorphism (localCoefficientRings R) (localCoefficientRings S))
    [e.inverse.IsEquivalence] (A : Sheaf K (Type u))
    (a : A ⟶ (presentationForget S).obj (SheafOfModules.unit (localCoefficientRings S)))
    (s : RingedSheafSliceAdjunctionData (localCoefficientRings S) A)
    (t : RingedSheafSliceAdjunctionData (localCoefficientRings R) (e.inverse.obj A)) :
    (sliceMorphism e A s t).inverse.map
        ((presentationForget (presentationElementRing S A)).map
          (presentationScalar _ (presentationGeneralizedSection S A a))) ≫
        (sliceMorphism e A s t).ringMap =
      (sliceMorphism e A s t).ringMap ≫
        (presentationForget (presentationElementRing R (e.inverse.obj A))).map
          (presentationScalar _ (presentationGeneralizedSection R (e.inverse.obj A)
            (e.inverse.map a ≫ e.ringMap))) := by
  let p := (productFibreIso A s).app (ringSets (localCoefficientRings S))
  let q := (productFibreIso (e.inverse.obj A) t).app (ringSets (localCoefficientRings R))
  let c := s.fibreEquivalence.counitIso.symm.app
      ((productOver A).obj (ringSets (localCoefficientRings S))) ≪≫
    s.fibreEquivalence.functor.mapIso p
  let z := (productPostIso e.inverse A).hom.app (ringSets (localCoefficientRings S)) ≫
    (productOver (e.inverse.obj A)).map e.ringMap
  let γ := t.fibreEquivalence.inverse.map ((Over.post e.inverse).map c.inv ≫ z) ≫ q.hom
  have hγ : γ = (sliceComparison e.inverse A s t).inv.app
      (ringSets (localCoefficientRings S)) ≫
        (elementSheafPullback (e.inverse.obj A)).map e.ringMap := by
    apply (cancel_epi ((sliceComparison e.inverse A s t).hom.app
      (ringSets (localCoefficientRings S)))).mp
    rw [Iso.hom_inv_id_app_assoc, sliceComparison_hom]
    change (productFibreIso (e.inverse.obj A) t).inv.app
        (e.inverse.obj (ringSets (localCoefficientRings S))) ≫
      t.fibreEquivalence.inverse.map
        ((productPostIso e.inverse A).inv.app (ringSets (localCoefficientRings S))) ≫
      t.fibreEquivalence.inverse.map ((Over.post e.inverse).map c.hom) ≫
      t.fibreEquivalence.inverse.map ((Over.post e.inverse).map c.inv ≫ z) ≫ q.hom = _
    dsimp only [z]
    simp only [← Functor.map_comp_assoc,
      Iso.hom_inv_id, Functor.map_id, Category.id_comp, Iso.inv_hom_id_app_assoc]
    dsimp only [q, Iso.app_hom]
    erw [(productFibreIso (e.inverse.obj A) t).hom.naturality]
    rw [Iso.inv_hom_id_app_assoc]
  have H := generalizedFibre_endomorphism s.fibreEquivalence t.fibreEquivalence
    (Over.post e.inverse) (generalizedScalarOver S A a)
    (generalizedScalarOver R (e.inverse.obj A) (e.inverse.map a ≫ e.ringMap))
    ((presentationForget (presentationElementRing S A)).map
      (presentationScalar _ (presentationGeneralizedSection S A a)))
    ((presentationForget (presentationElementRing R (e.inverse.obj A))).map
      (presentationScalar _ (presentationGeneralizedSection R (e.inverse.obj A)
        (e.inverse.map a ≫ e.ringMap)))) p q z
    (generalizedScalar_fibre S A a s)
    (generalizedScalar_fibre R (e.inverse.obj A) (e.inverse.map a ≫ e.ringMap) t)
    (generalizedScalar_post e A a)
  change (sliceEquivalence e.inverse A s t).functor.map
      ((presentationForget (presentationElementRing S A)).map
        (presentationScalar _ (presentationGeneralizedSection S A a))) ≫ γ = γ ≫
      (presentationForget (presentationElementRing R (e.inverse.obj A))).map
        (presentationScalar _ (presentationGeneralizedSection R (e.inverse.obj A)
          (e.inverse.map a ≫ e.ringMap))) at H
  rw [hγ] at H
  simpa only [sliceMorphism_inverse, sliceMorphism_ringMap] using H

private theorem generalizedSlice_scalarModules
    {C D : Type u} [SmallCategory C] [SmallCategory D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    {R : Sheaf J CommRingCat.{u}} {S : Sheaf K CommRingCat.{u}}
    (e : RingedToposMorphism (localCoefficientRings R) (localCoefficientRings S))
    [e.inverse.IsEquivalence] (A : Sheaf K (Type u))
    (a : A ⟶ (presentationForget S).obj (SheafOfModules.unit (localCoefficientRings S)))
    (s : RingedSheafSliceAdjunctionData (localCoefficientRings S) A)
    (t : RingedSheafSliceAdjunctionData (localCoefficientRings R) (e.inverse.obj A))
    (v : RingedPresentationAt (sliceMorphism e A s t)) :
    v.transport.modules.functor.map
        (presentationScalar _ (presentationGeneralizedSection S A a)) ≫
      v.transport.forward.unit.hom =
    v.transport.forward.unit.hom ≫
      presentationScalar _ (presentationGeneralizedSection R (e.inverse.obj A)
        (e.inverse.map a ≫ e.ringMap)) := by
  apply (presentationForget (presentationElementRing R (e.inverse.obj A))).map_injective
  simp only [Functor.map_comp, v.structural, Category.assoc]
  have hn := v.underlying.hom.naturality
    (presentationScalar (presentationElementRing S A) (presentationGeneralizedSection S A a))
  dsimp only [Functor.comp_map] at hn
  erw [reassoc_of% hn]
  exact congrArg (fun f ↦ v.underlying.hom.app
    (SheafOfModules.unit (localCoefficientRings (presentationElementRing S A))) ≫ f)
      (generalizedSlice_scalarSets e A a s t)

private theorem generalizedTest_changeIso
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (R : Sheaf J CommRingCat.{u}) (N : PresentationDerived R)
    (A B : Sheaf J (Type u)) (p : A ≅ B)
    (a : A ⟶ (presentationForget R).obj (SheafOfModules.unit (localCoefficientRings R)))
    (b : B ⟶ (presentationForget R).obj (SheafOfModules.unit (localCoefficientRings R)))
    (h : p.hom ≫ b = a) :
    IsZero (presentationGeneralizedTest R A a N) ↔
      IsZero (presentationGeneralizedTest R B b N) := by
  rw [presentationGeneralizedTest_isZero_iff, presentationGeneralizedTest_isZero_iff]
  have ha (U : Cᵒᵖ) (x : A.obj.obj U) :
      b.hom.app U (p.hom.hom.app U x) = a.hom.app U x :=
    congrArg (fun f ↦ f.hom.app U x) h
  constructor
  · intro hz U y
    have hx := hz U (p.inv.hom.app (op U) y)
    have hp : p.hom.hom.app (op U) (p.inv.hom.app (op U) y) = y :=
      congrArg (fun f ↦ f.hom.app (op U) y) p.inv_hom_id
    rw [← ha, hp] at hx
    exact hx
  · intro hz U x
    rw [← ha]
    exact hz U (p.hom.hom.app (op U) x)

private theorem generalizedSliceModules
    {C D : Type u} [SmallCategory C] [SmallCategory D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    {R : Sheaf J CommRingCat.{u}} {S : Sheaf K CommRingCat.{u}}
    (e : RingedToposMorphism (localCoefficientRings R) (localCoefficientRings S))
    [e.inverse.IsEquivalence] [IsIso e.ringMap]
    (w : RingedPresentationAt e) (A : Sheaf K (Type u))
    (s : RingedSheafSliceAdjunctionData (localCoefficientRings S) A)
    (t : RingedSheafSliceAdjunctionData (localCoefficientRings R) (e.inverse.obj A))
    (v : RingedPresentationAt (sliceMorphism e A s t)) :
    Nonempty (w.transport.modules.functor ⋙
      elementModulePullback (localCoefficientRings R) (e.inverse.obj A) ≅
      elementModulePullback (localCoefficientRings S) A ⋙ v.transport.modules.functor) := by
  let := sliceMorphism_ringIso e A s t
  exact ⟨(Functor.isoWhiskerLeft w.transport.modules.functor
    (restrictModulesIso (elementProjection (e.inverse.obj A))
      (localCoefficientRings R))).symm ≪≫
    moduleSquare (elementProjection (e.inverse.obj A)) (elementProjection A)
      e (sliceMorphism e A s t) (sliceMorphismComparison e A s t)
      (sliceMorphismComparison_structural e A s t)
      w.transport.modules w.pushforward v.transport.modules v.pushforward ≪≫
    Functor.isoWhiskerRight
      (restrictModulesIso (elementProjection A) (localCoefficientRings S))
      v.transport.modules.functor⟩

private def generalizedRestriction
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (R : Sheaf J CommRingCat.{u}) (A : Sheaf J (Type u)) :
    PresentationDerived R ⥤ PresentationDerived (presentationElementRing R A) :=
  presentationDerivedMap (elementModulePullback (localCoefficientRings R) A)
    (presentationElementRestriction_additive R A)
    (presentationElementRestriction_exact R A).1
    (presentationElementRestriction_exact R A).2.1

private theorem generalizedDerivedSlice
    {C D : Type u} [SmallCategory C] [SmallCategory D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    {R : Sheaf J CommRingCat.{u}} {S : Sheaf K CommRingCat.{u}}
    (e : RingedToposMorphism (localCoefficientRings R) (localCoefficientRings S))
    [e.inverse.IsEquivalence] [IsIso e.ringMap]
    (w : RingedPresentationAt e) (A : Sheaf K (Type u))
    (s : RingedSheafSliceAdjunctionData (localCoefficientRings S) A)
    (t : RingedSheafSliceAdjunctionData (localCoefficientRings R) (e.inverse.obj A))
    (v : RingedPresentationAt (sliceMorphism e A s t)) :
    Nonempty (w.transport.forward.derived ⋙ generalizedRestriction R (e.inverse.obj A) ≅
      generalizedRestriction S A ⋙ v.transport.forward.derived) := by
  let := HasDerivedCategory.standard (PresentationModules R)
  let := HasDerivedCategory.standard (PresentationModules S)
  let := HasDerivedCategory.standard
    (PresentationModules (presentationElementRing R (e.inverse.obj A)))
  let := HasDerivedCategory.standard (PresentationModules (presentationElementRing S A))
  let := w.transport.forward.additive
  let := w.transport.forward.finiteLimits
  let := w.transport.forward.finiteColimits
  let := v.transport.forward.additive
  let := v.transport.forward.finiteLimits
  let := v.transport.forward.finiteColimits
  let := presentationElementRestriction_additive R (e.inverse.obj A)
  let := (presentationElementRestriction_exact R (e.inverse.obj A)).1
  let := (presentationElementRestriction_exact R (e.inverse.obj A)).2.1
  let := presentationElementRestriction_additive S A
  let := (presentationElementRestriction_exact S A).1
  let := (presentationElementRestriction_exact S A).2.1
  obtain ⟨q⟩ := generalizedSliceModules e w A s t v
  let := HasDerivedCategory.standard
    (ringedSiteModules.{u} (elementRing (localCoefficientRings R) (e.inverse.obj A)))
  let := HasDerivedCategory.standard
    (ringedSiteModules.{u} (elementRing (localCoefficientRings S) A))
  exact ⟨(Functor.mapDerivedCategoryCompIso _ _).symm ≪≫
    Functor.mapDerivedCategoryNatIso q ≪≫ Functor.mapDerivedCategoryCompIso _ _⟩

/-- A ringed equivalence transports one generalized scalar localization test.
Source: Stacks Project, algebraization.tex, Tag 099J, with sites-modules.tex, Tags 04IE and 04J4.
(blueprint: lem-weil-pbc-generalized-test-transport).
Proof: construct the slice equivalence and transport the product scalar through
its fibre comparison, then apply the exact module and localization squares.
The scalar square identifies localizations, and the derived module square
identifies the second internal-Hom argument. Reflect zero objects through the
resulting derived equivalence and change the indexing sheaf along the given isomorphism. -/
theorem presentation_generalized_test_transport
    {C D : Type u} [SmallCategory C] [SmallCategory D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    {R : Sheaf J CommRingCat.{u}} {S : Sheaf K CommRingCat.{u}}
    (e : RingedToposMorphism (localCoefficientRings R) (localCoefficientRings S))
    [e.inverse.IsEquivalence] [IsIso e.ringMap]
    (w : RingedPresentationAt e) (N : PresentationDerived S)
    (A : Sheaf K (Type u)) (B : Sheaf J (Type u))
    (p : e.inverse.obj A ≅ B)
    (a : A ⟶ (presentationForget S).obj (SheafOfModules.unit (localCoefficientRings S)))
    (b : B ⟶ (presentationForget R).obj (SheafOfModules.unit (localCoefficientRings R)))
    (h : p.hom ≫ b = e.inverse.map a ≫ e.ringMap) :
    IsZero (presentationGeneralizedTest S A a N) ↔
      IsZero (presentationGeneralizedTest R B b
        (w.transport.forward.derived.obj N)) := by
  obtain ⟨s⟩ := ringed_sheaf_slice_adjunction (localCoefficientRings S) A
  obtain ⟨t⟩ := ringed_sheaf_slice_adjunction (localCoefficientRings R) (e.inverse.obj A)
  let := sliceMorphism_ringIso e A s t
  obtain ⟨v⟩ := generalizedTransportAt (sliceMorphism e A s t)
  obtain ⟨q⟩ := generalizedDerivedSlice e w A s t v
  let := HasDerivedCategory.standard (PresentationModules (presentationElementRing S A))
  let := HasDerivedCategory.standard
    (PresentationModules (presentationElementRing R (e.inverse.obj A)))
  let := v.transport.forward.additive
  let := v.transport.forward.finiteLimits
  let := v.transport.forward.finiteColimits
  obtain ⟨l⟩ := generalizedTransportLocalizationTest v.transport.forward
    (presentationGeneralizedSection S A a)
    (presentationGeneralizedSection R (e.inverse.obj A) (e.inverse.map a ≫ e.ringMap))
    (generalizedSlice_scalarModules e A a s t v)
    ((generalizedRestriction S A).obj N)
    ((generalizedRestriction R (e.inverse.obj A)).obj (w.transport.forward.derived.obj N))
    (q.symm.app N)
  change v.transport.forward.derived.obj (presentationGeneralizedTest S A a N) ≅
    presentationGeneralizedTest R (e.inverse.obj A) (e.inverse.map a ≫ e.ringMap)
      (w.transport.forward.derived.obj N) at l
  have hv : IsZero (presentationGeneralizedTest S A a N) ↔
      IsZero (presentationGeneralizedTest R (e.inverse.obj A) (e.inverse.map a ≫ e.ringMap)
        (w.transport.forward.derived.obj N)) := by
    let : v.transport.forward.derived.IsEquivalence :=
      inferInstanceAs v.transport.modules.functor.mapDerivedCategory.IsEquivalence
    constructor
    · intro hz
      exact l.isZero_iff.mp (v.transport.forward.derived.map_isZero hz)
    · intro hz
      exact IsZero.of_full_of_faithful_of_isZero v.transport.forward.derived _
        (l.isZero_iff.mpr hz)
  exact hv.trans (generalizedTest_changeIso R (w.transport.forward.derived.obj N)
    (e.inverse.obj A) B p (e.inverse.map a ≫ e.ringMap) b h)
end CategoryTheory
