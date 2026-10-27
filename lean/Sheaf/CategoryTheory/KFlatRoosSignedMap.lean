/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.CategoryTheory.KFlatAugmentedRoosDefinitions
public import Sheaf.CategoryTheory.InjectiveTowerRoosShifts

/-! # The signed tensor map between strict Roos fibres -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe a b
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated MonoidalCategory
open CochainComplex HomologicalComplex
namespace CategoryTheory.KFlatAugmentedRoos.GenericSigned
variable (M : Type a) [Category.{b} M] [Abelian M]
  [MonoidalCategory M] [MonoidalPreadditive M] [HasCoproducts.{0} M]
  [HasCountableProducts M] [HasLimitsOfShape ℕᵒᵖ M]

local instance genericTotalExists (A B : CochainComplex M ℤ) :
    HomologicalComplex.HasMapBifunctor A B (curriedTensor M) (.up ℤ) := inferInstance

/-- Total tensor commutes with the mapping cocone through the canonical signed shift
and cone comparisons. -/
def tensorCoconeIso (A U V : CochainComplex M ℤ) (f : U ⟶ V) :
    ((curriedTensor M).map₂CochainComplex.obj A).obj (mappingCocone f) ≅
      mappingCocone (((curriedTensor M).map₂CochainComplex.obj A).map f) :=
  mapBifunctorShift₂Iso A (mappingCone f) (curriedTensor M) (-1) ≪≫
    (shiftFunctor _ (-1 : ℤ)).mapIso (mapBifunctorMappingCone₂Iso A f (curriedTensor M))

/-- The map between tensor Roos fibres induced by a commuting product square. -/
def signedFiberMap (A : CochainComplex M ℤ)
    (I J : CochainComplex (ℕᵒᵖ ⥤ M) ℤ)
    (b : ((curriedTensor M).map₂CochainComplex.obj A).obj (roosP I) ⟶ roosP J)
    (hb : ((curriedTensor M).map₂CochainComplex.obj A).map (roosU I) ≫ b = b ≫ roosU J) :
    ((curriedTensor M).map₂CochainComplex.obj A).obj (roosF.obj I) ⟶ roosF.obj J :=
  (tensorCoconeIso M A _ _ (roosU I)).hom ≫
    (mappingCone.map _ _ b b hb)⟦(-1 : ℤ)⟧'

omit [MonoidalCategory M] [MonoidalPreadditive M] [HasCoproducts M]
  [HasCountableProducts M] [HasLimitsOfShape ℕᵒᵖ M] in
@[reassoc] private lemma coneMap_fst (U V : CochainComplex M ℤ)
    (f : U ⟶ U) (g : V ⟶ V) (b : U ⟶ V) (hb : f ≫ b = b ≫ g) (n : ℤ) :
    (mappingCone.map f g b b hb).f n ≫ (mappingCone.fst g).1.v n (n + 1) rfl =
      (mappingCone.fst f).1.v n (n + 1) rfl ≫ b.f (n + 1) := by
  apply mappingCone.ext_from f (n + 1) n rfl
  · simp [mappingCone.map, HomComplex.Cochain.zero_cochain_comp_v, Category.assoc]
  · simp [mappingCone.map, Category.assoc]

omit [HasCountableProducts M] [HasLimitsOfShape ℕᵒᵖ M] in
@[reassoc] private lemma tensorCone_fst (A U : CochainComplex M ℤ) (f : U ⟶ U)
    (p q n : ℤ) (hpq : p + q = n) :
    ιMapBifunctor A (mappingCone f) (curriedTensor M) p q n hpq ≫
      (mapBifunctorMappingCone₂Iso A f (curriedTensor M)).hom.f n ≫
        (mappingCone.fst (((curriedTensor M).map₂CochainComplex.obj A).map f)).1.v n (n + 1) rfl =
      p.negOnePow • (((curriedTensor M).obj (A.X p)).map
        ((mappingCone.fst f).1.v q (q + 1) rfl) ≫
          ιMapBifunctor A U (curriedTensor M) p (q + 1) (n + 1) (by omega)) := by
  dsimp only [mapBifunctorMappingCone₂Iso, mapBifunctorMappingCone₂Iso.hom]
  erw [mappingCone.lift_f_fst_v]
  exact mapBifunctorMappingCone₂Iso.ι_p₁₀_v A f (curriedTensor M) p q n hpq
    (n + 1) rfl (q + 1) rfl

omit [MonoidalCategory M] [MonoidalPreadditive M] [HasCoproducts M]
  [HasCountableProducts M] [HasLimitsOfShape ℕᵒᵖ M] in
private lemma coneProjection (U : CochainComplex M ℤ) (f : U ⟶ U) (q : ℤ) :
    (homotopyCofiber.XIsoBiprod f q (q + 1) rfl).hom ≫ biprod.fst =
      (mappingCone.fst f).1.v q (q + 1) rfl := by rfl

omit [MonoidalCategory M] [MonoidalPreadditive M] [HasCoproducts M]
  [HasCountableProducts M] [HasLimitsOfShape ℕᵒᵖ M] in
@[reassoc] private lemma coneMap_snd (U V : CochainComplex M ℤ)
    (f : U ⟶ U) (g : V ⟶ V) (b : U ⟶ V) (hb : f ≫ b = b ≫ g) (n : ℤ) :
    (mappingCone.map f g b b hb).f n ≫ (mappingCone.snd g).v n n (add_zero n) =
      (mappingCone.snd f).v n n (add_zero n) ≫ b.f n := by
  apply mappingCone.ext_from f (n + 1) n rfl
  · simp [mappingCone.map, HomComplex.Cochain.zero_cochain_comp_v, Category.assoc]
  · simp [mappingCone.map, Category.assoc]

omit [HasCountableProducts M] [HasLimitsOfShape ℕᵒᵖ M] in
@[reassoc] private lemma tensorCone_snd (A U : CochainComplex M ℤ)
    (f : U ⟶ U) (p q n : ℤ) (hpq : p + q = n) :
    ιMapBifunctor A (mappingCone f) (curriedTensor M) p q n hpq ≫
      (mapBifunctorMappingCone₂Iso A f (curriedTensor M)).hom.f n ≫
        (mappingCone.snd (((curriedTensor M).map₂CochainComplex.obj A).map f)).v n n (add_zero n) =
      ((curriedTensor M).obj (A.X p)).map ((mappingCone.snd f).v q q (add_zero q)) ≫
        ιMapBifunctor A U (curriedTensor M) p q n hpq := by
  dsimp only [mapBifunctorMappingCone₂Iso, mapBifunctorMappingCone₂Iso.hom]
  erw [mappingCone.lift_f_snd_v]
  exact mapBifunctorMappingCone₂Iso.ι_p₂_v A f (curriedTensor M) p q n hpq

omit [MonoidalCategory M] [MonoidalPreadditive M] [HasCoproducts M]
  [HasCountableProducts M] [HasLimitsOfShape ℕᵒᵖ M] in
private lemma coneProjection_snd (U : CochainComplex M ℤ)
    (f : U ⟶ U) (q : ℤ) :
    (homotopyCofiber.XIsoBiprod f q (q + 1) rfl).hom ≫ biprod.snd =
      (mappingCone.snd f).v q q (add_zero q) := by
  simp only [mappingCone.snd, HomComplex.Cochain.ofHoms_v]
  apply (cancel_epi (homotopyCofiber.XIsoBiprod f q (q + 1) rfl).inv).1
  apply biprod.hom_ext'
  · simp only [Iso.inv_hom_id_assoc, biprod.inl_snd]
    rw [← Category.assoc, homotopyCofiber.inl_XIsoBiprod_inv]
    change _ = homotopyCofiber.inlX f (q + 1) q rfl ≫ homotopyCofiber.sndX f q
    exact (homotopyCofiber.inlX_sndX f (q + 1) q rfl).symm
  · simp only [Iso.inv_hom_id_assoc, biprod.inr_snd]
    rw [← Category.assoc, homotopyCofiber.inr_XIsoBiprod_inv]
    change _ = homotopyCofiber.inrX f q ≫ homotopyCofiber.sndX f q
    exact (homotopyCofiber.inrX_sndX f q).symm


omit [MonoidalCategory M] [MonoidalPreadditive M] [HasCoproducts M] in
@[reassoc] private lemma inclusion_fst
    (I : CochainComplex (ℕᵒᵖ ⥤ M) ℤ) (n : ℤ) :
    (roosι I).f (n + 1) ≫ (roosχ I n).hom ≫ biprod.fst = 0 := by
  rw [← Category.assoc, roosι_χ, biprod.lift_fst]

omit [MonoidalCategory M] [MonoidalPreadditive M] [HasCoproducts M] in
@[reassoc] private lemma inclusion_snd
    (I : CochainComplex (ℕᵒᵖ ⥤ M) ℤ) (n : ℤ) :
    (roosι I).f (n + 1) ≫ (roosχ I n).hom ≫ biprod.snd =
      (InjectiveTowerRoos.inclusion I).f (n + 1) := by
  rw [← Category.assoc, roosι_χ, biprod.lift_snd]

attribute [local implicit_reducible] roosF roosConeFunctor
  Functor.map₂HomologicalComplex mappingCocone

attribute [local irreducible] roosχ roosι towerTransitionEndomorphism signedFiberMap tensorCoconeIso
  mappingCone.map

/-- The strict signed tensor map on Roos fibres, with its full limit inclusion equation.
Source: Stacks sites-cohomology.tex Tags 06YM and 0941; the signed calculation in
steps 6--7 of lem-sfb-kflat-augmented-roos-comparison.
(blueprint: lem-sfb-kflat-roos-signed-map).
Proof: distribute total tensor over the two Roos summands and send (x,y) to
(b(x),(-1)^p b(y)) on the summand of tensor degree p. The commuting product square
makes these maps commute with the differentials: the shifted components in both
composites are b(a tensor Ux)-b(a tensor dy)+(-1)^(p+1)b(da tensor y).
The direct-sum universal property assembles the summands. On the ordinary limit
inclusion the shifted component vanishes and the product projections are the given
limit projections, proving the entire inclusion square. This works also for zero
complexes and arbitrary tensor degree, without any exact-products hypothesis. -/
theorem signedFiberMap_spec (A : CochainComplex M ℤ)
    (I J : CochainComplex (ℕᵒᵖ ⥤ M) ℤ)
    (b : ((curriedTensor M).map₂CochainComplex.obj A).obj (roosP I) ⟶ roosP J)
    (θ : ((curriedTensor M).map₂CochainComplex.obj A).obj (limit I.asFunctor) ⟶ limit J.asFunctor)
    (hb : ((curriedTensor M).map₂CochainComplex.obj A).map (roosU I) ≫ b = b ≫ roosU J)
    (hθ : ((curriedTensor M).map₂CochainComplex.obj A).map (InjectiveTowerRoos.inclusion I) ≫ b =
      θ ≫ InjectiveTowerRoos.inclusion J) :
    SignedCoordinates A I J b (signedFiberMap M A I J b hb) ∧
      ((curriedTensor M).map₂CochainComplex.obj A).map (roosι I) ≫
        signedFiberMap M A I J b hb = θ ≫ roosι J := by
  have hcoords : SignedCoordinates A I J b (signedFiberMap M A I J b hb) := by
    intro p q n hpq
    constructor
    · dsimp only [roosF, Functor.comp_obj, roosConeFunctor]
      unfold signedFiberMap tensorCoconeIso
      try dsimp only [Iso.trans_hom, Functor.mapIso_hom, HomologicalComplex.comp_f]
      simp only [Category.assoc]
      change _ ≫ (mapBifunctorShift₂Iso A (mappingCone (roosU I))
        (curriedTensor M) (-1)).hom.f (n + 1) ≫ _ = _
      erw [ι_mapBifunctorShift₂Iso_hom_f_assoc A (mappingCone (roosU I))
        (curriedTensor M) (-1) p (q + 1) (n + 1) (by omega) q n (by omega) (by omega)]
      simp only [shiftFunctor_map_f', roosχ, Iso.trans_hom, Category.assoc]
      simp only [Linear.units_smul_comp, Category.assoc]
      dsimp only [shiftFunctorObjXIso]
      erw [← HomologicalComplex.XIsoOfEq_inv_naturality_assoc
        (mapBifunctorMappingCone₂Iso A (roosU I) (curriedTensor M)).hom
        (by omega : n + 1 + -1 = n)]
      erw [← HomologicalComplex.XIsoOfEq_inv_naturality_assoc
        (mappingCone.map _ _ b b hb) (by omega : n + 1 + -1 = n)]
      try simp only [HomologicalComplex.XIsoOfEq_inv_comp_XIsoOfEq_hom_assoc,
        HomologicalComplex.XIsoOfEq_rfl, Iso.refl_hom, Category.id_comp]
      simp only [biprod.braiding, biprod.lift_snd]
      simp only [coneProjection]
      rw [coneMap_fst M _ _ _ _ b hb n]
      erw [tensorCone_fst_assoc M A (roosP I) (roosU I) p q n hpq]
      rw [MonoidalCategory.whiskerLeft_comp]
      simp only [Category.assoc]
      simp only [Linear.comp_units_smul, Linear.units_smul_comp,
        mul_neg_one, Int.negOnePow_neg, smul_smul, Int.units_mul_self, one_smul,
        Category.assoc]
      rfl
    · dsimp only [roosF, Functor.comp_obj, roosConeFunctor]
      unfold signedFiberMap tensorCoconeIso
      try dsimp only [Iso.trans_hom, Functor.mapIso_hom, HomologicalComplex.comp_f]
      simp only [Category.assoc]
      change _ ≫ (mapBifunctorShift₂Iso A (mappingCone (roosU I))
        (curriedTensor M) (-1)).hom.f (n + 1) ≫ _ = _
      erw [ι_mapBifunctorShift₂Iso_hom_f_assoc A (mappingCone (roosU I))
        (curriedTensor M) (-1) p (q + 1) (n + 1) (by omega) q n (by omega) (by omega)]
      simp only [shiftFunctor_map_f', roosχ, Iso.trans_hom, Category.assoc]
      simp only [Linear.units_smul_comp, Category.assoc]
      dsimp only [shiftFunctorObjXIso]
      erw [← HomologicalComplex.XIsoOfEq_inv_naturality_assoc
        (mapBifunctorMappingCone₂Iso A (roosU I) (curriedTensor M)).hom
        (by omega : n + 1 + -1 = n)]
      erw [← HomologicalComplex.XIsoOfEq_inv_naturality_assoc
        (mappingCone.map _ _ b b hb) (by omega : n + 1 + -1 = n)]
      try simp only [HomologicalComplex.XIsoOfEq_inv_comp_XIsoOfEq_hom_assoc,
        HomologicalComplex.XIsoOfEq_rfl, Iso.refl_hom, Category.id_comp]
      simp only [biprod.braiding, biprod.lift_fst]
      simp only [coneProjection_snd]
      rw [coneMap_snd M _ _ _ _ b hb n]
      erw [tensorCone_snd_assoc M A (roosP I) (roosU I) p q n hpq]
      rw [MonoidalCategory.whiskerLeft_comp]
      simp only [Category.assoc]
      simp only [mul_neg_one, Int.negOnePow_neg]
      rfl
  refine ⟨hcoords, ?_⟩
  apply HomologicalComplex.hom_ext
  intro k
  obtain ⟨n, rfl⟩ := (Equiv.addRight (1 : ℤ)).surjective k
  simp only [Equiv.coe_addRight, HomologicalComplex.comp_f]
  apply (cancel_mono (roosχ J n).hom).1
  apply biprod.hom_ext
  · apply HomologicalComplex.mapBifunctor.hom_ext (K₁ := A) (K₂ := limit I.asFunctor)
      (F := curriedTensor M) (c := .up ℤ)
    intro p t hpt
    obtain ⟨q, rfl⟩ := (Equiv.addRight (1 : ℤ)).surjective t
    simp only [Equiv.coe_addRight] at hpt ⊢
    change p + (q + 1) = n + 1 at hpt
    simp only [Category.assoc]
    erw [HomologicalComplex.ι_mapBifunctorMap_assoc]
    simp only [HomologicalComplex.id_f, Functor.map_id, NatTrans.id_app,
      Category.id_comp]
    simp only [curriedTensor_obj_map]
    rw [(hcoords p q n (by omega)).2]
    simp only [Linear.comp_units_smul]
    rw [← MonoidalCategory.whiskerLeft_comp_assoc]
    rw [inclusion_fst M I q]
    simp only [MonoidalPreadditive.whiskerLeft_zero, zero_comp,
      smul_zero, inclusion_fst M J n, comp_zero]
  · apply HomologicalComplex.mapBifunctor.hom_ext (K₁ := A) (K₂ := limit I.asFunctor)
      (F := curriedTensor M) (c := .up ℤ)
    intro p t hpt
    obtain ⟨q, rfl⟩ := (Equiv.addRight (1 : ℤ)).surjective t
    simp only [Equiv.coe_addRight] at hpt ⊢
    change p + (q + 1) = n + 1 at hpt
    simp only [Category.assoc]
    erw [HomologicalComplex.ι_mapBifunctorMap_assoc]
    simp only [HomologicalComplex.id_f, Functor.map_id, NatTrans.id_app,
      Category.id_comp]
    simp only [curriedTensor_obj_map]
    rw [(hcoords p q n (by omega)).1]
    rw [← MonoidalCategory.whiskerLeft_comp_assoc]
    rw [inclusion_snd M I q, inclusion_snd M J n]
    have h := congrArg (fun f ↦ f.f (n + 1)) hθ
    simp only [HomologicalComplex.comp_f] at h
    have h' := congrArg (ιMapBifunctor A (limit I.asFunctor) (curriedTensor M) p (q + 1)
      (n + 1) (by omega) ≫ ·) h
    erw [HomologicalComplex.ι_mapBifunctorMap_assoc] at h'
    simp only [HomologicalComplex.id_f, Functor.map_id, NatTrans.id_app,
      Category.id_comp] at h'
    simpa only [curriedTensor_obj_map,
      Category.assoc] using h' 

end CategoryTheory.KFlatAugmentedRoos.GenericSigned

namespace CategoryTheory.KFlatAugmentedRoos
open SheafOfModules.TotalTensorSigns
universe u v r
variable {C : Type u} [Category.{v} C] [EssentiallySmall.{r} C]
  {𝒥 : GrothendieckTopology C} (R : Sheaf 𝒥 CommRingCat.{r})

/-- Total tensor commutes with the mapping cocone through the canonical signed shift
and cone comparisons. -/
def tensorCoconeIso (A U V : CochainComplex (Modules R) ℤ) (f : U ⟶ V) :
    ((total R).obj A).obj (mappingCocone f) ≅
      mappingCocone (((total R).obj A).map f) :=
  shiftLeft R A (mappingCone f) (-1) ≪≫
    (shiftFunctor _ (-1 : ℤ)).mapIso (coneLeft R A f)

/-- The map between tensor Roos fibres induced by a commuting product square. -/
def signedFiberMap (A : CochainComplex (Modules R) ℤ)
    (I J : CochainComplex (ℕᵒᵖ ⥤ Modules R) ℤ)
    (b : ((total R).obj A).obj (roosP I) ⟶ roosP J)
    (hb : ((total R).obj A).map (roosU I) ≫ b = b ≫ roosU J) :
    ((total R).obj A).obj (roosF.obj I) ⟶ roosF.obj J :=
  (tensorCoconeIso R A _ _ (roosU I)).hom ≫
    (mappingCone.map _ _ b b hb)⟦(-1 : ℤ)⟧'

/-- The generic signed cone calculation specialized to module sheaves.
Source: Stacks Tags 0941 and 06YM (blueprint: lem-sfb-kflat-roos-signed-map).
Proof: use the generic calculation; its tensor, cone and shift maps are definitionally
those of the sheaf total tensor, so both coordinates and the whole square specialize. -/
theorem signedFiberMap_spec (A : CochainComplex (Modules R) ℤ)
    (I J : CochainComplex (ℕᵒᵖ ⥤ Modules R) ℤ)
    (b : ((total R).obj A).obj (roosP I) ⟶ roosP J)
    (θ : ((total R).obj A).obj (limit I.asFunctor) ⟶ limit J.asFunctor)
    (hb : ((total R).obj A).map (roosU I) ≫ b = b ≫ roosU J)
    (hθ : ((total R).obj A).map (InjectiveTowerRoos.inclusion I) ≫ b =
      θ ≫ InjectiveTowerRoos.inclusion J) :
    SignedCoordinates A I J b (signedFiberMap R A I J b hb) ∧
      ((total R).obj A).map (roosι I) ≫ signedFiberMap R A I J b hb = θ ≫ roosι J := by
  exact GenericSigned.signedFiberMap_spec (Modules R) A I J b θ hb hθ

end CategoryTheory.KFlatAugmentedRoos
