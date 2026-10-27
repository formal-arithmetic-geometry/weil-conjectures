/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.SixFunctors.RegularRoosKoszulData
import Sheaf.SixFunctors.PrincipalStrictLimitReflector
import all Sheaf.CategoryTheory.RingedStrictTowerHomotopyLimitIndependentCoefficients
import Mathlib.Tactic.TFAE

/-! # Regular quotient Roos completeness and the canonical Koszul unit

Source: Stacks Project, Tags 099B, 0A0E and 0941.
(blueprint: lem-sf-regular-roos-koszul-unit).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe c v r w
open CategoryTheory CategoryTheory.Limits Opposite
namespace CategoryTheory.Q4Core
universe a h g
variable {A : Type a} [Category.{h} A] [Abelian A]
  [HasLimitsOfShape ℕᵒᵖ A] [HasCountableProducts A]
  [HasDerivedCategory.{w} A] [HasCountableProducts (DerivedCategory.{w} A)]
  [IsGrothendieckAbelian.{g} (ℕᵒᵖ ⥤ A)] [HasDerivedCategory.{w} (ℕᵒᵖ ⥤ A)]


private theorem normalizedComparison
    (RF : DerivedCategory.{w} (ℕᵒᵖ ⥤ A) ⥤ DerivedCategory.{w} A)
    (η : CoreWork.L ⋙ DerivedCategory.Q ⟶ DerivedCategory.Q ⋙ RF)
    (hI : ∀ I, CochainComplex.IsKInjective I → IsIso (η.app I))
    (E : DerivedCategory.{w} (ℕᵒᵖ ⥤ A) ⥤ (ℕᵒᵖ ⥤ DerivedCategory.{w} A))
    (ε : DerivedCategory.Q ⋙ E ≅ CoreWork.evQ) (X : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) :
    η.app X ≫ (CoreWork.pNat RF η hI E ε).app (DerivedCategory.Q.obj X) =
      DerivedCategory.Q.map (CoreWork.inc.app X) ≫ CoreWork.pc.app X ≫
        CoreWork.DP.map (ε.inv.app X) := by
  let q := (CoreWork.q (A := A)).app X
  let I := (CoreWork.F (A := A)).obj X
  have hq : QuasiIso q := CoreWork.q_quasiIso X
  have hηI : IsIso (η.app I) := hI I inferInstance
  have (Y : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) :
      IsIso ((Functor.whiskerLeft (CoreWork.F (A := A)) η).app Y) := hI _ inferInstance
  have : IsIso (Functor.whiskerLeft (CoreWork.F (A := A)) η) :=
    NatIso.isIso_of_isIso_app _
  have : IsIso (CoreWork.evQ.map q) := by
    have : ∀ n : ℕᵒᵖ, IsIso ((CoreWork.evQ.map q).app n) := by
      intro n
      change IsIso (DerivedCategory.Q.map
        ((((evaluation ℕᵒᵖ A).obj n).mapHomologicalComplex (.up ℤ)).map q))
      infer_instance
    exact NatIso.isIso_of_isIso_app _
  have (Y : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) :
      IsIso ((Functor.whiskerRight (CoreWork.q (A := A)) CoreWork.evQ).app Y) := by
    have := CoreWork.q_quasiIso Y
    have : ∀ n : ℕᵒᵖ,
        IsIso ((CoreWork.evQ.map (CoreWork.q.app Y)).app n) := by
      intro n
      change IsIso (DerivedCategory.Q.map
        ((((evaluation ℕᵒᵖ A).obj n).mapHomologicalComplex (.up ℤ)).map
          (CoreWork.q.app Y)))
      infer_instance
    change IsIso (CoreWork.evQ.map (CoreWork.q.app Y))
    exact NatIso.isIso_of_isIso_app _
  have : IsIso (Functor.whiskerRight (CoreWork.q (A := A)) CoreWork.evQ) :=
    NatIso.isIso_of_isIso_app _
  have ha : η.app X ≫ (CoreWork.aIso RF η hI).inv.app X =
      DerivedCategory.Q.map (CoreWork.L.map q) := by
    have hn := η.naturality q
    change DerivedCategory.Q.map (CoreWork.L.map q) ≫ η.app I =
      η.app X ≫ RF.map (DerivedCategory.Q.map q) at hn
    dsimp only [CoreWork.aIso, Iso.trans_inv, Iso.symm_inv,
      Functor.isoWhiskerRight_inv, NatTrans.comp_app, Functor.whiskerRight_app,
      asIso_inv, asIso_hom, Functor.associator, NatTrans.id_app,
      Category.id_comp, Category.comp_id]
    simp only [Category.comp_id, NatIso.isIso_inv_app, Functor.whiskerLeft_app]
    change η.app X ≫ (RF.map (DerivedCategory.Q.map q) ≫ inv (η.app I)) = _
    rw [← Category.assoc, ← hn, Category.assoc, IsIso.hom_inv_id, Category.comp_id]
  have hb : (CoreWork.bIso E ε).hom.app X =
      CoreWork.pc.app I ≫ CoreWork.DP.map
        (inv (CoreWork.evQ.map q) ≫ ε.inv.app X) := by
    dsimp only [CoreWork.bIso, Iso.trans_hom, Iso.symm_hom,
      Functor.isoWhiskerRight_hom, NatTrans.comp_app, Functor.whiskerLeft_app,
      Functor.whiskerRight_app, asIso_hom, asIso_inv, Functor.associator,
      NatTrans.id_app, Category.id_comp, Category.comp_id]
    simp only [NatIso.isIso_inv_app, Functor.whiskerRight_app, Category.id_comp, Category.comp_id]
    rfl
  rw [CoreWork.pNat_app]
  change η.app X ≫ ((CoreWork.aIso RF η hI).inv.app X ≫
    DerivedCategory.Q.map (CoreWork.inc.app I) ≫ (CoreWork.bIso E ε).hom.app X) = _
  rw [← Category.assoc, ← Category.assoc, ha, ← Functor.map_comp]
  have hn : CoreWork.L.map q ≫ CoreWork.inc.app I =
      CoreWork.inc.app X ≫ CoreWork.P.map q := CoreWork.inc.naturality q
  have hn' : DerivedCategory.Q.map (CoreWork.P.map q) ≫ CoreWork.pc.app I =
      CoreWork.pc.app X ≫ CoreWork.DP.map (CoreWork.evQ.map q) :=
    CoreWork.pc.naturality q
  rw [hn, Functor.map_comp, hb]
  simp only [Category.assoc]
  rw [reassoc_of% hn']
  have he : CoreWork.DP.map (CoreWork.evQ.map q) ≫
      CoreWork.DP.map (inv (CoreWork.evQ.map q) ≫ ε.inv.app X) =
        CoreWork.DP.map (ε.inv.app X) := by
    exact (CoreWork.DP.map_comp _ _).symm.trans
      (congrArg CoreWork.DP.map (IsIso.hom_inv_id_assoc _ _))
  exact congrArg (fun a ↦ DerivedCategory.Q.map (CoreWork.inc.app X) ≫
    CoreWork.pc.app X ≫ a) he


private theorem roos_normalized
    (RF : DerivedCategory.{w} (ℕᵒᵖ ⥤ A) ⥤ DerivedCategory.{w} A)
    (η : CoreWork.L ⋙ DerivedCategory.Q ⟶ DerivedCategory.Q ⋙ RF)
    (hI : ∀ I, CochainComplex.IsKInjective I → IsIso (η.app I))
    (X : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) :
    ∃ (p : RF.obj (DerivedCategory.Q.obj X) ⟶
        ∏ᶜ (fun n : ℕ ↦ DerivedCategory.Q.{w}.obj (X.asFunctor.obj (op n))))
      (δ : (∏ᶜ (fun n : ℕ ↦ DerivedCategory.Q.{w}.obj (X.asFunctor.obj (op n)))) ⟶
        (RF.obj (DerivedCategory.Q.obj X))⟦(1 : ℤ)⟧),
      IsDerivedLimitTriangle
        (fun n : ℕ ↦ DerivedCategory.Q.{w}.map
          (X.asFunctor.map (homOfLE (Nat.le_succ n)).op))
        (RF.obj (DerivedCategory.Q.obj X)) p δ ∧
      ∀ n, η.app X ≫ p ≫ Pi.π _ n = DerivedCategory.Q.map
        ((NatTrans.mapHomologicalComplex (lim.π (op n)) (.up ℤ)).app X) := by
  obtain ⟨E, ⟨ε⟩⟩ := evaluationData (A := A)
  let Z := DerivedCategory.Q.{w}.obj X
  let B := Pi.mapIso (fun n : ℕ ↦ (ε.app X).app (op n))
  let p := (CoreWork.pNat RF η hI E ε).app Z ≫ B.hom
  let δ := B.inv ≫ (CoreWork.deltaNat RF η hI E ε).app Z
  refine ⟨p, δ, ?_, ?_⟩
  · have ht := CoreWork.roos_Q RF η hI E ε X
    have hn := towerTransitionEndomorphism_natural_backward
      (fun n : ℕ ↦ (E.obj Z).map (homOfLE (Nat.le_succ n)).op)
      (fun n : ℕ ↦ DerivedCategory.Q.{w}.map
        (X.asFunctor.map (homOfLE (Nat.le_succ n)).op))
      (fun n ↦ (ε.app X).hom.app (op n))
      (fun n ↦ ((ε.app X).hom.naturality (homOfLE (Nat.le_succ n)).op).symm)
    exact Pretriangulated.isomorphic_distinguished _ ht _
      (Pretriangulated.Triangle.isoMk _ _ (Iso.refl _) B.symm B.symm
        (by simp [p, Z])
        (by
          change towerTransitionEndomorphism _ ≫ B.inv = B.inv ≫ _
          apply (Iso.comp_inv_eq B).2
          rw [Category.assoc]
          exact (Iso.eq_inv_comp B).2 hn)
        (by simp [δ, Z]))
  · intro n
    have hp := normalizedComparison RF η hI E ε X
    change η.app X ≫ (_ ≫ B.hom) ≫ Pi.π _ n = _
    rw [← Category.assoc, ← Category.assoc, hp]
    have hb : CoreWork.DP.map (ε.inv.app X) ≫ B.hom = 𝟙 _ := by
      change CoreWork.DP.map (ε.inv.app X) ≫ CoreWork.DP.map (ε.hom.app X) = _
      rw [← Functor.map_comp, Iso.inv_hom_id_app, Functor.map_id]
    simp only [Category.assoc]
    rw [reassoc_of% hb]
    change DerivedCategory.Q.map (CoreWork.inc.app X) ≫
      piComparison DerivedCategory.Q (fun n : ℕ ↦ X.asFunctor.obj (op n)) ≫ Pi.π _ n = _
    rw [piComparison_comp_π, ← Functor.map_comp]
    have hi : CoreWork.inc.app X ≫ Pi.π (fun n : ℕ ↦ X.asFunctor.obj (op n)) n =
        (NatTrans.mapHomologicalComplex (lim.π (op n)) (.up ℤ)).app X :=
      Pi.lift_π _ n
    exact congrArg DerivedCategory.Q.map hi


private theorem natural_unit
    {D E : Type*} [Category* D] [Category* E] {F G : D ⥤ E} (η : F ⟶ G)
    {X Y : D} (a : X ⟶ Y) {P P' : E} (f : P ⟶ P')
    (u : P ⟶ F.obj X) (u' : P' ⟶ G.obj X) (h : u ≫ η.app X = f ≫ u') :
    (u ≫ F.map a) ≫ η.app Y = f ≫ (u' ≫ G.map a) := by
  rw [Category.assoc, η.naturality, ← Category.assoc, h, Category.assoc]


private theorem tensorUnitComponent_natural
    {B : Type*} [Category* B] [Preadditive B] [MonoidalCategory B]
    [(MonoidalCategory.curriedTensor B).PreservesZeroMorphisms]
    [∀ Z, ((MonoidalCategory.curriedTensor B).obj Z).PreservesZeroMorphisms]
    (U P P' : CochainComplex B ℤ)
    [HomologicalComplex.HasMapBifunctor U P (MonoidalCategory.curriedTensor B) (.up ℤ)]
    [HomologicalComplex.HasMapBifunctor U P' (MonoidalCategory.curriedTensor B) (.up ℤ)]
    (u : MonoidalCategory.tensorUnit B ⟶ U.X 0) (f : P ⟶ P') (i : ℤ) :
    ((MonoidalCategory.leftUnitor (P.X i)).inv ≫
      MonoidalCategory.whiskerRight u (P.X i) ≫
      HomologicalComplex.ιMapBifunctor U P (MonoidalCategory.curriedTensor B)
        (.up ℤ) 0 i i (zero_add i)) ≫
      (HomologicalComplex.mapBifunctorMap (𝟙 U) f
        (MonoidalCategory.curriedTensor B) (.up ℤ)).f i =
      f.f i ≫ (MonoidalCategory.leftUnitor (P'.X i)).inv ≫
        MonoidalCategory.whiskerRight u (P'.X i) ≫
        HomologicalComplex.ιMapBifunctor U P' (MonoidalCategory.curriedTensor B)
          (.up ℤ) 0 i i (zero_add i) := by
  simp only [Category.assoc, HomologicalComplex.ι_mapBifunctorMap,
    HomologicalComplex.id_f, Functor.map_id, NatTrans.id_app, Category.id_comp,
    MonoidalCategory.curriedTensor_obj_map,
    ← MonoidalCategory.whisker_exchange_assoc,
    ← MonoidalCategory.leftUnitor_inv_naturality_assoc]


private theorem roos_transport
    {D : Type*} [Category* D] [HasZeroObject D] [HasShift D ℤ] [Preadditive D]
    [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]
    {K : ℕ → D} [HasProduct K] (f : ∀ n, K (n + 1) ⟶ K n)
    {P U : D} (i : P ≅ U) (p : U ⟶ ∏ᶜ K) (δ : ∏ᶜ K ⟶ U⟦(1 : ℤ)⟧)
    (ht : IsDerivedLimitTriangle f U p δ) :
    IsDerivedLimitTriangle f P (i.hom ≫ p) (δ ≫ i.inv⟦(1 : ℤ)⟧') := by
  exact Pretriangulated.isomorphic_distinguished _ ht _
    (Pretriangulated.Triangle.isoMk _ _ i (Iso.refl _) (Iso.refl _)
      (by simp) (by simp) (by simp [← Functor.map_comp]))


private theorem augmented_naturality
    {D T E F : Type*} [Category* D] [Category* T] [Category* E] [Category* F]
    {Δ : D ⥤ T} {L : T ⥤ D} (adj : Δ ⊣ L)
    (q : D ⥤ E) (qT : T ⥤ F) (RF : F ⥤ E) (η : L ⋙ q ⟶ qT ⋙ RF)
    {Q Q' : D} {X Y : T} (α : Δ.obj Q ⟶ X) (β : Δ.obj Q' ⟶ Y)
    (f : Q ⟶ Q') (g : X ⟶ Y) (h : α ≫ g = Δ.map f ≫ β) :
    (q.map (adj.unit.app Q ≫ L.map α) ≫ η.app X) ≫ RF.map (qT.map g) =
      q.map f ≫ (q.map (adj.unit.app Q' ≫ L.map β) ≫ η.app Y) := by
  have hn := η.naturality g
  dsimp only [Functor.comp_map] at hn
  rw [Category.assoc, ← hn, ← Category.assoc, ← q.map_comp]
  have hm : (adj.unit.app Q ≫ L.map α) ≫ L.map g =
      f ≫ (adj.unit.app Q' ≫ L.map β) := by
    rw [Category.assoc, ← L.map_comp, h, L.map_comp, ← Category.assoc]
    have hu := adj.unit.naturality f
    dsimp only [Functor.id_map, Functor.comp_map] at hu
    rw [← hu, Category.assoc]
  rw [hm, q.map_comp, Category.assoc]


private theorem completeness_criteria
    {D : Type*} [Category* D] (complete : D → Prop)
    {P V U : D} (c : V ≅ U) (v : P ⟶ V) (u : P ⟶ U)
    (hu : v ≫ c.hom = u) (hcrit : complete P ↔ IsIso v)
    (hV : complete V) (hiso : ∀ {X Y : D}, (X ≅ Y) → complete Y → complete X)
    (roos : Prop) (hr : roos → Nonempty (P ≅ V)) (hn : IsIso u → roos) :
    List.TFAE [roos, complete P, IsIso v, IsIso u] := by
  tfae_have 1 → 2 := fun h ↦ hiso (Classical.choice (hr h)) hV
  tfae_have 2 ↔ 3 := hcrit
  tfae_have 3 ↔ 4 := by
    rw [← hu]
    exact (isIso_comp_right_iff _ c.hom).symm
  tfae_have 4 → 1 := hn
  tfae_finish


private theorem comparison_iso
    {D : Type*} [Category* D] {P V V' U U' : D}
    (c : V ≅ U) (c' : V' ≅ U') (i : V ≅ V')
    (v : P ⟶ V) (v' : P ⟶ V') (u : P ⟶ U) (u' : P ⟶ U')
    (h : v ≫ c.hom = u) (h' : v' ≫ c'.hom = u') (hi : v ≫ i.hom = v') :
    ∃ j : U ≅ U', u ≫ j.hom = u' ∧ i.hom ≫ c'.hom = c.hom ≫ j.hom := by
  let j := c.symm ≪≫ i ≪≫ c'
  refine ⟨j, ?_, ?_⟩
  · rw [← h]
    change (v ≫ c.hom) ≫ (c.inv ≫ i.hom ≫ c'.hom) = _
    rw [Category.assoc, Iso.hom_inv_id_assoc, ← Category.assoc, hi, h']
  · simp only [j, Iso.trans_hom, Iso.symm_hom, Iso.hom_inv_id_assoc]

end CategoryTheory.Q4Core

namespace CategoryTheory.RegularRoosKoszul
attribute [local instance 20000] principalKoszulHasSheafCompose
variable {C : Type c} [Category.{v} C] {J : GrothendieckTopology C}
  (R : Sheaf J CommRingCat.{max c v r})
  [HasSheafify J AddCommGrpCat.{max c v r}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max c v r}]
  [HasDerivedCategory.{w} (Modules.{c, v, r} R)]
  [HasDerivedCategory.{w} (ℕᵒᵖ ⥤ Modules.{c, v, r} R)]

attribute [local instance] SheafOfModules.isMonoidal_W_independentCoefficients
attribute [local instance] SheafOfModules.monoidalCategory
attribute [local instance]
  SheafOfModules.preservesZeroMorphisms_curriedTensor_independentCoefficients
attribute [local instance]
  SheafOfModules.preservesZeroMorphisms_curriedTensor_obj_independentCoefficients

attribute [local irreducible] koszulRlim limitComparison constantUnit augmentedUnit
  koszulUnit quotientUnit comparison tensorTowerMap koszulMap quotientMap

attribute [local irreducible] globalSectionMultiplication endoPow
  principalKoszulTower principalReductionTower
attribute [local irreducible] derivedInternalHomOfUniverses
  ringedSectionLocalizationOfUniverses restriction



private theorem towerMap_comp
    {T U V : ℕᵒᵖ ⥤ CochainComplex (Modules.{c, v, r} R) ℤ}
    (a : T ⟶ U) (b : U ⟶ V) :
    koszulTowerComplexMap.{c, v, max c v r} R (a ≫ b) =
      koszulTowerComplexMap.{c, v, max c v r} R a ≫
        koszulTowerComplexMap.{c, v, max c v r} R b := by
  ext i n
  rfl


private theorem tensorTowerMap_naturality
    {Q Q' : CochainComplex (Modules.{c, v, r} R) ℤ} (f : Q ⟶ Q')
    {T U : ℕᵒᵖ ⥤ CochainComplex (Modules.{c, v, r} R) ℤ} (a : T ⟶ U) :
    tensorTowerMap.{c, v, r} R f T ≫
        Functor.whiskerRight a (koszulTensorFunctor.{c, v, max c v r} R Q') =
      Functor.whiskerRight a (koszulTensorFunctor.{c, v, max c v r} R Q) ≫
        tensorTowerMap.{c, v, r} R f U := by
  apply NatTrans.ext
  funext n
  unfold tensorTowerMap
  exact ((tensorComplexMap.{c, v, r} R f).naturality (a.app n)).symm


private theorem tensorUnit_naturality
    {Q Q' : CochainComplex (Modules.{c, v, r} R) ℤ} (f : Q ⟶ Q') :
    koszulTensorUnitInclusion.{c, v, max c v r} R Q ≫
        ((tensorComplexMap.{c, v, r} R f).app
          ((CochainComplex.singleFunctor _ 0).obj (SheafOfModules.unit (ring.{c, v, r} R)))) =
      f ≫ koszulTensorUnitInclusion.{c, v, max c v r} R Q' := by
  unfold tensorComplexMap
  apply HomologicalComplex.Hom.ext
  funext i
  dsimp only [koszulTensorUnitInclusion, koszulTensorUnitComponent]
  exact Q4Core.tensorUnitComponent_natural
    ((CochainComplex.singleFunctor (Modules.{c, v, r} R) 0).obj
      (SheafOfModules.unit (ring.{c, v, r} R))) Q Q'
    (HomologicalComplex.singleObjXSelf (.up ℤ) 0
      (SheafOfModules.unit (ring.{c, v, r} R))).inv f i


set_option backward.isDefEq.respectTransparency false in
private theorem augmentation_naturality
    {Q Q' : CochainComplex (Modules.{c, v, r} R) ℤ} (f : Q ⟶ Q')
    (t : (SheafOfModules.unit (ring.{c, v, r} R)).sections) :
    koszulStrictAugmentation.{c, v, max c v r} R Q t ≫
        tensorTowerMap.{c, v, r} R f (principalKoszulTower.{c, v, max c v r} R t) =
      (Functor.const ℕᵒᵖ).map f ≫ koszulStrictAugmentation.{c, v, max c v r} R Q' t := by
  apply NatTrans.ext
  funext n
  unfold tensorTowerMap
  dsimp only [NatTrans.comp_app, koszulStrictAugmentation,
    NatTrans.ofOpSequence_app, Functor.whiskerLeft_app, Functor.const_map_app,
    koszulRepresentativeAugmentation]
  have h := Q4Core.natural_unit (tensorComplexMap.{c, v, r} R f)
    (CochainComplex.mappingCone.inr
      (principalKoszulScalarComplex.{c, v, max c v r} R t n.unop))
    f (koszulTensorUnitInclusion.{c, v, max c v r} R Q)
    (koszulTensorUnitInclusion.{c, v, max c v r} R Q')
    (tensorUnit_naturality.{c, v, r} R f)
  unfold principalKoszulTower
  dsimp only [Functor.ofOpSequence_obj, principalKoszul]
  exact h



private theorem augmentedUnit_naturality
    {Q Q' : CochainComplex (Modules.{c, v, r} R) ℤ} (f : Q ⟶ Q')
    {T T' : ℕᵒᵖ ⥤ CochainComplex (Modules.{c, v, r} R) ℤ}
    (α : (Functor.const ℕᵒᵖ).obj Q ⟶ T)
    (α' : (Functor.const ℕᵒᵖ).obj Q' ⟶ T') (a : T ⟶ T')
    (h : α ≫ a = (Functor.const ℕᵒᵖ).map f ≫ α') :
    augmentedUnit.{c, v, r, w} R Q T α ≫
        (koszulRlim R).map (DerivedCategory.Q.map (koszulTowerComplexMap.{c, v, max c v r} R a)) =
      DerivedCategory.Q.map f ≫ augmentedUnit.{c, v, r, w} R Q' T' α' := by
  unfold augmentedUnit
  exact Q4Core.augmented_naturality
    ((constLimAdj : (Functor.const ℕᵒᵖ : Modules.{c, v, r} R ⥤ _) ⊣ lim).mapHomologicalComplex
      (.up ℤ)) DerivedCategory.Q DerivedCategory.Q (koszulRlim R)
    (limitComparison.{c, v, r, w} R)
    (koszulTowerComplexMap.{c, v, max c v r} R α)
    (koszulTowerComplexMap.{c, v, max c v r} R α') f
    (koszulTowerComplexMap.{c, v, max c v r} R a) (by
      rw [← towerMap_comp.{c, v, r} R, h, towerMap_comp.{c, v, r} R]
      rfl)


private theorem unit_comparison
    (P : DerivedCategory.{w} (Modules.{c, v, r} R))
    (Q : CochainComplex (Modules.{c, v, r} R) ℤ)
    (e : DerivedCategory.Q.{w}.obj Q ≅ P)
    (t : (SheafOfModules.unit (ring.{c, v, r} R)).sections) :
    koszulUnit.{c, v, r, w} R P Q e t ≫ comparison.{c, v, r, w} R Q t =
      quotientUnit.{c, v, r, w} R P Q e t := by
  unfold koszulUnit quotientUnit comparison
  have h := augmentedUnit_naturality.{c, v, r, w} R (𝟙 Q)
    (koszulStrictAugmentation.{c, v, max c v r} R Q t)
    (koszulStrictAugmentation.{c, v, max c v r} R Q t ≫
      koszulTensorTowerComparison.{c, v, max c v r} R Q t)
    (koszulTensorTowerComparison.{c, v, max c v r} R Q t) (by simp)
  simpa only [Functor.map_id, Category.id_comp, Category.assoc] using
    congrArg (fun z ↦ e.inv ≫ z) h


private theorem comparison_naturality
    {Q Q' : CochainComplex (Modules.{c, v, r} R) ℤ} (f : Q ⟶ Q')
    (t : (SheafOfModules.unit (ring.{c, v, r} R)).sections) :
    koszulMap.{c, v, r, w} R f t ≫ comparison.{c, v, r, w} R Q' t =
      comparison.{c, v, r, w} R Q t ≫ quotientMap.{c, v, r, w} R f t := by
  let F : CochainComplex (ℕᵒᵖ ⥤ Modules.{c, v, r} R) ℤ ⥤
      DerivedCategory.{w} (Modules.{c, v, r} R) := DerivedCategory.Q ⋙ koszulRlim R
  have h := congrArg (fun a ↦ F.map (koszulTowerComplexMap.{c, v, max c v r} R a))
    (tensorTowerMap_naturality.{c, v, r} R f (principalTowerComparison.{c, v, max c v r} R t))
  unfold koszulMap comparison quotientMap
  simpa only [koszulTensorTowerComparison, towerMap_comp.{c, v, r},
    Functor.map_comp, F, Functor.comp_map] using h


private theorem limit_data :
    (koszulRlim R).IsRightDerivedFunctor (limitComparison.{c, v, r, w} R)
      (HomologicalComplex.quasiIso (ℕᵒᵖ ⥤ Modules.{c, v, r} R) (.up ℤ)) ∧
    (∀ I : CochainComplex (ℕᵒᵖ ⥤ Modules.{c, v, r} R) ℤ,
      I.IsKInjective → IsIso ((limitComparison.{c, v, r, w} R).app I)) ∧
    HasCountableProducts (DerivedCategory.{w} (Modules.{c, v, r} R)) := by
  have h := Classical.choose_spec (Classical.choose_spec
    (ringedStrictTowerHomotopyLimitIndependentCoefficients.{w, c, v, max c v r} J
      (ring.{c, v, r} R) (fun U a b ↦ @mul_comm (R.obj.obj U) _ a b)))
  unfold limitComparison
  unfold koszulRlim
  exact
    And.intro h.1 (And.intro h.2.1 h.2.2.2.choose_spec.choose)


set_option backward.isDefEq.respectTransparency true in
private theorem normalized_roos
    [HasCountableProducts (DerivedCategory.{w} (Modules.{c, v, r} R))]
    (Q : CochainComplex (Modules.{c, v, r} R) ℤ)
    (T : ℕᵒᵖ ⥤ CochainComplex (Modules.{c, v, r} R) ℤ)
    (α : (Functor.const ℕᵒᵖ).obj Q ⟶ T) :
    ∃ (p : towerLimit.{c, v, r, w} R T ⟶
        ∏ᶜ (fun n : ℕ ↦ DerivedCategory.Q.{w}.obj (T.obj (op n))))
      (δ : (∏ᶜ (fun n : ℕ ↦ DerivedCategory.Q.{w}.obj (T.obj (op n)))) ⟶
        (towerLimit.{c, v, r, w} R T)⟦(1 : ℤ)⟧),
      IsDerivedLimitTriangle
        (fun n : ℕ ↦ DerivedCategory.Q.{w}.map (T.map (homOfLE (Nat.le_succ n)).op))
        (towerLimit.{c, v, r, w} R T) p δ ∧
      ∀ n, augmentedUnit.{c, v, r, w} R Q T α ≫ p ≫ Pi.π _ n =
        DerivedCategory.Q.map (α.app (op n)) := by
  let A := Modules.{c, v, r} R
  let : IsGrothendieckAbelian.{max c v r} A := moduleSheaves_grothendieck J (ring.{c, v, r} R)
  let : IsGrothendieckAbelian.{max c v r} (ℕᵒᵖ ⥤ A) := tower_grothendieck A
  have hh := Q4Core.roos_normalized.{w, (max c v r) + 1, max c v r, max c v r}
    (koszulRlim R) (limitComparison.{c, v, r, w} R)
    (limit_data.{c, v, r, w} R).2.1 (koszulTowerComplex.{c, v, max c v r} R T)
  rcases hh with ⟨p, δ, ht, hp⟩
  refine ⟨p, δ, ht, ?_⟩
  intro n
  let X := koszulTowerComplex.{c, v, max c v r} R T
  let L := (lim : (ℕᵒᵖ ⥤ A) ⥤ A).mapHomologicalComplex (.up ℤ)
  let μ : Q ⟶ L.obj X :=
    ((constLimAdj : (Functor.const ℕᵒᵖ : A ⥤ _) ⊣ lim).mapHomologicalComplex
      (.up ℤ)).unit.app Q ≫ L.map (koszulTowerComplexMap.{c, v, max c v r} R α)
  have hm : μ ≫ ((NatTrans.mapHomologicalComplex (lim.π (op n)) (.up ℤ)).app X) =
      α.app (op n) := by
    apply HomologicalComplex.hom_ext
    intro i
    simp [μ, L, Adjunction.mapHomologicalComplex_unit_app_f,
      koszulTowerComplexMap, constLimAdj]
  unfold augmentedUnit
  change (DerivedCategory.Q.map μ ≫ (limitComparison.{c, v, r, w} R).app X) ≫ p ≫ Pi.π _ n = _
  simp only [Category.assoc]
  rw [hp]
  exact (DerivedCategory.Q.map_comp μ
    ((NatTrans.mapHomologicalComplex (lim.π (op n)) (.up ℤ)).app X)).symm.trans
      (congrArg DerivedCategory.Q.map hm)



variable [∀ W : C, HasSheafify (J.over W) AddCommGrpCat.{max c v r}]
  [∀ W : C, HasSheafify (J.over W) CommRingCat.{max c v r}]
  [∀ W : C, (J.over W).WEqualsLocallyBijective AddCommGrpCat.{max c v r}]
  [∀ W : C, HasDerivedCategory.{w}
  (SheafOfModules.{max c v r} ((sheafCompose (J.over W)
    (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj (R.over W)))]


private theorem precompose_iso_bijective
    {D : Type*} [Category* D] {X P K L : D} (e : X ≅ P) (u : X ⟶ K)
    (hb : Function.Bijective (fun f : K ⟶ L ↦ u ≫ f)) :
    Function.Bijective (fun f : K ⟶ L ↦ (e.inv ≫ u) ≫ f) := by
  constructor
  · intro f g h
    apply hb.injective
    simpa only [Category.assoc, Iso.hom_inv_id_assoc] using
      congrArg (fun z ↦ e.hom ≫ z) h
  · intro f
    obtain ⟨g, hg⟩ := hb.surjective (e.hom ≫ f)
    refine ⟨g, ?_⟩
    simpa only [Category.assoc, Iso.inv_hom_id_assoc] using
      congrArg (fun z ↦ e.inv ≫ z) hg


private theorem representative_reflector
    (t : (SheafOfModules.unit (ring.{c, v, r} R)).sections)
    (hreg : Mono (globalSectionMultiplication.{c, v, max c v r} R t))
    (P : DerivedCategory.{w} (Modules.{c, v, r} R))
    (Q : CochainComplex (Modules.{c, v, r} R) ℤ)
    (e : DerivedCategory.Q.{w}.obj Q ≅ P) :
    locallyComplete.{c, v, r, w} R t (koszulCompletion R Q t) ∧
      ∀ L, locallyComplete.{c, v, r, w} R t L →
        Function.Bijective (fun f : koszulCompletion R Q t ⟶ L ↦
        koszulUnit.{c, v, r, w} R P Q e t ≫ f) := by
  obtain ⟨hc, hb⟩ := principal_strict_limit_reflector.{c, v, r, w} R t hreg Q
  refine ⟨hc, fun L hL ↦ ?_⟩
  unfold koszulUnit
  have hh := hb L hL
  unfold koszulUnit at hh
  simp only [Iso.refl_inv, Category.id_comp] at hh
  exact precompose_iso_bijective e _ hh


private theorem reflection_unit_iff
    {D : Type*} [Category* D] (complete : D → Prop)
    (hiso : ∀ {X Y : D}, (X ≅ Y) → complete Y → complete X)
    {P K : D} (u : P ⟶ K) (hc : complete K)
    (hb : ∀ L, complete L → Function.Bijective (fun f : K ⟶ L ↦ u ≫ f)) :
    complete P ↔ IsIso u := by
  constructor
  · intro hP
    obtain ⟨v, hv⟩ := (hb P hP).surjective (𝟙 P)
    have hvu : v ≫ u = 𝟙 K := (hb K hc).injective (by simp [← Category.assoc, hv])
    exact ⟨⟨v, hv, hvu⟩⟩
  · intro hu
    exact hiso (asIso u) hc


private theorem reflection_iso
    {D : Type*} [Category* D] {P K K' : D} (u : P ⟶ K) (u' : P ⟶ K')
    (hb : ∀ L : D, L = K ∨ L = K' → Function.Bijective (fun f : K ⟶ L ↦ u ≫ f))
    (hb' : ∀ L : D, L = K ∨ L = K' → Function.Bijective (fun f : K' ⟶ L ↦ u' ≫ f)) :
    ∃ i : K ≅ K', u ≫ i.hom = u' := by
  obtain ⟨f, hf⟩ := (hb K' (Or.inr rfl)).surjective u'
  obtain ⟨g, hg⟩ := (hb' K (Or.inl rfl)).surjective u
  have hfg : f ≫ g = 𝟙 K := (hb K (Or.inl rfl)).injective (by
    simp only [← Category.assoc, hf, hg, Category.comp_id])
  have hgf : g ≫ f = 𝟙 K' := (hb' K' (Or.inr rfl)).injective (by
    simp only [← Category.assoc, hg, hf, Category.comp_id])
  exact ⟨⟨f, g, hfg, hgf⟩, hf⟩


private theorem assemble_criterion
    {A D : Type*} [Category* A] [Category* D] (q : A ⥤ D) (V U : A → D)
    (κ : ∀ (P : D) (Q : A), (q.obj Q ≅ P) → (P ⟶ V Q))
    (υ : ∀ (P : D) (Q : A), (q.obj Q ≅ P) → (P ⟶ U Q))
    (c : ∀ Q, V Q ⟶ U Q) (complete : D → Prop) (valid : A → Prop)
    (roos : ∀ (P : D) (Q : A), (q.obj Q ≅ P) → Prop)
    (mV : ∀ {Q Q' : A}, (Q ⟶ Q') → (V Q ⟶ V Q'))
    (mU : ∀ {Q Q' : A}, (Q ⟶ Q') → (U Q ⟶ U Q'))
    (hiso : ∀ {X Y : D}, (X ≅ Y) → complete Y → complete X)
    (hc : ∀ Q, valid Q → IsIso (c Q))
    (hu : ∀ P Q e, κ P Q e ≫ c Q = υ P Q e)
    (hreflect : ∀ P Q e, complete (V Q) ∧
      ∀ L, complete L → Function.Bijective (fun f : V Q ⟶ L ↦ κ P Q e ≫ f))
    (hr : ∀ P Q e, valid Q → roos P Q e → Nonempty (P ≅ V Q))
    (hn : ∀ P Q e, IsIso (υ P Q e) → roos P Q e)
    (hnat : ∀ P Q e Q' (f : Q ⟶ Q'),
      mV f ≫ c Q' = c Q ≫ mU f ∧
      κ P Q e ≫ mV f = e.inv ≫ q.map f ≫ κ (q.obj Q') Q' (Iso.refl _) ∧
      υ P Q e ≫ mU f = e.inv ≫ q.map f ≫ υ (q.obj Q') Q' (Iso.refl _)) :
    ∀ P Q e, valid Q → ∃ cP : V Q ≅ U Q,
      cP.hom = c Q ∧ κ P Q e ≫ cP.hom = υ P Q e ∧
      List.TFAE [roos P Q e, complete P, IsIso (κ P Q e), IsIso (υ P Q e)] ∧
      (∀ Q' e', valid Q' → ∃ (hV : V Q ≅ V Q') (hU : U Q ≅ U Q'),
        κ P Q e ≫ hV.hom = κ P Q' e' ∧ υ P Q e ≫ hU.hom = υ P Q' e' ∧
        cP.hom ≫ hU.hom = hV.hom ≫ c Q') ∧
      (∀ Q' (f : Q ⟶ Q'), mV f ≫ c Q' = cP.hom ≫ mU f ∧
        κ P Q e ≫ mV f = e.inv ≫ q.map f ≫ κ (q.obj Q') Q' (Iso.refl _) ∧
        υ P Q e ≫ mU f = e.inv ≫ q.map f ≫ υ (q.obj Q') Q' (Iso.refl _)) := by
  intro P Q e hQ
  let := hc Q hQ
  let cP := asIso (c Q)
  obtain ⟨hcomplete, hb⟩ := hreflect P Q e
  refine ⟨cP, rfl, hu P Q e, ?_, ?_, hnat P Q e⟩
  · exact Q4Core.completeness_criteria complete cP _ _ (hu P Q e)
      (reflection_unit_iff complete (fun i h ↦ hiso i h) _ hcomplete hb)
      hcomplete (fun i h ↦ hiso i h) _ (hr P Q e hQ) (hn P Q e)
  · intro Q' e' hQ'
    let := hc Q' hQ'
    let cP' := asIso (c Q')
    obtain ⟨hcomplete', hb'⟩ := hreflect P Q' e'
    obtain ⟨hV, hVunit⟩ := reflection_iso (κ P Q e) (κ P Q' e')
      (fun L h ↦ hb L (by rcases h with rfl | rfl <;> assumption))
      (fun L h ↦ hb' L (by rcases h with rfl | rfl <;> assumption))
    obtain ⟨hU, hUunit, hsquare⟩ := Q4Core.comparison_iso cP cP' hV _ _ _ _
      (hu P Q e) (hu P Q' e') hVunit
    exact ⟨hV, hU, hVunit, hUunit, hsquare.symm⟩

set_option maxHeartbeats 250000 in
-- The criterion carries unbounded towers, slice tests and three naturality equations.
/-- Regular quotient Roos completeness detects the specified Koszul and quotient units.

Source: Stacks Project, algebraization.tex, Tags 099B and 0A0E; sites-cohomology.tex,
Tag 0941; derived.tex, Tags 09T5 and 0FND
(blueprint: lem-sf-regular-roos-koszul-unit).

The four entries of `List.TFAE` are precisely (i)--(iv). A global section on the slice
is equivalent to a section over `W`, by evaluation at its terminal object `Over.mk (𝟙 W)`.
Since multiplication by `t` is monic, its image ideal is isomorphic to the unit module;
thus membership in `(t)O(W)` is precisely the displayed existence of a factor `y`.
All product instances are in the conclusion. None of them asserts exact products.

Proof:
1. Apply lem-pur-derived-complete-koszul-reconstruction to Q. The strict level quotient
maps are quasi-isomorphisms, giving exactly `comparison` as an isomorphism. Quotient after
the degree-zero Koszul inclusion is the actual quotient map. Applying total inverse limit
and the normalized adjunction of lem-coef-derived-tower-counit-projections gives the unit
equation. Tensor functoriality gives the comparison square and both unit naturalities.
2. Apply lem-sf-principal-strict-limit-reflector to the regular generator t. Its
strict unit is exactly `koszulUnit`. Hence (ii) iff (iii), and the unit equation with the
comparison isomorphism gives (iii) iff (iv).
3. Under (i), reconstruction supplies an isomorphism from P to the Koszul completion.
The latter is locally complete by the reflector; restriction and derived internal Hom
preserve this isomorphism and hence vanishing. Thus (i) implies (ii). No equality of this
existential isomorphism with the specified unit is used.
4. Under (iv), the proved generic strict-tower construction CoreWork.roos_Q supplies a
Roos triangle. Naturality along a K-injective resolution normalizes its actual limit
projections. Transport its first vertex along the
quotient unit. The ordinary constant/limit adjunction triangle identity identifies
its first components with the prescribed quotients. This gives (i).
5. For another K-flat representative use the reflector's Hom bijection in both directions.
Uniqueness gives inverse comparisons carrying the specified units to one another. Conjugate
by the quotient comparison to obtain the quotient-limit identification and its square.
No boundedness, finiteness, or exactness of sheaf products is used. -/
theorem regular_roos_koszul_unit
    (t : (SheafOfModules.unit (ring.{c, v, r} R)).sections)
    (_hreg : Mono (globalSectionMultiplication.{c, v, max c v r} R t)) :
    ∃ _hproducts : HasCountableProducts (DerivedCategory.{w} (Modules.{c, v, r} R)),
      ∀ (P : DerivedCategory.{w} (Modules.{c, v, r} R))
        (Q : CochainComplex (Modules.{c, v, r} R) ℤ)
        (e : DerivedCategory.Q.{w}.obj Q ≅ P)
        (_hQ : CochainComplex.IsKFlatIndependentCoefficients (R := R) Q),
      ∃ cP : koszulCompletion R Q t ≅ quotientLimit.{c, v, r, w} R Q t,
        cP.hom = comparison.{c, v, r, w} R Q t ∧
        koszulUnit.{c, v, r, w} R P Q e t ≫ cP.hom =
          quotientUnit.{c, v, r, w} R P Q e t ∧
        List.TFAE [
          (∃ (p : P ⟶ ∏ᶜ (fun n : ℕ ↦ DerivedCategory.Q.{w}.obj
                ((reductionTensorTower.{c, v, max c v r} R Q t).obj (op n))))
              (δ : (∏ᶜ (fun n : ℕ ↦ DerivedCategory.Q.{w}.obj
                ((reductionTensorTower.{c, v, max c v r} R Q t).obj (op n)))) ⟶ P⟦(1 : ℤ)⟧),
            IsDerivedLimitTriangle
              (fun n : ℕ ↦ DerivedCategory.Q.{w}.map
                ((reductionTensorTower.{c, v, max c v r} R Q t).map
                  (homOfLE (Nat.le_succ n)).op)) P p δ ∧
            ∀ n : ℕ, p ≫ Pi.π _ n =
              e.inv ≫ DerivedCategory.Q.{w}.map
                (koszulRepresentativeQuotient.{c, v, max c v r} R Q t n)),
          (∀ (W : C) (f : ((R.over W).obj ⋙ forget CommRingCat).sections),
            (∃ y : R.obj.obj (op W),
              (globalSectionMultiplication.{c, v, max c v r} R t).val.app (op W) y =
                f.val (op (Over.mk (𝟙 W)))) →
            IsZero ((derivedInternalHomOfUniverses.{max c v, v, r, w}
                (J.over W) (R.over W)).obj
              (op ((DerivedCategory.singleFunctor _ 0).obj
                (ringedSectionLocalizationOfUniverses.{max c v r, max c v, v} (R.over W) f)),
                (restriction.{c, v, r, w} R W).obj P))),
          IsIso (koszulUnit.{c, v, r, w} R P Q e t),
          IsIso (quotientUnit.{c, v, r, w} R P Q e t)] ∧
        (∀ (Q' : CochainComplex (Modules.{c, v, r} R) ℤ)
            (e' : DerivedCategory.Q.{w}.obj Q' ≅ P)
            (_hQ' : CochainComplex.IsKFlatIndependentCoefficients (R := R) Q'),
          ∃ (hV : koszulCompletion R Q t ≅ koszulCompletion R Q' t)
            (hU : quotientLimit.{c, v, r, w} R Q t ≅ quotientLimit.{c, v, r, w} R Q' t),
            koszulUnit.{c, v, r, w} R P Q e t ≫ hV.hom =
              koszulUnit.{c, v, r, w} R P Q' e' t ∧
            quotientUnit.{c, v, r, w} R P Q e t ≫ hU.hom =
              quotientUnit.{c, v, r, w} R P Q' e' t ∧
            cP.hom ≫ hU.hom = hV.hom ≫ comparison.{c, v, r, w} R Q' t) ∧
        (∀ (Q' : CochainComplex (Modules.{c, v, r} R) ℤ) (f : Q ⟶ Q'),
          koszulMap.{c, v, r, w} R f t ≫ comparison.{c, v, r, w} R Q' t =
            cP.hom ≫ quotientMap.{c, v, r, w} R f t ∧
          koszulUnit.{c, v, r, w} R P Q e t ≫ koszulMap.{c, v, r, w} R f t =
            e.inv ≫ DerivedCategory.Q.{w}.map f ≫
              koszulUnit.{c, v, r, w} R (DerivedCategory.Q.{w}.obj Q') Q' (Iso.refl _) t ∧
          quotientUnit.{c, v, r, w} R P Q e t ≫ quotientMap.{c, v, r, w} R f t =
            e.inv ≫ DerivedCategory.Q.{w}.map f ≫
              quotientUnit.{c, v, r, w} R (DerivedCategory.Q.{w}.obj Q') Q' (Iso.refl _) t) := by
  classical
  let := (limit_data.{c, v, r, w} R).2.2
  refine ⟨inferInstance, ?_⟩
  let roos (P : DerivedCategory.{w} (Modules.{c, v, r} R))
      (Q : CochainComplex (Modules.{c, v, r} R) ℤ)
      (e : DerivedCategory.Q.{w}.obj Q ≅ P) : Prop :=
    (∃ (p : P ⟶ ∏ᶜ (fun n : ℕ ↦ DerivedCategory.Q.{w}.obj
                ((reductionTensorTower.{c, v, max c v r} R Q t).obj (op n))))
              (δ : (∏ᶜ (fun n : ℕ ↦ DerivedCategory.Q.{w}.obj
                ((reductionTensorTower.{c, v, max c v r} R Q t).obj (op n)))) ⟶ P⟦(1 : ℤ)⟧),
            IsDerivedLimitTriangle
              (fun n : ℕ ↦ DerivedCategory.Q.{w}.map
                ((reductionTensorTower.{c, v, max c v r} R Q t).map
                  (homOfLE (Nat.le_succ n)).op)) P p δ ∧
            ∀ n : ℕ, p ≫ Pi.π _ n =
              e.inv ≫ DerivedCategory.Q.{w}.map
                (koszulRepresentativeQuotient.{c, v, max c v r} R Q t n))
  have hiso {M N} (i : M ≅ N)
      (h : locallyComplete.{c, v, r, w} R t N) :
      locallyComplete.{c, v, r, w} R t M := by
    unfold locallyComplete at h ⊢
    intro W f hf
    exact (h W f hf).of_iso
      ((derivedInternalHomOfUniverses.{max c v, v, r, w} (J.over W) (R.over W)).mapIso
        ((Iso.refl _).prod ((restriction.{c, v, r, w} R W).mapIso i)))
  have hc (Q : CochainComplex (Modules.{c, v, r} R) ℤ)
      (hQ : CochainComplex.IsKFlatIndependentCoefficients (R := R) Q) :
      IsIso (comparison.{c, v, r, w} R Q t) := by
    unfold comparison
    exact (derivedComplete_koszul_reconstruction.{c, v, max c v r, w}
      R t _hreg Q hQ).2.2.2.1
  have hr (P : DerivedCategory.{w} (Modules.{c, v, r} R))
      (Q : CochainComplex (Modules.{c, v, r} R) ℤ)
      (e : DerivedCategory.Q.{w}.obj Q ≅ P)
      (hQ : CochainComplex.IsKFlatIndependentCoefficients (R := R) Q)
      (h : roos P Q e) : Nonempty (P ≅ koszulCompletion R Q t) := by
    rcases h with ⟨pU, δU, ht, hp⟩
    obtain ⟨hV, hU, pV, δV, hv, ha, hreconstruct⟩ :=
      (derivedComplete_koszul_reconstruction.{c, v, max c v r, w} R t _hreg Q hQ).2.2.2.2.2
    obtain ⟨φ, _⟩ := hreconstruct P e pU δU ht hp
    exact ⟨φ⟩
  have hn (P : DerivedCategory.{w} (Modules.{c, v, r} R))
      (Q : CochainComplex (Modules.{c, v, r} R) ℤ)
      (e : DerivedCategory.Q.{w}.obj Q ≅ P)
      (hu : IsIso (quotientUnit.{c, v, r, w} R P Q e t)) : roos P Q e := by
    let := hu
    obtain ⟨pU, δU, ht, hp⟩ := normalized_roos.{c, v, r, w} R Q
      (reductionTensorTower.{c, v, max c v r} R Q t)
      (koszulStrictAugmentation.{c, v, max c v r} R Q t ≫
        koszulTensorTowerComparison.{c, v, max c v r} R Q t)
    let i := asIso (quotientUnit.{c, v, r, w} R P Q e t)
    refine ⟨i.hom ≫ pU, δU ≫ i.inv⟦(1 : ℤ)⟧', Q4Core.roos_transport _ i pU δU ht, ?_⟩
    intro n
    dsimp only [i, asIso_hom]
    unfold quotientUnit
    simp only [Category.assoc]
    rw [hp]
    exact congrArg (fun f ↦ e.inv ≫ DerivedCategory.Q.map f)
      (koszulRepresentativeAugmentation_quotient.{c, v, max c v r} R Q t n)
  have hnat (P : DerivedCategory.{w} (Modules.{c, v, r} R))
      (Q : CochainComplex (Modules.{c, v, r} R) ℤ)
      (e : DerivedCategory.Q.{w}.obj Q ≅ P)
      (Q' : CochainComplex (Modules.{c, v, r} R) ℤ) (f : Q ⟶ Q') :
      koszulMap.{c, v, r, w} R f t ≫ comparison.{c, v, r, w} R Q' t =
          comparison.{c, v, r, w} R Q t ≫ quotientMap.{c, v, r, w} R f t ∧
        koszulUnit.{c, v, r, w} R P Q e t ≫ koszulMap.{c, v, r, w} R f t =
          e.inv ≫ DerivedCategory.Q.{w}.map f ≫
            koszulUnit.{c, v, r, w} R (DerivedCategory.Q.{w}.obj Q') Q' (Iso.refl _) t ∧
        quotientUnit.{c, v, r, w} R P Q e t ≫ quotientMap.{c, v, r, w} R f t =
          e.inv ≫ DerivedCategory.Q.{w}.map f ≫
            quotientUnit.{c, v, r, w} R (DerivedCategory.Q.{w}.obj Q') Q' (Iso.refl _) t := by
    refine ⟨comparison_naturality.{c, v, r, w} R f t, ?_, ?_⟩
    · have h := augmentedUnit_naturality.{c, v, r, w} R f
        (koszulStrictAugmentation.{c, v, max c v r} R Q t)
        (koszulStrictAugmentation.{c, v, max c v r} R Q' t)
        (tensorTowerMap.{c, v, r} R f (principalKoszulTower.{c, v, max c v r} R t))
        (augmentation_naturality.{c, v, r} R f t)
      simpa only [koszulUnit, koszulMap, Iso.refl_inv, Category.id_comp, Category.assoc] using
        congrArg (fun z ↦ e.inv ≫ z) h
    · have h := augmentedUnit_naturality.{c, v, r, w} R f
        (koszulStrictAugmentation.{c, v, max c v r} R Q t ≫
          koszulTensorTowerComparison.{c, v, max c v r} R Q t)
        (koszulStrictAugmentation.{c, v, max c v r} R Q' t ≫
          koszulTensorTowerComparison.{c, v, max c v r} R Q' t)
        (tensorTowerMap.{c, v, r} R f (principalReductionTower.{c, v, max c v r} R t)) (by
          dsimp only [koszulTensorTowerComparison]
          rw [Category.assoc, ← tensorTowerMap_naturality.{c, v, r} R f
            (principalTowerComparison.{c, v, max c v r} R t), ← Category.assoc,
            augmentation_naturality.{c, v, r} R f t, Category.assoc])
      simpa only [quotientUnit, quotientMap, Iso.refl_inv, Category.id_comp, Category.assoc] using
        congrArg (fun z ↦ e.inv ≫ z) h
  have h := assemble_criterion DerivedCategory.Q
    (fun Q ↦ koszulCompletion R Q t) (fun Q ↦ quotientLimit.{c, v, r, w} R Q t)
    (fun P Q e ↦ koszulUnit.{c, v, r, w} R P Q e t)
    (fun P Q e ↦ quotientUnit.{c, v, r, w} R P Q e t)
    (fun Q ↦ comparison.{c, v, r, w} R Q t) (locallyComplete.{c, v, r, w} R t)
    (fun Q ↦ CochainComplex.IsKFlatIndependentCoefficients (R := R) Q) roos
    (fun {_ _} f ↦ koszulMap.{c, v, r, w} R f t)
    (fun {_ _} f ↦ quotientMap.{c, v, r, w} R f t)
    (fun i h ↦ hiso i h) hc (fun P Q e ↦ unit_comparison.{c, v, r, w} R P Q e t)
    (fun P Q e ↦ representative_reflector.{c, v, r, w} R t _hreg P Q e) hr hn hnat
  unfold locallyComplete at h
  exact h

end CategoryTheory.RegularRoosKoszul
