/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.SixFunctors.ClosedCostalkEtaleOperations
public import Sheaf.Algebra.Homology.RingedDerivedTensorNative
import WeilConjectures.AlgebraicGeometry.EtaleInverseImageModuleAdjunction
import WeilConjectures.AlgebraicGeometry.EtaleModuleRingIsoAdjunction
import all WeilConjectures.AlgebraicGeometry.EtaleModuleInverseImageTransport
import WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful
import WeilConjectures.AlgebraicGeometry.EtaleInverseImageExact
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Sheaf.CategoryTheory.AlgebraicInverseImage
import Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification

/-! # Native derived tensor and arbitrary étale inverse image

Source: Stacks, Modules on Sites, Tag 03EL; Cohomology on Sites, Tags 07A4 and 0G7E.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme

private theorem etaleModulePresentation {X Y : Scheme.{u}} (f : X ⟶ Y)
    (R : Sheaf Y.smallEtaleTopology CommRingCat.{u + 1}) :
    let S := (closedCostalkEtaleRingPullback f).obj R
    let P := SheafOfModules.toSheaf.{u + 1}
      ((sheafCompose Y.smallEtaleTopology
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R)
    let Q := SheafOfModules.toSheaf.{u + 1}
      ((sheafCompose X.smallEtaleTopology
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj S)
    ∃ (p : closedCostalkEtaleModules Y R ⥤ closedCostalkEtaleModules X S)
      (a : p ⊣ closedCostalkEtaleModulePush f R)
      (e : p ⋙ Q ≅ P ⋙ Etale.upperStar AddCommGrpCat.{u + 1} f),
      ∀ M N (h : p.obj M ⟶ N),
        P.map (a.homEquiv M N h) =
          (Etale.upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} f).homEquiv
            (P.obj M) (Q.obj N) (e.inv.app M ≫ Q.map h) := by
  dsimp only
  obtain ⟨Lr, ar, er, ea, L0, e0, a0, hr, ha, hact, hlin, _hm, _hu, _hc⟩ :=
    AlgebraicGeometry.etaleInverseImageModuleAdjunction X Y f R
  let c := (ar.leftAdjointUniq (closedCostalkEtaleRingAdjunction f)).app R
  have hc : ar.homEquiv R _ c.hom = (closedCostalkEtaleRingAdjunction f).unit.app R :=
    ar.homEquiv_leftAdjointUniq_hom_app (closedCostalkEtaleRingAdjunction f) R
  obtain ⟨p, e, t, a, _he, hm⟩ := AlgebraicGeometry.etaleModuleRingIsoAdjunction X Y f R
    ((closedCostalkEtaleRingPullback f).obj R) Lr ar
    ((closedCostalkEtaleRingAdjunction f).unit.app R) c hc L0 e0 hlin
  exact ⟨p, a, e, hm⟩

private theorem etaleModuleUnderlying {X Y : Scheme.{u}} (f : X ⟶ Y)
    (R : Sheaf Y.smallEtaleTopology CommRingCat.{u + 1})
    (p : closedCostalkEtaleModules Y R ⥤
      closedCostalkEtaleModules X ((closedCostalkEtaleRingPullback f).obj R))
    (a : p ⊣ closedCostalkEtaleModulePush f R) :
    let S := (closedCostalkEtaleRingPullback f).obj R
    let P := SheafOfModules.toSheaf.{u + 1}
      ((sheafCompose Y.smallEtaleTopology
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R)
    let Q := SheafOfModules.toSheaf.{u + 1}
      ((sheafCompose X.smallEtaleTopology
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj S)
    ∃ e : p ⋙ Q ≅ P ⋙ Etale.upperStar AddCommGrpCat.{u + 1} f,
      (∀ M, P.map (a.unit.app M) =
        (Etale.upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} f).unit.app (P.obj M) ≫
          (Etale.lowerStar AddCommGrpCat.{u + 1} f).map (e.inv.app M)) ∧
      (∀ N, Q.map (a.counit.app N) =
        e.hom.app ((closedCostalkEtaleModulePush f R).obj N) ≫
          (Etale.upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} f).counit.app (Q.obj N)) := by
  dsimp only
  let S := (closedCostalkEtaleRingPullback f).obj R
  let P := SheafOfModules.toSheaf.{u + 1}
    ((sheafCompose Y.smallEtaleTopology
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R)
  let Q := SheafOfModules.toSheaf.{u + 1}
    ((sheafCompose X.smallEtaleTopology
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj S)
  obtain ⟨p0, a0, e0, hm⟩ := etaleModulePresentation f R
  let t := a0.leftAdjointUniq a
  let e : p ⋙ Q ≅ P ⋙ Etale.upperStar AddCommGrpCat.{u + 1} f :=
    Functor.isoWhiskerRight t.symm Q ≪≫ e0
  have he (M) (N) (h : p.obj M ⟶ N) :
      P.map (a.homEquiv M N h) =
        (Etale.upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} f).homEquiv
          (P.obj M) (Q.obj N) (e.inv.app M ≫ Q.map h) := by
    have hh : a.homEquiv M N h = a0.homEquiv M N (t.hom.app M ≫ h) := by
      rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit, Functor.map_comp]
      rw [← Category.assoc, a0.unit_leftAdjointUniq_hom_app a M]
    rw [hh, hm]
    simp only [e, Iso.trans_inv, Functor.isoWhiskerRight_inv, NatTrans.comp_app,
      Functor.whiskerRight_app, Iso.symm_inv, Functor.map_comp, Category.assoc]
    rfl
  refine ⟨e, ?_⟩
  have h := AlgebraicGeometry.adjunctionForgetUnitCounit p (closedCostalkEtaleModulePush f R)
    (Etale.upperStar AddCommGrpCat.{u + 1} f) (Etale.lowerStar AddCommGrpCat.{u + 1} f)
    P Q a (Etale.upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} f) e (Iso.refl _)
    (by intro M N h; exact (Category.comp_id _).trans (he M N h))
  constructor
  · intro M
    exact (Category.comp_id _).symm.trans (h.1 M)
  · intro N
    have hn := h.2 N
    change Q.map (a.counit.app N) = e.hom.app _ ≫
      (Etale.upperStar AddCommGrpCat.{u + 1} f).map (𝟙 _) ≫ _ at hn
    rw [(Etale.upperStar AddCommGrpCat.{u + 1} f).map_id] at hn
    erw [Category.id_comp] at hn
    exact hn

private abbrev etaleForget (X : Scheme.{u})
    (R : Sheaf X.smallEtaleTopology CommRingCat.{u + 1}) :=
  SheafOfModules.toSheaf.{u + 1} ((sheafCompose X.smallEtaleTopology
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R)

private theorem etalePullExact {X Y : Scheme.{u}} (f : X ⟶ Y)
    (R : Sheaf Y.smallEtaleTopology CommRingCat.{u + 1})
    (p : closedCostalkEtaleModules Y R ⥤
      closedCostalkEtaleModules X ((closedCostalkEtaleRingPullback f).obj R))
    (a : p ⊣ closedCostalkEtaleModulePush f R) :
    PreservesFiniteLimits p ∧ PreservesFiniteColimits p := by
  obtain ⟨e, _, _⟩ := etaleModuleUnderlying f R p a
  let P := etaleForget Y R
  let Q := etaleForget X ((closedCostalkEtaleRingPullback f).obj R)
  have : PreservesFiniteLimits (p ⋙ Q) := preservesFiniteLimits_of_natIso e.symm
  have : PreservesFiniteColimits (p ⋙ Q) := preservesFiniteColimits_of_natIso e.symm
  exact ⟨preservesFiniteLimits_of_reflects_of_preserves p Q,
    preservesFiniteColimits_of_reflects_of_preserves p Q⟩


private abbrev etaleSetsAdj {X Y : Scheme.{u}} (f : X ⟶ Y) :=
  Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
    (MorphismProperty.Over.pullback @Etale ⊤ f) (Type (u + 1))
    (Y.smallGrothendieckTopology @Etale) (X.smallGrothendieckTopology @Etale)

private theorem etaleInverseImage_map_ext
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    {T : Sheaf Y.smallEtaleTopology (Type (u + 1))}
    {H : Sheaf X.smallEtaleTopology (Type (u + 1))}
    (a b : (etaleSetPullback f).obj T ⟶ H)
    (h : ∀ (U : Y.Etaleᵒᵖ) (x : T.obj.obj U),
      a.hom.app ((MorphismProperty.Over.pullback @Etale ⊤ f).op.obj U)
          (((etaleSetsAdj f).unit.app T).hom.app U x) =
      b.hom.app ((MorphismProperty.Over.pullback @Etale ⊤ f).op.obj U)
          (((etaleSetsAdj f).unit.app T).hom.app U x)) :
    a = b := by
  apply ((etaleSetsAdj f).homEquiv T H).injective
  ext U x
  exact h U x

private def binaryMap
    {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    (X Y Z : Sheaf J (Type w))
    (op : ∀ U : Cᵒᵖ, X.obj.obj U → Y.obj.obj U → Z.obj.obj U)
    (hn : ∀ {U V : Cᵒᵖ} (i : U ⟶ V) x y,
      op V (X.obj.map i x) (Y.obj.map i y) = Z.obj.map i (op U x y))
    {T : Sheaf J (Type w)} (a : T ⟶ X) (b : T ⟶ Y) : T ⟶ Z :=
  ⟨{ app := fun U ↦ ↾fun x ↦ op U (a.hom.app U x) (b.hom.app U x)
     naturality := by
       intro U V i
       ext x
       change op V (a.hom.app V (T.obj.map i x)) (b.hom.app V (T.obj.map i x)) = _
       have ha := congrArg (fun q ↦ q x) (a.hom.naturality i)
       have hb := congrArg (fun q ↦ q x) (b.hom.naturality i)
       change a.hom.app V (T.obj.map i x) = X.obj.map i (a.hom.app U x) at ha
       change b.hom.app V (T.obj.map i x) = Y.obj.map i (b.hom.app U x) at hb
       rw [ha, hb]
       exact hn i _ _ }⟩

private theorem etaleTransportBinary
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    {A B C : Sheaf Y.smallEtaleTopology (Type (u + 1))}
    {A' B' C' : Sheaf X.smallEtaleTopology (Type (u + 1))}
    (eA : (etaleSetPullback f).obj A ≅ A')
    (eB : (etaleSetPullback f).obj B ≅ B')
    (eC : (etaleSetPullback f).obj C ≅ C')
    (op : ∀ U : Y.Etaleᵒᵖ, A.obj.obj U → B.obj.obj U → C.obj.obj U)
    (op' : ∀ V : X.Etaleᵒᵖ, A'.obj.obj V → B'.obj.obj V → C'.obj.obj V)
    (hn : ∀ {U V : X.Etaleᵒᵖ} (i : U ⟶ V) x y,
      op' V (A'.obj.map i x) (B'.obj.map i y) = C'.obj.map i (op' U x y))
    (hu : ∀ (U : Y.Etaleᵒᵖ) x y,
      eC.hom.hom.app ((MorphismProperty.Over.pullback @Etale ⊤ f).op.obj U)
          (((etaleSetsAdj f).unit.app C).hom.app U
            (op U x y)) =
      op' ((MorphismProperty.Over.pullback @Etale ⊤ f).op.obj U)
        (eA.hom.hom.app ((MorphismProperty.Over.pullback @Etale ⊤ f).op.obj U)
          (((etaleSetsAdj f).unit.app A).hom.app U x))
        (eB.hom.hom.app ((MorphismProperty.Over.pullback @Etale ⊤ f).op.obj U)
          (((etaleSetsAdj f).unit.app B).hom.app U y)))
    (T : Sheaf Y.smallEtaleTopology (Type (u + 1))) (a : T ⟶ A) (b : T ⟶ B) (t : T ⟶ C)
    (ht : ∀ U x, t.hom.app U x = op U (a.hom.app U x) (b.hom.app U x)) :
    ∀ V x,
      eC.hom.hom.app V (((etaleSetPullback f).map t).hom.app V x) =
      op' V
        (eA.hom.hom.app V (((etaleSetPullback f).map a).hom.app V x))
        (eB.hom.hom.app V (((etaleSetPullback f).map b).hom.app V x)) := by
  let L := etaleSetPullback f
  let eta := (etaleSetsAdj f).unit
  have hh : L.map t ≫ eC.hom =
      binaryMap A' B' C' op' hn (L.map a ≫ eA.hom) (L.map b ≫ eB.hom) := by
    apply etaleInverseImage_map_ext f
    intro U x
    have ha := congrArg (fun q ↦ q.hom.app U x) (eta.naturality a)
    have hb := congrArg (fun q ↦ q.hom.app U x) (eta.naturality b)
    have hc := congrArg (fun q ↦ q.hom.app U x) (eta.naturality t)
    change eC.hom.hom.app _ ((L.map t).hom.app _ (eta.app T |>.hom.app U x)) =
      op' _ (eA.hom.hom.app _ ((L.map a).hom.app _ (eta.app T |>.hom.app U x)))
        (eB.hom.hom.app _ ((L.map b).hom.app _ (eta.app T |>.hom.app U x)))
    change (eta.app A).hom.app U (a.hom.app U x) =
      (L.map a).hom.app _ ((eta.app T).hom.app U x) at ha
    change (eta.app B).hom.app U (b.hom.app U x) =
      (L.map b).hom.app _ ((eta.app T).hom.app U x) at hb
    change (eta.app C).hom.app U (t.hom.app U x) =
      (L.map t).hom.app _ ((eta.app T).hom.app U x) at hc
    rw [← ha, ← hb, ← hc, ht]
    exact hu U _ _
  intro V x
  exact congrArg (fun q ↦ q.hom.app V x) hh



private theorem etaleUnderlyingUnits {X Y : Scheme.{u}} (f : X ⟶ Y)
    (R : Sheaf Y.smallEtaleTopology CommRingCat.{u + 1})
    (p : closedCostalkEtaleModules Y R ⥤
      closedCostalkEtaleModules X ((closedCostalkEtaleRingPullback f).obj R))
    (a : p ⊣ closedCostalkEtaleModulePush f R) :
    let S := (closedCostalkEtaleRingPullback f).obj R
    let L := etaleSetPullback f
    let FrY := sheafForget (D := CommRingCat.{u + 1}) Y.smallEtaleTopology
    let FrX := sheafForget (D := CommRingCat.{u + 1}) X.smallEtaleTopology
    let FaY := sheafForget (D := AddCommGrpCat.{u + 1}) Y.smallEtaleTopology
    let FaX := sheafForget (D := AddCommGrpCat.{u + 1}) X.smallEtaleTopology
    let FY := etaleForget Y R
    let FX := etaleForget X S
    ∃ (eR : L.obj (FrY.obj R) ≅ FrX.obj S)
      (eM : p ⋙ FX ⋙ FaX ≅ FY ⋙ FaY ⋙ L),
      (∀ (U : Y.Etaleᵒᵖ) (r : R.obj.obj U),
        eR.hom.hom.app ((MorphismProperty.Over.pullback @Etale ⊤ f).op.obj U)
          (((etaleSetsAdj f).unit.app (FrY.obj R)).hom.app U r) =
          ((closedCostalkEtaleRingAdjunction f).unit.app R).hom.app U r) ∧
      (∀ (M : closedCostalkEtaleModules Y R) (U : Y.Etaleᵒᵖ) (m : M.val.obj U),
        (eM.inv.app M).hom.app ((MorphismProperty.Over.pullback @Etale ⊤ f).op.obj U)
          (((etaleSetsAdj f).unit.app ((FY ⋙ FaY).obj M)).hom.app U m) =
          (a.unit.app M).val.app U m) := by
  dsimp only
  let S := (closedCostalkEtaleRingPullback f).obj R
  let FrY := sheafForget (D := CommRingCat.{u + 1}) Y.smallEtaleTopology
  let FrX := sheafForget (D := CommRingCat.{u + 1}) X.smallEtaleTopology
  let FaY := sheafForget (D := AddCommGrpCat.{u + 1}) Y.smallEtaleTopology
  let FaX := sheafForget (D := AddCommGrpCat.{u + 1}) X.smallEtaleTopology
  let FY := etaleForget Y R
  let FX := etaleForget X S
  obtain ⟨Lr, ar, er, ea, _LM, _e, _am, hr, ha, _hact, _hlin, _hm, _hu, _hc⟩ :=
    AlgebraicGeometry.etaleInverseImageModuleAdjunction X Y f R
  let c := (ar.leftAdjointUniq (closedCostalkEtaleRingAdjunction f)).app R
  let eR := (er.app R).symm ≪≫ FrX.mapIso c
  obtain ⟨ep, hup, _⟩ := etaleModuleUnderlying f R p a
  let eM : p ⋙ FX ⋙ FaX ≅ FY ⋙ FaY ⋙ etaleSetPullback f :=
    Functor.isoWhiskerRight ep FaX ≪≫ Functor.isoWhiskerLeft FY ea
  refine ⟨eR, eM, ?_, ?_⟩
  · intro U r
    have h := hr R S c.hom
    have hc : ar.homEquiv R S c.hom =
        (closedCostalkEtaleRingAdjunction f).unit.app R :=
      ar.homEquiv_leftAdjointUniq_hom_app (closedCostalkEtaleRingAdjunction f) R
    rw [hc] at h
    exact (congrArg (fun t ↦ t.hom.app U r) h).symm
  · intro M U m
    have h := ha (FY.obj M) (FX.obj (p.obj M)) (ep.inv.app M)
    rw [Adjunction.homEquiv_unit] at h
    have hu := hup M
    have hh := congrArg (fun t : FY.obj M ⟶
      FY.obj ((closedCostalkEtaleModulePush f R).obj (p.obj M)) ↦
        (FaY.map t).hom.app U m) hu
    exact (congrArg (fun t ↦ t.hom.app U m) h).symm.trans hh.symm

/-- The operation-graph argument of proEtaleAlgebraicInverseImage_exists, applied to
unit-normalized etale ring and module adjunctions. -/
private theorem etaleAlgebraicPresentation {X Y : Scheme.{u}} (f : X ⟶ Y)
    (R : Sheaf Y.smallEtaleTopology CommRingCat.{u + 1})
    (p : closedCostalkEtaleModules Y R ⥤
      closedCostalkEtaleModules X ((closedCostalkEtaleRingPullback f).obj R))
    (amod : p ⊣ closedCostalkEtaleModulePush f R) :
    ∃ I : SheafOfModules.AlgebraicInverseImage (etaleSetPullback f) R
      ((closedCostalkEtaleRingPullback f).obj R), I.modules = p := by
  let S := (closedCostalkEtaleRingPullback f).obj R
  obtain ⟨eR, eM, hr, hm⟩ := etaleUnderlyingUnits f R p amod
  refine ⟨{
    ringUnderlying := eR
    modules := p
    moduleUnderlying := eM
    ringAdd := ?_
    ringMul := ?_
    ringZero := ?_
    ringOne := ?_
    moduleAdd := ?_
    moduleZero := ?_
    moduleSMul := ?_
  }, rfl⟩
  · intro T a b t ht
    exact etaleTransportBinary f eR eR eR
      (fun U x y ↦ @Add.add (R.obj.obj U) inferInstance x y)
      (fun V x y ↦ @Add.add (S.obj.obj V) inferInstance x y)
      (fun i x y ↦ (S.obj.map i).hom.map_add x y |>.symm)
      (by
        intro U x y
        rw [hr, hr, hr]
        exact (((closedCostalkEtaleRingAdjunction f).unit.app R).hom.app U).hom.map_add
          x y) T a b t ht
  · intro T a b t ht
    exact etaleTransportBinary f eR eR eR
      (fun U x y ↦ @Mul.mul (R.obj.obj U) inferInstance x y)
      (fun V x y ↦ @Mul.mul (S.obj.obj V) inferInstance x y)
      (fun i x y ↦ (S.obj.map i).hom.map_mul x y |>.symm)
      (by
        intro U x y
        rw [hr, hr, hr]
        exact (((closedCostalkEtaleRingAdjunction f).unit.app R).hom.app U).hom.map_mul
          x y) T a b t ht
  · intro T a ha
    exact etaleTransportBinary f eR eR eR
      (fun U _ _ ↦ (0 : R.obj.obj U))
      (fun V _ _ ↦ (0 : S.obj.obj V))
      (fun i _ _ ↦ (S.obj.map i).hom.map_zero.symm)
      (by
        intro U x y
        rw [hr]
        exact (((closedCostalkEtaleRingAdjunction f).unit.app R).hom.app U).hom.map_zero)
      T a a a ha
  · intro T a ha
    exact etaleTransportBinary f eR eR eR
      (fun U _ _ ↦ (1 : R.obj.obj U))
      (fun V _ _ ↦ (1 : S.obj.obj V))
      (fun i _ _ ↦ (S.obj.map i).hom.map_one.symm)
      (by
        intro U x y
        rw [hr]
        exact (((closedCostalkEtaleRingAdjunction f).unit.app R).hom.app U).hom.map_one)
      T a a a ha
  · intro M T a b t ht
    exact etaleTransportBinary f (eM.app M).symm (eM.app M).symm
      (eM.app M).symm
      (fun U x y ↦ @Add.add (M.val.obj U) inferInstance x y)
      (fun V x y ↦ @Add.add ((p.obj M).val.obj V) inferInstance x y)
      (fun i x y ↦ ((p.obj M).val.map i).hom.map_add x y |>.symm)
      (by
        intro U x y
        change M.val.obj U at x y
        exact (hm M U (x + y)).trans
          ((((amod.unit.app M).val.app U).hom.map_add x y).trans
            (congrArg₂ (fun a b : (p.obj M).val.obj
              ((MorphismProperty.Over.pullback @Etale ⊤ f).op.obj U) ↦ a + b)
              (hm M U x).symm (hm M U y).symm)))
      T a b t ht
  · intro M T a ha
    exact etaleTransportBinary f (eM.app M).symm (eM.app M).symm
      (eM.app M).symm
      (fun U _ _ ↦ (0 : M.val.obj U))
      (fun V _ _ ↦ (0 : (p.obj M).val.obj V))
      (fun i _ _ ↦ ((p.obj M).val.map i).hom.map_zero.symm)
      (by
        intro U x y
        exact (hm M U 0).trans ((amod.unit.app M).val.app U).hom.map_zero)
      T a a a ha
  · intro M T a b t ht
    exact etaleTransportBinary f eR (eM.app M).symm (eM.app M).symm
      (fun U x y ↦ @SMul.smul (R.obj.obj U) (M.val.obj U) inferInstance x y)
      (fun V x y ↦ @SMul.smul (S.obj.obj V)
        ((p.obj M).val.obj V) inferInstance x y)
      (fun i x y ↦ ((p.obj M).val.map_smul i x y).symm)
      (by
        intro U x y
        change R.obj.obj U at x
        change M.val.obj U at y
        have hs : (amod.unit.app M).val.app U (x • y) =
            @SMul.smul (S.obj.obj
                ((MorphismProperty.Over.pullback @Etale ⊤ f).op.obj U))
              ((p.obj M).val.obj ((MorphismProperty.Over.pullback @Etale ⊤ f).op.obj U))
              inferInstance ((closedCostalkEtaleRingAdjunction f).unit.app R |>.hom.app U x)
              ((amod.unit.app M).val.app U y) :=
          ((amod.unit.app M).val.app U).hom.map_smul x y
        exact (hm M U (x • y)).trans (hs.trans
          (congrArg₂
            (fun (r : S.obj.obj ((MorphismProperty.Over.pullback @Etale ⊤ f).op.obj U))
              (m : (p.obj M).val.obj
                ((MorphismProperty.Over.pullback @Etale ⊤ f).op.obj U)) ↦ r • m)
            (hr U x).symm (hm M U y).symm)))
      T a b t ht


open SheafOfModules

private noncomputable def etaleScalarExtensionPresheaf
    {C : Type (u + 1)} [Category.{u} C] {J : GrothendieckTopology C}
    {R S : Sheaf J CommRingCat.{u + 1}} (c : R ⟶ S) :
    SheafOfModules.{u + 1} ((sheafCompose J (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R) ⥤
      PresheafOfModules.{u + 1}
      ((sheafCompose J (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj S).obj where
  obj M := changeOfRingsPresheaf.{u, u + 1, u + 1} c M
  map {M N} f :=
    { app := fun U ↦ (ModuleCat.extendScalars.{u + 1, u + 1, u + 1} (c.hom.app U).hom).map
        (f.val.app U)
      naturality := changeOfRingsHom_naturality.{u, u + 1, u + 1} c M f }
  map_id M := by
    ext U : 1
    simp
    rfl
  map_comp f g := by
    ext U : 1
    exact (ModuleCat.extendScalars.{u + 1, u + 1, u + 1} (c.hom.app U).hom).map_comp _ _

private theorem etaleScalarExtensionPresheaf_additive
    {C : Type (u + 1)} [Category.{u} C] {J : GrothendieckTopology C}
    {R S : Sheaf J CommRingCat.{u + 1}} (c : R ⟶ S) :
    (etaleScalarExtensionPresheaf c).Additive where
  map_add {M N} f g := by
    ext U : 1
    have : (ModuleCat.extendScalars.{u + 1, u + 1, u + 1} (c.hom.app U).hom).Additive :=
      (ModuleCat.extendRestrictScalarsAdj.{u + 1, u + 1, u + 1}
        (c.hom.app U).hom).left_adjoint_additive
    simpa only [etaleScalarExtensionPresheaf, add_val, PresheafOfModules.add_app] using
      (ModuleCat.extendScalars.{u + 1, u + 1, u + 1} (c.hom.app U).hom).map_add
        (f := f.val.app U) (g := g.val.app U)

private noncomputable def etaleScalarExtension
    {C : Type (u + 1)} [Category.{u} C] {J : GrothendieckTopology C}
    {R S : Sheaf J CommRingCat.{u + 1}} (c : R ⟶ S) :
    SheafOfModules.{u + 1} ((sheafCompose J (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R) ⥤
      SheafOfModules.{u + 1}
      ((sheafCompose J (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj S) :=
  etaleScalarExtensionPresheaf c ⋙ PresheafOfModules.sheafification.{u + 1}
    (𝟙 ((sheafCompose J (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj S).obj)

private theorem etaleScalarExtension_additive
    {C : Type (u + 1)} [Category.{u} C] {J : GrothendieckTopology C}
    {R S : Sheaf J CommRingCat.{u + 1}} (c : R ⟶ S) :
    (etaleScalarExtension c).Additive := by
  have hsheaf : (PresheafOfModules.sheafification.{u + 1}
      (𝟙 ((sheafCompose J (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj S).obj)).Additive :=
    (PresheafOfModules.sheafificationAdjunction.{u + 1} (𝟙 _)).left_adjoint_additive
  have := etaleScalarExtensionPresheaf_additive c
  dsimp only [etaleScalarExtension]
  infer_instance

set_option backward.isDefEq.respectTransparency false in
private noncomputable def etaleScalarExtensionPresheafIdIso
    {C : Type (u + 1)} [Category.{u} C] {J : GrothendieckTopology C}
    (R : Sheaf J CommRingCat.{u + 1})
    (M : SheafOfModules.{u + 1}
      ((sheafCompose J (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R)) :
    M.val ≅ (etaleScalarExtensionPresheaf (𝟙 R)).obj M := by
  refine PresheafOfModules.isoMk
    (fun U ↦ ((ModuleCat.extendScalarsId.{u + 1, u + 1} (R.obj.obj U)).app (M.val.obj U)).symm) ?_
  intro U V i
  ext m
  change (ModuleCat.extendScalarsId.{u + 1, u + 1} (R.obj.obj V)).inv.app (M.val.obj V)
      (M.val.map i m) =
    changeOfRingsMap (𝟙 R) M i
      ((ModuleCat.extendScalarsId.{u + 1, u + 1} (R.obj.obj U)).inv.app (M.val.obj U) m)
  rw [ModuleCat.extendScalarsId_inv_app_apply, ModuleCat.extendScalarsId_inv_app_apply]
  simpa [changeOfRingsMap] using
    (Classical.choose_spec (exists_changeOfRingsMap (𝟙 R) M i)
      (1 : R.obj.obj U) m).symm

private noncomputable def etaleScalarExtensionIdIsoApp
    {C : Type (u + 1)} [Category.{u} C] {J : GrothendieckTopology C}
    (R : Sheaf J CommRingCat.{u + 1})
    (M : SheafOfModules.{u + 1}
      ((sheafCompose J (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R)) :
    (etaleScalarExtension (𝟙 R)).obj M ≅ M :=
  (PresheafOfModules.sheafification.{u + 1} (𝟙 _)).mapIso
      (etaleScalarExtensionPresheafIdIso R M).symm ≪≫
    asIso ((PresheafOfModules.sheafificationAdjunction.{u + 1} (𝟙 _)).counit.app M)

set_option backward.isDefEq.respectTransparency false in
private noncomputable def etaleScalarExtensionIdIso
    {C : Type (u + 1)} [Category.{u} C] {J : GrothendieckTopology C}
    (R : Sheaf J CommRingCat.{u + 1}) : etaleScalarExtension (𝟙 R) ≅ 𝟭 _ := by
  refine NatIso.ofComponents (etaleScalarExtensionIdIsoApp R) ?_
  intro M N a
  let F := PresheafOfModules.sheafification.{u + 1}
    (𝟙 ((sheafCompose J (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R).obj)
  let ψ := (etaleScalarExtensionPresheaf (𝟙 R)).map a
  have hp : (etaleScalarExtensionPresheafIdIso R M).hom ≫ ψ =
      a.val ≫ (etaleScalarExtensionPresheafIdIso R N).hom := by
    ext U m
    change (ModuleCat.extendScalars.{u + 1, u + 1, u + 1} (RingHom.id (R.obj.obj U))).map
        (a.val.app U)
      ((ModuleCat.extendScalarsId.{u + 1, u + 1} (R.obj.obj U)).inv.app (M.val.obj U) m) =
        (ModuleCat.extendScalarsId.{u + 1, u + 1} (R.obj.obj U)).inv.app
        (N.val.obj U) (a.val.app U m)
    exact ConcreteCategory.congr_hom
      ((ModuleCat.extendScalarsId.{u + 1, u + 1} (R.obj.obj U)).inv.naturality
      (a.val.app U)) m
  have hp' : (etaleScalarExtensionPresheafIdIso R M).inv ≫ a.val =
      ψ ≫ (etaleScalarExtensionPresheafIdIso R N).inv := by
    rw [← cancel_epi (etaleScalarExtensionPresheafIdIso R M).hom]
    simp only [← Category.assoc, hp]
    simp
  symm
  change F.map (etaleScalarExtensionPresheafIdIso R M).inv ≫
      (PresheafOfModules.sheafificationAdjunction.{u + 1} (𝟙 _)).counit.app M ≫ a =
    F.map ψ ≫ F.map (etaleScalarExtensionPresheafIdIso R N).inv ≫
      (PresheafOfModules.sheafificationAdjunction.{u + 1} (𝟙 _)).counit.app N
  rw [← (PresheafOfModules.sheafificationAdjunction.{u + 1} (𝟙 _)).counit_naturality a]
  change F.map (etaleScalarExtensionPresheafIdIso R M).inv ≫ F.map a.val ≫ _ = _
  rw [← F.map_comp_assoc, hp', F.map_comp_assoc]


private theorem derivedIso
    {C D : Type (u + 2)} [Category.{u + 1} C] [Category.{u + 1} D]
    [Abelian C] [Abelian D] [HasDerivedCategory.{u + 2} C]
    [HasDerivedCategory.{u + 2} D]
    (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (d : DerivedCategory C ⥤ DerivedCategory D)
    (ε : DerivedCategory.Q ⋙ d ≅
      F.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q) :
    Nonempty (F.mapDerivedCategory ≅ d) := by
  let : Localization.Lifting DerivedCategory.Q
      (HomologicalComplex.quasiIso C (ComplexShape.up ℤ))
      (F.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q) d := ⟨ε⟩
  exact ⟨Localization.liftNatIso DerivedCategory.Q
    (HomologicalComplex.quasiIso C (ComplexShape.up ℤ))
    (F.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
    (F.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
    F.mapDerivedCategory d (Iso.refl _)⟩

private abbrev etaleNativeTensor (X : Scheme.{u})
    (R : Sheaf X.smallEtaleTopology CommRingCat.{u + 1}) :=
  @MonoidalCategory.tensor _ _
    (RingedDerivedNative.monoidal.{u + 1, u, 0, u + 2} X.smallEtaleTopology R)

private def etaleFlatRepresentatives (X : Scheme.{u})
    (R : Sheaf X.smallEtaleTopology CommRingCat.{u + 1}) :
    ObjectProperty (CochainComplex (closedCostalkEtaleModules X R) ℤ) :=
  fun P ↦ P.IsAcyclicTensorKFlat ∧
    ∀ n : ℤ, IsFlatOnSite (J := X.smallEtaleTopology) (R := R) (P.X n)

private def etaleTensorRepresentative (X : Scheme.{u})
    (R : Sheaf X.smallEtaleTopology CommRingCat.{u + 1}) :
    ((etaleFlatRepresentatives X R).ι.prod (etaleFlatRepresentatives X R).ι) ⋙
      Functor.uncurry.obj
        ((@MonoidalCategory.curriedTensor (closedCostalkEtaleModules X R) _
          (monoidalCategory R)).map₂HomologicalComplex
            (ComplexShape.up ℤ) (ComplexShape.up ℤ) (ComplexShape.up ℤ)) ⋙ DerivedCategory.Q ≅
      (((etaleFlatRepresentatives X R).ι ⋙ DerivedCategory.Q).prod
        ((etaleFlatRepresentatives X R).ι ⋙ DerivedCategory.Q)) ⋙ etaleNativeTensor X R :=
  NatIso.ofComponents
    (fun P ↦ RingedDerivedNative.tensorIso.{u + 1, u, 0, u + 2}
      X.smallEtaleTopology R P.1.obj P.2.obj (Or.inl P.1.property.1))
    (fun f ↦ RingedDerivedNative.tensorIso_naturality.{u + 1, u, 0, u + 2}
      X.smallEtaleTopology R _ _ _ _ _ _ f.1.hom f.2.hom)

/-- Exact inverse image with inverse-image coefficients preserves native derived tensor.
This is an inverse-image assertion for any morphism, independent of closed support.
Source: Stacks Tags 03EL, 07A4 and 0G7E; the tensor-pullback step of the current
closed-costalk-duality blueprint proof.
(blueprint: lem-weil-etale-native-tensor-pullback).

Proof: lift the set-sheaf inverse image to rings and modules by transporting the
operation graphs through finite-product comparisons. Uniqueness of the ring and
module adjunctions identifies these lifts with the displayed coefficient inverse
image and with p, compatibly with units. Thus p is exact, and the ring map in this
presentation is the identity. On module tensors, the bilinear universal property
identifies p(M tensor N) with p(M) tensor p(N), naturally in both variables.
Exact inverse image with unchanged coefficients preserves flat modules and flat-term
K-flat complexes (03EL, 0G7E). Resolve both complexes by such complexes. Canonical
signed total-tensor comparison and the native tensor representative isomorphisms
give the desired comparison on these representatives. Canonical tensor-pullback
descent (07A4) gives a natural isomorphism on the unbounded derived categories.
The supplied factorization identifies d with exact termwise localization by
uniqueness of localization lifts. Transport along this identification gives precisely
the displayed natural isomorphism. Empty schemes and the zero ring require no change. -/
theorem etaleNativeTensorPullback
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (R : Sheaf Y.smallEtaleTopology CommRingCat.{u + 1})
    (p : closedCostalkEtaleModules Y R ⥤
      closedCostalkEtaleModules X ((closedCostalkEtaleRingPullback f).obj R))
    [p.Additive] (a : p ⊣ closedCostalkEtaleModulePush f R)
    (d : DerivedCategory (closedCostalkEtaleModules Y R) ⥤
      DerivedCategory (closedCostalkEtaleModules X ((closedCostalkEtaleRingPullback f).obj R)))
    (factors : DerivedCategory.Q ⋙ d ≅
      p.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q) :
    let S := (closedCostalkEtaleRingPullback f).obj R
    let tY := @MonoidalCategory.tensor _ _
      (RingedDerivedNative.monoidal.{u + 1, u, 0, u + 2} Y.smallEtaleTopology R)
    let tX := @MonoidalCategory.tensor _ _
      (RingedDerivedNative.monoidal.{u + 1, u, 0, u + 2} X.smallEtaleTopology S)
    Nonempty (tY ⋙ d ≅ d.prod d ⋙ tX) := by
  dsimp only
  let S := (closedCostalkEtaleRingPullback f).obj R
  let L := etaleSetPullback f
  let V := (MorphismProperty.Over.pullback @Etale ⊤ f).sheafPushforwardContinuous
    (Type (u + 1)) (Y.smallGrothendieckTopology @Etale)
    (X.smallGrothendieckTopology @Etale)
  have : PreservesFiniteLimits L :=
    (AlgebraicGeometry.etaleInverseImageAlgebraicStructures X Y f).1
  obtain ⟨hp, hp'⟩ := etalePullExact f R p a
  have : PreservesFiniteLimits p := hp
  have : PreservesFiniteColimits p := hp'
  obtain ⟨I, hI⟩ := etaleAlgebraicPresentation f R p a
  have : I.modules.Additive := by rw [hI]; infer_instance
  have := etaleScalarExtension_additive (𝟙 S)
  let uStar := I.modules ⋙ etaleScalarExtension (𝟙 S)
  have : uStar.Additive := inferInstance
  let e : uStar ≅ p :=
    Functor.isoWhiskerLeft I.modules (etaleScalarExtensionIdIso S) ≪≫
      I.modules.rightUnitor ≪≫ eqToIso hI
  have : PreservesFiniteLimits uStar := preservesFiniteLimits_of_natIso e.symm
  have : PreservesFiniteColimits uStar := preservesFiniteColimits_of_natIso e.symm
  have hobj (M) : uStar.obj M = changeOfRings (𝟙 S) (I.modules.obj M) := rfl
  have hmap {M N} (g : M ⟶ N) : uStar.map g = eqToHom (hobj M) ≫
      changeOfRingsHom (𝟙 S) (I.modules.obj M) (I.modules.map g) ≫
        eqToHom (hobj N).symm := by
    simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
    rfl
  obtain ⟨⟨k⟩, _⟩ :=
    SheafOfModules.CanonicalTensorPullbackOfUniverses.canonicalRingedTensorComparison_existsUnique
      R S S L I (𝟙 S) uStar hobj V (etaleSetsAdj f) hmap
  have hLF : uStar.mapDerivedCategory.IsLeftDerivedFunctor
      uStar.mapDerivedCategoryFactorsh.hom
      (HomotopyCategory.quasiIso (closedCostalkEtaleModules Y R) (ComplexShape.up ℤ)) :=
    Functor.isLeftDerivedFunctor_of_inverts _ _ uStar.mapDerivedCategoryFactorsh
  obtain ⟨alpha, _, _⟩ :=
    (SheafOfModules.CanonicalTensorPullbackOfUniverses.ringedTopoiCanonicalDerivedTensorPullback
      L V (etaleSetsAdj f) I (𝟙 S) uStar hobj hmap uStar.mapDerivedCategory
      uStar.mapDerivedCategoryFactorsh.hom hLF
      (etaleFlatRepresentatives Y R) (etaleFlatRepresentatives X S)
      (fun _ ↦ Iff.rfl) (fun _ ↦ Iff.rfl)
      (etaleNativeTensor Y R) (etaleNativeTensor X S)
      (etaleTensorRepresentative Y R) (etaleTensorRepresentative X S)
      k (closedCostalkEtaleModulePush f R) (a.ofNatIsoLeft e.symm)).2
  obtain ⟨ed⟩ := derivedIso p d factors
  let eD := Functor.mapDerivedCategoryNatIso e ≪≫ ed
  exact ⟨Functor.isoWhiskerLeft (etaleNativeTensor Y R) eD.symm ≪≫ alpha ≪≫
    Functor.isoWhiskerRight (NatIso.prod eD eD) (etaleNativeTensor X S)⟩

end AlgebraicGeometry.Scheme
