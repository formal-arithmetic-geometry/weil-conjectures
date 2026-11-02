/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Realization.DiagonalRealizationPullbackEndpoints
public import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Realization.DiagonalRealizationPullbackCanonicalComparison
public import WeilConjectures.AlgebraicGeometry.Cartesian.CartesianCoefficientTwistsSupplement
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.SingleFunctor
public import WeilConjectures.CategoryTheory.DerivedCategory.Shift.ExactFunctor
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.KFlatDerivedAdjunctionTransportShifts
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperStarShift

/-! # Canonical derived diagonal realization endpoint comparison -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option linter.style.haveILetI false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.Obj CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.DiagonalCoefficients

private theorem freeUnit_pullback
    {C D : Type*} [Category C] [Category D] [MonoidalCategory C] [MonoidalCategory D]
    (F : C ⥤ D) [F.Monoidal] {R : C} [MonObj R] {S : D} [MonObj S]
    (a : F.obj R ⟶ S) [IsMonHom a] {M : C} {N : D} (b : F.obj M ⟶ N) :
    F.map ((Mod.freeForgetAdjunction R).unit.app M) ≫
      Functor.OplaxMonoidal.δ F R M ≫ (a ⊗ₘ b) =
        b ≫ (Mod.freeForgetAdjunction S).unit.app N := by
  change F.map ((λ_ M).inv ≫ η[R] ▷ M ≫ 𝟙 _) ≫ _ ≫ _ =
    b ≫ (λ_ N).inv ≫ η[S] ▷ N ≫ 𝟙 _
  simp only [Functor.map_comp, Category.comp_id]
  rw [Functor.Monoidal.map_leftUnitor_inv]
  simp only [Category.assoc]
  rw [← Functor.OplaxMonoidal.δ_natural_left_assoc, Functor.Monoidal.μ_δ_assoc]
  rw [MonoidalCategory.tensorHom_def, ← comp_whiskerRight_assoc, ← comp_whiskerRight_assoc]
  change (λ_ (F.obj M)).inv ≫ (η[F.obj R] ≫ a) ▷ F.obj M ≫ S ◁ b = _
  rw [IsMonHom.one_hom, ← whisker_exchange, ← leftUnitor_inv_naturality_assoc]

private theorem root_adjunct_naturality
    (l : ℕ) [Fact l.Prime] {X S : Scheme.{u}} (f : X ⟶ S)
    (rX : IntegralRoots l (bottomField l) X) (rS : IntegralRoots l (bottomField l) S)
    (a : Scheme.purTwistZlOne S l ⟶
      (lowerStar Ab.{u + 1} f).obj (Scheme.purTwistZlOne X l))
    (ha : ∀ (n : ℕ) (U : S.ProEtᵒᵖ) (z : (Scheme.purTwistZlOne S l).obj.obj U),
      (limit.π (Scheme.proEtaleRootsOfUnityTower X l Fact.out) (op n)).hom.app
          ((Scheme.proEtaleBaseChange f).op.obj U) (a.hom.app U z) =
        (Scheme.proEtaleRootsOfUnityDirectImageMap f (l ^ (n + 1))).hom.app U
          ((limit.π (Scheme.proEtaleRootsOfUnityTower S l Fact.out)
            (op n)).hom.app U z)) :
    a ≫ (lowerStar Ab.{u + 1} f).map rX.hom =
      rS.hom ≫ (Scheme.proEtaleSheafAdjunction f Ab.{u + 1}).homEquiv _ _
        (spIntegralComparison f l (bottomField l)) := by
  let adj := Scheme.proEtaleSheafAdjunction f Ab.{u + 1}
  let L := Scheme.proEtaleSheafInverseImage f Ab.{u + 1}
  let t := (adj.homEquiv _ _).symm a
  have ht (n : ℕ) :
      t ≫ limit.π (Scheme.proEtaleRootsOfUnityTower X l Fact.out) (op n) =
        L.map (limit.π (Scheme.proEtaleRootsOfUnityTower S l Fact.out) (op n)) ≫
          Scheme.proEtaleRootsOfUnityInverseImageMap f (l ^ (n + 1)) := by
    apply (adj.homEquiv _ _).injective
    rw [adj.homEquiv_naturality_right, adj.homEquiv_naturality_left]
    simp only [t, Equiv.apply_symm_apply]
    change a ≫ (lowerStar Ab.{u + 1} f).map _ =
      _ ≫ adj.homEquiv _ _ ((adj.homEquiv _ _).symm _)
    rw [Equiv.apply_symm_apply]
    ext U z
    exact ha n U z
  have h : t ≫ rX.hom = L.map rS.hom ≫ spIntegralComparison f l (bottomField l) := by
    apply (isLimitOfPreserves
      (Mod.forget (C := Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
        (D := Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
        (condensedRingObj
          (Profinite.padicIntegersRingObj.{u} l (bottomField l).1) X))
      (limit.isLimit (spIntegralTwistSystem X l (bottomField l)))).hom_ext
    rintro ⟨n⟩
    change (t ≫ rX.hom) ≫
      (limit.π (spIntegralTwistSystem X l (bottomField l)) (op n)).hom =
      (L.map rS.hom ≫ spIntegralComparison f l (bottomField l)) ≫
        (limit.π (spIntegralTwistSystem X l (bottomField l)) (op n)).hom
    rw [Category.assoc, rX.projections, ← Category.assoc, ht]
    rw [Category.assoc (L.map rS.hom), integralComparison_π]
    change _ = L.map rS.hom ≫
      L.map (limit.π (spIntegralTwistSystem S l (bottomField l)) (op n)).hom ≫ _
    have hf := freeUnit_pullback (upperStar Ab.{u + 1} f)
      (condensedPullbackHom (spEllPointRingObj l (bottomField l) n) f)
      (Scheme.proEtaleRootsOfUnityInverseImageMap f (l ^ (n + 1)))
    change L.map ((Mod.freeForgetAdjunction
        (condensedRingObj (spEllPointRingObj l (bottomField l) n) S)).unit.app
          (Scheme.proEtaleRootsOfUnitySheaf S (l ^ (n + 1)))) ≫
        integralLevelComparison f l (bottomField l) n = _ at hf
    have hp := congrArg (fun z ↦ L.map z ≫ integralLevelComparison f l (bottomField l) n)
      (rS.projections n)
    simp only [L.map_comp, Category.assoc] at hp
    exact (Category.assoc _ _ _).trans
      ((congrArg (fun z ↦ L.map
        (limit.π (Scheme.proEtaleRootsOfUnityTower S l Fact.out) (op n)) ≫ z)
        hf.symm).trans hp.symm)
  have h' := congrArg (adj.homEquiv _ _) h
  rw [adj.homEquiv_naturality_right, adj.homEquiv_naturality_left] at h'
  simpa only [t, Equiv.apply_symm_apply] using h'

private theorem ordinary_line_component
    (l : ℕ) [Fact l.Prime] {X S : Scheme.{u}} (f : X ⟶ S)
    [IsIso (diagonalCompletedCoefficientMap l f)]
    (eX : CompletedRealization l X) (eS : CompletedRealization l S)
    (line : PullEndpoint (Profinite.continuousMapRingObj.{u} ℤ_[l]) f
      (zlLine l S) (zlLine l X)
      (((upperStarLowerStarAdjunction Ab.{u + 1} f).homEquiv _ _).symm
        ((Scheme.proEtaleSheafAdjunction f Ab.{u + 1}).homEquiv _ _
          (spIntegralComparison f l (bottomField l)))))
    (d : DiagonalRealizationPullbackEndpointData l f (diagonalPullbackCoefficientIso l f)) :
    (diagonalPullbackOrdinaryComparison l f eX eS).hom.app
        (Scheme.purTwistZlModule S l) ≫
      (CondensedRing.upperStar (Profinite.continuousMapRingObj.{u} ℤ_[l]) f).map
        eS.lineIso.hom ≫ line.iso.hom =
      eX.F.map d.completedLine.hom ≫ eX.lineIso.hom := by
  let M := Scheme.purTwistZlModule S l
  let N := Scheme.purTwistZlModule X l
  let α := (Scheme.proEtaleRingModuleAdjunction f (Scheme.purTwistZlCompletion S l)
    (Scheme.purTwistZlCompletion X l) (diagonalPullbackCoefficientIso l f)).homEquiv
      M N d.completedLine.hom
  let a : Scheme.purTwistZlOne S l ⟶
      (lowerStar Ab.{u + 1} f).obj (Scheme.purTwistZlOne X l) :=
    (SheafOfModules.toSheaf _).map α
  have ha := root_adjunct_naturality l f eX.roots eS.roots a
    d.completedLine_normalization
  have hx : eX.lineIso.hom.hom = eX.underlying.hom.app N ≫ eX.roots.hom := by
    apply (cancel_epi (eX.underlying.inv.app N)).1
    rw [Iso.inv_hom_id_app_assoc]
    exact eq_of_heq eX.line_normalization
  have hs : eS.underlying.inv.app M ≫ eS.lineIso.hom.hom = eS.roots.hom :=
    eq_of_heq eS.line_normalization
  have hr : ((diagonalPullbackRightComparison l f eX eS).hom.app N).hom ≫
      (lowerStar Ab.{u + 1} f).map (eX.underlying.hom.app N) =
      eS.underlying.hom.app
        ((Scheme.proEtaleRingModuleDirectImage f (Scheme.purTwistZlCompletion S l)
          (Scheme.purTwistZlCompletion X l) (diagonalPullbackCoefficientIso l f)).obj N) := by
    have hn := (Classical.choice
      (completedCoefficientOrdinarySquare_exists l f eX eS)).normalization N
    dsimp only [diagonalPullbackRightComparison, Iso.trans_hom, NatTrans.comp_app,
      Functor.isoWhiskerRight_hom, Functor.whiskerRight_app, Iso.symm_hom,
      Mod.comp_hom']
    rw [Category.assoc, eq_of_heq hn]
    have hb := eS.underlying.hom.naturality ((diagonalPullbackPushBridge l f).inv.app N)
    apply Sheaf.hom_ext
    ext U z
    have hb' := congrArg (fun q ↦ q.hom.app U z) hb
    exact hb'.trans (by rfl)
  apply (cancel_epi ((diagonalPullbackOrdinaryComparison l f eX eS).inv.app M)).1
  dsimp only [M]
  simp only [Iso.inv_hom_id_app_assoc]
  apply ((CondensedRing.upperStarLowerStarAdjunction
    (Profinite.continuousMapRingObj.{u} ℤ_[l]) f).homEquiv _ _).injective
  rw [Adjunction.homEquiv_naturality_left, ← Category.assoc,
    Adjunction.homEquiv_naturality_right,
    diagonalPullbackOrdinaryComparison_transpose]
  apply Mod.hom_ext
  simp only [Mod.comp_hom', CondensedRing.lowerStar_map_hom]
  rw [line.normalization, Equiv.apply_symm_apply]
  apply (cancel_epi (eS.underlying.inv.app M)).1
  rw [← Category.assoc, hs]
  simp only [Category.assoc]
  change eS.roots.hom ≫ _ = eS.underlying.inv.app M ≫ (eS.F.map α).hom ≫
    ((diagonalPullbackRightComparison l f eX eS).hom.app N).hom ≫
      (lowerStar Ab.{u + 1} f).map eX.lineIso.hom.hom
  rw [hx, Functor.map_comp]
  rw [reassoc_of% hr]
  have hn := eS.underlying.hom.naturality α
  change (eS.F.map α).hom ≫ eS.underlying.hom.app _ =
    eS.underlying.hom.app M ≫ a at hn
  rw [reassoc_of% hn]
  simp only [Iso.inv_hom_id_app_assoc]
  exact ha.symm

private theorem shift_endpoint_square
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    [HasShift A ℤ] [HasShift B ℤ] [HasShift C ℤ] [HasShift D ℤ]
    (F : A ⥤ B) (G : B ⥤ D) (H : A ⥤ C) (I : C ⥤ D)
    [F.CommShift ℤ] [G.CommShift ℤ] [H.CommShift ℤ] [I.CommShift ℤ]
    (α : F ⋙ G ⟶ H ⋙ I) [NatTrans.CommShift α ℤ]
    {M : A} {N : B} {T : C} {W : D}
    (m : F.obj M ⟶ N) (h : H.obj M ⟶ T) (g : G.obj N ⟶ W) (q : I.obj T ⟶ W)
    (e : α.app M ≫ I.map h ≫ q = G.map m ≫ g) (r : ℤ) :
    α.app (M⟦r⟧) ≫ I.map ((H.commShiftIso r).hom.app M ≫ h⟦r⟧') ≫
        (I.commShiftIso r).hom.app T ≫ q⟦r⟧' =
      G.map ((F.commShiftIso r).hom.app M ≫ m⟦r⟧') ≫
        (G.commShiftIso r).hom.app N ≫ g⟦r⟧' := by
  simp only [Functor.map_comp, Category.assoc]
  rw [I.commShiftIso_hom_naturality_assoc]
  have hc := NatTrans.shift_app_comm α r M
  simp only [Functor.commShiftIso_comp_hom_app] at hc
  rw [reassoc_of% hc.symm]
  simp only [← Functor.map_comp]
  rw [e]
  simp only [Functor.map_comp]
  rw [G.commShiftIso_hom_naturality_assoc]

private theorem shift_endpoint_square_iso
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    [HasShift A ℤ] [HasShift B ℤ] [HasShift C ℤ] [HasShift D ℤ]
    (F : A ⥤ B) (G : B ⥤ D) (H : A ⥤ C) (I : C ⥤ D)
    [F.CommShift ℤ] [G.CommShift ℤ] [H.CommShift ℤ] [I.CommShift ℤ]
    (α : F ⋙ G ⟶ H ⋙ I) [NatTrans.CommShift α ℤ]
    {M : A} {N : B} {T₀ T : C} {W₀ W : D}
    (m : F.obj M ≅ N) (h₁ : H.obj M ⟶ T₀) (h₂ : T₀ ⟶ T)
    (g₁ : G.obj N ⟶ W₀) (g₂ : W₀ ⟶ W) (q : I.obj T ⟶ W)
    (e : α.app M ≫ I.map (h₁ ≫ h₂) ≫ q = G.map m.hom ≫ g₁ ≫ g₂) (r : ℤ) :
    α.app (M⟦r⟧) ≫ I.map ((H.commShiftIso r).hom.app M ≫ h₁⟦r⟧' ≫ h₂⟦r⟧') ≫
        (I.commShiftIso r).hom.app T ≫ q⟦r⟧' =
      G.map (((F.commShiftIso r).app M ≪≫ (shiftFunctor B r).mapIso m).hom) ≫
        (G.commShiftIso r).hom.app N ≫ g₁⟦r⟧' ≫ g₂⟦r⟧' := by
  simpa only [Iso.trans_hom, Iso.app_hom, Functor.mapIso_hom, Functor.map_comp,
    Category.assoc] using
      shift_endpoint_square F G H I α m.hom (h₁ ≫ h₂) (g₁ ≫ g₂) q e r

private theorem derived_square_single (c : F ⋙ G ≅ H ⋙ I) (M : A) :
    (Functor.mapDerivedCategorySquareIso c).hom.app
        ((DerivedCategory.singleFunctor A 0).obj M) ≫
      I.mapDerivedCategory.map ((H.mapDerivedCategorySingleFunctor 0).hom.app M) ≫
      (I.mapDerivedCategorySingleFunctor 0).hom.app (H.obj M) =
    G.mapDerivedCategory.map ((F.mapDerivedCategorySingleFunctor 0).hom.app M) ≫
      (G.mapDerivedCategorySingleFunctor 0).hom.app (F.obj M) ≫
      (DerivedCategory.singleFunctor D 0).map (c.hom.app M) := by
  apply (cancel_epi ((Functor.mapDerivedCategoryCompIso F G).hom.app
    ((DerivedCategory.singleFunctor A 0).obj M))).1
  simp only [Functor.mapDerivedCategorySquareIso, Iso.trans_hom, Iso.symm_hom,
    NatTrans.comp_app, Category.assoc, Iso.hom_inv_id_app_assoc]
  rw [Functor.mapDerivedCategoryCompIso_hom_app_singleFunctor,
    Functor.mapDerivedCategoryNatIso_hom_app_singleFunctor]
  erw [reassoc_of% (Functor.mapDerivedCategoryCompIso_hom_app_singleFunctor F G M)]

private theorem derived_square_endpoint (c : F ⋙ G ≅ H ⋙ I) (M : A)
    {N : B} {T : C} {W : D} (m : F.obj M ⟶ N) (h : H.obj M ⟶ T)
    (g : G.obj N ⟶ W) (q : I.obj T ⟶ W)
    (e : c.hom.app M ≫ I.map h ≫ q = G.map m ≫ g) :
    (Functor.mapDerivedCategorySquareIso c).hom.app
        ((DerivedCategory.singleFunctor A 0).obj M) ≫
      I.mapDerivedCategory.map ((H.mapDerivedCategorySingleFunctor 0).hom.app M ≫
        (DerivedCategory.singleFunctor C 0).map h) ≫
      (I.mapDerivedCategorySingleFunctor 0).hom.app T ≫
      (DerivedCategory.singleFunctor D 0).map q =
    G.mapDerivedCategory.map ((F.mapDerivedCategorySingleFunctor 0).hom.app M ≫
      (DerivedCategory.singleFunctor B 0).map m) ≫
      (G.mapDerivedCategorySingleFunctor 0).hom.app N ≫
      (DerivedCategory.singleFunctor D 0).map g := by
  simp only [Functor.map_comp, Category.assoc]
  rw [reassoc_of% (I.mapDerivedCategorySingleFunctor 0).hom.naturality h]
  rw [reassoc_of% derived_square_single F G H I c M]
  rw [reassoc_of% (G.mapDerivedCategorySingleFunctor 0).hom.naturality m]
  simp only [← Functor.map_comp]
  rw [e]

private theorem derived_shift_endpoint_square (c : F ⋙ G ≅ H ⋙ I) (M : A)
    {N : B} {T : C} {W : D} (m : F.obj M ≅ N) (h : H.obj M ⟶ T)
    (g : G.obj N ⟶ W) (q : I.obj T ⟶ W)
    (J : DerivedCategory C ⥤ DerivedCategory D) [J.CommShift ℤ]
    (p : J ≅ I.mapDerivedCategory) [NatTrans.CommShift p.hom ℤ]
    (qD : J.obj ((DerivedCategory.singleFunctor C 0).obj T) ⟶
      (DerivedCategory.singleFunctor D 0).obj W)
    (qe : qD = p.hom.app _ ≫ (I.mapDerivedCategorySingleFunctor 0).hom.app T ≫
      (DerivedCategory.singleFunctor D 0).map q)
    (e : c.hom.app M ≫ I.map h ≫ q = G.map m.hom ≫ g) (r : ℤ) :
    (Functor.mapDerivedCategorySquareIso c ≪≫
      Functor.isoWhiskerLeft H.mapDerivedCategory p.symm).hom.app
        (((DerivedCategory.singleFunctor A 0).obj M)⟦r⟧) ≫
      J.map ((H.mapDerivedCategory.commShiftIso r).hom.app _ ≫
        ((H.mapDerivedCategorySingleFunctor 0).hom.app M)⟦r⟧' ≫
        ((DerivedCategory.singleFunctor C 0).map h)⟦r⟧') ≫
      (J.commShiftIso r).hom.app _ ≫ qD⟦r⟧' =
    G.mapDerivedCategory.map
      (((F.mapDerivedCategory.commShiftIso r).app _ ≪≫
        (shiftFunctor (DerivedCategory B) r).mapIso
          ((F.mapDerivedCategorySingleFunctor 0).app M ≪≫
            (DerivedCategory.singleFunctor B 0).mapIso m)).hom) ≫
      (G.mapDerivedCategory.commShiftIso r).hom.app _ ≫
      ((G.mapDerivedCategorySingleFunctor 0).hom.app N)⟦r⟧' ≫
      ((DerivedCategory.singleFunctor D 0).map g)⟦r⟧' := by
  let α := (Functor.mapDerivedCategorySquareIso c ≪≫
    Functor.isoWhiskerLeft H.mapDerivedCategory p.symm).hom
  let mi := (F.mapDerivedCategorySingleFunctor 0).app M ≪≫
    (DerivedCategory.singleFunctor B 0).mapIso m
  have eD : α.app ((DerivedCategory.singleFunctor A 0).obj M) ≫
      J.map ((H.mapDerivedCategorySingleFunctor 0).hom.app M ≫
        (DerivedCategory.singleFunctor C 0).map h) ≫ qD =
    G.mapDerivedCategory.map mi.hom ≫
      (G.mapDerivedCategorySingleFunctor 0).hom.app N ≫
      (DerivedCategory.singleFunctor D 0).map g := by
    change ((Functor.mapDerivedCategorySquareIso c).hom.app _ ≫ p.inv.app _) ≫ _ ≫ _ = _
    simp only [Category.assoc]
    rw [qe, ← p.inv.naturality_assoc, Iso.inv_hom_id_app_assoc]
    simpa only [mi, Iso.trans_hom, Iso.app_hom, Functor.mapIso_hom] using
      derived_square_endpoint F G H I c M m.hom h g q e
  letI : NatTrans.CommShift p.symm.hom ℤ := inferInstance
  letI : NatTrans.CommShift (Functor.mapDerivedCategorySquareIso c).hom ℤ := by
    change NatTrans.CommShift
      ((Functor.mapDerivedCategoryCompIso F G).inv ≫
        (Functor.mapDerivedCategoryNatIso c).hom ≫
        (Functor.mapDerivedCategoryCompIso H I).hom) ℤ
    letI : NatTrans.CommShift (Functor.mapDerivedCategoryCompIso F G).inv ℤ := by
      infer_instance
    letI : NatTrans.CommShift (Functor.mapDerivedCategoryNatIso c).hom ℤ := by
      infer_instance
    letI : NatTrans.CommShift (Functor.mapDerivedCategoryCompIso H I).hom ℤ := by
      infer_instance
    exact NatTrans.CommShift.comp
      (τ := (Functor.mapDerivedCategoryCompIso F G).inv)
      (τ' := (Functor.mapDerivedCategoryNatIso c).hom ≫
        (Functor.mapDerivedCategoryCompIso H I).hom) ℤ
  letI : NatTrans.CommShift α ℤ := by
    change NatTrans.CommShift ((Functor.mapDerivedCategorySquareIso c).hom ≫
      Functor.whiskerLeft H.mapDerivedCategory p.symm.hom) ℤ
    exact NatTrans.CommShift.comp
      (τ := (Functor.mapDerivedCategorySquareIso c).hom)
      (τ' := Functor.whiskerLeft H.mapDerivedCategory p.symm.hom) ℤ
  exact shift_endpoint_square_iso F.mapDerivedCategory G.mapDerivedCategory
    H.mapDerivedCategory J α mi ((H.mapDerivedCategorySingleFunctor 0).hom.app M)
    ((DerivedCategory.singleFunctor C 0).map h)
    ((G.mapDerivedCategorySingleFunctor 0).hom.app N)
    ((DerivedCategory.singleFunctor D 0).map g) qD eD r

private theorem derived_shift_normalized_endpoint_square
    (c : F ⋙ G ≅ H ⋙ I) (M : A) {N : B} {T : C} {W : D}
    (m : F.obj M ≅ N) (h : H.obj M ⟶ T) (g : G.obj N ⟶ W) (q : I.obj T ⟶ W)
    (J : DerivedCategory C ⥤ DerivedCategory D) [J.CommShift ℤ]
    (p : J ≅ I.mapDerivedCategory) [NatTrans.CommShift p.hom ℤ]
    (qD : J.obj ((DerivedCategory.singleFunctor C 0).obj T) ⟶
      (DerivedCategory.singleFunctor D 0).obj W)
    (qe : qD = p.hom.app _ ≫ (I.mapDerivedCategorySingleFunctor 0).hom.app T ≫
      (DerivedCategory.singleFunctor D 0).map q)
    (e : c.hom.app M ≫ I.map h ≫ q = G.map m.hom ≫ g) (r : ℤ)
    (α : F.mapDerivedCategory ⋙ G.mapDerivedCategory ≅ H.mapDerivedCategory ⋙ J)
    (ha : α = Functor.mapDerivedCategorySquareIso c ≪≫
      Functor.isoWhiskerLeft H.mapDerivedCategory p.symm)
    (sH : H.mapDerivedCategory.obj (((DerivedCategory.singleFunctor A 0).obj M)⟦r⟧) ⟶
      ((DerivedCategory.singleFunctor C 0).obj T)⟦r⟧)
    (hH : sH = (H.mapDerivedCategory.commShiftIso r).hom.app _ ≫
      ((H.mapDerivedCategorySingleFunctor 0).hom.app M)⟦r⟧' ≫
      ((DerivedCategory.singleFunctor C 0).map h)⟦r⟧')
    (sG : G.mapDerivedCategory.obj (((DerivedCategory.singleFunctor B 0).obj N)⟦r⟧) ⟶
      ((DerivedCategory.singleFunctor D 0).obj W)⟦r⟧)
    (hG : sG = (G.mapDerivedCategory.commShiftIso r).hom.app _ ≫
      ((G.mapDerivedCategorySingleFunctor 0).hom.app N)⟦r⟧' ≫
      ((DerivedCategory.singleFunctor D 0).map g)⟦r⟧')
    (qS : J.obj (((DerivedCategory.singleFunctor C 0).obj T)⟦r⟧) ⟶
      ((DerivedCategory.singleFunctor D 0).obj W)⟦r⟧)
    (hq : qS = (J.commShiftIso r).hom.app _ ≫ qD⟦r⟧') :
    α.hom.app (((DerivedCategory.singleFunctor A 0).obj M)⟦r⟧) ≫ J.map sH ≫ qS =
      G.mapDerivedCategory.map
        (((F.mapDerivedCategory.commShiftIso r).app _ ≪≫
          (shiftFunctor (DerivedCategory B) r).mapIso
            ((F.mapDerivedCategorySingleFunctor 0).app M ≪≫
              (DerivedCategory.singleFunctor B 0).mapIso m)).hom) ≫ sG := by
  rw [ha, hH, hG, hq]
  exact derived_shift_endpoint_square F G H I c M m h g q J p qD qe e r

private theorem realized_shift_eq
    (l : ℕ) [Fact l.Prime] (X : Scheme.{u}) [DiagonalTraceLocalizations l X]
    (e : CompletedRealization l X) :
    e.shiftedLine l X = (e.F.mapDerivedCategory.commShiftIso (2 : ℤ)).hom.app _ ≫
      ((e.F.mapDerivedCategorySingleFunctor 0).hom.app (Scheme.purTwistZlModule X l))
        ⟦(2 : ℤ)⟧' ≫
      ((DerivedCategory.singleFunctor
        (Modules (Profinite.continuousMapRingObj.{u} ℤ_[l]) X) 0).map e.lineIso.hom)
        ⟦(2 : ℤ)⟧' := rfl

private theorem endpoint_derived_eq :
    e.derived = (CondensedRing.leftDerivedUpperStarIsoMapDerivedCategory R f).hom.app _ ≫
      ((CondensedRing.upperStar R f).mapDerivedCategorySingleFunctor 0).hom.app M ≫
      (DerivedCategory.singleFunctor (Modules R X) 0).map e.iso.hom := by
  change ((CondensedRing.leftDerivedUpperStarIsoMapDerivedCategory R f).hom.app _ ≫
    ((CondensedRing.upperStar R f).mapDerivedCategorySingleFunctor 0).hom.app M) ≫
      (DerivedCategory.singleFunctor (Modules R X) 0).map e.iso.hom = _
  exact Category.assoc _ _ _

private theorem endpoint_shift_eq :
    e.shift = ((derivedUpper R f).commShiftIso
      (self := derivedUpperCommShift R f) (2 : ℤ)).hom.app _ ≫
      e.derived⟦(2 : ℤ)⟧' := rfl

private theorem canonical_derived_line
    (l : ℕ) [Fact l.Prime]
    {X S : Scheme.{u}} (f : X ⟶ S)
    [IsIso (diagonalCompletedCoefficientMap l f)]
    [DiagonalTraceLocalizations l X] [DiagonalTraceLocalizations l S]
    (eX : CompletedRealization l X) (eS : CompletedRealization l S)
    (line : PullEndpoint (Profinite.continuousMapRingObj.{u} ℤ_[l]) f
      (zlLine l S) (zlLine l X)
      (((upperStarLowerStarAdjunction Ab.{u + 1} f).homEquiv _ _).symm
        ((Scheme.proEtaleSheafAdjunction f Ab.{u + 1}).homEquiv _ _
          (spIntegralComparison f l (bottomField l)))))
    (d : DiagonalRealizationPullbackEndpointData l f (diagonalPullbackCoefficientIso l f)) :
    (diagonalPullbackDerivedComparison l f eX eS).hom.app
      ((DiagonalTrace.completedLine l S)⟦(2 : ℤ)⟧) ≫
      (derivedUpper (Profinite.continuousMapRingObj.{u} ℤ_[l]) f).map
        (eS.shiftedLine l S) ≫ line.shift =
    eX.F.mapDerivedCategory.map
      (((Scheme.proEtaleRingModulePullback f (Scheme.purTwistZlCompletion S l)
        (Scheme.purTwistZlCompletion X l)
        (diagonalPullbackCoefficientIso l f)).mapDerivedCategory.commShiftIso (2 : ℤ)).app _
      ≪≫ (shiftFunctor (DerivedCategory (DiagonalCompleted l X)) (2 : ℤ)).mapIso
        ((Scheme.proEtaleRingModulePullback f (Scheme.purTwistZlCompletion S l)
          (Scheme.purTwistZlCompletion X l)
          (diagonalPullbackCoefficientIso l f)).mapDerivedCategorySingleFunctor 0 |>.app
            (Scheme.purTwistZlModule S l) |>.trans
              ((DerivedCategory.singleFunctor (DiagonalCompleted l X) 0).mapIso
                d.completedLine))).hom ≫
      eX.shiftedLine l X := by
  letI : (derivedUpper (Profinite.continuousMapRingObj.{u} ℤ_[l]) f).CommShift ℤ :=
    derivedUpperCommShift (Profinite.continuousMapRingObj.{u} ℤ_[l]) f
  letI : NatTrans.CommShift
      (F₁ := derivedUpper (Profinite.continuousMapRingObj.{u} ℤ_[l]) f)
      (F₂ := (CondensedRing.upperStar
        (Profinite.continuousMapRingObj.{u} ℤ_[l]) f).mapDerivedCategory)
      (CondensedRing.leftDerivedUpperStarIsoMapDerivedCategory
        (Profinite.continuousMapRingObj.{u} ℤ_[l]) f).hom ℤ :=
    geometric_shift (Profinite.continuousMapRingObj.{u} ℤ_[l]) f
  exact derived_shift_normalized_endpoint_square
    (A := DiagonalCompleted l S) (B := DiagonalCompleted l X)
    (C := Modules (Profinite.continuousMapRingObj.{u} ℤ_[l]) S)
    (D := Modules (Profinite.continuousMapRingObj.{u} ℤ_[l]) X)
    (Scheme.proEtaleRingModulePullback f (Scheme.purTwistZlCompletion S l)
      (Scheme.purTwistZlCompletion X l) (diagonalPullbackCoefficientIso l f))
    eX.F eS.F (CondensedRing.upperStar (Profinite.continuousMapRingObj.{u} ℤ_[l]) f)
    (diagonalPullbackOrdinaryComparison l f eX eS)
    (Scheme.purTwistZlModule S l) d.completedLine eS.lineIso.hom eX.lineIso.hom
    line.iso.hom (derivedUpper (Profinite.continuousMapRingObj.{u} ℤ_[l]) f)
    (CondensedRing.leftDerivedUpperStarIsoMapDerivedCategory
      (Profinite.continuousMapRingObj.{u} ℤ_[l]) f)
    line.derived (endpoint_derived_eq line)
    (ordinary_line_component l f eX eS line d) (2 : ℤ)
    (diagonalPullbackDerivedComparison l f eX eS) (derived_comparison_eq l f eX eS)
    (eS.shiftedLine l S) (realized_shift_eq l S eS)
    (eX.shiftedLine l X) (realized_shift_eq l X eX)
    line.shift (endpoint_shift_eq line)

/-- The canonical derived comparison has the prescribed shifted-line component.
Source: diagonal coefficient changes paragraph (3), endpoint transport.
(blueprint: lem-sfb-diagonal-realization-pullback-line-component).

Proof: transport `coeff` to the canonical map using `hc`. At the ordinary
completed line, cancel the canonical ordinary comparison and apply the upper-star
adjunction's Hom bijection. Use `diagonalPullbackOrdinaryComparison_transpose` and the
underlying-sheaf normalization of the ordinary right square. Before localization,
compose the integral line adjoints with each finite-root projection: the normalization
in `d` and the realization's line normalization identify both with the canonical
finite direct-image root map. The limit universal property identifies the integral
adjoints; localization and faithfulness of forgetting module action give the ordinary
line equation. Apply the exact-derived single component formula to that equation,
then shift by two. The canonical comparison commutes with shifts: exact-derived
squares have their canonical shift structure, and the geometric upper-star comparison
preserves it by K-flat adjunction transport. Naturality of these shift and single
comparisons identifies the resulting expression with the displayed equation.
Finite-root projections are used only on ordinary integral maps. -/
theorem diagonalRealization_pullback_line_component
    (l : ℕ) [Fact l.Prime]
    {X S : Scheme.{u}} (f : X ⟶ S) [IsNoetherian X] [IsNoetherian S]
    (coeff : (Scheme.proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj
      (Scheme.purTwistZlCompletion S l) ≅ Scheme.purTwistZlCompletion X l)
    (hc : coeff.hom = diagonalCompletedCoefficientMap l f)
    (hX : IsUnit (l : Γ(X, ⊤))) (hS : IsUnit (l : Γ(S, ⊤)))
    [DiagonalTraceLocalizations l X] [DiagonalTraceLocalizations l S]
    (eX : CompletedRealization l X) (eS : CompletedRealization l S)
    (unit : UnitPullEndpoint (Profinite.continuousMapRingObj.{u} ℤ_[l]) f)
    (line : PullEndpoint (Profinite.continuousMapRingObj.{u} ℤ_[l]) f
      (zlLine l S) (zlLine l X)
      (((upperStarLowerStarAdjunction Ab.{u + 1} f).homEquiv _ _).symm
        ((Scheme.proEtaleSheafAdjunction f Ab.{u + 1}).homEquiv _ _
          (spIntegralComparison f l (bottomField l)))))
    (d : DiagonalRealizationPullbackEndpointData l f coeff) :
    (diagonalRealization_pullback_canonical_comparison l f eX eS coeff hc).hom.app
      ((DiagonalTrace.completedLine l S)⟦(2 : ℤ)⟧) ≫
      (derivedUpper (Profinite.continuousMapRingObj.{u} ℤ_[l]) f).map
        (eS.shiftedLine l S) ≫ line.shift =
    eX.F.mapDerivedCategory.map
      (((Scheme.proEtaleRingModulePullback f (Scheme.purTwistZlCompletion S l)
        (Scheme.purTwistZlCompletion X l) coeff).mapDerivedCategory.commShiftIso (2 : ℤ)).app _
      ≪≫ (shiftFunctor (DerivedCategory (DiagonalCompleted l X)) (2 : ℤ)).mapIso
        ((Scheme.proEtaleRingModulePullback f (Scheme.purTwistZlCompletion S l)
          (Scheme.purTwistZlCompletion X l) coeff).mapDerivedCategorySingleFunctor 0 |>.app
            (Scheme.purTwistZlModule S l) |>.trans
              ((DerivedCategory.singleFunctor (DiagonalCompleted l X) 0).mapIso
                d.completedLine))).hom ≫
      eX.shiftedLine l X := by
  haveI : IsIso (diagonalCompletedCoefficientMap l f) := by
    rw [← hc]
    infer_instance
  have hcoeff : coeff = diagonalPullbackCoefficientIso l f := Iso.ext hc
  subst coeff
  rw [diagonalRealization_pullback_canonical_comparison_normalized]
  exact canonical_derived_line l f eX eS line d

end AlgebraicGeometry.ProEtale.DiagonalCoefficients
