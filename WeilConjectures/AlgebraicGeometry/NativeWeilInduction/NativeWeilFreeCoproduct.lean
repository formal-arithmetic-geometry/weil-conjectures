/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.NativeWeilInduction.NativeWeilInductionComparisonData
import WeilConjectures.CategoryTheory.Exact.ExactFunctorCoproducts
import Mathlib.Algebra.Homology.HomologicalComplexLimits
import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate

/-! # The localized free Weil coproduct cocone -/

@[expose] public noncomputable section

set_option autoImplicit false

universe u v w

open CategoryTheory CategoryTheory.Limits CategoryTheory.Endofunctor

attribute [instance] AlgebraicGeometry.Compactification.over

-- An orbit cofan is characterized by its invertible recurrence and its zeroth leg.
private def orbit_cofan_isColimit
    {D : Type v} [Category.{w} D] (G : D ⥤ D) [G.IsEquivalence]
    (E : ℤ → D) (d : ∀ n, G.obj (E n) ≅ E (n + 1))
    (A : D) (e0 : A ≅ E 0)
    (B : IsoAlgebra G) (j : ∀ n, E n ⟶ B.carrier)
    (hj : ∀ n, G.map (j n) ≫ B.str.hom = (d n).hom ≫ j (n + 1))
    (hc : IsColimit (Cofan.mk B.carrier j)) :
    IsColimit (Cofan.mk B.carrier (IsoAlgebra.Free.hom B (e0.hom ≫ j 0))) := by
  classical
  let a := e0.hom ≫ j 0
  let P (n : ℤ) := ∃ e : IsoAlgebra.Free.obj G A n ≅ E n,
    e.hom ≫ j n = IsoAlgebra.Free.hom B a n
  have forward (n : ℤ) (ih : P n) : P (n + 1) := by
    obtain ⟨e, he⟩ := ih
    refine ⟨(IsoAlgebra.Free.objSucc G A n).symm ≪≫ G.mapIso e ≪≫ d n, ?_⟩
    dsimp only [Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom]
    rw [Category.assoc, Category.assoc, ← hj, ← G.map_comp_assoc, he,
      IsoAlgebra.Free.map_hom_comp_str]
    simp only [Iso.inv_hom_id_assoc]
  have backward (n : ℤ) (ih : P (n + 1)) : P n := by
    obtain ⟨e, he⟩ := ih
    refine ⟨G.preimageIso
      (IsoAlgebra.Free.objSucc G A n ≪≫ e ≪≫ (d n).symm), ?_⟩
    apply G.map_injective
    apply (cancel_mono B.str.hom).1
    rw [G.map_comp, Category.assoc, hj]
    simp only [Functor.preimageIso_hom, Functor.map_preimage,
      Iso.trans_hom, Iso.symm_hom, Category.assoc, Iso.inv_hom_id_assoc]
    rw [he]
    exact (IsoAlgebra.Free.map_hom_comp_str B a n).symm
  have he (n : ℤ) : P n :=
    Int.induction_on n ⟨e0, rfl⟩
      (fun n ih ↦ forward n ih)
      (fun n ih ↦ backward (-(n : ℤ) - 1) (by simpa using ih))
  choose e he using he
  let α : Discrete.functor (IsoAlgebra.Free.obj G A) ≅ Discrete.functor E :=
    Discrete.natIso (fun n ↦ e n.as)
  apply (IsColimit.equivOfNatIsoOfIso α _ _ ?_).symm hc
  refine Cocone.ext (Iso.refl _) ?_
  intro n
  change ((e n.as).inv ≫ IsoAlgebra.Free.hom B a n.as) ≫ 𝟙 _ = j n.as
  rw [← he]
  simp

-- Construct the heart coproduct degree by degree, before applying localization.
section ComplexOrbits

variable {C : Type v} [Category.{w} C] [Abelian C]
  (F : C ⥤ C) [F.Additive] [F.IsEquivalence]

private abbrev orbitFunctor (n : ℤ) : C ⥤ C where
  obj X := IsoAlgebra.Free.obj F X n
  map f := IsoAlgebra.Free.objMap F f n
  map_id X := by
    cases n with
    | ofNat n =>
      induction n with
      | zero => rfl
      | succ n ih =>
        simpa only [IsoAlgebra.Free.objMap, IsoAlgebra.Free.posMap,
          IsoAlgebra.Free.obj, IsoAlgebra.Free.posObj, F.map_id] using congrArg F.map ih
    | negSucc n =>
      induction n with
      | zero => exact F.inv.map_id X
      | succ n ih =>
        simpa only [IsoAlgebra.Free.objMap, IsoAlgebra.Free.negMap,
          IsoAlgebra.Free.obj, IsoAlgebra.Free.negObj, F.inv.map_id] using
          congrArg F.inv.map ih
  map_comp f g := by
    cases n with
    | ofNat n =>
      induction n with
      | zero => rfl
      | succ n ih =>
        simpa only [IsoAlgebra.Free.objMap, IsoAlgebra.Free.posMap,
          F.map_comp] using congrArg F.map ih
    | negSucc n =>
      induction n with
      | zero => exact F.inv.map_comp f g
      | succ n ih =>
        simpa only [IsoAlgebra.Free.objMap, IsoAlgebra.Free.negMap,
          F.inv.map_comp] using congrArg F.inv.map ih

private instance orbitInverse_additive : F.inv.Additive := by
  have : F.asEquivalence.functor.Additive := inferInstanceAs F.Additive
  exact Equivalence.inverse_additive F.asEquivalence

private instance orbitFunctor_additive (n : ℤ) : (orbitFunctor F n).Additive where
  map_add {X Y} f g := by
    cases n with
    | ofNat n =>
      induction n with
      | zero => rfl
      | succ n ih =>
        simpa only [orbitFunctor, IsoAlgebra.Free.objMap, IsoAlgebra.Free.posMap,
          F.map_add] using congrArg F.map ih
    | negSucc n =>
      induction n with
      | zero => exact F.inv.map_add (f := f) (g := g)
      | succ n ih =>
        simpa only [orbitFunctor, IsoAlgebra.Free.objMap, IsoAlgebra.Free.negMap,
          F.inv.map_add] using congrArg F.inv.map ih

private abbrev orbitStep (n : ℤ) : orbitFunctor F n ⋙ F ≅ orbitFunctor F (n + 1) :=
  NatIso.ofComponents (fun X ↦ IsoAlgebra.Free.objSucc F X n)
    (fun f ↦ IsoAlgebra.Free.map_objMap_comp_objSucc f n)

variable [HasCoproducts.{0} C]

private abbrev orbitLeg (n : ℤ) : orbitFunctor F n ⟶ IsoAlgebra.Free.functor F ⋙
    IsoAlgebra.forget F where
  app X := Sigma.ι (IsoAlgebra.Free.obj F X) n
  naturality X Y f := by
    change IsoAlgebra.Free.objMap F f n ≫ Sigma.ι _ n =
      Sigma.ι _ n ≫ Limits.Sigma.map _
    rw [Sigma.ι_map]

private abbrev orbitComplexCofan (K : CochainComplex C ℤ) :
    Cofan (fun n : ℤ ↦ ((orbitFunctor F n).mapHomologicalComplex (.up ℤ)).obj K) :=
  Cofan.mk (((IsoAlgebra.Free.functor F ⋙ IsoAlgebra.forget F).mapHomologicalComplex
    (.up ℤ)).obj K)
    (fun n ↦ ((orbitLeg F n).mapHomologicalComplex (.up ℤ)).app K)

private def orbitComplexCofan_isColimit (K : CochainComplex C ℤ) :
    IsColimit (orbitComplexCofan F K) := by
  apply HomologicalComplex.isColimitOfEval
  intro i
  refine (Cofan.isColimitMapCoconeEquiv
    (HomologicalComplex.eval C (.up ℤ) i) _ (orbitComplexCofan F K)).symm ?_
  exact coproductIsCoproduct (IsoAlgebra.Free.obj F (K.X i))

private abbrev orbitComplexStructure (K : CochainComplex C ℤ) :
    (F.mapHomologicalComplex (.up ℤ)).obj (orbitComplexCofan F K).pt ≅
      (orbitComplexCofan F K).pt :=
  (NatIso.mapHomologicalComplex (IsoAlgebra.strNatIso F) (.up ℤ)).app
    (((IsoAlgebra.Free.functor F).mapHomologicalComplex (.up ℤ)).obj K)

private abbrev orbitComplexStep (K : CochainComplex C ℤ) (n : ℤ) :
    (F.mapHomologicalComplex (.up ℤ)).obj
      (((orbitFunctor F n).mapHomologicalComplex (.up ℤ)).obj K) ≅
    ((orbitFunctor F (n + 1)).mapHomologicalComplex (.up ℤ)).obj K :=
  (NatIso.mapHomologicalComplex (orbitStep F n) (.up ℤ)).app K

private theorem orbitComplex_rec (K : CochainComplex C ℤ) (n : ℤ) :
    (F.mapHomologicalComplex (.up ℤ)).map ((orbitComplexCofan F K).inj n) ≫
        (orbitComplexStructure F K).hom =
      (orbitComplexStep F K n).hom ≫ (orbitComplexCofan F K).inj (n + 1) := by
  ext i
  exact IsoAlgebra.Free.map_ι_comp_str F (K.X i) n

variable [HasDerivedCategory.{w} C] [Abelian.HasKInjectiveResolutions C]
  [PreservesFiniteLimits (IsoAlgebra.Free.functor F)]

private abbrev orbitLocalizedPair (K : CochainComplex C ℤ) :
    IsoAlgebra F.mapDerivedCategory :=
  IsoAlgebra.mk (DerivedCategory.Q.obj (orbitComplexCofan F K).pt)
    (F.mapDerivedCategoryFactors.app (orbitComplexCofan F K).pt ≪≫
      DerivedCategory.Q.mapIso (orbitComplexStructure F K))

variable [HasDerivedCategory.{w} (IsoAlgebra F)] [IsGrothendieckAbelian.{w} C]

-- Keep the specified exact localization comparisons, including their unit normalization.
private abbrev derivedFreeStructure :
    (IsoAlgebra.forget F).mapDerivedCategory ⋙ F.mapDerivedCategory ≅
      (IsoAlgebra.forget F).mapDerivedCategory :=
  (Functor.mapDerivedCategoryCompIso _ _).symm ≪≫
    Functor.mapDerivedCategoryNatIso (IsoAlgebra.strNatIso F)

private def freeLocalization (K : CochainComplex C ℤ) :
    (IsoAlgebra.forget F).mapDerivedCategory.obj
        ((IsoAlgebra.Free.functor F).mapDerivedCategory.obj (DerivedCategory.Q.obj K)) ≅
      (orbitLocalizedPair F K).carrier :=
  (IsoAlgebra.forget F).mapDerivedCategory.mapIso
      ((IsoAlgebra.Free.functor F).mapDerivedCategoryFactors.app K) ≪≫
    (IsoAlgebra.forget F).mapDerivedCategoryFactors.app
      (((IsoAlgebra.Free.functor F).mapHomologicalComplex (.up ℤ)).obj K)

omit [HasCoproducts.{0} C] [Abelian.HasKInjectiveResolutions C]
  [PreservesFiniteLimits (IsoAlgebra.Free.functor F)] [IsGrothendieckAbelian.{w} C] in
private theorem derivedFreeStructure_fac (K : CochainComplex (IsoAlgebra F) ℤ) :
    (derivedFreeStructure F).hom.app (DerivedCategory.Q.obj K) ≫
        (IsoAlgebra.forget F).mapDerivedCategoryFactors.hom.app K =
      F.mapDerivedCategory.map
          ((IsoAlgebra.forget F).mapDerivedCategoryFactors.hom.app K) ≫
        F.mapDerivedCategoryFactors.hom.app
          (((IsoAlgebra.forget F).mapHomologicalComplex (.up ℤ)).obj K) ≫
        DerivedCategory.Q.map
          ((NatTrans.mapHomologicalComplex (IsoAlgebra.strNatIso F).hom (.up ℤ)).app K) := by
  dsimp only [derivedFreeStructure, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app]
  rw [Category.assoc, Functor.mapDerivedCategoryNatIso_fac]
  rw [← Functor.mapDerivedCategoryCompIso_hom_app_factors
    (IsoAlgebra.forget F) F K]
  simp only [Category.assoc, Iso.inv_hom_id_app_assoc]

omit [Abelian.HasKInjectiveResolutions C] [IsGrothendieckAbelian.{w} C] in
private theorem freeLocalization_str (K : CochainComplex C ℤ) :
    F.mapDerivedCategory.map (freeLocalization F K).hom ≫
        (orbitLocalizedPair F K).str.hom =
      (derivedFreeStructure F).hom.app
          ((IsoAlgebra.Free.functor F).mapDerivedCategory.obj (DerivedCategory.Q.obj K)) ≫
        (freeLocalization F K).hom := by
  let I := IsoAlgebra.Free.functor F
  let U := IsoAlgebra.forget F
  let Ic := I.mapHomologicalComplex (.up ℤ)
  have h := (derivedFreeStructure F).hom.naturality
    (I.mapDerivedCategoryFactors.hom.app K)
  dsimp only [Functor.comp_map] at h
  change F.mapDerivedCategory.map
      (U.mapDerivedCategory.map (I.mapDerivedCategoryFactors.hom.app K) ≫
        U.mapDerivedCategoryFactors.hom.app (Ic.obj K)) ≫
      (F.mapDerivedCategoryFactors.hom.app _ ≫
        DerivedCategory.Q.map (orbitComplexStructure F K).hom) = _
  rw [F.mapDerivedCategory.map_comp]
  simp only [Category.assoc]
  erw [← derivedFreeStructure_fac F (Ic.obj K)]
  simpa [freeLocalization, I, U, Ic, Category.assoc] using
    congrArg (fun t ↦ t ≫ U.mapDerivedCategoryFactors.hom.app (Ic.obj K)) h

omit [Abelian.HasKInjectiveResolutions C] in
private theorem freeLocalization_unit (K : CochainComplex C ℤ) :
    (IsoAlgebra.freeWeilDerivedAdjunction F).unit.app (DerivedCategory.Q.obj K) ≫
        (freeLocalization F K).hom =
      DerivedCategory.Q.map ((orbitComplexCofan F K).inj 0) := by
  let I := IsoAlgebra.Free.functor F
  let U := IsoAlgebra.forget F
  let : CatCommSq (I.mapHomologicalComplex (.up ℤ)) DerivedCategory.Q
      DerivedCategory.Q I.mapDerivedCategory := ⟨I.mapDerivedCategoryFactors.symm⟩
  let : CatCommSq (U.mapHomologicalComplex (.up ℤ)) DerivedCategory.Q
      DerivedCategory.Q U.mapDerivedCategory := ⟨U.mapDerivedCategoryFactors.symm⟩
  have h := Adjunction.Localization.ε_app
    ((IsoAlgebra.Free.adjunction F).mapHomologicalComplex (.up ℤ))
    DerivedCategory.Q (HomologicalComplex.quasiIso C (.up ℤ))
    DerivedCategory.Q I.mapDerivedCategory U.mapDerivedCategory K
  change (IsoAlgebra.freeWeilDerivedAdjunction F).unit.app (DerivedCategory.Q.obj K) =
    DerivedCategory.Q.map
        (((IsoAlgebra.Free.adjunction F).mapHomologicalComplex (.up ℤ)).unit.app K) ≫
      U.mapDerivedCategoryFactors.inv.app
        ((I.mapHomologicalComplex (.up ℤ)).obj K) ≫
      U.mapDerivedCategory.map (I.mapDerivedCategoryFactors.inv.app K) at h
  rw [h]
  change (_ ≫ U.mapDerivedCategoryFactors.inv.app _ ≫
      U.mapDerivedCategory.map (I.mapDerivedCategoryFactors.inv.app K)) ≫
    (U.mapDerivedCategory.map (I.mapDerivedCategoryFactors.hom.app K) ≫
      U.mapDerivedCategoryFactors.hom.app _) = _
  simp only [Category.assoc, ← U.mapDerivedCategory.map_comp_assoc,
    Iso.inv_hom_id_app]
  erw [CategoryTheory.Functor.map_id]
  simp only [Category.id_comp, Iso.inv_hom_id_app, Category.comp_id]
  apply congrArg DerivedCategory.Q.map
  ext i
  rw [(IsoAlgebra.Free.adjunction F).mapHomologicalComplex_unit_app_f (.up ℤ) K i]
  change Sigma.ι (IsoAlgebra.Free.obj F (K.X i)) 0 ≫ 𝟙 _ = Sigma.ι _ 0
  exact Category.comp_id _

-- Work with any complex representative; no strictification of derived fixed pairs is used.
private theorem localized_free_coproduct (A : DerivedCategory C) :
    Nonempty (IsColimit (Cofan.mk
      ((IsoAlgebra.forget F).mapDerivedCategory.obj
        ((IsoAlgebra.Free.functor F).mapDerivedCategory.obj A))
      (IsoAlgebra.Free.hom
        (IsoAlgebra.mk _ ((derivedFreeStructure F).app
          ((IsoAlgebra.Free.functor F).mapDerivedCategory.obj A)))
        ((IsoAlgebra.freeWeilDerivedAdjunction F).unit.app A)))) := by
  let I := IsoAlgebra.Free.functor F
  let U := IsoAlgebra.forget F
  let G := F.mapDerivedCategory
  let Q := DerivedCategory.Q (C := C)
  let K := Q.objPreimage A
  let r : Q.obj K ≅ A := Q.objObjPreimageIso A
  let c := orbitComplexCofan F K
  let N : IsoAlgebra G :=
    IsoAlgebra.mk _ ((derivedFreeStructure F).app (I.mapDerivedCategory.obj A))
  let e : N.carrier ≅ (orbitLocalizedPair F K).carrier :=
    (I.mapDerivedCategory ⋙ U.mapDerivedCategory).mapIso r.symm ≪≫ freeLocalization F K
  let E (n : ℤ) := Q.obj (((orbitFunctor F n).mapHomologicalComplex (.up ℤ)).obj K)
  let d (n : ℤ) : G.obj (E n) ≅ E (n + 1) :=
    F.mapDerivedCategoryFactors.app _ ≪≫ Q.mapIso (orbitComplexStep F K n)
  let j (n : ℤ) : E n ⟶ N.carrier := Q.map (c.inj n) ≫ e.inv
  have he : G.map e.hom ≫ (orbitLocalizedPair F K).str.hom = N.str.hom ≫ e.hom := by
    change G.map (U.mapDerivedCategory.map (I.mapDerivedCategory.map r.inv) ≫
      (freeLocalization F K).hom) ≫ (orbitLocalizedPair F K).str.hom = _
    rw [G.map_comp, Category.assoc]
    erw [freeLocalization_str]
    simpa [e, N, I, U, G, Q, Category.assoc] using
      congrArg (fun t ↦ t ≫ (freeLocalization F K).hom)
        ((derivedFreeStructure F).hom.naturality (I.mapDerivedCategory.map r.inv))
  have hu : (IsoAlgebra.freeWeilDerivedAdjunction F).unit.app A ≫ e.hom =
      r.inv ≫ Q.map (c.inj 0) := by
    have hn : (IsoAlgebra.freeWeilDerivedAdjunction F).unit.app A ≫
        U.mapDerivedCategory.map (I.mapDerivedCategory.map r.inv) =
        r.inv ≫ (IsoAlgebra.freeWeilDerivedAdjunction F).unit.app (Q.obj K) :=
      ((IsoAlgebra.freeWeilDerivedAdjunction F).unit.naturality r.inv).symm
    change (IsoAlgebra.freeWeilDerivedAdjunction F).unit.app A ≫
      (U.mapDerivedCategory.map (I.mapDerivedCategory.map r.inv) ≫
        (freeLocalization F K).hom) = _
    rw [← Category.assoc, hn, Category.assoc]
    exact congrArg (fun t ↦ r.inv ≫ t) (freeLocalization_unit F K)
  have hzero : r.inv ≫ j 0 = (IsoAlgebra.freeWeilDerivedAdjunction F).unit.app A := by
    apply (cancel_mono e.hom).1
    simpa only [j, Category.assoc, Iso.inv_hom_id, Category.comp_id] using hu.symm
  have : PreservesColimitsOfShape (Discrete ℤ) Q := derived_Q_preservesCoproducts ℤ
  have hcQ : IsColimit (Cofan.mk (Q.obj c.pt) (fun n ↦ Q.map (c.inj n))) :=
    (Cofan.isColimitMapCoconeEquiv Q _ c)
      (isColimitOfPreserves Q (orbitComplexCofan_isColimit F K))
  have hc : IsColimit (Cofan.mk N.carrier j) := by
    apply IsColimit.ofIsoColimit hcQ
    refine Cocone.ext e.symm ?_
    intro n
    rfl
  have hj (n : ℤ) : G.map (j n) ≫ N.str.hom = (d n).hom ≫ j (n + 1) := by
    have hq : G.map (Q.map (c.inj n)) ≫ (orbitLocalizedPair F K).str.hom =
        (d n).hom ≫ Q.map (c.inj (n + 1)) := by
      change G.map (Q.map (c.inj n)) ≫
        (F.mapDerivedCategoryFactors.hom.app c.pt ≫
          Q.map (orbitComplexStructure F K).hom) =
        (F.mapDerivedCategoryFactors.hom.app _ ≫
          Q.map (orbitComplexStep F K n).hom) ≫ Q.map (c.inj (n + 1))
      rw [← Category.assoc]
      erw [F.mapDerivedCategoryFactors.hom.naturality]
      simp only [CategoryTheory.Functor.comp_map, Category.assoc]
      rw [← Q.map_comp, orbitComplex_rec, Q.map_comp]
    apply (cancel_mono e.hom).1
    simp only [Category.assoc, j, Iso.inv_hom_id, Category.comp_id]
    rw [← he, ← G.map_comp_assoc]
    simpa only [Category.assoc, Iso.inv_hom_id, Category.comp_id] using hq
  have h := orbit_cofan_isColimit G E d A r.symm N j hj hc
  change IsColimit (Cofan.mk N.carrier (IsoAlgebra.Free.hom N (r.inv ≫ j 0))) at h
  rw [hzero] at h
  exact ⟨h⟩

end ComplexOrbits

namespace AlgebraicGeometry.NativeWeilInduction

variable (k₀ : Type u) [Field k₀] [Finite k₀] (l : ℕ) [Fact l.Prime]
  [Fact (ringChar k₀ ≠ l)]

omit [Fact (ringChar k₀ ≠ l)] in
/-- The integer cofan defined by the localized free unit and structure is colimiting.
Source: free-derived-resolution proof steps 3--4 and native comparison proof step 2.
(blueprint: lem-sf-native-weil-free-coproduct)

Proof: represent A by a complex. The heart free induction is the coproduct of integer
Frobenius translates, with its unit the zeroth coprojection. Termwise coproducts
compute ordinary derived coproducts in the Grothendieck heart. Localizing the free
adjunction identifies its unit with that zeroth coprojection after the specified exact
factorizations. Positive and negative induction with the free structure recurrence
identifies the localized leg at n with inclusion at n. Transport the termwise
colimiting cofan through the exact factorizations. For arbitrary derived A, transport
along a representative isomorphism; naturality of the localized unit and structure
preserves every leg. Thus the specified cofan is colimiting. -/
theorem nativeWeil_free_coproduct
    (T : Scheme.{u}) [T.Over (Spec (.of k₀))]
    (A : _root_.DerivedCategory
      (ProEtale.AdicSheaf l (T ↘ Spec (.of k₀)).geometricFiber)) :
    Nonempty (IsColimit (Cofan.mk
      ((forget k₀ l T).obj ((induction k₀ l T).obj A)) (inclusion k₀ l T A))) := by
  let C := ProEtale.AdicSheaf l (T ↘ Spec (.of k₀)).geometricFiber
  have : HasCoproducts.{u + 1} C := fun J ↦
    IsGrothendieckAbelian.hasColimitsOfShape_discrete.{u + 2, u + 1, u + 1} C J
  have : HasCoproducts.{0} C := hasCoproducts_shrink.{0, u + 1}
  have : Abelian.HasKInjectiveResolutions C :=
    Abelian.hasKInjectiveResolutions_of_isGrothendieckAbelian.{u + 1}
  exact localized_free_coproduct (WeilSheaf.frobeniusPullback k₀ l T) A

end AlgebraicGeometry.NativeWeilInduction
