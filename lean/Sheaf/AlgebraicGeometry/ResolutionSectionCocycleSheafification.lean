/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF groups P7, F2
-/
module

public import Sheaf.CategoryTheory.OrdinaryComplexAdjunct
public import Sheaf.AlgebraicGeometry.ResolutionCocycleHomologyTail

/-! # Sheafification of a section cocycle

Source: Stacks Project, Tag 072W.
(blueprint: lem-weil-pbc-resolution-section-cocycle-sheafification).
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.Functor AlgebraicGeometry.Etale
namespace AlgebraicGeometry.Etale

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 2048
set_option backward.defeqAttrib.useBackward true
attribute [local instance] RawRestrictedComparison.etaleComposition
  RawRestrictedComparison.etaleIdentities RawRestrictedComparison.etalePullbacks
  RawRestrictedComparison.etaleBaseChange RawRestrictedComparison.sheafifyInstance
  RawRestrictedComparison.weakSheafifyInstance
attribute [local irreducible] normalizationResolutionCocycleIso
  RawRestrictedComparison.chainEvaluation upperStar

private theorem map_cycles_projection
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    (L : C ⥤ D) [L.Additive] [L.PreservesHomology] (T : ShortComplex C) :
    L.map T.homologyπ ≫ (T.mapHomologyIso L).inv =
      (T.mapCyclesIso L).inv ≫ (T.map L).homologyπ := by
  let h := T.homologyData.left
  rw [h.mapHomologyIso_eq L, h.mapCyclesIso_eq L]
  simp only [Iso.trans_inv, Functor.mapIso_inv, Iso.symm_inv]
  rw [← L.map_comp_assoc, h.homologyπ_comp_homologyIso_hom,
    L.map_comp, Category.assoc]
  erw [(h.map L).π_comp_homologyIso_inv]
  simp only [Category.assoc]

private theorem evaluation_cycles_projection
    {C : Type*} [Category C] [Abelian C]
    (E : C ⥤ AddCommGrpCat.{u + 1}) [E.Additive] [E.PreservesHomology]
    (T : ShortComplex C) :
    (T.mapCyclesIso E).hom ≫ E.map T.homologyπ =
      (T.map E).homologyπ ≫ (T.mapHomologyIso E).hom := by
  rw [← cancel_mono (T.mapHomologyIso E).inv, Category.assoc, Category.assoc,
    Iso.hom_inv_id, Category.comp_id, map_cycles_projection, Iso.hom_inv_id_assoc]

private theorem ordinary_adjunct_f0
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    (L : C ⥤ D) (R : D ⥤ C) [L.Additive] [R.Additive] (adj : L ⊣ R)
    (A : C) (J : CochainComplex D ℤ)
    (c : (CochainComplex.singleFunctor D 0).obj (L.obj A) ⟶ J) :
    (HomologicalComplex.singleObjXSelf (.up ℤ) 0 A).inv ≫
        (ordinaryComplexAdjunct L R adj A J c).f 0 =
      adj.unit.app A ≫ R.map
        ((HomologicalComplex.singleObjXSelf (.up ℤ) 0 (L.obj A)).inv ≫ c.f 0) := by
  unfold ordinaryComplexAdjunct
  simp only [HomologicalComplex.comp_f, Functor.mapCochainComplexSingleFunctor,
    CochainComplex.singleFunctor, CochainComplex.singleFunctors,
    HomologicalComplex.single_map_f_self,
    HomologicalComplex.singleMapHomologicalComplex_inv_app_self,
    Functor.mapHomologicalComplex_map_f, Category.assoc]
  simp only [Functor.comp_obj, Functor.map_comp]
  erw [Iso.inv_hom_id_assoc]
  simp only [Iso.inv_hom_id_assoc]

private theorem adjunction_cycles_projection
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    (L : C ⥤ D) (R : D ⥤ C) [L.Additive] [R.Additive] [L.PreservesHomology]
    (adj : L ⊣ R) (K : CochainComplex D ℤ) (i : ℤ) :
    let P := (R.mapHomologicalComplex (.up ℤ)).obj K
    let a := P.liftCycles (R.map (K.iCycles i)) ((ComplexShape.up ℤ).next i) rfl
      (by change R.map (K.iCycles i) ≫ R.map _ = 0
          rw [← R.map_comp, K.iCycles_d, R.map_zero])
    a ≫ P.homologyπ i ≫ adj.unit.app (P.homology i) ≫
        R.map (((P.sc i).mapHomologyIso L).inv ≫
          HomologicalComplex.homologyMap
            ((NatTrans.mapHomologicalComplex adj.counit (.up ℤ)).app K) i) =
      R.map (K.homologyπ i) := by
  dsimp only
  let P := (R.mapHomologicalComplex (.up ℤ)).obj K
  let a := P.liftCycles (R.map (K.iCycles i)) ((ComplexShape.up ℤ).next i) rfl
    (by change R.map (K.iCycles i) ≫ R.map _ = 0
        rw [← R.map_comp, K.iCycles_d, R.map_zero])
  let ε : (L.mapHomologicalComplex (.up ℤ)).obj P ⟶ K :=
    (NatTrans.mapHomologicalComplex adj.counit (.up ℤ)).app K
  change a ≫ P.homologyπ i ≫ adj.unit.app (P.homology i) ≫
    R.map (((P.sc i).mapHomologyIso L).inv ≫ HomologicalComplex.homologyMap ε i) = _
  have ha : L.map a ≫ ((P.sc i).mapCyclesIso L).inv ≫
      HomologicalComplex.cyclesMap ε i = adj.counit.app (K.cycles i) := by
    apply (cancel_mono (K.iCycles i)).1
    rw [Category.assoc, Category.assoc]
    erw [HomologicalComplex.cyclesMap_i]
    change L.map a ≫ ((P.sc i).mapCyclesIso L).inv ≫
      (P.sc i |>.map L).iCycles ≫ adj.counit.app (K.X i) = _
    have hi : ((P.sc i).mapCyclesIso L).inv ≫ (P.sc i |>.map L).iCycles =
        L.map (P.iCycles i) := by
      rw [← ShortComplex.mapCyclesIso_hom_iCycles, Iso.inv_hom_id_assoc]
      rfl
    rw [← Category.assoc _ _ (adj.counit.app (K.X i)), hi,
      ← L.map_comp_assoc, HomologicalComplex.liftCycles_i]
    exact adj.counit.naturality (K.iCycles i)
  have hcomp : L.map a ≫ L.map (P.homologyπ i) ≫
      ((P.sc i).mapHomologyIso L).inv ≫ HomologicalComplex.homologyMap ε i =
      adj.counit.app (K.cycles i) ≫ K.homologyπ i := by
    calc
      _ = L.map a ≫ (L.map (P.homologyπ i) ≫
          ((P.sc i).mapHomologyIso L).inv) ≫
            HomologicalComplex.homologyMap ε i := by simp only [Category.assoc]
      _ = L.map a ≫ ((P.sc i).mapCyclesIso L).inv ≫
          ((L.mapHomologicalComplex (.up ℤ)).obj P).homologyπ i ≫
            HomologicalComplex.homologyMap ε i := by
        erw [map_cycles_projection]
        simp only [Category.assoc]
        rfl
      _ = (L.map a ≫ ((P.sc i).mapCyclesIso L).inv ≫
          HomologicalComplex.cyclesMap ε i) ≫ K.homologyπ i := by
        erw [HomologicalComplex.homologyπ_naturality]
        simp only [Category.assoc]
      _ = _ := by rw [ha]
  calc
    _ = adj.unit.app (R.obj (K.cycles i)) ≫
        R.map (L.map a ≫ L.map (P.homologyπ i) ≫
          ((P.sc i).mapHomologyIso L).inv ≫ HomologicalComplex.homologyMap ε i) := by
      have hn := congrArg
        (fun b => b ≫ R.map (((P.sc i).mapHomologyIso L).inv ≫
          HomologicalComplex.homologyMap ε i))
        (adj.unit.naturality (a ≫ P.homologyπ i))
      simpa only [Functor.id_map, Functor.comp_map, L.map_comp, R.map_comp,
        Category.assoc] using hn
    _ = _ := by
      rw [hcomp, R.map_comp, ← Category.assoc,
        adj.right_triangle_components]
      exact Category.id_comp _

-- Compare the two section constructions before substituting a pullback chart.
-- This keeps the kernel from expanding localization data at that large object.
private theorem normalization_sections_iso_app {X : Scheme.{u}} (W : X.Etale)
    (B : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) :
    (normalizationSectionsIso W).hom.app B =
      (RawRestrictedComparison.sectionsIso W B).hom := by
  rfl

/-- The sheafification/counit comparison evaluates the ordinary termwise adjunct.
Source: Stacks Project, Tag 072W, proof of lemma-higher-direct-images.
(blueprint: lem-weil-pbc-resolution-section-cocycle-sheafification).

Proof: let A be the free sheaf on V and W its pullback to X. The generator in
RawRestrictedComparison is the ordinary adjunction unit at A evaluated on the identity
generator, transported by sectionsIso. The normalizationSectionsIso is that same sections
isomorphism, so naturality moves c through it. Thus the image of chainEvaluation is the
sectionwise homology class of the termwise adjunct d. Commuting termwise sections with q
and using naturality of the homology shift identifies the class in degree q. Finally
calculate the sheafification/counit comparison on the cycle supplied by the adjunct.
Exactness of sheafification commutes the projection from cycles with mapHomologyIso;
counit naturality moves the cycle inclusion past the counit, and the adjunction triangle
identity cancels the unit with the counit. The resulting map sends a cycle to its class
in the homology sheaf.
Evaluating at V gives the formula. For a boundary both sides vanish; zero c, q=0 and
empty charts obey the same functorial identities. Finally postcompose with the two
prescribed classical resolution comparisons.
No derived adjunction or shifted augmentation occurs in this calculation. -/
theorem resolution_section_cocycle_sheafification {X S : Scheme.{u}} (f : X ⟶ S)
    (q : ℕ) (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    (I : InjectiveResolution F) (V : S.Etale)
    (c : (CochainComplex.singleFunctor _ 0).obj
      ((upperStar AddCommGrpCat.{u + 1} f).obj (RawRestrictedComparison.freeSheaf S V)) ⟶
        (normalizationShiftedResolution F I q).obj) :
    let R := lowerStar AddCommGrpCat.{u + 1} f
    let A := RawRestrictedComparison.freeSheaf S V
    let d : (CochainComplex.singleFunctor _ 0).obj A ⟶
        (R.mapHomologicalComplex (.up ℤ)).obj (normalizationShiftedResolution F I q).obj :=
      ordinaryComplexAdjunct (upperStar AddCommGrpCat.{u + 1} f) R
        (upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} f) A
        (normalizationShiftedResolution F I q).obj c
    let e := ((toSheafify S.smallEtaleTopology
      (uliftYoneda.{u + 1}.obj V ⋙ AddCommGrpCat.free)).app (op V)).hom
        (FreeAbelianGroup.of (ULift.up (𝟙 V)))
    (normalizationResolutionClass f q F I).app (op V)
      ((normalizationResolutionCocycleIso f q F I V).hom
        (RawRestrictedComparison.chainEvaluation f V _ c)) =
      (((HomologicalComplex.singleObjHomologySelfIso (.up ℤ) 0 A).inv ≫
        HomologicalComplex.homologyMap d 0 ≫
        resolutionCocycleHomologyTail f q F I).hom.app (op V)).hom e := by
  let R := lowerStar AddCommGrpCat.{u + 1} f
  let U := sheafToPresheaf S.smallEtaleTopology AddCommGrpCat.{u + 1}
  let L := presheafToSheaf S.smallEtaleTopology AddCommGrpCat.{u + 1}
  let E := (evaluation S.Etaleᵒᵖ AddCommGrpCat.{u + 1}).obj (op V)
  let A := RawRestrictedComparison.freeSheaf S V
  let B := (upperStar AddCommGrpCat.{u + 1} f).obj A
  let W := (MorphismProperty.Over.pullback @Etale ⊤ f).obj V
  let T := RawRestrictedComparison.underivedSections W
  let J := I.cochainComplex
  let K := (R.mapHomologicalComplex (.up ℤ)).obj J
  let P := normalizationPresheafComplex f F I
  let d := ordinaryComplexAdjunct (upperStar AddCommGrpCat.{u + 1} f) R
    (upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} f) A
    (normalizationShiftedResolution F I q).obj c
  let e := ((toSheafify S.smallEtaleTopology
    (uliftYoneda.{u + 1}.obj V ⋙ AddCommGrpCat.free)).app (op V)).hom
      (FreeAbelianGroup.of (ULift.up (𝟙 V)))
  let N := (CochainComplex.singleFunctor _ 0).obj B
  let M := (T.mapHomologicalComplex (.up ℤ)).obj N
  let t := (HomologicalComplex.singleMapHomologicalComplex T (.up ℤ) 0).app B
  let v := HomologicalComplex.cyclesMap t.inv 0
    ((HomologicalComplex.singleObjCyclesSelfIso (.up ℤ) 0 (T.obj B)).inv
      (RawRestrictedComparison.generator f V))
  let φ : M.sc 0 ⟶ (P.sc (q : ℤ)).map E :=
    (HomologicalComplex.shortComplexFunctor _ (.up ℤ) 0).map
        ((T.mapHomologicalComplex (.up ℤ)).map c) ≫
      (HomologicalComplex.shortComplexFunctor _ (.up ℤ) 0).map
        (((T.mapHomologicalComplex (.up ℤ)).commShiftIso (q : ℤ)).hom.app J) ≫
      (CochainComplex.shiftShortComplexFunctorIso _ (q : ℤ) 0 (q : ℤ)
        (add_zero _)).hom.app ((T.mapHomologicalComplex (.up ℤ)).obj J) ≫
      (HomologicalComplex.shortComplexFunctor _ (.up ℤ) (q : ℤ)).map
        ((NatIso.mapHomologicalComplex (normalizationSectionsIso W) (.up ℤ)).hom.app J)
  let ψ : ((CochainComplex.singleFunctor _ 0).obj A).sc 0 ⟶ K.sc (q : ℤ) :=
    (HomologicalComplex.shortComplexFunctor _ (.up ℤ) 0).map d ≫
      (HomologicalComplex.shortComplexFunctor _ (.up ℤ) 0).map
        (((R.mapHomologicalComplex (.up ℤ)).commShiftIso (q : ℤ)).hom.app J) ≫
      (CochainComplex.shiftShortComplexFunctorIso _ (q : ℤ) 0 (q : ℤ)
        (add_zero _)).hom.app K
  let y : A ⟶ K.cycles (q : ℤ) :=
    (HomologicalComplex.singleObjCyclesSelfIso (.up ℤ) 0 A).inv ≫
      ShortComplex.cyclesMap ψ
  let a := P.liftCycles (U.map (K.iCycles (q : ℤ)))
    ((ComplexShape.up ℤ).next (q : ℤ)) rfl
    (by change U.map (K.iCycles (q : ℤ)) ≫
          U.map (K.d (q : ℤ) ((ComplexShape.up ℤ).next (q : ℤ))) = 0
        rw [← U.map_comp, K.iCycles_d, U.map_zero])
  let z := ((P.sc (q : ℤ)).mapCyclesIso E).hom (ShortComplex.cyclesMap φ v)
  have hb : (RawRestrictedComparison.underivedSingleIso W B).inv
      (RawRestrictedComparison.generator f V) = M.homologyπ 0 v := by
    dsimp only [RawRestrictedComparison.underivedSingleIso, Iso.trans_inv,
      Functor.mapIso_inv, HomologicalComplex.homologyFunctor_map]
    have h := ConcreteCategory.congr_hom
      (HomologicalComplex.singleObjCyclesSelfIso_inv_homologyπ (.up ℤ) 0 (T.obj B))
      (RawRestrictedComparison.generator f V)
    simp only [ConcreteCategory.comp_apply] at h
    simp only [ConcreteCategory.comp_apply]
    erw [← h]
    exact ConcreteCategory.congr_hom (HomologicalComplex.homologyπ_naturality t.inv 0) _
  have hz : (normalizationResolutionCocycleIso f q F I V).hom
      (RawRestrictedComparison.chainEvaluation f V _ c) = (E.map (P.homologyπ _)) z := by
    have hn := ConcreteCategory.congr_hom (ShortComplex.homologyπ_naturality φ) v
    have he := ConcreteCategory.congr_hom
      (evaluation_cycles_projection E (P.sc (q : ℤ))) (ShortComplex.cyclesMap φ v)
    simp only [ConcreteCategory.comp_apply] at hn he
    calc
      _ = ((P.sc (q : ℤ)).mapHomologyIso E).hom
          (ShortComplex.homologyMap φ
            ((RawRestrictedComparison.underivedSingleIso W B).inv
              (RawRestrictedComparison.generator f V))) := by
        simp only [φ, ShortComplex.homologyMap_comp,
          RawRestrictedComparison.chainEvaluation, normalizationResolutionCocycleIso,
          Iso.trans_hom, Functor.mapIso_hom, HomologicalComplex.homologyFunctor_map,
          ConcreteCategory.comp_apply]
        rfl
      _ = _ :=
        (congrArg ((P.sc (q : ℤ)).mapHomologyIso E).hom
          ((congrArg (ShortComplex.homologyMap φ) hb).trans hn)).trans he.symm
  have hx : z = (E.map (U.map y ≫ a)) e := by
    have hv : M.iCycles 0 v =
        T.map (HomologicalComplex.singleObjXSelf (.up ℤ) 0 B).inv
          (RawRestrictedComparison.generator f V) := by
      have hv' : (HomologicalComplex.singleObjCyclesSelfIso (.up ℤ) 0 (T.obj B)).inv ≫
          HomologicalComplex.cyclesMap t.inv 0 ≫ M.iCycles 0 =
          T.map (HomologicalComplex.singleObjXSelf (.up ℤ) 0 B).inv := by
        erw [HomologicalComplex.cyclesMap_i]
        dsimp only [t]
        erw [HomologicalComplex.singleMapHomologicalComplex_inv_app_self]
        erw [HomologicalComplex.singleObjCyclesSelfIso_inv_iCycles_assoc,
          Iso.inv_hom_id_assoc]
      exact ConcreteCategory.congr_hom hv' (RawRestrictedComparison.generator f V)
    have hy : y ≫ K.iCycles (q : ℤ) =
        (HomologicalComplex.singleObjXSelf (.up ℤ) 0 A).inv ≫ ψ.τ₂ := by
      change (HomologicalComplex.singleObjCyclesSelfIso (.up ℤ) 0 A).inv ≫
        ShortComplex.cyclesMap ψ ≫ (K.sc (q : ℤ)).iCycles = _
      rw [ShortComplex.cyclesMap_i]
      exact HomologicalComplex.singleObjCyclesSelfIso_inv_iCycles_assoc _ _ _ _
    apply (AddCommGrpCat.mono_iff_injective (E.map (P.iCycles (q : ℤ)))).mp
      inferInstance
    have hzi : ShortComplex.cyclesMap φ ≫ ((P.sc (q : ℤ)).mapCyclesIso E).hom ≫
        E.map (P.iCycles (q : ℤ)) = M.iCycles 0 ≫ φ.τ₂ := by
      change ShortComplex.cyclesMap φ ≫ ((P.sc (q : ℤ)).mapCyclesIso E).hom ≫
        E.map (P.sc (q : ℤ)).iCycles = (M.sc 0).iCycles ≫ φ.τ₂
      rw [ShortComplex.mapCyclesIso_hom_iCycles]
      exact ShortComplex.cyclesMap_i φ
    have hzi' := ConcreteCategory.congr_hom hzi v
    simp only [ConcreteCategory.comp_apply] at hzi'
    change (E.map (P.iCycles (q : ℤ))) z = _ at hzi'
    have hr : (E.map (P.iCycles (q : ℤ))) ((E.map (U.map y ≫ a)) e) =
        (E.map (U.map
          ((HomologicalComplex.singleObjXSelf (.up ℤ) 0 A).inv ≫ ψ.τ₂))) e := by
      rw [← ConcreteCategory.comp_apply, ← E.map_comp, Category.assoc,
        HomologicalComplex.liftCycles_i, ← U.map_comp, hy]
      rfl
    let h : (normalizationShiftedResolution F I q).obj.X 0 ⟶ J.X (q : ℤ) :=
      (J.XIsoOfEq (zero_add (q : ℤ))).hom
    let b := (HomologicalComplex.singleObjXSelf (.up ℤ) 0 B).inv ≫ c.f 0 ≫ h
    have hφ : T.map (HomologicalComplex.singleObjXSelf (.up ℤ) 0 B).inv ≫ φ.τ₂ =
        T.map b ≫ (normalizationSectionsIso W).hom.app (J.X (q : ℤ)) := by
      simp only [φ, b, h, ShortComplex.comp_τ₂,
        HomologicalComplex.shortComplexFunctor_map_τ₂,
        Functor.mapHomologicalComplex_map_f,
        Functor.mapHomologicalComplex_commShiftIso_hom_app_f,
        CochainComplex.shiftShortComplexFunctorIso_hom_app_τ₂,
        NatIso.mapHomologicalComplex_hom_app_f, T.map_comp, Category.assoc]
      dsimp only [CochainComplex.shiftEval, HomologicalComplex.XIsoOfEq]
      simp only [eqToIso.hom, eqToHom_map]
      rfl
    have hψ : (HomologicalComplex.singleObjXSelf (.up ℤ) 0 A).inv ≫ ψ.τ₂ =
        (upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} f).unit.app A ≫ R.map b := by
      calc
        _ = ((HomologicalComplex.singleObjXSelf (.up ℤ) 0 A).inv ≫ d.f 0) ≫
            R.map h := by
          simp only [ψ, h, ShortComplex.comp_τ₂,
            HomologicalComplex.shortComplexFunctor_map_τ₂,
            Functor.mapHomologicalComplex_commShiftIso_hom_app_f, Category.assoc,
            CochainComplex.shiftShortComplexFunctorIso_hom_app_τ₂]
          dsimp only [CochainComplex.shiftEval, HomologicalComplex.XIsoOfEq]
          simp only [eqToIso.hom, eqToHom_map]
          rfl
        _ = _ := by
          rw [ordinary_adjunct_f0]
          simp only [b, R.map_comp, Category.assoc]
          rfl
    have hn := ConcreteCategory.congr_hom ((normalizationSectionsIso W).hom.naturality b)
      (RawRestrictedComparison.generator f V)
    have hφ' := ConcreteCategory.congr_hom hφ (RawRestrictedComparison.generator f V)
    simp only [ConcreteCategory.comp_apply] at hn hφ'
    have hg : (normalizationSectionsIso W).hom.app B
        (RawRestrictedComparison.generator f V) =
      (((upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} f).unit.app A).hom.app
        (op V)) e := by
      rw [normalization_sections_iso_app]
      change (RawRestrictedComparison.sectionsIso W B).hom
        ((RawRestrictedComparison.sectionsIso W B).inv _) = _
      exact Iso.inv_hom_id_apply _ _
    have hψeval := ConcreteCategory.congr_hom (E.congr_map (U.congr_map hψ)) e
    simp only [U.map_comp, E.map_comp, ConcreteCategory.comp_apply] at hψeval
    have hterm : φ.τ₂
        (T.map (HomologicalComplex.singleObjXSelf (.up ℤ) 0 B).inv
          (RawRestrictedComparison.generator f V)) =
        (E.map (U.map
          ((HomologicalComplex.singleObjXSelf (.up ℤ) 0 A).inv ≫ ψ.τ₂))) e :=
      hφ'.trans (hn.trans
        ((congrArg (fun v => (E.map (U.map (R.map b))) v) hg).trans hψeval.symm))
    exact hzi'.trans ((congrArg φ.τ₂ hv).trans (hterm.trans hr.symm))
  let θ := sheafificationAdjunction S.smallEtaleTopology AddCommGrpCat.{u + 1}
  let ε : (L.mapHomologicalComplex (.up ℤ)).obj P ⟶ K :=
    (NatTrans.mapHomologicalComplex θ.counit (.up ℤ)).app K
  let σ := θ.unit.app (P.homology (q : ℤ)) ≫
    U.map (((P.sc (q : ℤ)).mapHomologyIso L).inv ≫
      HomologicalComplex.homologyMap ε (q : ℤ))
  have hπ := adjunction_cycles_projection L U θ K (q : ℤ)
  have hproject : (E.map σ)
      ((normalizationResolutionCocycleIso f q F I V).hom
        (RawRestrictedComparison.chainEvaluation f V _ c)) =
      (E.map (U.map (y ≫ K.homologyπ (q : ℤ)))) e := by
    have hs := congrArg (E.map σ)
      (hz.trans (congrArg (E.map (P.homologyπ (q : ℤ))) hx))
    have hh : (U.map y ≫ a) ≫ P.homologyπ (q : ℤ) ≫ σ =
        U.map (y ≫ K.homologyπ (q : ℤ)) := by
      simp only [σ, Category.assoc]
      erw [hπ]
      simp only [U.map_comp]
    apply hs.trans
    simpa only [E.map_comp, ConcreteCategory.comp_apply] using!
      ConcreteCategory.congr_hom (E.congr_map hh) e
  let shiftComplex :
      ((R.mapHomologicalComplex (.up ℤ)).obj
        (normalizationShiftedResolution F I q).obj).homology 0 ⟶
        (K⟦(q : ℤ)⟧).homology 0 := HomologicalComplex.homologyMap
    (((R.mapHomologicalComplex (.up ℤ)).commShiftIso (q : ℤ)).hom.app J) 0
  let shiftHomology : (K⟦(q : ℤ)⟧).homology 0 ⟶ K.homology (q : ℤ) :=
    ((HomologicalComplex.homologyFunctor
    (Sheaf S.smallEtaleTopology AddCommGrpCat.{u + 1}) (.up ℤ) 0).shiftIso
      (q : ℤ) 0 (q : ℤ) (add_zero _)).hom.app K
  let shiftTail := shiftComplex ≫ shiftHomology
  let b := (HomologicalComplex.singleObjHomologySelfIso (.up ℤ) 0 A).inv ≫
    HomologicalComplex.homologyMap d 0 ≫ shiftTail
  have hcore : y ≫ K.homologyπ (q : ℤ) = b := by
    have hyπ : y ≫ K.homologyπ (q : ℤ) =
        (HomologicalComplex.singleObjHomologySelfIso (.up ℤ) 0 A).inv ≫
          ShortComplex.homologyMap ψ := by
      change (HomologicalComplex.singleObjCyclesSelfIso (.up ℤ) 0 A).inv ≫
        ShortComplex.cyclesMap ψ ≫ (K.sc (q : ℤ)).homologyπ = _
      rw [← ShortComplex.homologyπ_naturality]
      exact HomologicalComplex.singleObjCyclesSelfIso_inv_homologyπ_assoc _ _ _ _
    rw [hyπ]
    simp only [b, shiftTail, shiftComplex, shiftHomology, ψ,
      ShortComplex.homologyMap_comp]
    erw [CochainComplex.ShiftSequence.shiftIso_hom_app]
    rfl
  have hsection : (E.map σ)
      ((normalizationResolutionCocycleIso f q F I V).hom
        (RawRestrictedComparison.chainEvaluation f V _ c)) =
      (E.map (U.map b)) e :=
    hproject.trans (ConcreteCategory.congr_hom (E.congr_map (U.congr_map hcore)) e)
  let k : K.homology (q : ℤ) ⟶
      (DerivedCategory.Plus.homologyFunctor
        (Sheaf S.smallEtaleTopology AddCommGrpCat.{u + 1}) (q : ℤ)).obj
        (R.rightDerivedFunctorPlus.obj ((DerivedCategory.Plus.singleFunctor _ 0).obj F)) :=
    (I.isoRightDerivedObjCochainComplex R q).inv ≫
      (R.homologyRightDerivedFunctorPlusObjSingleFunctorIso F q).inv
  have hclass : normalizationResolutionClass f q F I = σ ≫ U.map k := by
    change θ.unit.app _ ≫ U.map
      (((P.sc (q : ℤ)).mapHomologyIso L).inv ≫
        HomologicalComplex.homologyMap ε (q : ℤ) ≫ k) =
      (θ.unit.app _ ≫ U.map
        (((P.sc (q : ℤ)).mapHomologyIso L).inv ≫
          HomologicalComplex.homologyMap ε (q : ℤ))) ≫ U.map k
    rw [← Category.assoc ((P.sc (q : ℤ)).mapHomologyIso L).inv
      (HomologicalComplex.homologyMap ε (q : ℤ)) k, U.map_comp, Category.assoc]
  have htail : resolutionCocycleHomologyTail f q F I = shiftTail ≫ k := by
    unfold resolutionCocycleHomologyTail
    exact (Category.assoc shiftComplex shiftHomology k).symm
  have hpost := congrArg (fun x => (E.map (U.map k)) x) hsection
  change (E.map (normalizationResolutionClass f q F I))
      ((normalizationResolutionCocycleIso f q F I V).hom
        (RawRestrictedComparison.chainEvaluation f V _ c)) =
    (E.map (U.map
      ((HomologicalComplex.singleObjHomologySelfIso (.up ℤ) 0 A).inv ≫
        HomologicalComplex.homologyMap d 0 ≫ resolutionCocycleHomologyTail f q F I))) e
  rw [hclass, htail]
  simpa only [E.map_comp, U.map_comp, ConcreteCategory.comp_apply, b] using! hpost

end AlgebraicGeometry.Etale
