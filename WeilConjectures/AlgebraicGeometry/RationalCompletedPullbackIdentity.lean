/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.RationalRealizationPullbackComparison
public import WeilConjectures.AlgebraicGeometry.PbcActualRingedExchange
import all WeilConjectures.AlgebraicGeometry.RationalRealizationPullbackComparison
import WeilConjectures.AlgebraicGeometry.PbcScalarRestriction
import WeilConjectures.AlgebraicGeometry.PbcUniformCompleteTriangulated
import WeilConjectures.CategoryTheory.ScalarLocalizationNaturalIso

/-! # Completed identity and descent to all raw rational fraction arrows.

Source: Bhatt--Scholze, Remark 6.8.15, p. 62; Stacks Tags 03CB, 0D6D, 07A4, 099N.
(blueprint: lem-per-rational-completed-pullback-identity).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme

attribute [local irreducible] Functor.sheafPullbackConstruction.sheafPullback
  proEtaleRingInverseImageComp LocallyRingedSpace.comp PresheafedSpace.comp

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

variable {X Y Z : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y] [IsNoetherian Z]
  [Fact (∃ n : ℕ, topologicalKrullDim X ≤ n)]
  [Fact (∃ n : ℕ, topologicalKrullDim Y ≤ n)]
  [Fact (∃ n : ℕ, topologicalKrullDim Z ≤ n)]
  [Fact (∀ x : X, IsUnit (l : X.presheaf.stalk x))]
  [Fact (∀ y : Y, IsUnit (l : Y.presheaf.stalk y))]
  [Fact (∀ z : Z, IsUnit (l : Z.presheaf.stalk z))]


omit [IsNoetherian X] [Fact (∃ n : ℕ, topologicalKrullDim X ≤ n)]
  [Fact (∀ x : X, IsUnit (l : X.presheaf.stalk x))] in
private theorem identityModuleUnit
    (M : pbcModules X (pbcAdicCompletion X (pbcIntegralDatum l E)))
    (V : X.ProEt) (m : M.val.obj (op V)) :
    ((pbcActualModulePullIdIso (pbcIntegralDatum l E) X).hom.app M).val.app
        (op ((proEtaleBaseChange (𝟙 X)).obj V))
        (pbcActualModuleUnitSection (𝟙 X) (pbcIntegralDatum l E) M V m) =
      M.val.map ((MorphismProperty.Over.pullbackId _ _ X).hom.app V).op m := by
  let d := pbcIntegralDatum l E
  let e := pbcActualModuleDirectIdIso d X
  let adj := pbcActualModuleAdjunction (𝟙 X) d
  have h := unit_conjugateEquiv_symm
    (Adjunction.id (C := pbcModules X (pbcAdicCompletion X d))) adj e.inv M
  have h' := congrArg (fun q ↦ q.val.app (op V) m) h
  simp only [Adjunction.id_unit, NatTrans.id_app, Category.id_comp] at h'
  have hu := (pbcActualModuleAdjunction_exists (𝟙 X) d).exists.choose_spec M V m
  have hi : (e.inv.app M).val.app (op V) m =
      M.val.map ((MorphismProperty.Over.pullbackId _ _ X).hom.app V).op m := by
    have he := (pbcActualModuleDirectIdIso_exists d X).exists.choose_spec
    have h₁ := congrArg (fun q ↦ q.val.app (op V) m) (e.inv_hom_id_app M)
    have h₂ := he M V (M.val.map
      ((MorphismProperty.Over.pullbackId _ _ X).hom.app V).op m)
    dsimp only [SheafOfModules.comp_val, PresheafOfModules.comp_app,
      ConcreteCategory.comp_apply, SheafOfModules.id_val, PresheafOfModules.id_app,
      ModuleCat.id_apply] at h₁
    have h₃ : M.val.map ((MorphismProperty.Over.pullbackId _ _ X).inv.app V).op
        (M.val.map ((MorphismProperty.Over.pullbackId _ _ X).hom.app V).op m) = m := by
      rw [← M.val.map_comp_apply, ← op_comp, Iso.inv_hom_id_app]
      simp
    let eV := ((SheafOfModules.forget _ ⋙ PresheafOfModules.evaluation _ (op V)).mapIso
      (e.app M))
    apply (ConcreteCategory.bijective_of_isIso eV.hom).1
    exact h₁.trans (h₂.trans h₃).symm
  change (e.inv.app M).val.app (op V) m =
    ((pbcActualModulePullIdIso d X).hom.app M).val.app
      (op ((proEtaleBaseChange (𝟙 X)).obj V))
      (((adj.unit.app M).val.app (op V)) m) at h'
  erw [hi] at h'
  dsimp only [adj] at h'
  erw [hu] at h'
  exact h'.symm

omit [IsNoetherian X] [Fact (∃ n : ℕ, topologicalKrullDim X ≤ n)] in
private theorem scalarUnitMap
    {R S : Sheaf (ProEt.topology X) CommRingCat.{u + 1}} (c : R ⟶ S)
    {M N : pbcModules X R} (f : M ⟶ N) (U : X.ProEtᵒᵖ) (m : M.val.obj U) :
    ((pbcExtend c).map f).val.app U (pbcTensorSection c M U 1 m) =
      pbcTensorSection c N U 1 (f.val.app U m) := by
  have h := congrArg (fun q ↦ q.val.app U m) ((pbcScalarAdjunction c).unit.naturality f)
  change ((pbcScalarAdjunction c).unit.app N).val.app U (f.val.app U m) =
    ((pbcExtend c).map f).val.app U
      (((pbcScalarAdjunction c).unit.app M).val.app U m) at h
  erw [(pbcScalarAdjunction_exists c).exists.choose_spec,
    (pbcScalarAdjunction_exists c).exists.choose_spec] at h
  exact h.symm

omit [IsNoetherian X] [Fact (∃ n : ℕ, topologicalKrullDim X ≤ n)] in
private theorem scalarUnitRestrict
    {R S : Sheaf (ProEt.topology X) CommRingCat.{u + 1}} (c : R ⟶ S)
    (M : pbcModules X R) {U V : X.ProEtᵒᵖ} (f : U ⟶ V) (m : M.val.obj U) :
    ((pbcExtend c).obj M).val.map f (pbcTensorSection c M U 1 m) =
      pbcTensorSection c M V 1 (M.val.map f m) := by
  have h := congrArg (fun q ↦ q m) (((pbcScalarAdjunction c).unit.app M).val.naturality f)
  change ((pbcScalarAdjunction c).unit.app M).val.app V (M.val.map f m) =
    ((pbcExtend c).obj M).val.map f
      (((pbcScalarAdjunction c).unit.app M).val.app U m) at h
  erw [(pbcScalarAdjunction_exists c).exists.choose_spec,
    (pbcScalarAdjunction_exists c).exists.choose_spec] at h
  exact h.symm

private theorem identityModuleSquare
    (s : RationalModuleRealization l E X)
    (a : RationalRealizationPullbackComparison l E (𝟙 X) s s)
    (o : rationalPullModule l E (𝟙 X) a.rationalCoefficient ≅ 𝟭 _)
    (ho : ∀ (M : pbcModules X (rationalCoefficientSheaf l X E)) (V : X.ProEt)
      (m : M.val.obj (op V)),
      (o.hom.app M).val.app (op ((proEtaleBaseChange (𝟙 X)).obj V))
        (pbcTensorSection a.rationalCoefficient
          ((proEtaleRingModulePullback (𝟙 X) (rationalCoefficientSheaf l X E)
            ((proEtaleSheafInverseImage (𝟙 X) CommRingCat.{u + 1}).obj
              (rationalCoefficientSheaf l X E)) (Iso.refl _)).obj M)
          (op ((proEtaleBaseChange (𝟙 X)).obj V)) 1
          (proEtaleRingModuleUnitSection (𝟙 X) (rationalCoefficientSheaf l X E)
            ((proEtaleSheafInverseImage (𝟙 X) CommRingCat.{u + 1}).obj
              (rationalCoefficientSheaf l X E)) (Iso.refl _) M V m)) =
        M.val.map ((MorphismProperty.Over.pullbackId _ _ X).hom.app V).op m) :
    a.moduleComparison.hom ≫ whiskerLeft (pbcExtend (rationalPullScalar l E s)) o.hom =
      whiskerRight (pbcActualModulePullIdIso (pbcIntegralDatum l E) X).hom
        (pbcExtend (rationalPullScalar l E s)) := by
  let c := rationalPullScalar l E s
  let adj := (pbcActualModuleAdjunction (𝟙 X) (pbcIntegralDatum l E)).comp
    (pbcScalarAdjunction c)
  apply NatTrans.ext
  funext M
  apply (adj.homEquiv M ((pbcExtend c).obj M)).injective
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro U
  ext m
  obtain ⟨V⟩ := U
  simp only [Adjunction.homEquiv_unit, adj, Adjunction.comp_unit_app,
    SheafOfModules.comp_val, PresheafOfModules.comp_app, ConcreteCategory.comp_apply,
    NatTrans.comp_app, whiskerLeft_app, whiskerRight_app]
  change (o.hom.app ((pbcExtend c).obj M)).val.app _
      ((a.moduleComparison.hom.app M).val.app _
        (((pbcScalarAdjunction c).unit.app _).val.app
          (op ((proEtaleBaseChange (𝟙 X)).obj V))
          (((pbcActualModuleAdjunction (𝟙 X) (pbcIntegralDatum l E)).unit.app M).val.app
            (op V) m))) =
    ((pbcExtend c).map ((pbcActualModulePullIdIso (pbcIntegralDatum l E) X).hom.app M)).val.app
      _ (((pbcScalarAdjunction c).unit.app _).val.app
          (op ((proEtaleBaseChange (𝟙 X)).obj V))
        (((pbcActualModuleAdjunction (𝟙 X) (pbcIntegralDatum l E)).unit.app M).val.app
          (op V) m))
  erw [(pbcActualModuleAdjunction_exists (𝟙 X) (pbcIntegralDatum l E)).exists.choose_spec,
    (pbcScalarAdjunction_exists c).exists.choose_spec]
  erw [a.module_unit, ho, scalarUnitMap, identityModuleUnit, scalarUnitRestrict]
  rfl

omit [IsNoetherian X] [Fact (∃ n : ℕ, topologicalKrullDim X ≤ n)]
  [Fact (∀ x : X, IsUnit (l : X.presheaf.stalk x))] in
private theorem identityDerivedNormalization
    (P : CochainComplex (pbcModules X (pbcAdicCompletion X (pbcIntegralDatum l E))) ℤ) :
    (pbcActualDerivedPullIdIso (pbcIntegralDatum l E) X).hom.app (DerivedCategory.Q.obj P) =
      pbcActualPullComplexCounit (𝟙 X) (pbcIntegralDatum l E) P ≫
        DerivedCategory.Q.map ((pbcActualModulePullIdComplexIso
          (pbcIntegralDatum l E) X).hom.app P) := by
  let d := pbcIntegralDatum l E
  obtain ⟨i, hi⟩ := rationalPullDescendIso
    (pbcActualDerivedPull (𝟙 X) d) (𝟭 _) _ _
    (rationalPullOrdinaryFactors l E (𝟙 X)) (DerivedCategory.Q.rightUnitor)
    (isoWhiskerRight (pbcActualModulePullIdComplexIso d X) DerivedCategory.Q)
  have hn (T : CochainComplex (pbcModules X (pbcAdicCompletion X d)) ℤ) :
      i.hom.app (DerivedCategory.Q.obj T) =
        pbcActualPullComplexCounit (𝟙 X) d T ≫
          DerivedCategory.Q.map ((pbcActualModulePullIdComplexIso d X).hom.app T) := by
    have ht := hi T
    change i.hom.app (DerivedCategory.Q.obj T) ≫ 𝟙 _ =
      pbcActualPullComplexCounit (𝟙 X) d T ≫
        DerivedCategory.Q.map ((pbcActualModulePullIdComplexIso d X).hom.app T) at ht
    simpa only [Category.comp_id] using ht
  have he : i = pbcActualDerivedPullIdIso d X :=
    (pbcActualDerivedPullIdIso_exists d X).unique (fun T _ _ ↦ hn T)
      (pbcActualDerivedPullIdIso_exists d X).exists.choose_spec
  rw [← he]
  exact hn P

private theorem identityDerivedSquare
    (s : RationalModuleRealization l E X)
    (a : RationalRealizationPullbackComparison l E (𝟙 X) s s)
    (o : rationalPullModule l E (𝟙 X) a.rationalCoefficient ≅ 𝟭 _)
    (hm : a.moduleComparison.hom ≫ whiskerLeft (pbcExtend (rationalPullScalar l E s))
      o.hom = whiskerRight (pbcActualModulePullIdIso (pbcIntegralDatum l E) X).hom
        (pbcExtend (rationalPullScalar l E s)))
    (d : rationalPullDerived l E (𝟙 X) a.rationalCoefficient ≅ 𝟭 _)
    (hd : ∀ P : CochainComplex (pbcModules X (rationalCoefficientSheaf l X E)) ℤ,
      d.hom.app (DerivedCategory.Q.obj P) =
        rationalPullComplexCounit l E (𝟙 X) a.rationalCoefficient P ≫
          DerivedCategory.Q.map ((NatIso.mapHomologicalComplex o (.up ℤ) ≪≫
            Functor.mapHomologicalComplexIdIso _ (.up ℤ)).hom.app P)) :
    a.ordinaryComparison.hom ≫
        whiskerLeft (pbcDerivedExtend (rationalPullScalar l E s)) d.hom =
      whiskerRight (pbcActualDerivedPullIdIso (pbcIntegralDatum l E) X).hom
        (pbcDerivedExtend (rationalPullScalar l E s)) := by
  let c := rationalPullScalar l E s
  let S := pbcExtend c
  let F := pbcDerivedExtend c
  let D := rationalPullDerived l E (𝟙 X) a.rationalCoefficient
  have := s.ordinary_exact.1
  have := s.ordinary_exact.2
  let b := rationalPullScalarFactors c
  let oC := NatIso.mapHomologicalComplex o (.up ℤ) ≪≫
    Functor.mapHomologicalComplexIdIso _ (.up ℤ)
  apply Localization.natTrans_ext DerivedCategory.Q
    (HomologicalComplex.quasiIso (pbcModules X (pbcAdicCompletion X (pbcIntegralDatum l E)))
      (.up ℤ))
  intro P
  change a.ordinaryComparison.hom.app (DerivedCategory.Q.obj P) ≫
    d.hom.app (F.obj (DerivedCategory.Q.obj P)) =
      F.map ((pbcActualDerivedPullIdIso (pbcIntegralDatum l E) X).hom.app
        (DerivedCategory.Q.obj P))
  apply (cancel_mono (b.hom.app P)).1
  let AP := ((pbcActualModulePull (𝟙 X) (pbcIntegralDatum l E)).mapHomologicalComplex
    (.up ℤ)).obj P
  let SP := (S.mapHomologicalComplex (.up ℤ)).obj P
  let iP := (pbcActualModulePullIdComplexIso (pbcIntegralDatum l E) X).hom.app P
  let mP := (NatIso.mapHomologicalComplex a.moduleComparison (.up ℤ)).hom.app P
  have hchain : mP ≫ oC.hom.app SP = (S.mapHomologicalComplex (.up ℤ)).map iP := by
    apply HomologicalComplex.hom_ext
    intro n
    change a.moduleComparison.hom.app (P.X n) ≫
      (o.hom.app (S.obj (P.X n)) ≫ 𝟙 _) =
        S.map ((pbcActualModulePullIdIso (pbcIntegralDatum l E) X).hom.app (P.X n) ≫ 𝟙 _)
    simpa only [NatTrans.comp_app, whiskerLeft_app, whiskerRight_app,
      Category.comp_id] using congr_app hm (P.X n)
  have hn := d.hom.naturality (b.hom.app P)
  change D.map (b.hom.app P) ≫ d.hom.app (DerivedCategory.Q.obj SP) =
    d.hom.app (F.obj (DerivedCategory.Q.obj P)) ≫ b.hom.app P at hn
  have hb := b.hom.naturality iP
  dsimp only [Functor.comp_map] at hb
  calc
    _ = a.ordinaryComparison.hom.app (DerivedCategory.Q.obj P) ≫
        D.map (b.hom.app P) ≫ rationalPullComplexCounit l E (𝟙 X)
          a.rationalCoefficient SP ≫ DerivedCategory.Q.map (oC.hom.app SP) := by
      simp only [Category.assoc]
      rw [← hn, hd]
    _ = (F.map (pbcActualPullComplexCounit (𝟙 X) (pbcIntegralDatum l E) P) ≫
        b.hom.app AP ≫ DerivedCategory.Q.map mP) ≫
          DerivedCategory.Q.map (oC.hom.app SP) := by
      simpa only [b, rationalPullScalarFactors, rationalPullCounit, pbcComplexCounit,
        asIso_hom, NatTrans.comp_app, whiskerRight_app, whiskerLeft_app,
        Category.assoc] using congrArg
        (fun t ↦ t ≫ DerivedCategory.Q.map (oC.hom.app SP)) (a.derived_normalization P)
    _ = F.map (pbcActualPullComplexCounit (𝟙 X) (pbcIntegralDatum l E) P) ≫
        b.hom.app AP ≫ DerivedCategory.Q.map ((S.mapHomologicalComplex (.up ℤ)).map iP) := by
      rw [Category.assoc, Category.assoc, ← DerivedCategory.Q.map_comp, hchain]
    _ = F.map (pbcActualPullComplexCounit (𝟙 X) (pbcIntegralDatum l E) P) ≫
        F.map (DerivedCategory.Q.map iP) ≫ b.hom.app P := by
      simpa only [F, Functor.id_obj] using congrArg
        (fun t ↦ F.map (pbcActualPullComplexCounit (𝟙 X) (pbcIntegralDatum l E) P) ≫ t)
        hb.symm
    _ = _ := by
      rw [← F.map_comp_assoc, ← identityDerivedNormalization l E P]

private def identityIntegral
    (a : RationalPullIntegral l E (𝟙 X)) : a.completedFunctor l E ≅ 𝟭 _ := by
  let O := pbcConditionalIntegral (pbcIntegralDatum l E)
    (pbcActualDerivedPull (𝟙 X) (pbcIntegralDatum l E)) a.ordinary_mem
  let u : O ≅ a.completedFunctor l E := NatIso.ofComponents
    (fun K ↦ ObjectProperty.isoMk _
      (@asIso _ _ _ _
        ((pbcActualStrictCompletedPullUnit (pbcIntegralDatum l E) (𝟙 X)).app K.obj)
        (a.unit_isIso K))) (by
      intro K L f
      apply ObjectProperty.hom_ext
      exact (pbcActualStrictCompletedPullUnit (pbcIntegralDatum l E) (𝟙 X)).naturality
        f.hom)
  let i : O ≅ 𝟭 _ := NatIso.ofComponents
    (fun K ↦ ObjectProperty.isoMk _
      ((pbcActualDerivedPullIdIso (pbcIntegralDatum l E) X).app K.obj)) (by
      intro K L f
      apply ObjectProperty.hom_ext
      exact (pbcActualDerivedPullIdIso (pbcIntegralDatum l E) X).hom.naturality f.hom)
  exact u.symm ≪≫ i

omit [IsNoetherian X] [Fact (∃ n : ℕ, topologicalKrullDim X ≤ n)]
  [Fact (∀ x : X, IsUnit (l : X.presheaf.stalk x))] in
private theorem identityIntegral_unit (a : RationalPullIntegral l E (𝟙 X))
    (K : PbcBoundedConstructibleComplete X (pbcIntegralDatum l E)) :
    (pbcActualStrictCompletedPullUnit (pbcIntegralDatum l E) (𝟙 X)).app K.obj ≫
        ((identityIntegral l E a).hom.app K).hom =
      (pbcActualDerivedPullIdIso (pbcIntegralDatum l E) X).hom.app K.obj := by
  let := a.unit_isIso K
  simp only [identityIntegral, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    NatIso.ofComponents_inv_app, NatIso.ofComponents_hom_app,
    ObjectProperty.FullSubcategory.comp_hom, ObjectProperty.isoMk_inv,
    ObjectProperty.isoMk_hom, ObjectProperty.homMk_hom, asIso_inv,
    Iso.app_hom, IsIso.hom_inv_id_assoc]

private theorem identityRaw (s : RationalModuleRealization l E X)
    (a : RationalRealizationPullbackComparison l E (𝟙 X) s s)
    (i : a.integral.completedFunctor l E ≅ 𝟭 _) :
    ∃ r : a.rawPull ≅ 𝟭 _,
      ∀ K : PbcBoundedConstructibleComplete X (pbcIntegralDatum l E),
        r.hom.app ((pbcRationalization X (pbcIntegralDatum l E)
          (pbcUniformizer l E)).obj K) = eqToHom (a.raw_objects K) ≫
            (pbcRationalization X (pbcIntegralDatum l E) (pbcUniformizer l E)).map
              (i.hom.app K) := by
  let Q := pbcRationalization X (pbcIntegralDatum l E) (pbcUniformizer l E)
  let e : Q ⋙ a.rawPull ≅ Q ⋙ 𝟭 _ := NatIso.ofComponents
    (fun K ↦ eqToIso (a.raw_objects K) ≪≫ Q.mapIso (i.app K)) (by
      intro K L f
      have hf := a.raw_fractions K L f 0
      simp only [rationalPullFraction, pow_zero, one_smul] at hf
      dsimp only [Functor.comp_map, Functor.id_map]
      simp only [Iso.trans_hom, eqToIso.hom, Functor.mapIso_hom]
      rw [hf]
      simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
      rw [← Q.map_comp, ← Q.map_comp]
      apply congrArg (fun t ↦ eqToHom (a.raw_objects K) ≫ t)
      simpa only [Iso.app_hom, Functor.id_map] using congrArg Q.map (i.hom.naturality f))
  let := (pbcIntegralUniformComplete_isTriangulated l E X Fact.out Fact.out).2
  obtain ⟨r, hr, _⟩ := ScalarLocalization.naturalIso_of_integral
    (PbcIntegralRing l E) (PbcBoundedConstructibleComplete X (pbcIntegralDatum l E))
    (pbcUniformizer l E) a.rawPull (𝟭 _) e
  exact ⟨r, hr⟩

private theorem identityRawCompatibility
    (s : RationalModuleRealization l E X)
    (a : RationalRealizationPullbackComparison l E (𝟙 X) s s)
    (i : a.integral.completedFunctor l E ≅ 𝟭 _)
    (hi : ∀ K : PbcBoundedConstructibleComplete X (pbcIntegralDatum l E),
      (pbcActualStrictCompletedPullUnit (pbcIntegralDatum l E) (𝟙 X)).app K.obj ≫
        (i.hom.app K).hom =
          (pbcActualDerivedPullIdIso (pbcIntegralDatum l E) X).hom.app K.obj)
    (r : a.rawPull ≅ 𝟭 _)
    (hr : ∀ K : PbcBoundedConstructibleComplete X (pbcIntegralDatum l E),
      r.hom.app ((pbcRationalization X (pbcIntegralDatum l E) (pbcUniformizer l E)).obj K) =
        eqToHom (a.raw_objects K) ≫
          (pbcRationalization X (pbcIntegralDatum l E) (pbcUniformizer l E)).map
            (i.hom.app K))
    (d : rationalPullDerived l E (𝟙 X) a.rationalCoefficient ≅ 𝟭 _)
    (hd : a.ordinaryComparison.hom ≫
        whiskerLeft (pbcDerivedExtend (rationalPullScalar l E s)) d.hom =
      whiskerRight (pbcActualDerivedPullIdIso (pbcIntegralDatum l E) X).hom
        (pbcDerivedExtend (rationalPullScalar l E s))) :
    a.alpha.hom ≫ whiskerLeft s.J d.hom = whiskerRight r.hom s.J := by
  let F := pbcDerivedExtend (rationalPullScalar l E s)
  let D := rationalPullDerived l E (𝟙 X) a.rationalCoefficient
  let Q := pbcRationalization X (pbcIntegralDatum l E) (pbcUniformizer l E)
  apply NatTrans.ext
  funext V
  obtain ⟨K⟩ := V
  change a.alpha.hom.app (Q.obj K) ≫ d.hom.app (s.J.obj (Q.obj K)) =
    s.J.map (r.hom.app (Q.obj K))
  let g := (pbcActualStrictCompletedPullUnit (pbcIntegralDatum l E) (𝟙 X)).app K.obj
  let H := eqToHom (s.objects ((a.integral.completedFunctor l E).obj K)).symm ≫
    s.J.map (eqToHom (a.raw_objects K).symm)
  let := a.integral.unit_isIso K
  apply (cancel_epi (F.map g ≫ H)).1
  apply (cancel_mono (eqToHom (s.objects K))).1
  have hn := d.hom.naturality (eqToHom (s.objects K))
  dsimp only [Functor.id_map] at hn
  have hα := a.alpha_normalization K
  have hOrd := congr_app hd K.obj
  have hmap := s.fractions ((a.integral.completedFunctor l E).obj K) K (i.hom.app K) 0
  simp only [pow_zero, inv_one, map_one, one_smul] at hmap
  calc
    _ = a.ordinaryComparison.hom.app K.obj ≫ d.hom.app (F.obj K.obj) := by
      have hh := congrArg (fun t ↦ t ≫ d.hom.app (F.obj K.obj)) hα
      simp only [Category.assoc] at hh
      rw [hn] at hh
      simpa only [H, Category.assoc] using hh
    _ = F.map ((pbcActualDerivedPullIdIso (pbcIntegralDatum l E) X).hom.app K.obj) :=
      hOrd
    _ = F.map g ≫ F.map (i.hom.app K).hom := by rw [← F.map_comp, hi]
    _ = _ := by
      rw [hr, s.J.map_comp, hmap]
      simp only [H, Category.assoc, ← s.J.map_comp_assoc, eqToHom_trans,
        eqToHom_refl, s.J.map_id, Category.id_comp, eqToHom_trans_assoc,
        Category.comp_id]
      rfl


set_option maxHeartbeats 800000 in
-- Nested chart conversions arise in the explicit tensor-section normalization.
/-- Completed identity and descent to all raw rational fraction arrows.
Source: Stacks Tags 099N, 099J, 0A0E, 0B65 and 0DV0; BS Remark 6.8.15.

Proof: restrict QuotientCompleted.identity to bounded constructible complete
objects. QuotientCompleted.identity_unit gives the displayed strict unit equation,
with the recorded object inclusions. The unit_isIso field makes gamma_id invertible.
The normalized ordinary comparison and the supplied tensor identity determine the
ordinary identity square, by testing on generators and flat-term K-flat resolutions;
hderived and derived_normalization retain the fixed derived counits. Substitute
alpha_normalization and cancel realization of gamma_id to obtain the identity
square on integral objects. On a raw object define rawId by rationalizing the
integral identity and inserting raw_objects. Its inverse rationalizes the inverse.
The inverse identities are functoriality. On each f/varpi^n, raw_fractions reduces
naturality to the integral identity naturality multiplied by the same central
scalar varpi^(-n). Every raw object has an integral representative, so the object
calculation gives the displayed equality of natural transformations on the entire
raw category, without any full-faithfulness hypothesis.
(blueprint: lem-per-rational-completed-pullback-identity). -/
theorem rationalCompletedPullbackIdentity (sX : RationalModuleRealization l E X)
    (a : RationalRealizationPullbackComparison l E (𝟙 X) sX sX)
    (hcoefficient : (a.rationalCoefficient =
  (proEtaleRingInverseImageId X).hom.app
    (rationalCoefficientSheaf l X E)))
    (moduleId : rationalPullModule l E (𝟙 X) a.rationalCoefficient ≅ 𝟭 _)
    (hmodule :
      let unitSection {S T : Scheme.{u}} (g : S ⟶ T)
          (c : (proEtaleSheafInverseImage g CommRingCat.{u + 1}).obj
            (rationalCoefficientSheaf l T E) ⟶ rationalCoefficientSheaf l S E)
          (M : pbcModules T (rationalCoefficientSheaf l T E))
          (V : T.ProEt) (m : M.val.obj (op V)) :
          ((rationalPullModule l E g c).obj M).val.obj
            (op ((proEtaleBaseChange g).obj V)) :=
        pbcTensorSection c
          ((proEtaleRingModulePullback g (rationalCoefficientSheaf l T E)
            ((proEtaleSheafInverseImage g CommRingCat.{u + 1}).obj
              (rationalCoefficientSheaf l T E)) (Iso.refl _)).obj M)
          (op ((proEtaleBaseChange g).obj V)) 1
          (proEtaleRingModuleUnitSection g (rationalCoefficientSheaf l T E)
            ((proEtaleSheafInverseImage g CommRingCat.{u + 1}).obj
              (rationalCoefficientSheaf l T E)) (Iso.refl _) M V m)
      let scalarMul (T : Scheme.{u})
          (M : pbcModules T (rationalCoefficientSheaf l T E)) (V : T.ProEtᵒᵖ)
          (e : (rationalCoefficientSheaf l T E).obj.obj V) (m : M.val.obj V) : M.val.obj V :=
        e • m
      (∀ (M : pbcModules X (rationalCoefficientSheaf l X E)) (V : X.ProEt)
        (m : M.val.obj (op V))
        (e : (rationalCoefficientSheaf l X E).obj.obj (op ((proEtaleBaseChange (𝟙 X)).obj V))),
      (moduleId.hom.app M).val.app (op ((proEtaleBaseChange (𝟙 X)).obj V))
          (scalarMul X
            ((rationalPullModule l E (𝟙 X) a.rationalCoefficient).obj M)
            (op ((proEtaleBaseChange (𝟙 X)).obj V)) e
            (unitSection (𝟙 X) a.rationalCoefficient M V m)) =
        scalarMul X M (op ((proEtaleBaseChange (𝟙 X)).obj V)) e
          (M.val.map ((MorphismProperty.Over.pullbackId _ _ X).hom.app V).op m)))
    (ambientId : rationalPullDerived l E (𝟙 X) a.rationalCoefficient ≅ 𝟭 _)
    (hderived : (∀ P : CochainComplex (pbcModules X (rationalCoefficientSheaf l X E)) ℤ,
  ambientId.hom.app (DerivedCategory.Q.obj P) =
    rationalPullComplexCounit l E (𝟙 X) a.rationalCoefficient P ≫
      DerivedCategory.Q.map
        ((NatIso.mapHomologicalComplex moduleId (.up ℤ) ≪≫
          Functor.mapHomologicalComplexIdIso _ (.up ℤ)).hom.app P))) :
    ∃ (integralId : a.integral.completedFunctor l E ≅ 𝟭 _),
      (∀ K : PbcBoundedConstructibleComplete X (pbcIntegralDatum l E),
      (pbcActualStrictCompletedPullUnit (pbcIntegralDatum l E) (𝟙 X)).app K.obj ≫
        (integralId.hom.app K).hom =
          (pbcActualDerivedPullIdIso (pbcIntegralDatum l E) X).hom.app K.obj) ∧
      ∃ (rawId : a.rawPull ≅ 𝟭 _),
      (∀ K : PbcBoundedConstructibleComplete X (pbcIntegralDatum l E),
      rawId.hom.app
          ((pbcRationalization X (pbcIntegralDatum l E) (pbcUniformizer l E)).obj K) =
        eqToHom (a.raw_objects K) ≫
          (pbcRationalization X (pbcIntegralDatum l E) (pbcUniformizer l E)).map
            (integralId.hom.app K)) ∧
      (a.alpha.hom ≫ whiskerLeft sX.J ambientId.hom = whiskerRight rawId.hom sX.J) := by
  have _ := hcoefficient
  let i := identityIntegral l E a.integral
  have hi := identityIntegral_unit l E a.integral
  obtain ⟨r, hr⟩ := identityRaw l E sX a i
  refine ⟨i, hi, r, hr, ?_⟩
  have ho := fun M V m ↦ hmodule M V m 1
  simp only [one_smul] at ho
  exact identityRawCompatibility l E sX a i hi r hr ambientId
    (identityDerivedSquare l E sX a moduleId
      (identityModuleSquare l E sX a moduleId ho) ambientId hderived)

end AlgebraicGeometry.Scheme
