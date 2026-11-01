/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Algebra.Homology.System.SystemEvaluationNormalizationData
public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.Limits.EssentiallySmall
public import Mathlib.CategoryTheory.ShrinkYoneda
public import Mathlib.CategoryTheory.Sites.Equivalence
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
public import WeilConjectures.Algebra.Homology.SequenceCoinduced.SystemCoinducedAdjunction
public import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
public import WeilConjectures.Algebra.Homology.System.SystemDerivedEvaluation
public import WeilConjectures.Algebra.Homology.System.SystemRestrictionLevelMateInvertibility
public import WeilConjectures.Algebra.Homology.System.SystemSingletonGeometricPullback
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import WeilConjectures.SmoothPurity.SystemRestrictionMateCoherenceEquations
public import WeilConjectures.SmoothPurity.SystemSingletonEvaluationMate

/-! # Restriction mates and their coherence

Source: Stacks Project, Tags 03D2, 0D6E and 07A6; Zheng, Construction 4.1.
(blueprint: lem-route-system-restriction-scalar-mate-invertibility).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 2048
universe u v u' v' w
open CategoryTheory CategoryTheory.Limits Opposite
namespace SheafOfModules

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [EssentiallySmall.{w} C]
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasSheafify J AddCommGrpCat.{w}]
  {D : Type u'} [Category.{v'} D] {K : GrothendieckTopology D}
  [EssentiallySmall.{w} D]
  [K.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [K.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasSheafify K AddCommGrpCat.{w}]
  (AY : Sheaf J CommRingCat.{w}) (AX : Sheaf K CommRingCat.{w})
  (BY : ℕᵒᵖ ⥤ Sheaf J CommRingCat.{w}) (BX : ℕᵒᵖ ⥤ Sheaf K CommRingCat.{w})
  (aY : (Functor.const ℕᵒᵖ).obj AY ⟶ BY)
  (aX : (Functor.const ℕᵒᵖ).obj AX ⟶ BX)
  (uTop : GeometricMorphism (Sheaf K (Type w)) (Sheaf J (Type w)))
  (IA : AlgebraicInverseImage uTop.inverse AY AX)
  (IB : ∀ n : ℕ, AlgebraicInverseImage uTop.inverse (BY.obj (op n)) (BX.obj (op n)))
  (FB : SystemGeometricInverseImageData BY BX uTop IB)
  (FA : SystemGeometricInverseImageData
    ((Functor.const ℕᵒᵖ).obj AY) ((Functor.const ℕᵒᵖ).obj AX) uTop (fun _ ↦ IA))

variable (HB : StrictRingSystem BX ⥤ StrictRingSystem BY) [HB.Additive]
  (HA : StrictRingSystem ((Functor.const ℕᵒᵖ).obj AX) ⥤
    StrictRingSystem ((Functor.const ℕᵒᵖ).obj AY)) [HA.Additive]
  [Abelian.HasKInjectiveResolutions (StrictRingSystem BX)]
  [Abelian.HasKInjectiveResolutions (StrictRingSystem ((Functor.const ℕᵒᵖ).obj AX))]
  (adjB : FB.functor ⊣ HB) (adjA : FA.functor ⊣ HA)

private def inverseImageIso (F G : SystemGeometricInverseImageData BY BX uTop I) :
    F.functor ≅ G.functor := by
  let e (n : ℕ) := F.evaluation n ≪≫ (G.evaluation n).symm
  let p (H : SystemGeometricInverseImageData BY BX uTop I)
      (M : StrictRingSystem BY) (n : ℕ) :=
    (systemGeometricUnderlying BX n).map ((H.evaluation n).hom.app M) ≫
      (I n).moduleUnderlying.hom.app (M.level n)
  have hp (H : SystemGeometricInverseImageData BY BX uTop I)
      (M : StrictRingSystem BY) {n m : ℕ} (h : n ≤ m) :
      (systemGeometricUnderlying BX m).map ((H.functor.obj M).transition h) ≫ p H M n =
        p H M m ≫
          uTop.inverse.map ((systemGeometricUnderlying BY m).map (M.transition h)) := by
    have hh := congrArg (fun t ↦ t ≫ (I n).moduleUnderlying.hom.app (M.level n))
      (H.transition M h)
    simp only [Category.assoc, Iso.inv_hom_id_app] at hh
    erw [Category.comp_id] at hh
    exact hh.symm
  have he (M : StrictRingSystem BY) (n : ℕ) :
      (systemGeometricUnderlying BX n).map ((e n).hom.app M) ≫ p G M n = p F M n := by
    dsimp only [e, p, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app]
    simp only [Functor.map_comp, Category.assoc]
    erw [← (systemGeometricUnderlying BX n).map_comp_assoc
      ((G.evaluation n).inv.app M) ((G.evaluation n).hom.app M),
      Iso.inv_hom_id_app, CategoryTheory.Functor.map_id, Category.id_comp]
  let f (M : StrictRingSystem BY) : F.functor.obj M ⟶ G.functor.obj M :=
    { app := fun n ↦ (e n).hom.app M
      comm := by
        intro n m h
        apply (systemGeometricUnderlying BX m).map_injective
        have : IsIso (p G M n) := by
          change IsIso (((systemGeometricUnderlying BX n).mapIso
            ((G.evaluation n).app M) ≪≫ (I n).moduleUnderlying.app (M.level n)).hom)
          infer_instance
        apply (cancel_mono (p G M n)).1
        simp only [Functor.map_comp, Category.assoc]
        change (systemGeometricUnderlying BX m).map ((e m).hom.app M) ≫
            (systemGeometricUnderlying BX m).map ((G.functor.obj M).transition h) ≫
              p G M n =
          (systemGeometricUnderlying BX m).map ((F.functor.obj M).transition h) ≫
            (systemGeometricUnderlying BX n).map ((e n).hom.app M) ≫ p G M n
        rw [hp G M h, ← Category.assoc, he, Category.assoc, he, hp F M h]
        simp only [p, Category.assoc] }
  have hf (M : StrictRingSystem BY) : IsIso (f M) := by
    apply (strictRingSystem_isIso_iff BX (f M)).2
    intro n
    change IsIso ((e n).hom.app M)
    infer_instance
  exact NatIso.ofComponents (fun M ↦ asIso (f M)) (by
    intro M N t
    apply strictRingSystem_hom_ext BX
    intro n
    exact (e n).hom.naturality t)

private theorem inverseImageIso_evaluation
    (F G : SystemGeometricInverseImageData BY BX uTop I)
    (M : StrictRingSystem BY) (n : ℕ) :
    (systemEvaluation BX n).map ((inverseImageIso F G).hom.app M) ≫
        (G.evaluation n).hom.app M = (F.evaluation n).hom.app M := by
  change ((F.evaluation n).hom.app M ≫ (G.evaluation n).inv.app M) ≫ _ = _
  simp only [Category.assoc, Iso.inv_hom_id_app, Category.comp_id]

private def levelAdjunction
    (S : SystemScalarAssignment (J := J)) (T : SystemTensorCoherence S)
    (F : SystemGeometricInverseImageData BY BX uTop I)
    {H : StrictRingSystem BX ⥤ StrictRingSystem BY} (adj : F.functor ⊣ H) (n : ℕ) :
    F.levelFunctor n ⊣ SequenceCoinduced.rightExtension BX n ⋙ H ⋙ systemEvaluation BY n :=
  ((systemSingleAdjunction S T BY n).comp adj |>.comp
    (SequenceCoinduced.adjunction BX n)).ofNatIsoLeft
      (Functor.associator _ _ _ ≪≫
        Functor.isoWhiskerLeft (systemSingleFunctor S T BY n) (F.evaluation n) ≪≫
        (Functor.associator _ _ _).symm ≪≫
        Functor.isoWhiskerRight (systemSingletonOrdinaryMultiplication S T n)
          (F.levelFunctor n) ≪≫ (F.levelFunctor n).leftUnitor)

private theorem evaluationMate_isIso
    (SY : SystemScalarAssignment (J := J)) (TY : SystemTensorCoherence SY)
    (SX : SystemScalarAssignment (J := K)) (TX : SystemTensorCoherence SX)
    (F : SystemGeometricInverseImageData BY BX uTop I)
    (htransition : ∀ {n m : ℕ} (h : n ≤ m),
      uTop.inverse.map ((sheafCompose J (CategoryTheory.forget CommRingCat.{w})).map
          (BY.map (homOfLE h).op)) ≫ (I n).ringUnderlying.hom =
        (I m).ringUnderlying.hom ≫
          (sheafCompose K (CategoryTheory.forget CommRingCat.{w})).map
            (BX.map (homOfLE h).op))
    {H : StrictRingSystem BX ⥤ StrictRingSystem BY} [H.Additive]
    [Abelian.HasKInjectiveResolutions (StrictRingSystem BX)] (adj : F.functor ⊣ H)
    (n : ℕ)
    {Hn : systemLevel BX n ⥤ systemLevel BY n} [Hn.Additive]
    [Abelian.HasKInjectiveResolutions (systemLevel BX n)]
    (adjn : F.levelFunctor n ⊣ Hn) :
    IsIso (SystemEvaluationNormalization.derivedMate adj adjn (F.evaluation n)) := by
  have : (I n).modules.Additive := F.levelAdditive n
  have : PreservesFiniteLimits (I n).modules := F.levelLimits n
  have : PreservesFiniteColimits (I n).modules := F.levelColimits n
  have : ∀ k : ℕ, (I k).modules.Additive := F.levelAdditive
  obtain ⟨G, hG⟩ := systemSingletonGeometricPullback BY BX uTop I htransition SY TY SX TX
  let e := inverseImageIso F G
  let o : systemSingleFunctor SY TY BY n ⋙ F.functor ≅
      F.levelFunctor n ⋙ systemSingleFunctor SX TX BX n :=
    Functor.isoWhiskerLeft (systemSingleFunctor SY TY BY n) e ≪≫ hG.choose n
  have hc (P : systemLevel BY n) :
      (systemEvaluation BX n).map (o.hom.app P) ≫
          (systemSingletonOrdinaryMultiplication (BY := BX) SX TX n).hom.app
            ((F.levelFunctor n).obj P) =
        (F.evaluation n).hom.app ((systemSingleFunctor SY TY BY n).obj P) ≫
          (F.levelFunctor n).map
            ((systemSingletonOrdinaryMultiplication (BY := BY) SY TY n).hom.app P) := by
    dsimp only [o, Iso.trans_hom, NatTrans.comp_app,
      Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app]
    rw [Functor.map_comp, Category.assoc]
    erw [hG.choose_spec.choose_spec.choose_spec.choose_spec.2.2.2.1 n P]
    rw [← Category.assoc, inverseImageIso_evaluation]
    rfl
  let dY := systemSingleDerivedExtension BY n SY TY
  let dX := systemSingleDerivedExtension BX n SX TX
  let s := F.derivedEvaluation n
  let τ := derivedExtensionMate dY dX F.functor (F.levelFunctor n).mapDerivedCategory s.inv
  have ho (P : systemLevel BY n) :
      dX.ordinaryAdj.homEquiv _ _ (o.inv.app P) =
        (F.levelFunctor n).map (dY.ordinaryAdj.unit.app P) ≫
          (F.evaluation n).inv.app (dY.ordinary.obj P) := by
    change (systemSingletonOrdinaryMultiplication (BY := BX) SX TX n).inv.app
        ((F.levelFunctor n).obj P) ≫
        (systemEvaluation BX n).map (o.inv.app P) =
      (F.levelFunctor n).map
          ((systemSingletonOrdinaryMultiplication (BY := BY) SY TY n).inv.app P) ≫
        (F.evaluation n).inv.app ((systemSingleFunctor SY TY BY n).obj P)
    exact inverseSquare_eq
      ((systemEvaluation BX n).mapIso (o.app P))
      ((systemSingletonOrdinaryMultiplication (BY := BX) SX TX n).app _)
      ((F.evaluation n).app ((systemSingleFunctor SY TY BY n).obj P))
      ((F.levelFunctor n).mapIso
        ((systemSingletonOrdinaryMultiplication (BY := BY) SY TY n).app P)) (hc P)
  have hs (Q : CochainComplex (StrictRingSystem BY) ℤ) :
      s.inv.app (DerivedCategory.Q.obj Q) ≫
          (derivedSystemEvaluation BX n).map (F.functor.mapDerivedCategoryFactors.hom.app Q) ≫
          (systemEvaluation BX n).mapDerivedCategoryFactors.hom.app
            ((F.functor.mapHomologicalComplex (.up ℤ)).obj Q) =
        (F.levelFunctor n).mapDerivedCategory.map
            ((systemEvaluation BY n).mapDerivedCategoryFactors.hom.app Q) ≫
          (F.levelFunctor n).mapDerivedCategoryFactors.hom.app
            (((systemEvaluation BY n).mapHomologicalComplex (.up ℤ)).obj Q) ≫
          DerivedCategory.Q.map (((F.evaluation n).inv.mapHomologicalComplex (.up ℤ)).app Q) := by
    let sq : systemEvaluation BY n ⋙ F.levelFunctor n ≅
        F.functor ⋙ systemEvaluation BX n := (F.evaluation n).symm
    have hi : (Functor.mapDerivedCategorySquareIso sq).hom = s.inv := by
      simp only [sq, s, SystemGeometricInverseImageData.derivedEvaluation,
        Functor.mapDerivedCategorySquareIso, Iso.trans_hom, Iso.trans_inv,
        Iso.symm_hom, Iso.symm_inv, Functor.mapDerivedCategoryNatIso_symm, Category.assoc]
    rw [← hi]
    exact exactSquare_fac sq Q
  have ht : IsIso τ := derivedExtensionMate_isIso dY dX (F.levelFunctor n) F.functor
    (F.levelFunctor n).mapDerivedCategory (F.levelFunctor n).mapDerivedCategoryFactors
    s.inv (F.evaluation n).inv hs o.symm ho
    (systemLevel_kFlatResolution BY n)
    (fun Q hQ ↦ geometricLevelKFlat SX n Q hQ)
  let c := asIso τ
  let k := conjugateIsoEquiv
    (dY.adjunction.comp adj.mapDerivedCategoryRightDerivedAdjunction)
    (adjn.mapDerivedCategoryRightDerivedAdjunction.comp dX.adjunction) c
  have hm : mateEquiv dY.adjunction dX.adjunction
      (TwoSquare.mk _ _ _ _ τ) = TwoSquare.mk _ _ _ _ s.inv :=
    (mateEquiv dY.adjunction dX.adjunction).apply_symm_apply _
  have hi := iterated_mateEquiv_conjugateEquiv dY.adjunction dX.adjunction
    adjn.mapDerivedCategoryRightDerivedAdjunction
    adj.mapDerivedCategoryRightDerivedAdjunction (TwoSquare.mk _ _ _ _ τ)
  rw [hm] at hi
  have hk : k.hom = SystemEvaluationNormalization.derivedMate adj adjn (F.evaluation n) :=
    hi.symm
  rw [← hk]
  infer_instance

/-- Scalar restriction of strict systems commutes with the geometric derived direct image.

Source: Stacks Project, Tag 0D6E, via the sequence-site realization of Zheng,
Construction 4.1 (blueprint: lem-route-system-restriction-scalar-mate-invertibility).

Proof: Construct level right adjoints by composing ordinary singleton extension,
the supplied system adjunction, and evaluation/coinduction. Geometric inverse-image
data with the same level presentations are uniquely isomorphic, by their evaluation
and underlying transition equations. Transfer the ordinary normalized singleton
comparison along this isomorphism. Its left derived mate is invertible by flat-term
K-flat resolutions, geometric preservation of the resolving class, and the normalized
derived-extension comparison. Iterated mate conjugation therefore makes every derived
evaluation mate invertible, for the supplied adjunctions. Apply the coefficient-level
restriction-mate theorem. Localizing d.scalarEvaluation and pasting mates identifies
the evaluated scalar mate, up to invertible factors, with this level restriction mate
and the evaluation mate. It is thus invertible at every level. Derived evaluations
jointly detect isomorphisms, proving the assertion. No flatness of the coefficient
maps or boundedness is used. -/
theorem systemRestrictionScalarMateInvertibility
    (htransition : ∀ {n m : ℕ} (h : n ≤ m),
      uTop.inverse.map ((sheafCompose J (CategoryTheory.forget CommRingCat.{w})).map
          (BY.map (homOfLE h).op)) ≫ (IB n).ringUnderlying.hom =
        (IB m).ringUnderlying.hom ≫
          (sheafCompose K (CategoryTheory.forget CommRingCat.{w})).map
            (BX.map (homOfLE h).op))
    (halgebra : ∀ n : ℕ,
      uTop.inverse.map ((sheafCompose J (CategoryTheory.forget CommRingCat.{w})).map
          (aY.app (op n))) ≫ (IB n).ringUnderlying.hom =
        IA.ringUnderlying.hom ≫
          (sheafCompose K (CategoryTheory.forget CommRingCat.{w})).map (aX.app (op n)))
    (d : SystemNormalizationSquares AY AX BY BX aY aX uTop IA IB FB FA) :
    IsIso (SystemEvaluationNormalization.derivedMate adjB adjA d.scalar) := by
  classical
  let SY : SystemScalarAssignment (J := J) :=
    fun φ ↦ Classical.choice (nonempty_systemScalarModel φ)
  let SX : SystemScalarAssignment (J := K) :=
    fun φ ↦ Classical.choice (nonempty_systemScalarModel φ)
  let TY := systemTensorCoherence SY
  let TX := systemTensorCoherence SX
  let Hn (n : ℕ) :=
    SequenceCoinduced.rightExtension BX n ⋙ HB ⋙ systemEvaluation BY n
  let adjn (n : ℕ) : FB.levelFunctor n ⊣ Hn n := levelAdjunction SY TY FB adjB n
  let H0 := SequenceCoinduced.rightExtension ((Functor.const ℕᵒᵖ).obj AX) 0 ⋙ HA ⋙
    systemEvaluation ((Functor.const ℕᵒᵖ).obj AY) 0
  let adj0 : FA.levelFunctor 0 ⊣ H0 := levelAdjunction SY TY FA adjA 0
  have : ∀ n : ℕ, (Hn n).Additive := fun n ↦ (adjn n).right_adjoint_additive
  have : H0.Additive := adj0.right_adjoint_additive
  have : ∀ n : ℕ, IsGrothendieckAbelian.{w} (systemLevel BX n) :=
    fun n ↦ isGrothendieckAbelian_coefficientUniverse _
  have : ∀ n : ℕ, IsGrothendieckAbelian.{w}
      (systemLevel ((Functor.const ℕᵒᵖ).obj AX) n) :=
    fun n ↦ isGrothendieckAbelian_coefficientUniverse _
  have : ∀ n : ℕ, Abelian.HasKInjectiveResolutions (systemLevel BX n) :=
    fun n ↦ inferInstance
  have : ∀ n : ℕ, Abelian.HasKInjectiveResolutions
      (systemLevel ((Functor.const ℕᵒᵖ).obj AX) n) := fun n ↦ inferInstance
  have hconst : ∀ {n m : ℕ} (h : n ≤ m),
      uTop.inverse.map ((sheafCompose J (CategoryTheory.forget CommRingCat.{w})).map
          (((Functor.const ℕᵒᵖ).obj AY).map (homOfLE h).op)) ≫ IA.ringUnderlying.hom =
        IA.ringUnderlying.hom ≫
          (sheafCompose K (CategoryTheory.forget CommRingCat.{w})).map
            (((Functor.const ℕᵒᵖ).obj AX).map (homOfLE h).op) := by
    intro n m h
    simp only [Functor.const_obj_map]
    erw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id, Category.id_comp]
  have hl := (systemRestrictionLevelMateInvertibility AY AX BY BX aY aX uTop IA IB
    FB FA Hn adjn H0 adj0 htransition halgebra d).1
  have (Z : DerivedCategory (StrictRingSystem BX)) :
      IsIso ((SystemEvaluationNormalization.derivedMate adjB adjA d.scalar).app Z) := by
    apply (systemDerivedEvaluation_isIso_iff ((Functor.const ℕᵒᵖ).obj AY) _).2
    intro n
    have hb := evaluationMate_isIso SY TY SX TX FB htransition adjB n (adjn n)
    have ha := evaluationMate_isIso SY TY SX TX FA hconst adjA n adj0
    have hk := hl n
    have he := scalar_coherence AY AX BY BX aY aX uTop IA IB FB FA
      HB HA adjB adjA Hn adjn H0 adj0 d n Z
    have ht : IsIso
        ((systemNormalizationDerivedRestrictionEvaluation aY n).inv.app
            (HB.rightDerivedFunctor.obj Z) ≫
          (derivedSystemEvaluation ((Functor.const ℕᵒᵖ).obj AY) n).map
            ((SystemEvaluationNormalization.derivedMate adjB adjA d.scalar).app Z) ≫
          (SystemEvaluationNormalization.derivedMate adjA adj0 (FA.evaluation n)).app
            ((systemNormalizationRestriction aX).mapDerivedCategory.obj Z) ≫
          H0.rightDerivedFunctor.map
            ((systemNormalizationDerivedRestrictionEvaluation aX n).hom.app Z)) := by
      rw [← he]
      infer_instance
    have ht' := (isIso_comp_left_iff _ _).mp ht
    exact (isIso_comp_right_iff _ _).mp ht'
  exact NatIso.isIso_of_isIso_app _

end SheafOfModules
