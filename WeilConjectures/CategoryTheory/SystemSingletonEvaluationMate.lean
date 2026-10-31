/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.SystemEvaluationNormalizationData
import WeilConjectures.CategoryTheory.DerivedCategory.ExtensionEvaluationComparison

/-! # The singleton comparison as an evaluation mate

Source: Stacks Project, Tags 03D2, 0D6E and 07A6; Zheng, Construction 4.1.
(blueprint: lem-route-system-singleton-evaluation-mate).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 2048
universe u v u' v' w
open CategoryTheory CategoryTheory.Limits Opposite
attribute [local irreducible] Functor.mapDerivedCategory Functor.rightDerivedFunctor
  Functor.mapDerivedCategoryCompIso Functor.mapDerivedCategoryNatIso
  Adjunction.mapDerivedCategoryRightDerivedAdjunction
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private theorem cachedRingCompose {T : Type*} [Category T]
    [EssentiallySmall.{w} T] (τ : GrothendieckTopology T) :
    τ.HasSheafCompose (CategoryTheory.forget RingCat.{w}) := inferInstance
private theorem cachedAddCompose {T : Type*} [Category T]
    [EssentiallySmall.{w} T] (τ : GrothendieckTopology T) :
    τ.HasSheafCompose (CategoryTheory.forget AddCommGrpCat.{w}) := inferInstance
private theorem cachedCommCompose {T : Type*} [Category T]
    [EssentiallySmall.{w} T] (τ : GrothendieckTopology T) :
    τ.HasSheafCompose (CategoryTheory.forget CommRingCat.{w}) := inferInstance
attribute [local instance 20000] cachedRingCompose cachedAddCompose cachedCommCompose
attribute [local instance 20000] comp_preservesFiniteLimits comp_preservesFiniteColimits

private theorem exactSquare_fac
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    [Abelian A] [Abelian B] [Abelian C] [Abelian D]
    [HasDerivedCategory A] [HasDerivedCategory B]
    [HasDerivedCategory C] [HasDerivedCategory D]
    {R : A ⥤ B} {G : B ⥤ D} {H : A ⥤ C} {S : C ⥤ D}
    [R.Additive] [G.Additive] [H.Additive] [S.Additive]
    [PreservesFiniteLimits R] [PreservesFiniteColimits R]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    [PreservesFiniteLimits H] [PreservesFiniteColimits H]
    [PreservesFiniteLimits S] [PreservesFiniteColimits S]
    (δ : R ⋙ G ≅ H ⋙ S) (K : CochainComplex A ℤ) :
    (Functor.mapDerivedCategorySquareIso δ).hom.app (DerivedCategory.Q.obj K) ≫
        S.mapDerivedCategory.map (H.mapDerivedCategoryFactors.hom.app K) ≫
        S.mapDerivedCategoryFactors.hom.app ((H.mapHomologicalComplex (.up ℤ)).obj K) =
      G.mapDerivedCategory.map (R.mapDerivedCategoryFactors.hom.app K) ≫
        G.mapDerivedCategoryFactors.hom.app ((R.mapHomologicalComplex (.up ℤ)).obj K) ≫
        DerivedCategory.Q.map ((δ.hom.mapHomologicalComplex (.up ℤ)).app K) := by
  have hc := Functor.mapDerivedCategoryCompIso_hom_app_factors R G K
  have hi : (Functor.mapDerivedCategoryCompIso R G).inv.app (DerivedCategory.Q.obj K) ≫
      (R ⋙ G).mapDerivedCategoryFactors.hom.app K =
    G.mapDerivedCategory.map (R.mapDerivedCategoryFactors.hom.app K) ≫
      G.mapDerivedCategoryFactors.hom.app ((R.mapHomologicalComplex (.up ℤ)).obj K) := by
    apply (cancel_epi
      ((Functor.mapDerivedCategoryCompIso R G).hom.app (DerivedCategory.Q.obj K))).mp
    rw [Iso.hom_inv_id_app_assoc]
    exact hc.symm
  simp only [Functor.mapDerivedCategorySquareIso, Iso.trans_hom, Iso.symm_hom,
    NatTrans.comp_app, Category.assoc]
  rw [Functor.mapDerivedCategoryCompIso_hom_app_factors,
    Functor.mapDerivedCategoryNatIso_fac]
  rw [← Category.assoc, hi, Category.assoc]


private theorem inverseComparison_eq {E : Type*} [Category E] {W X Y Z : E}
    (a : W ⟶ X) [IsIso a] (b : Y ⟶ Z) (i : X ≅ Z) (c : W ≅ Y)
    (t : Y ⟶ W) (ht : t ≫ a = b ≫ i.inv) (hc : c.hom ≫ b = a ≫ i.hom) :
    t = c.inv := by
  apply (cancel_mono a).1
  rw [ht]
  apply (cancel_epi c.hom).1
  simp only [← Category.assoc, Iso.hom_inv_id, Category.id_comp]
  rw [hc]
  simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]

private theorem inverseSquare_eq {E : Type*} [Category E] {W X Y Z : E}
    (a : W ≅ X) (b : X ≅ Y) (c : W ≅ Z) (d : Z ≅ Y)
    (h : a.hom ≫ b.hom = c.hom ≫ d.hom) : b.inv ≫ a.inv = d.inv ≫ c.inv := by
  have h' : a ≪≫ b = c ≪≫ d := Iso.ext h
  exact congrArg Iso.inv h'

namespace SheafOfModules

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [EssentiallySmall.{w} C]
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasSheafify J AddCommGrpCat.{w}]

variable {D : Type u'} [Category.{v'} D] {K : GrothendieckTopology D}
  [EssentiallySmall.{w} D]
  [K.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [K.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasSheafify K AddCommGrpCat.{w}]
  {BY : ℕᵒᵖ ⥤ Sheaf J CommRingCat.{w}} {BX : ℕᵒᵖ ⥤ Sheaf K CommRingCat.{w}}
  {uTop : GeometricMorphism (Sheaf K (Type w)) (Sheaf J (Type w))}
  {I : ∀ n : ℕ, AlgebraicInverseImage uTop.inverse (BY.obj (op n)) (BX.obj (op n))}
  (SY : SystemScalarAssignment (J := J)) (TY : SystemTensorCoherence SY)
  (SX : SystemScalarAssignment (J := K)) (TX : SystemTensorCoherence SX)
  (F : SystemGeometricInverseImageData BY BX uTop I)

variable (H : StrictRingSystem BX ⥤ StrictRingSystem BY) [H.Additive]
  [Abelian.HasKInjectiveResolutions (StrictRingSystem BX)]
  (adj : F.functor ⊣ H)
  (Hn : ∀ n : ℕ, systemLevel BX n ⥤ systemLevel BY n)
  [∀ n : ℕ, (Hn n).Additive]
  [∀ n : ℕ, Abelian.HasKInjectiveResolutions (systemLevel BX n)]
  (adjn : ∀ n : ℕ, F.levelFunctor n ⊣ Hn n)

set_option maxHeartbeats 2000000 in
-- Comparing the normalized singleton packages exceeds the default elaboration budget.
/-- The specified singleton conjugate is the right mate of exact evaluation.

Source: Zheng, Construction 4.1 and the comparison before Lemma 4.10; Stacks 07A6
(blueprint: lem-route-system-singleton-evaluation-mate).

Proof: Take the right mate of the inverse-image/evaluation square under the normalized
singleton adjunctions. On a flat-term K-flat representative its inverse is the ordinary
singleton geometric comparison: transpose its ordinary multiplication identity using the
singleton unit, and then use the representative formula for the normalized derived
adjunction. The representative clause in SystemSingletonGeometricComparisons identifies
this with the specified comparison on every resolving complex. Every derived object is
isomorphic to such a representative, so naturality identifies the two singleton maps
on every object. Taking their conjugates under the two composite geometric/singleton
adjunctions gives the claimed equality of right mates, by horizontal mate pasting. -/
theorem systemSingletonEvaluationMate
    (hF : SystemSingletonGeometricComparisons SY TY SX TX F) (n : ℕ) :
    (systemNormalizationEvaluation SY TY SX TX F H adj Hn adjn hF n).hom =
      CategoryTheory.SystemEvaluationNormalization.derivedMate adj (adjn n) (F.evaluation n) := by
  have : (I n).modules.Additive := F.levelAdditive n
  have : PreservesFiniteLimits (I n).modules := F.levelLimits n
  have : PreservesFiniteColimits (I n).modules := F.levelColimits n
  let dY := systemSingleDerivedExtension BY n SY TY
  let dX := systemSingleDerivedExtension BX n SX TX
  let s : F.functor.mapDerivedCategory ⋙ derivedSystemEvaluation BX n ≅
      derivedSystemEvaluation BY n ⋙ (F.levelFunctor n).mapDerivedCategory :=
    F.derivedEvaluation n
  let c := systemNormalizationSingleton SY TY SX TX F hF n
  let τ := derivedExtensionMate dY dX F.functor (F.levelFunctor n).mapDerivedCategory s.inv
  let o := hF.choose n
  -- Multiplication fixes the ordinary comparison's adjunction transpose.
  have ho (P : systemLevel BY n) :
      dX.ordinaryAdj.homEquiv _ _ ((o).inv.app P) =
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
        ((systemSingletonOrdinaryMultiplication (BY := BY) SY TY n).app P))
      (hF.choose_spec.choose_spec.choose_spec.choose_spec.2.2.2.1 n P)
  have hs (K : CochainComplex (StrictRingSystem BY) ℤ) :
      s.inv.app (DerivedCategory.Q.obj K) ≫
          (derivedSystemEvaluation BX n).map (F.functor.mapDerivedCategoryFactors.hom.app K) ≫
          (systemEvaluation BX n).mapDerivedCategoryFactors.hom.app
            ((F.functor.mapHomologicalComplex (.up ℤ)).obj K) =
        (F.levelFunctor n).mapDerivedCategory.map
            ((systemEvaluation BY n).mapDerivedCategoryFactors.hom.app K) ≫
          (F.levelFunctor n).mapDerivedCategoryFactors.hom.app
            (((systemEvaluation BY n).mapHomologicalComplex (.up ℤ)).obj K) ≫
          DerivedCategory.Q.map (((F.evaluation n).inv.mapHomologicalComplex (.up ℤ)).app K) := by
    let e : systemEvaluation BY n ⋙ F.levelFunctor n ≅
        F.functor ⋙ systemEvaluation BX n := (F.evaluation n).symm
    have hi : (Functor.mapDerivedCategorySquareIso e).hom = s.inv := by
      simp only [e, s, SystemGeometricInverseImageData.derivedEvaluation,
        Functor.mapDerivedCategorySquareIso, Iso.trans_hom, Iso.trans_inv,
        Iso.symm_hom, Iso.symm_inv, Functor.mapDerivedCategoryNatIso_symm, Category.assoc]
    rw [← hi]
    exact exactSquare_fac e K
  -- Localize the ordinary transpose using the normalized derived adjunctions.
  have hrep (P : CochainComplex (systemLevel BY n) ℤ) :
      τ.app (DerivedCategory.Q.obj P) ≫
          F.functor.mapDerivedCategory.map (dY.comparison.app P) ≫
          F.functor.mapDerivedCategoryFactors.hom.app
            ((dY.ordinary.mapHomologicalComplex (.up ℤ)).obj P) =
        dX.derived.map ((F.levelFunctor n).mapDerivedCategoryFactors.hom.app P) ≫
          dX.comparison.app (((F.levelFunctor n).mapHomologicalComplex (.up ℤ)).obj P) ≫
          DerivedCategory.Q.map ((NatIso.mapHomologicalComplex o.symm (.up ℤ)).hom.app P) :=
    derivedExtensionMate_rep dY dX (F.levelFunctor n) F.functor
      (F.levelFunctor n).mapDerivedCategory (F.levelFunctor n).mapDerivedCategoryFactors
      s.inv (F.evaluation n).inv hs o.symm ho P
  -- Compare on resolving representatives, then transport along their isomorphisms.
  have he : τ = c.inv := by
    have hp (P : CochainComplex (systemLevel BY n) ℤ) (hP : systemLevelKFlat BY n P) :
        τ.app (DerivedCategory.Q.obj P) = c.inv.app (DerivedCategory.Q.obj P) := by
      have := dY.computes P hP
      have hc := hF.choose_spec.choose_spec.choose_spec.choose_spec.2.2.2.2.2.1 n P hP
      change c.hom.app _ ≫ _ ≫ _ = _ at hc
      apply inverseComparison_eq
        (F.functor.mapDerivedCategory.map (dY.comparison.app P) ≫
          F.functor.mapDerivedCategoryFactors.hom.app
            ((dY.ordinary.mapHomologicalComplex (.up ℤ)).obj P))
        (dX.derived.map ((F.levelFunctor n).mapDerivedCategoryFactors.hom.app P) ≫
          dX.comparison.app (((F.levelFunctor n).mapHomologicalComplex (.up ℤ)).obj P))
        (DerivedCategory.Q.mapIso ((NatIso.mapHomologicalComplex o (.up ℤ)).app P))
        (c.app (DerivedCategory.Q.obj P))
      · simpa only [Category.assoc, Functor.mapIso_inv, Iso.app_inv,
          NatIso.mapHomologicalComplex, Iso.symm_hom] using hrep P
      · simpa only [Category.assoc, Functor.mapIso_hom, Iso.app_hom, dY, dX, o,
          systemSingleDerivedExtension, SystemLeftExtensionDerivation.toExtension] using hc
    ext V
    let K := DerivedCategory.Q.objPreimage V
    obtain ⟨P, q, hP, hq⟩ := systemLevel_kFlatResolution BY n K
    have := hq
    let e : DerivedCategory.Q.obj P ≅ V :=
      asIso (DerivedCategory.Q.map q) ≪≫ DerivedCategory.Q.objObjPreimageIso V
    apply (cancel_epi
      (((F.levelFunctor n).mapDerivedCategory ⋙ dX.derived).mapIso e).hom).1
    change ((F.levelFunctor n).mapDerivedCategory ⋙ dX.derived).map e.hom ≫ _ =
      ((F.levelFunctor n).mapDerivedCategory ⋙ dX.derived).map e.hom ≫ _
    rw [τ.naturality, c.inv.naturality, hp P hP]
  -- The second mate is the conjugate under the composite adjunctions.
  have hm : mateEquiv dY.adjunction dX.adjunction
      (TwoSquare.mk _ _ _ _ c.inv) = TwoSquare.mk _ _ _ _ s.inv := by
    rw [← he]
    exact (mateEquiv dY.adjunction dX.adjunction).apply_symm_apply _
  have hi := iterated_mateEquiv_conjugateEquiv dY.adjunction dX.adjunction
    (adjn n).mapDerivedCategoryRightDerivedAdjunction
    adj.mapDerivedCategoryRightDerivedAdjunction (TwoSquare.mk _ _ _ _ c.inv)
  rw [hm] at hi
  exact hi.symm

end SheafOfModules
