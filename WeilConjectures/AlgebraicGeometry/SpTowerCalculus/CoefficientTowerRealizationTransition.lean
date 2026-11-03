/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SpTowerCalculus.CoefficientTowerIntrinsicTransitions
public import WeilConjectures.AlgebraicGeometry.SpTowerCalculus.CoefficientTowerGenericTransitions

/-! # Strict transitions in intrinsic coefficient coordinates

Source: Zheng, Construction 4.1; Stacks 07A6; the first step of the
coefficient-tower transition compatibility argument.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option Elab.async false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall

universe u v
open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme WeilConjectures

namespace AlgebraicGeometry.ProEtale.SpTowerCalculus

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

section ExactLocalization

variable {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
  [Abelian A] [Abelian B] [Abelian C] [Abelian D]
  [HasDerivedCategory A] [HasDerivedCategory B]
  [HasDerivedCategory C] [HasDerivedCategory D]

-- The supplied comparison on a complex, with its terminal evaluation factor exposed.
end ExactLocalization

private theorem comparison_rep (F : A ⥤ B) (G : B ⥤ C) (H : A ⥤ C)
    [F.Additive] [G.Additive] [H.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    [PreservesFiniteLimits H] [PreservesFiniteColimits H]
    (s : F ⋙ G ≅ H) (P : CochainComplex A ℤ) :
    ((Functor.mapDerivedCategoryCompIso F G).symm ≪≫
      Functor.mapDerivedCategoryNatIso s).hom.app (DerivedCategory.Q.obj P) ≫
        H.mapDerivedCategoryFactors.hom.app P =
    G.mapDerivedCategory.map (F.mapDerivedCategoryFactors.hom.app P) ≫
      G.mapDerivedCategoryFactors.hom.app ((F.mapHomologicalComplex (.up ℤ)).obj P) ≫
      DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex s.hom (.up ℤ)).app P) := by
  simp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, Category.assoc]
  rw [Functor.mapDerivedCategoryNatIso_fac,
    ← Functor.mapDerivedCategoryCompIso_hom_app_factors F G P]
  erw [Category.assoc, Iso.inv_hom_id_app_assoc]
  exact Category.assoc _ _ _

private theorem change_restriction_rep
    (N : A ⥤ C) (M : A ⥤ D) (R R' : D ⥤ C)
    [N.Additive] [M.Additive] [R.Additive] [R'.Additive]
    [PreservesFiniteLimits N] [PreservesFiniteColimits N]
    [PreservesFiniteLimits M] [PreservesFiniteColimits M]
    [PreservesFiniteLimits R] [PreservesFiniteColimits R]
    [PreservesFiniteLimits R'] [PreservesFiniteColimits R']
    (t : N ⟶ M ⋙ R)
    (td : N.mapDerivedCategory ⟶ M.mapDerivedCategory ⋙ R.mapDerivedCategory)
    (ht : ∀ P : CochainComplex A ℤ,
      td.app (DerivedCategory.Q.obj P) ≫
        R.mapDerivedCategory.map (M.mapDerivedCategoryFactors.hom.app P) ≫
        R.mapDerivedCategoryFactors.hom.app ((M.mapHomologicalComplex (.up ℤ)).obj P) =
      N.mapDerivedCategoryFactors.hom.app P ≫
        DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex t (.up ℤ)).app P))
    (s : R ≅ R') (P : CochainComplex A ℤ) :
    td.app (DerivedCategory.Q.obj P) ≫
      (Functor.mapDerivedCategoryNatIso s).hom.app (M.mapDerivedCategory.obj
        (DerivedCategory.Q.obj P)) ≫
      R'.mapDerivedCategory.map (M.mapDerivedCategoryFactors.hom.app P) ≫
      R'.mapDerivedCategoryFactors.hom.app ((M.mapHomologicalComplex (.up ℤ)).obj P) =
    N.mapDerivedCategoryFactors.hom.app P ≫
      DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex
        (t ≫ Functor.whiskerLeft M s.hom) (.up ℤ)).app P) := by
  rw [← (Functor.mapDerivedCategoryNatIso s).hom.naturality_assoc]
  erw [Functor.mapDerivedCategoryNatIso_fac]
  rw [reassoc_of% (ht P)]
  rw [← DerivedCategory.Q.map_comp]
  congr 1

-- A square of exact functors descends from its equations on complex representatives.

private theorem represented_square
    (F : A ⥤ B) (N : B ⥤ C) (M : B ⥤ D)
    (N' : A ⥤ C) (M' : A ⥤ D) (R : D ⥤ C)
    [F.Additive] [N.Additive] [M.Additive] [N'.Additive] [M'.Additive] [R.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits N] [PreservesFiniteColimits N]
    [PreservesFiniteLimits M] [PreservesFiniteColimits M]
    [PreservesFiniteLimits N'] [PreservesFiniteColimits N']
    [PreservesFiniteLimits M'] [PreservesFiniteColimits M']
    [PreservesFiniteLimits R] [PreservesFiniteColimits R]
    (t : N ⟶ M ⋙ R) (t' : N' ⟶ M' ⋙ R)
    (td : N.mapDerivedCategory ⟶ M.mapDerivedCategory ⋙ R.mapDerivedCategory)
    (td' : N'.mapDerivedCategory ⟶ M'.mapDerivedCategory ⋙ R.mapDerivedCategory)
    (ht : ∀ P : CochainComplex B ℤ,
      td.app (DerivedCategory.Q.obj P) ≫
        R.mapDerivedCategory.map (M.mapDerivedCategoryFactors.hom.app P) ≫
        R.mapDerivedCategoryFactors.hom.app ((M.mapHomologicalComplex (.up ℤ)).obj P) =
      N.mapDerivedCategoryFactors.hom.app P ≫
        DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex t (.up ℤ)).app P))
    (ht' : ∀ P : CochainComplex A ℤ,
      td'.app (DerivedCategory.Q.obj P) ≫
        R.mapDerivedCategory.map (M'.mapDerivedCategoryFactors.hom.app P) ≫
        R.mapDerivedCategoryFactors.hom.app ((M'.mapHomologicalComplex (.up ℤ)).obj P) =
      N'.mapDerivedCategoryFactors.hom.app P ≫
        DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex t' (.up ℤ)).app P))
    (sn : F ⋙ N ≅ N') (sm : F ⋙ M ≅ M')
    (hs : ∀ X : A, t.app (F.obj X) ≫ R.map (sm.hom.app X) =
      sn.hom.app X ≫ t'.app X) (K : DerivedCategory A) :
    td.app (F.mapDerivedCategory.obj K) ≫
      R.mapDerivedCategory.map
        (((Functor.mapDerivedCategoryCompIso F M).symm ≪≫
          Functor.mapDerivedCategoryNatIso sm).hom.app K) =
    ((Functor.mapDerivedCategoryCompIso F N).symm ≪≫
      Functor.mapDerivedCategoryNatIso sn).hom.app K ≫ td'.app K := by
  let cn := ((Functor.mapDerivedCategoryCompIso F N).symm ≪≫
    Functor.mapDerivedCategoryNatIso sn).hom
  let cm := ((Functor.mapDerivedCategoryCompIso F M).symm ≪≫
    Functor.mapDerivedCategoryNatIso sm).hom
  let a := Functor.whiskerLeft F.mapDerivedCategory td ≫
    Functor.whiskerRight cm R.mapDerivedCategory
  let b := cn ≫ td'
  have hab : a = b := by
    apply Localization.natTrans_ext DerivedCategory.Q (HomologicalComplex.quasiIso A (.up ℤ))
    intro P
    dsimp only [a, b, NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app]
    apply (cancel_mono
      (R.mapDerivedCategory.map (M'.mapDerivedCategoryFactors.hom.app P) ≫
        R.mapDerivedCategoryFactors.hom.app ((M'.mapHomologicalComplex (.up ℤ)).obj P))).mp
    simp only [Category.assoc]
    rw [ht' P]
    have hc := comparison_rep F N N' sn P
    change cn.app (DerivedCategory.Q.obj P) ≫
      N'.mapDerivedCategoryFactors.hom.app P = _ at hc
    rw [reassoc_of% hc]
    have hm := comparison_rep F M M' sm P
    change cm.app (DerivedCategory.Q.obj P) ≫
      M'.mapDerivedCategoryFactors.hom.app P = _ at hm
    rw [← R.mapDerivedCategory.map_comp_assoc, hm]
    simp only [Functor.map_comp, Category.assoc]
    erw [← td.naturality_assoc]
    erw [R.mapDerivedCategoryFactors.hom.naturality]
    erw [reassoc_of% (ht ((F.mapHomologicalComplex (.up ℤ)).obj P))]
    simp only [Functor.comp_map, ← DerivedCategory.Q.map_comp]
    congr 2
    congr 1
    ext i
    exact hs (P.X i)
  exact NatTrans.congr_app hab K

private theorem lift_transition_rep
    (N : A ⥤ C) (M : A ⥤ D) (R : D ⥤ C)
    [N.Additive] [M.Additive] [R.Additive]
    [PreservesFiniteLimits N] [PreservesFiniteColimits N]
    [PreservesFiniteLimits M] [PreservesFiniteColimits M]
    [PreservesFiniteLimits R] [PreservesFiniteColimits R]
    (t : N ⟶ M ⋙ R) (P : CochainComplex A ℤ) :
    (Localization.liftNatTrans DerivedCategory.Q
        (HomologicalComplex.quasiIso A (.up ℤ)) _ _
        N.mapDerivedCategory (M ⋙ R).mapDerivedCategory
        (Functor.whiskerRight (NatTrans.mapHomologicalComplex t (.up ℤ))
          DerivedCategory.Q) ≫ (Functor.mapDerivedCategoryCompIso M R).hom).app
        (DerivedCategory.Q.obj P) ≫
      R.mapDerivedCategory.map (M.mapDerivedCategoryFactors.hom.app P) ≫
      R.mapDerivedCategoryFactors.hom.app ((M.mapHomologicalComplex (.up ℤ)).obj P) =
    N.mapDerivedCategoryFactors.hom.app P ≫
      DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex t (.up ℤ)).app P) := by
  dsimp only [NatTrans.comp_app]
  rw [Category.assoc, Functor.mapDerivedCategoryCompIso_hom_app_factors,
    Localization.liftNatTrans_app]
  change (N.mapDerivedCategoryFactors.hom.app P ≫
    DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex t (.up ℤ)).app P) ≫
    (M ⋙ R).mapDerivedCategoryFactors.inv.app P) ≫
    (M ⋙ R).mapDerivedCategoryFactors.hom.app P = _
  simp only [Category.assoc, Iso.inv_hom_id_app]
  erw [Category.comp_id]

private theorem genericCoefficientMap_system (T : Scheme.{u}) {m n : ℕ} (h : m ≤ n) :
    SemilinearSections.coefficientMap (ProEt.topology T)
      (SpTowerShriek.B l E T) (SpTowerShriek.tau l E T) h =
      (spCoefficientCommRings l E T).map (homOfLE h).op := by
  let t : SemilinearSections.rings (ProEt.topology T)
      (SpTowerShriek.B l E T) (SpTowerShriek.tau l E T) ⟶
      spCoefficientCommRings l E T :=
    NatTrans.ofOpSequence (fun _ ↦ 𝟙 _) (by
      intro n
      simp only [SemilinearSections.rings, Functor.ofOpSequence_map_homOfLE_succ,
        Category.comp_id, Category.id_comp]
      rfl)
  exact (Category.comp_id _).symm.trans
    ((t.naturality (homOfLE h).op).trans (Category.id_comp _))

private theorem hom_function_heq {R : Type*} [Ring R]
    {M M' N N' : ModuleCat R} (hM : M = M') (hN : N = N')
    {f : M ⟶ N} {g : M' ⟶ N'} (hfg : HEq f g) :
    HEq (fun x ↦ f x) (fun x ↦ g x) := by
  cases hM
  cases hN
  cases hfg
  rfl

-- Match the horizontal coefficient maps before using the heterogeneous module equalities.
set_option maxHeartbeats 4000000 in
-- Unfolding the coefficient presentations requires a larger elaboration budget.
private theorem transition_functions (b : SpTowerShriek.Base l E)
    (T : Scheme.{u}) (a : SpCoefficientTowersAbelian l E T)
    (M : spCoefficientTowers l E T) {m n : ℕ} (h : m ≤ n) (U : T.ProEtᵒᵖ) :
    HEq (fun x ↦ ((SemilinearSections.transition (ProEt.topology T)
        (SpTowerShriek.B l E T) (SpTowerShriek.tau l E T) h).app
          ((b.realization T).functor.obj M)).val.app U x)
      (fun x ↦ ((a.equivalence.functor.obj M).transition h).val.app U x) := by
  have hg := (SemilinearSections.transition_exists (ProEt.topology T)
    (SpTowerShriek.B l E T) (SpTowerShriek.tau l E T) h).exists.choose_spec
      ((b.realization T).functor.obj M) U
  apply hg.trans
  have hB := b.restrictions T M (Prod.mkHom (homOfLE h) (𝟙 U.unop)).op
  have hD := a.transitions M h U
  refine hom_function_heq
    (eq_of_heq ((b.sections T M n U).trans (a.sections M n U).symm)) ?_
    (hB.trans hD.symm)
  have hm :
      ((SemilinearSections.ring (coefficientSequenceTopology (ProEt.topology T))
        (SemilinearSections.systemRing (ProEt.topology T)
          (SpTowerShriek.B l E T) (SpTowerShriek.tau l E T))).obj.map
          (Prod.mkHom (homOfLE h) (𝟙 U.unop)).op).hom =
      (((sheafCompose (ProEt.topology T)
          (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
            ((spCoefficientCommRings l E T).map (homOfLE h).op)).hom.app U).hom := by
    change ((forget₂ CommRingCat.{u + 1} RingCat.{u + 1}).map
      ((((SemilinearSections.rings (ProEt.topology T) (SpTowerShriek.B l E T)
        (SpTowerShriek.tau l E T)).map (homOfLE h).op).hom.app U) ≫
          (SpTowerShriek.B l E T m).obj.map (𝟙 U))).hom = _
    erw [(SpTowerShriek.B l E T m).obj.map_id U, Category.comp_id]
    change (((sheafCompose (ProEt.topology T)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
          (SemilinearSections.coefficientMap (ProEt.topology T)
            (SpTowerShriek.B l E T) (SpTowerShriek.tau l E T) h)).hom.app U).hom = _
    rw [genericCoefficientMap_system l E T h]
  rw [hm]
  exact congrArg (ModuleCat.restrictScalars
    (((sheafCompose (ProEt.topology T)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
        ((spCoefficientCommRings l E T).map (homOfLE h).op)).hom.app U).hom).obj
    (eq_of_heq ((b.sections T M m U).trans (a.sections M m U).symm))

private theorem restriction_congr_sections (T : Scheme.{u})
    {R S : Sheaf (ProEt.topology T) CommRingCat.{u + 1}}
    (φ ψ : R ⟶ S) (e : φ = ψ)
    (M : SemilinearSections.Mod (ProEt.topology T) S)
    (U : T.ProEtᵒᵖ) (x : M.val.obj U) :
    ((eqToIso (congrArg SemilinearSections.res e)).hom.app M).val.app U x = x := by
  subst ψ
  rfl

private theorem heq_apply {A B A' B' : Type v} {f : A → B} {g : A' → B'}
    (hA : A = A') (hB : B = B') (hf : HEq f g) {x : A} {y : A'} (hx : HEq x y) :
    HEq (f x) (g y) := by
  cases hA
  cases hB
  cases hf
  cases hx
  rfl

private theorem ordinary_transition_square (b : SpTowerShriek.Base l E)
    (q : Coordinates l E b) (T : Scheme.{u})
    (M : spCoefficientTowers l E T) {m n : ℕ} (h : m ≤ n) :
    (SemilinearSections.transition (ProEt.topology T)
        (SpTowerShriek.B l E T) (SpTowerShriek.tau l E T) h).app
          ((b.realization T).functor.obj M) ≫
      (eqToIso (congrArg SemilinearSections.res
        (genericCoefficientMap_eq l E T h))).hom.app
          ((SpTowerShriek.ev l E T m).obj ((b.realization T).functor.obj M)) ≫
      (SheafOfModules.restrictScalars ((sheafCompose (ProEt.topology T)
          (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
            (proEtaleConstantRingMap (T := T) (quotient l E h)))).map
        ((q.ordinaryEvaluation T m).hom.app M) =
    (q.ordinaryEvaluation T n).hom.app M ≫
      (((q.abelian T).equivalence.functor.obj M).transition h) ≫
      (q.scalar T h).restriction.hom.app
        ((spCoefficientEvaluation l E T (q.abelian T).equivalence m).obj M) := by
  ext U x
  have hs := (q.scalar T h).restriction_sections
    ((spCoefficientEvaluation l E T (q.abelian T).equivalence m).obj M) U
    ((((q.abelian T).equivalence.functor.obj M).transition h).val.app U
      (((q.ordinaryEvaluation T n).hom.app M).val.app U x))
  apply eq_of_heq
  apply (q.sections T m M U _).trans
  change HEq
    (((eqToIso (congrArg SemilinearSections.res
      (genericCoefficientMap_eq l E T h))).hom.app _).val.app U
      (((SemilinearSections.transition (ProEt.topology T)
        (SpTowerShriek.B l E T) (SpTowerShriek.tau l E T) h).app
          ((b.realization T).functor.obj M)).val.app U x))
    (((q.scalar T h).restriction.hom.app _).val.app U
      ((((q.abelian T).equivalence.functor.obj M).transition h).val.app U
        (((q.ordinaryEvaluation T n).hom.app M).val.app U x)))
  rw [restriction_congr_sections T _ _ (genericCoefficientMap_eq l E T h)]
  apply (heq_apply _ _ (transition_functions l E b T (q.abelian T) M h U)
    (q.sections T n M U x).symm).trans hs.symm
  · exact (type_eq_of_heq (q.sections T n M U 0)).symm
  · exact (type_eq_of_heq (q.sections T m M U 0)).symm

-- Transpose the recorded reduction before cancelling its localization factors.

private theorem system_transpose_rep (T : Scheme.{u})
    (a : SpCoefficientTowersAbelian l E T) {m n : ℕ} (h : m ≤ n)
    (P : CochainComplex (spCoefficientTowers l E T) ℤ) :
    let _ := a.hasDerived
    let _ := a.equivalenceAdditive
    let _ := a.evaluationLimits
    let _ := a.evaluationColimits
    (SheafOfModules.systemDerivedTensorAdj a.scalar
      (spCoefficientCommRings l E T) h).homEquiv _ _
        ((a.reduction h).app (DerivedCategory.Q.obj P)) ≫
      (systemRestriction l E T h).mapDerivedCategory.map
        ((spCoefficientEvaluation l E T a.equivalence m).mapDerivedCategoryFactors.hom.app P) ≫
      (systemRestriction l E T h).mapDerivedCategoryFactors.hom.app
        (((spCoefficientEvaluation l E T a.equivalence m).mapHomologicalComplex (.up ℤ)).obj P) =
    (spCoefficientEvaluation l E T a.equivalence n).mapDerivedCategoryFactors.hom.app P ≫
      DerivedCategory.Q.map
        ((NatTrans.mapHomologicalComplex
          (Functor.whiskerLeft a.equivalence.functor
            (SheafOfModules.strictSystemTransition (spCoefficientCommRings l E T) h))
          (.up ℤ)).app P) := by
  let _ := a.hasDerived
  let _ := a.equivalenceAdditive
  let _ := a.evaluationLimits
  let _ := a.evaluationColimits
  let D := a.scalar ((spCoefficientCommRings l E T).map (homOfLE h).op)
  let en := spCoefficientEvaluation l E T a.equivalence n
  let em := spCoefficientEvaluation l E T a.equivalence m
  let r := (NatTrans.mapHomologicalComplex (a.ordinaryReduction h) (.up ℤ)).app P
  let t := (NatTrans.mapHomologicalComplex
    (Functor.whiskerLeft a.equivalence.functor
      (SheafOfModules.strictSystemTransition (spCoefficientCommRings l E T) h))
    (.up ℤ)).app P
  have ht : (D.ordinaryAdj.mapHomologicalComplex (.up ℤ)).homEquiv
      ((en.mapHomologicalComplex (.up ℤ)).obj P)
      ((em.mapHomologicalComplex (.up ℤ)).obj P) r = t := by
    ext i : 1
    change D.ordinaryAdj.unit.app _ ≫ _ = _
    change (D.ordinaryAdj.homEquiv _ _ ((a.ordinaryReduction h).app (P.X i))) = _
    rw [a.ordinaryReduction_eq]
    exact (D.ordinaryAdj.homEquiv _ _).apply_symm_apply _
  have htrans := D.transpose ((en.mapHomologicalComplex (.up ℤ)).obj P)
    ((em.mapHomologicalComplex (.up ℤ)).obj P) r
  rw [ht] at htrans
  have hr : D.adjunction.homEquiv _ _ ((a.reduction h).app (DerivedCategory.Q.obj P)) =
      en.mapDerivedCategoryFactors.hom.app P ≫ DerivedCategory.Q.map t ≫
        (systemRestriction l E T h).mapDerivedCategoryFactors.inv.app
          ((em.mapHomologicalComplex (.up ℤ)).obj P) ≫
        (systemRestriction l E T h).mapDerivedCategory.map
          (em.mapDerivedCategoryFactors.inv.app P) := by
    rw [a.reduction_rep]
    change D.adjunction.homEquiv _ _
      (D.model.T.map (en.mapDerivedCategoryFactors.hom.app P) ≫
        D.model.ε.app _ ≫ DerivedCategory.Q.map r ≫
          em.mapDerivedCategoryFactors.inv.app P) = _
    calc
      _ = en.mapDerivedCategoryFactors.hom.app P ≫
          D.adjunction.homEquiv _ _
            ((D.model.ε.app _ ≫ DerivedCategory.Q.map r) ≫
              em.mapDerivedCategoryFactors.inv.app P) := by
        simpa only [Category.assoc] using D.adjunction.homEquiv_naturality_left
          (en.mapDerivedCategoryFactors.hom.app P)
          ((D.model.ε.app _ ≫ DerivedCategory.Q.map r) ≫
            em.mapDerivedCategoryFactors.inv.app P)
      _ = _ := by
        rw [D.adjunction.homEquiv_naturality_right]
        erw [htrans]
        simp only [Category.assoc]
  rw [hr]
  simp only [Category.assoc]
  change en.mapDerivedCategoryFactors.hom.app P ≫ DerivedCategory.Q.map t ≫
    (systemRestriction l E T h).mapDerivedCategoryFactors.inv.app
      ((em.mapHomologicalComplex (.up ℤ)).obj P) ≫
    (systemRestriction l E T h).mapDerivedCategory.map
      (em.mapDerivedCategoryFactors.inv.app P) ≫
    (systemRestriction l E T h).mapDerivedCategory.map
      (em.mapDerivedCategoryFactors.hom.app P) ≫
    (systemRestriction l E T h).mapDerivedCategoryFactors.hom.app
      ((em.mapHomologicalComplex (.up ℤ)).obj P) =
    en.mapDerivedCategoryFactors.hom.app P ≫ DerivedCategory.Q.map t
  simp only [← Functor.map_comp_assoc, Iso.inv_hom_id_app]
  erw [(systemRestriction l E T h).mapDerivedCategory.map_id,
    Category.id_comp, Iso.inv_hom_id_app, Category.comp_id]

private def systemDerivedTranspose (T : Scheme.{u})
    (a : SpCoefficientTowersAbelian l E T) {m n : ℕ} (h : m ≤ n) :
    spDerivedCoefficientEvaluation l E T a n ⟶
      spDerivedCoefficientEvaluation l E T a m ⋙
        (systemRestriction l E T h).mapDerivedCategory where
  app K := (SheafOfModules.systemDerivedTensorAdj a.scalar
    (spCoefficientCommRings l E T) h).homEquiv _ _ ((a.reduction h).app K)
  naturality {K L} f :=
    (SheafOfModules.systemDerivedTensorAdj a.scalar
      (spCoefficientCommRings l E T) h).homEquiv_naturality_left_square
      ((spDerivedCoefficientEvaluation l E T a n).map f) ((a.reduction h).app L)
      ((a.reduction h).app K) ((spDerivedCoefficientEvaluation l E T a m).map f)
      ((a.reduction h).naturality f)

/-- Section-preserving realization carries the localized strict transition to the
original tower transition in the supplied section-preserving evaluation coordinates.
Source: Zheng 4.1; blueprint Local pairs, section model, and Levels paragraph.
Proof: first apply reduction_rep and the scalar model's cochain transpose formula.
The ordinaryReduction_eq field identifies its ordinary transpose with the strict
horizontal transition. Exact localization and the evaluation compositors therefore
identify the recorded derived adjoint with the localized strict transition. The supplied
restriction comparison transports this equality to intrinsic restriction coordinates.
On ordinary modules both transitions are the horizontal restriction M(n,U) to
M(m,U). The sections and restrictions fields of the two realizations identify these
functions. The ordinary evaluation and restriction comparisons fix sections, so the
same square holds for the supplied comparisons by sectionwise extensionality.
Apply it termwise to complexes. Exact localization and its composition comparison
then give the displayed square for every derived tower. No geometric operation,
scalar-extension comparison, boundedness or Tor hypothesis enters this assertion.
(blueprint: lem-sp-tower-realization-strict-transition). -/
theorem realization_intrinsicTransition
    (b : SpTowerShriek.Base l E) (q : Coordinates l E b) (T : Scheme.{u})
    (K : spDerivedCoefficientTowers l E T (q.abelian T))
    {m n : ℕ} (v : m ≤ n) :
    (genericIntrinsicTransitions l E T v).app
        ((realization l E b T (q.abelian T)).functor.obj K) ≫
      (scalarRestriction (quotient l E v) T).map
        ((levelComparison l E b q T m).hom.app K) =
    (levelComparison l E b q T n).hom.app K ≫
      intrinsicTransition l E T (q.abelian T) v (q.scalar T v) K := by
  let a := q.abelian T
  let _ := a.hasDerived
  let _ := b.realizationAdditive T
  let _ := a.equivalenceAdditive
  let _ := a.evaluationLimits
  let _ := a.evaluationColimits
  let F := (b.realization T).functor
  let N := SpTowerShriek.ev l E T n
  let M := SpTowerShriek.ev l E T m
  let N' := spCoefficientEvaluation l E T a.equivalence n
  let M' := spCoefficientEvaluation l E T a.equivalence m
  let _ : N'.Additive := Functor.additive_of_iso (q.ordinaryEvaluation T n)
  let _ : M'.Additive := Functor.additive_of_iso (q.ordinaryEvaluation T m)
  let Rg := SemilinearSections.res (SemilinearSections.coefficientMap
    (ProEt.topology T) (SpTowerShriek.B l E T) (SpTowerShriek.tau l E T) v)
  let R0 := systemRestriction l E T v
  let R := SheafOfModules.restrictScalars ((sheafCompose (ProEt.topology T)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
      (proEtaleConstantRingMap (T := T) (quotient l E v)))
  let tg := SemilinearSections.transition (ProEt.topology T)
    (SpTowerShriek.B l E T) (SpTowerShriek.tau l E T) v
  let torig := Functor.whiskerLeft a.equivalence.functor
    (SheafOfModules.strictSystemTransition (spCoefficientCommRings l E T) v)
  let sg : Rg ≅ R := eqToIso (congrArg SemilinearSections.res
    (genericCoefficientMap_eq l E T v))
  let so : R0 ≅ R := (q.scalar T v).restriction
  let tdg := SemilinearSections.derivedTransition (ProEt.topology T)
    (SpTowerShriek.B l E T) (SpTowerShriek.tau l E T) v
  let tdo := systemDerivedTranspose l E T a v
  have hg (P : CochainComplex (SpTowerShriek.S l E T) ℤ) :
      tdg.app (DerivedCategory.Q.obj P) ≫
        Rg.mapDerivedCategory.map (M.mapDerivedCategoryFactors.hom.app P) ≫
        Rg.mapDerivedCategoryFactors.hom.app ((M.mapHomologicalComplex (.up ℤ)).obj P) =
      N.mapDerivedCategoryFactors.hom.app P ≫
        DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex tg (.up ℤ)).app P) := by
    exact lift_transition_rep N M Rg tg P
  have ho (P : CochainComplex (spCoefficientTowers l E T) ℤ) :
      tdo.app (DerivedCategory.Q.obj P) ≫
        R0.mapDerivedCategory.map (M'.mapDerivedCategoryFactors.hom.app P) ≫
        R0.mapDerivedCategoryFactors.hom.app ((M'.mapHomologicalComplex (.up ℤ)).obj P) =
      N'.mapDerivedCategoryFactors.hom.app P ≫
        DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex torig (.up ℤ)).app P) := by
    exact system_transpose_rep l E T a v P
  have hs (X : spCoefficientTowers l E T) :
      (tg ≫ Functor.whiskerLeft M sg.hom).app (F.obj X) ≫
        R.map ((q.ordinaryEvaluation T m).hom.app X) =
      (q.ordinaryEvaluation T n).hom.app X ≫
        (torig ≫ Functor.whiskerLeft M' so.hom).app X := by
    simpa only [F, M, M', R, tg, torig, sg, so, a, NatTrans.comp_app,
      Functor.whiskerLeft_app, SheafOfModules.strictSystemTransition, Category.assoc] using
      ordinary_transition_square l E b q T X v
  have h := represented_square F N M N' M' R
    (tg ≫ Functor.whiskerLeft M sg.hom)
    (torig ≫ Functor.whiskerLeft M' so.hom)
    (tdg ≫ Functor.whiskerLeft M.mapDerivedCategory
      (Functor.mapDerivedCategoryNatIso sg).hom)
    (tdo ≫ Functor.whiskerLeft M'.mapDerivedCategory
      (Functor.mapDerivedCategoryNatIso so).hom)
    (by
      intro P
      simpa only [NatTrans.comp_app, Functor.whiskerLeft_app, Category.assoc] using
        change_restriction_rep N M Rg R tg tdg hg sg P)
    (by
      intro P
      simpa only [NatTrans.comp_app, Functor.whiskerLeft_app, Category.assoc] using
        change_restriction_rep N' M' R0 R torig tdo ho so P)
    (q.ordinaryEvaluation T n) (q.ordinaryEvaluation T m) hs K
  exact h

set_option maxHeartbeats 4000000 in
-- Unfolding the coefficient presentations requires a larger elaboration budget.
set_option maxHeartbeats 4000000 in
-- Unfolding the coefficient presentations requires a larger elaboration budget.
set_option maxHeartbeats 4000000 in
-- The exact-functor calculation uses both large coefficient presentations.
end AlgebraicGeometry.ProEtale.SpTowerCalculus
attribute [instance high] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
