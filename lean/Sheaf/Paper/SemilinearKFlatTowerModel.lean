/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q130
-/
module

public import Sheaf.Paper.SmoothPurityCoefficientTowersAbelian
public import Sheaf.CategoryTheory.SystemScalarModel
public import Sheaf.Algebra.Homology.KFlatIndependentCoefficients
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel
public import Sheaf.CategoryTheory.RingedStrictTowerHomotopyLimitIndependentCoefficients
import all Sheaf.Paper.SmoothPurityCoefficientTowersAbelian
import Sheaf.CategoryTheory.SystemEvaluationKFlat
import all Sheaf.Paper.KFlatRingedToposPullback

/-!
# Compatible K-flat representatives of semilinear coefficient towers

Source: blueprint main-20261015, sec-smooth-purity, sk-lem-sp-tower.proof.md,
preliminary coherent-tower realization; Stacks 06YS, 0G7E, 06YY, 0940 and 0941;
Bhatt--Scholze, Definition 3.5.3
(blueprint: lem-sp-semilinear-kflat-tower-model).

The single complex P is a complex in the actual varying-coefficient tower category.
Its evaluations are the Q_n, and its horizontal arrows are the q_(n,m), including
identity arrows. Index n denotes positive exponent n+1. The predicate below merely
packages all conclusions of the theorem; its local instances are the dependency's
chosen localization and exact evaluations. No representative or morphism is chosen
from a mere existence theorem.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option linter.unusedVariables false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

attribute [local instance high] HasDerivedCategory.standard

universe t u

open CategoryTheory CategoryTheory.Limits Opposite SheafOfModules

section
universe a₁ a₂ a₃ a₄
variable {A : Type a₁} {B : Type a₂} {C : Type a₃} {D : Type a₄}
  [Category A] [Category B] [Category C] [Category D]
private theorem liftSquare (U : A ⥤ B) (V : B ⥤ D) (E : A ⥤ C) (R : C ⥤ D)
    (α : U ⋙ V ≅ E ⋙ R) {X Y : A} (a : X ⟶ Y)
    {UX : B} (i : U.obj X ≅ UX) {EX : C} (j : E.obj X ≅ EX) :
    V.map i.hom ≫ V.map (i.inv ≫ U.map a) ≫ α.hom.app Y =
      α.hom.app X ≫ R.map (j.hom ≫ (j.inv ≫ E.map a)) := by
  simp only [Iso.hom_inv_id_assoc]
  rw [← V.map_comp_assoc, i.hom_inv_id_assoc]
  exact α.hom.naturality a

end

namespace SheafOfModules

section
universe c v w
variable {X : Type c} [Category.{v} X] {J : GrothendieckTopology X}
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasSheafify J AddCommGrpCat.{w}]
  [EssentiallySmall.{w} X]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Sectionwise pure-tensor equation, expressed before specializing the coefficient site.
Source: Stacks 03D7 (blueprint: lem-sp-semilinear-kflat-tower-model). -/
def systemTensorSectionFormula {R S : Sheaf J CommRingCat.{w}} {φ : R ⟶ S}
    (A : SystemScalarModel φ)
    (P : ringedSiteModules.{w} (derivedChangeRingIndependentCoefficients J R))
    (M : ringedSiteModules.{w} (derivedChangeRingIndependentCoefficients J S))
    (f : A.model.E.obj P ⟶ M)
    (q : P ⟶ (restrictScalars.{w}
      ((sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).map φ)).obj M) : Prop :=
  ∀ (V : Xᵒᵖ) (c : S.obj.obj V) (x : P.val.obj V),
    f.val.app V (systemModelTmul A.model P V c x) =
      c • (show M.val.obj V from q.val.app V x)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem tensorSectionFormula_of_transpose
    {R S : Sheaf J CommRingCat.{w}} {φ : R ⟶ S} (A : SystemScalarModel φ)
    (P : ringedSiteModules.{w} (derivedChangeRingIndependentCoefficients J R))
    (M : ringedSiteModules.{w} (derivedChangeRingIndependentCoefficients J S))
    (f : A.model.E.obj P ⟶ M)
    (q : P ⟶ (restrictScalars.{w}
      ((sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).map φ)).obj M)
    (h : A.ordinaryAdj.homEquiv P M f = q) :
    systemTensorSectionFormula A P M f q := by
  intro V c x
  simpa only [h] using systemScalarModel_transpose_tmul A P M f V c x

end
end SheafOfModules

namespace SemilinearModelProof

section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe c v w
variable {X : Type c} [Category.{v} X] {J : GrothendieckTopology X}
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasSheafify J AddCommGrpCat.{w}]
  (B : ℕᵒᵖ ⥤ Sheaf J CommRingCat.{w}) (R : Sheaf J CommRingCat.{w})
  (rho : ∀ n : ℕ, R ⟶ B.obj (op n))
  (hrho : ∀ {m n : ℕ} (h : m ≤ n), rho n ≫ B.map (homOfLE h).op = rho m)

private abbrev res (n : ℕ) := restrictScalars.{w}
  ((sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).map (rho n))

private def restrictionArrow (M : StrictRingSystem B) {m n : ℕ} (h : m ≤ n) :
    (res B R rho n).obj (M.level n) ⟶ (res B R rho m).obj (M.level m) where
  val :=
    { app V := ModuleCat.ofHom
        (X := ((res B R rho n).obj (M.level n)).val.obj V)
        (Y := ((res B R rho m).obj (M.level m)).val.obj V)
        { toFun := fun x ↦ (M.transition h).val.app V x
          map_add' := map_add _
          map_smul' := by
            intro r x
            have he := congrArg (fun f ↦ f.hom.app V r) (hrho h)
            change (B.map (homOfLE h).op).hom.app V ((rho n).hom.app V r) =
              (rho m).hom.app V r at he
            have hh := ((M.transition h).val.app V).hom.map_smul
              ((rho n).hom.app V r) (show (M.level n).val.obj V from x)
            exact hh.trans (congrArg
              (fun r' : (B.obj (op m)).obj.obj V ↦
                r' • (show (M.level m).val.obj V from (M.transition h).val.app V x)) he) }
      naturality := by
        intro V W f
        ext x
        exact PresheafOfModules.naturality_apply (M.transition h).val f x }

private def restrictionFunctor : StrictRingSystem B ⥤
    (ℕᵒᵖ ⥤ SheafOfModules.{w}
      ((sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).obj R)) where
  obj M :=
    { obj n := (res B R rho n.unop).obj (M.level n.unop)
      map f := restrictionArrow B R rho (hrho := hrho) M (leOfHom f.unop)
      map_id n := by
        ext V x
        exact M.identity n.unop V x
      map_comp f g := by
        ext V x
        exact M.compose (leOfHom g.unop) (leOfHom f.unop) V x }
  map f :=
    { app n := (res B R rho n.unop).map (f.app n.unop)
      naturality := by
        intro m n h
        ext V x
        exact congrArg (fun a ↦ a.val.app V x) (f.comm (leOfHom h.unop)).symm }
  map_id M := by
    ext n V x
    rfl
  map_comp f g := by
    ext n V x
    rfl

private theorem restrictionFunctor_evaluation (n : ℕ) :
    restrictionFunctor B R rho hrho ⋙ (CategoryTheory.evaluation ℕᵒᵖ _).obj (op n) =
      systemEvaluation B n ⋙ res B R rho n := rfl

private theorem restrictionFunctor_limits :
    PreservesFiniteLimits.{max c w, max c w} (restrictionFunctor B R rho hrho) := by
  apply preservesFiniteLimits_of_evaluation
  rintro ⟨n⟩
  rw [restrictionFunctor_evaluation]
  exact comp_preservesFiniteLimits _ _

private theorem restrictionFunctor_colimits :
    PreservesFiniteColimits.{max c w, max c w} (restrictionFunctor B R rho hrho) := by
  apply preservesFiniteColimits_of_evaluation
  rintro ⟨n⟩
  rw [restrictionFunctor_evaluation]
  exact comp_preservesFiniteColimits _ _

end
end SemilinearModelProof


section
universe c₁ c₂ c₃
variable {A : Type c₁} {B : Type c₂} {D : Type c₃}
  [Category A] [Category B] [Category D]
private theorem transportReduction {Fn : A ⥤ B} {Fm : A ⥤ D} (T : B ⥤ D)
    (r : Fn ⋙ T ⟶ Fm) {X Y : A} (a : X ⟶ Y)
    {M : B} {N : D} (i : Fn.obj X ≅ M) (j : Fm.obj X ≅ N)
    (v : T.obj M ⟶ N) (hr : r.app X = T.map i.hom ≫ v ≫ j.inv) :
    T.map (i.inv ≫ Fn.map a) ≫ r.app Y = v ≫ j.inv ≫ Fm.map a := by
  rw [T.map_comp, Category.assoc]
  erw [r.naturality a, hr]
  simp only [← Category.assoc, ← T.map_comp,
    i.inv_hom_id, T.map_id, Category.id_comp]
end

namespace AlgebraicGeometry.ProEtale

attribute [local irreducible] DerivedCategory CategoryTheory.Functor.mapDerivedCategory
  HasDerivedCategory.standard

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (T : Scheme.{t})

set_option backward.isDefEq.respectTransparency false in
/-- The actual completed-coefficient quotient, retaining the commutative structures.
It is the unique completed coefficient-limit comparison followed by its nth projection.
Source: blueprint, coherent-tower realization and coefficient convention
(blueprint: lem-sp-semilinear-kflat-tower-model). -/
def spSemilinearCompletedProjection (n : ℕ) :
    WeilConjectures.completedIntegralCommRingSheafUnrestricted l E T ⟶
      (spCoefficientCommRings l E T).obj (op n) :=
  (sheafCompose (Scheme.ProEt.topology T)
    (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})).preimage
      ((sp_completed_coefficient_limit l E T).exists.choose.hom ≫
        limit.π (spCoefficientRings l E T) (op n))


attribute [local irreducible] spCoefficientCommRings spCoefficientRings
  spSemilinearCompletedProjection

/-- The chain transition of one complex of actual coefficient towers. This is evaluation
of its strict horizontal transition, for every ordered pair including identities.
Source: blueprint, coherent-tower realization, chain squares
(blueprint: lem-sp-semilinear-kflat-tower-model). -/
def spSemilinearChainTransition (D : SpCoefficientTowersAbelian l E T)
    (P : CochainComplex (spCoefficientTowers l E T) ℤ) {m n : ℕ} (h : m ≤ n) :
    letI : HasSheafify (Scheme.ProEt.topology T) AddCommGrpCat.{max u (t + 1)} :=
      surjectiveTower_hasSheafify.{t, u} T
    letI : (Scheme.ProEt.topology T).WEqualsLocallyBijective
        AddCommGrpCat.{max u (t + 1)} := surjectiveTower_wEqualsLocallyBijective.{t, u} T
    letI := D.equivalenceAdditive
    ((spCoefficientEvaluation l E T D.equivalence n).mapHomologicalComplex (.up ℤ)).obj P ⟶
      ((systemRestriction (spCoefficientCommRings l E T) h).mapHomologicalComplex
        (.up ℤ)).obj
          (((spCoefficientEvaluation l E T D.equivalence m).mapHomologicalComplex
            (.up ℤ)).obj P) :=
  letI : HasSheafify (Scheme.ProEt.topology T) AddCommGrpCat.{max u (t + 1)} :=
    surjectiveTower_hasSheafify.{t, u} T
  letI : (Scheme.ProEt.topology T).WEqualsLocallyBijective
      AddCommGrpCat.{max u (t + 1)} := surjectiveTower_wEqualsLocallyBijective.{t, u} T
  letI := D.equivalenceAdditive
  (NatTrans.mapHomologicalComplex
    (Functor.whiskerLeft D.equivalence.functor
      (strictSystemTransition (spCoefficientCommRings l E T) h)) (.up ℤ)).app P

attribute [local irreducible] spSemilinearChainTransition

private theorem chainTransition_f (D : SpCoefficientTowersAbelian l E T)
    (P : CochainComplex (spCoefficientTowers l E T) ℤ) {m n : ℕ} (h : m ≤ n)
    (i : ℤ) :
    letI : HasSheafify (Scheme.ProEt.topology T) AddCommGrpCat.{max u (t + 1)} :=
      surjectiveTower_hasSheafify.{t, u} T
    letI : (Scheme.ProEt.topology T).WEqualsLocallyBijective
        AddCommGrpCat.{max u (t + 1)} := surjectiveTower_wEqualsLocallyBijective.{t, u} T
    letI := D.equivalenceAdditive
    (spSemilinearChainTransition l E T D P h).f i =
      (D.equivalence.functor.obj (P.X i)).transition h := by
  unfold spSemilinearChainTransition
  rfl


/-- The specified derived evaluation isomorphisms of one tower representative.
They use the canonical exact-evaluation factorization and the same tower isomorphism.
Source: blueprint, coherent-tower realization, chain squares
(blueprint: lem-sp-semilinear-kflat-tower-model). -/
def spSemilinearEvaluationIso (D : SpCoefficientTowersAbelian l E T)
    (C : @DerivedCategory (spCoefficientTowers l E T) _ _ D.hasDerived)
    (P : CochainComplex (spCoefficientTowers l E T) ℤ)
    (a : (@DerivedCategory.Q (spCoefficientTowers l E T) _ _ D.hasDerived).obj P ≅ C) :=
  letI : HasSheafify (Scheme.ProEt.topology T) AddCommGrpCat.{max u (t + 1)} :=
    surjectiveTower_hasSheafify.{t, u} T
  letI : (Scheme.ProEt.topology T).WEqualsLocallyBijective
      AddCommGrpCat.{max u (t + 1)} := surjectiveTower_wEqualsLocallyBijective.{t, u} T
  letI := D.hasDerived
  letI := D.equivalenceAdditive
  letI := D.evaluationLimits
  letI := D.evaluationColimits
  letI : ∀ n : ℕ, (spCoefficientEvaluation l E T D.equivalence n).Additive :=
    fun n ↦ Functor.additive_of_preserves_binary_products
      (spCoefficientEvaluation l E T D.equivalence n)
  letI : EssentiallySmall.{max u (t + 1)} T.ProEt := essentiallySmallSelf.{u} _
  fun n : ℕ ↦
    ((spCoefficientEvaluation l E T D.equivalence n).mapDerivedCategoryFactors.app P).symm ≪≫
      (spCoefficientEvaluation l E T D.equivalence n).mapDerivedCategory.mapIso a

attribute [local irreducible] spSemilinearEvaluationIso

/-- The completed-ring derived lift, its specified evaluations and all derived-limit
projection squares. This is the completed-ring clause of the simultaneous model.
Source: blueprint, sk-lem-sp-tower.proof.md, coherent-tower realization;
Stacks 0940--0941 (blueprint: lem-sp-semilinear-kflat-tower-model). -/
def HasSpSemilinearCompletedLift (D : SpCoefficientTowersAbelian l E T)
    (C : @DerivedCategory (spCoefficientTowers l E T) _ _ D.hasDerived)
    (P : CochainComplex (spCoefficientTowers l E T) ℤ)
    (a : (@DerivedCategory.Q (spCoefficientTowers l E T) _ _ D.hasDerived).obj P ≅ C) :
    Prop :=
  letI : HasSheafify (Scheme.ProEt.topology T) AddCommGrpCat.{max u (t + 1)} :=
    surjectiveTower_hasSheafify.{t, u} T
  letI : (Scheme.ProEt.topology T).WEqualsLocallyBijective
      AddCommGrpCat.{max u (t + 1)} := surjectiveTower_wEqualsLocallyBijective.{t, u} T
  letI := D.hasDerived
  letI := D.equivalenceAdditive
  letI := D.evaluationLimits
  letI := D.evaluationColimits
  letI : ∀ n : ℕ, (spCoefficientEvaluation l E T D.equivalence n).Additive :=
    fun n ↦ Functor.additive_of_preserves_binary_products
      (spCoefficientEvaluation l E T D.equivalence n)
  letI : EssentiallySmall.{max u (t + 1)} T.ProEt := essentiallySmallSelf.{u} _
  let Ev := spCoefficientEvaluation l E T D.equivalence
  let R := WeilConjectures.completedIntegralCommRingSheafUnrestricted l E T
  let RM := SheafOfModules.{max u (t + 1)}
    ((sheafCompose (Scheme.ProEt.topology T)
      (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})).obj R)
  letI : HasDerivedCategory.{max u (t + 1) + 1} RM :=
    HasDerivedCategory.standard _
  letI : HasDerivedCategory.{max u (t + 1) + 1} (ℕᵒᵖ ⥤ RM) :=
    HasDerivedCategory.standard _
  let rho := spSemilinearCompletedProjection l E T
  let Res := fun n : ℕ ↦ restrictScalars.{max u (t + 1)}
    ((sheafCompose (Scheme.ProEt.topology T)
      (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})).map (rho n))
  let resAdd : ∀ n : ℕ, (Res n).Additive := fun _n ↦ inferInstance
  let resLimits : ∀ n : ℕ, PreservesFiniteLimits (Res n) := fun _n ↦ inferInstance
  let resColimits : ∀ n : ℕ, PreservesFiniteColimits (Res n) := fun _n ↦ inferInstance
  let e := spSemilinearEvaluationIso l E T D C P a
  ∃ (U : spCoefficientTowers l E T ⥤ (ℕᵒᵖ ⥤ RM))
    (hadd : U.Additive) (hlim : PreservesFiniteLimits U)
    (hcolim : PreservesFiniteColimits U),
    letI := hadd
    letI := hlim
    letI := hcolim
    ∃ hU : ∀ n : ℕ, U ⋙ (evaluation ℕᵒᵖ RM).obj (op n) = Ev n ⋙ Res n,
      (∀ (M : spCoefficientTowers l E T) {m n : ℕ} (h : m ≤ n)
        (V : T.ProEtᵒᵖ),
        HEq (fun x ↦ (((U.obj M).map (homOfLE h).op).val.app V) x)
          (fun x ↦ (((D.equivalence.functor.obj M).transition h).val.app V) x)) ∧
      let UP := (U.mapHomologicalComplex (.up ℤ)).obj P
      let b := (U.mapDerivedCategoryFactors.app P).symm ≪≫
        U.mapDerivedCategory.mapIso a
      let evR := fun n : ℕ ↦ (evaluation ℕᵒᵖ RM).obj (op n)
      let comparison := fun n : ℕ ↦
        letI := resAdd n
        letI := resLimits n
        letI := resColimits n
        letI := D.evaluationLimits n
        letI := D.evaluationColimits n
        letI : (Ev n).Additive := Functor.additive_of_preserves_binary_products _
        letI := comp_preservesFiniteLimits (Ev n) (Res n)
        letI := comp_preservesFiniteColimits (Ev n) (Res n)
        letI := comp_preservesFiniteLimits U (evR n)
        letI := comp_preservesFiniteColimits U (evR n)
        (Functor.mapDerivedCategoryCompIso U (evR n)).symm ≪≫
          Functor.mapDerivedCategoryNatIso (eqToIso (hU n)) ≪≫
            Functor.mapDerivedCategoryCompIso (Ev n) (Res n)
      (∀ n : ℕ,
        (evR n).mapDerivedCategory.map (U.mapDerivedCategoryFactors.hom.app P) ≫
            (evR n).mapDerivedCategory.map b.hom ≫ (comparison n).hom.app C =
          (comparison n).hom.app (DerivedCategory.Q.obj P) ≫
            (@Functor.mapDerivedCategory _ _ _ _ _ _ _ _ (Res n)
              (resAdd n) (resLimits n) (resColimits n)).map
                ((Ev n).mapDerivedCategoryFactors.hom.app P ≫ (e n).hom)) ∧
      (∀ (RF : DerivedCategory (ℕᵒᵖ ⥤ RM) ⥤ DerivedCategory RM)
        (eta : (lim : (ℕᵒᵖ ⥤ RM) ⥤ RM).mapHomologicalComplex (.up ℤ) ⋙
          DerivedCategory.Q ⟶ DerivedCategory.Q ⋙ RF)
        (_hRF : RF.IsRightDerivedFunctor eta
          (HomologicalComplex.quasiIso (ℕᵒᵖ ⥤ RM) (.up ℤ)))
        (V : DerivedCategory (ℕᵒᵖ ⥤ RM) ⥤ (ℕᵒᵖ ⥤ DerivedCategory RM))
        (_epsilon : DerivedCategory.Q ⋙ V ≅
          HomologicalComplex.complexOfFunctorsToFunctorToComplex ⋙
            (Functor.whiskeringRight ℕᵒᵖ (CochainComplex RM ℤ)
              (DerivedCategory RM)).obj DerivedCategory.Q)
        (pi : ∀ n : ℕ, RF ⟶ V ⋙ (evaluation ℕᵒᵖ (DerivedCategory RM)).obj (op n)),
        ∀ n : ℕ,
          RF.map b.hom ≫ (pi n).app (U.mapDerivedCategory.obj C) =
            (pi n).app (DerivedCategory.Q.obj UP) ≫ (V.map b.hom).app (op n))


section
set_option allowUnsafeReducibility true in
attribute [local semireducible] spCoefficientCommRings spCoefficientRings

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem completedProjection_comp {m n : ℕ} (h : m ≤ n) :
    spSemilinearCompletedProjection l E T n ≫
      (spCoefficientCommRings l E T).map (homOfLE h).op =
        spSemilinearCompletedProjection l E T m := by
  let F := sheafCompose (Scheme.ProEt.topology T)
    (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})
  apply F.map_injective
  rw [F.map_comp]
  simp only [spSemilinearCompletedProjection]
  dsimp only [F]
  rw [Functor.map_preimage, Functor.map_preimage]
  have hm : F.map ((spCoefficientCommRings l E T).map (homOfLE h).op) =
      (spCoefficientRings l E T).map (homOfLE h).op := by
    exact eq_of_heq (Functor.hcongr_hom (coefficientRings_eq l E T) (homOfLE h).op).symm
  rw [hm, Category.assoc, limit.w]

end

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem completedLift (D : SpCoefficientTowersAbelian l E T)
    (C : @DerivedCategory (spCoefficientTowers l E T) _ _ D.hasDerived)
    (P : CochainComplex (spCoefficientTowers l E T) ℤ)
    (a : (@DerivedCategory.Q (spCoefficientTowers l E T) _ _ D.hasDerived).obj P ≅ C) :
    HasSpSemilinearCompletedLift l E T D C P a := by
  let : HasSheafify (Scheme.ProEt.topology T) AddCommGrpCat.{max u (t + 1)} :=
    surjectiveTower_hasSheafify.{t, u} T
  let : (Scheme.ProEt.topology T).WEqualsLocallyBijective
      AddCommGrpCat.{max u (t + 1)} := surjectiveTower_wEqualsLocallyBijective.{t, u} T
  let := D.hasDerived
  let := D.equivalenceAdditive
  let := D.evaluationLimits
  let := D.evaluationColimits
  let : ∀ n : ℕ, (spCoefficientEvaluation l E T D.equivalence n).Additive :=
    fun n ↦ Functor.additive_of_preserves_binary_products
      (spCoefficientEvaluation l E T D.equivalence n)
  let : EssentiallySmall.{max u (t + 1)} T.ProEt := essentiallySmallSelf.{u} _
  let B := spCoefficientCommRings l E T
  let R := WeilConjectures.completedIntegralCommRingSheafUnrestricted l E T
  let RM := SheafOfModules.{max u (t + 1)}
    ((sheafCompose (Scheme.ProEt.topology T)
      (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})).obj R)
  let : HasDerivedCategory.{max u (t + 1) + 1} RM := HasDerivedCategory.standard _
  let : HasDerivedCategory.{max u (t + 1) + 1} (ℕᵒᵖ ⥤ RM) :=
    HasDerivedCategory.standard _
  let rho := spSemilinearCompletedProjection l E T
  let V := SemilinearModelProof.restrictionFunctor B R rho
    (fun h ↦ completedProjection_comp l E T h)
  have : PreservesFiniteLimits V := SemilinearModelProof.restrictionFunctor_limits B R rho
    (fun h ↦ completedProjection_comp l E T h)
  have : PreservesFiniteColimits V := SemilinearModelProof.restrictionFunctor_colimits B R rho
    (fun h ↦ completedProjection_comp l E T h)
  have : V.Additive := Functor.additive_of_preserves_binary_products _
  let U := D.equivalence.functor ⋙ V
  have : PreservesFiniteLimits U := comp_preservesFiniteLimits _ _
  have : PreservesFiniteColimits U := comp_preservesFiniteColimits _ _
  have : U.Additive := inferInstance
  refine ⟨U, inferInstance, inferInstance, inferInstance, fun _ ↦ rfl, ?_, ?_⟩
  · intro M m n h W
    rfl
  · constructor
    · intro n
      let Ev := spCoefficientEvaluation l E T D.equivalence
      let Res := SemilinearModelProof.res B R rho
      let RM := SheafOfModules.{max u (t + 1)}
        ((sheafCompose (Scheme.ProEt.topology T)
          (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})).obj R)
      let evR := fun n : ℕ ↦ (CategoryTheory.evaluation ℕᵒᵖ RM).obj (op n)
      let cmp := (Functor.mapDerivedCategoryCompIso U (evR n)).symm ≪≫
        Functor.mapDerivedCategoryNatIso (eqToIso (show U ⋙ evR n =
          Ev n ⋙ Res n from rfl)) ≪≫ Functor.mapDerivedCategoryCompIso (Ev n) (Res n)
      have ht := liftSquare U.mapDerivedCategory (evR n).mapDerivedCategory
        (Ev n).mapDerivedCategory (Res n).mapDerivedCategory cmp a.hom
        (U.mapDerivedCategoryFactors.app P) ((Ev n).mapDerivedCategoryFactors.app P)
      convert ht using 1 <;>
        simp only [spSemilinearEvaluationIso, Iso.trans_hom, Iso.symm_hom,
          Functor.mapIso_hom, Iso.app_hom, Iso.app_inv] <;> rfl
    · intro RF eta hRF W epsilon pi n
      exact (pi n).naturality _



private theorem kFlatRepresentative (D : SpCoefficientTowersAbelian l E T)
    (C : @DerivedCategory (spCoefficientTowers l E T) _ _ D.hasDerived) :
    letI : HasSheafify (Scheme.ProEt.topology T) AddCommGrpCat.{max u (t + 1)} :=
      surjectiveTower_hasSheafify.{t, u} T
    letI : (Scheme.ProEt.topology T).WEqualsLocallyBijective
        AddCommGrpCat.{max u (t + 1)} := surjectiveTower_wEqualsLocallyBijective.{t, u} T
    letI := D.hasDerived
    letI := D.equivalenceAdditive
    letI := D.evaluationLimits
    letI := D.evaluationColimits
    letI : ∀ n : ℕ, (spCoefficientEvaluation l E T D.equivalence n).Additive :=
      fun n ↦ Functor.additive_of_preserves_binary_products
        (spCoefficientEvaluation l E T D.equivalence n)
    letI : EssentiallySmall.{max u (t + 1)} T.ProEt := essentiallySmallSelf.{u} _
    let B := spCoefficientCommRings l E T
    let Ev := spCoefficientEvaluation l E T D.equivalence
    ∃ (P : CochainComplex (spCoefficientTowers l E T) ℤ)
      (a : DerivedCategory.Q.obj P ≅ C),
      ∀ n, systemLevelKFlat.{t + 1, t, max u (t + 1)} B n
        (((Ev n).mapHomologicalComplex (.up ℤ)).obj P) := by
  let : HasSheafify (Scheme.ProEt.topology T) AddCommGrpCat.{max u (t + 1)} :=
    surjectiveTower_hasSheafify.{t, u} T
  let : (Scheme.ProEt.topology T).WEqualsLocallyBijective
      AddCommGrpCat.{max u (t + 1)} := surjectiveTower_wEqualsLocallyBijective.{t, u} T
  let := D.hasDerived
  let := D.equivalenceAdditive
  let := D.evaluationLimits
  let := D.evaluationColimits
  let : ∀ n : ℕ, (spCoefficientEvaluation l E T D.equivalence n).Additive :=
    fun n ↦ Functor.additive_of_preserves_binary_products
      (spCoefficientEvaluation l E T D.equivalence n)
  let : EssentiallySmall.{max u (t + 1)} T.ProEt := essentiallySmallSelf.{u} _
  let B := spCoefficientCommRings l E T
  let Ev := spCoefficientEvaluation l E T D.equivalence
  classical
  let M := DerivedCategory.Q.objPreimage C
  let F := D.equivalence.mapHomologicalComplex (.up ℤ)
  obtain ⟨L, f, hL, hf⟩ := strictRingSystem_kFlatResolution B (F.functor.obj M)
  let P := F.inverse.obj L
  let p : P ⟶ M := F.inverse.map f ≫ F.unitIso.inv.app M
  have : QuasiIso f := hf
  have : QuasiIso (F.inverse.map f) := by
    change QuasiIso ((D.equivalence.inverse.mapHomologicalComplex (.up ℤ)).map f)
    infer_instance
  have : QuasiIso p := by dsimp only [p]; infer_instance
  refine ⟨P, asIso (DerivedCategory.Q.map p) ≪≫
    DerivedCategory.Q.objObjPreimageIso C, ?_⟩
  intro n
  let ec := ((systemEvaluation B n).mapHomologicalComplex (.up ℤ)).mapIso
    (F.counitIso.app L)
  exact ⟨SheafOfModules.kFlat_iso_independent (B.obj (op n)) ec.symm (hL n).1,
    fun i ↦ SheafOfModules.flatOnSite_of_iso (B.obj (op n))
      ((HomologicalComplex.eval _ (.up ℤ) i).mapIso ec).symm ((hL n).2 i)⟩


/-- All clauses of the simultaneous model statement, expressed using one strict
coefficient-tower complex and the original normalized reductions.

`e n` is the localization comparison followed by evaluation of `a`. The ordinary
reduction `beta h` is the scalar-adjunction transpose of the strict chain transition
`q h`, defined by `strictSystemTransition`; `ordinaryReduction_eq` fixes its local
formula b tensor x maps to b times q(x).
The functor U is required to be precisely scalar restriction on every level, arrow
and section, so it cannot be an arbitrary functor into completed-ring towers.
The lift b is the image of a under this exact functor, with its localization
comparison. Its evaluation formula specifies the same e_n. The final clause is
compatibility with each projection in any total-derived-limit Roos presentation.

Source: blueprint, sk-lem-sp-tower.proof.md, preliminary coherent realization;
Stacks 06YS, 0G7E, 06YY, 0940--0941
(blueprint: lem-sp-semilinear-kflat-tower-model). -/
def HasSpSemilinearKFlatTowerModel (D : SpCoefficientTowersAbelian l E T)
    (C : @DerivedCategory (spCoefficientTowers l E T) _ _ D.hasDerived) : Prop :=
  letI : HasSheafify (Scheme.ProEt.topology T) AddCommGrpCat.{max u (t + 1)} :=
    surjectiveTower_hasSheafify.{t, u} T
  letI : (Scheme.ProEt.topology T).WEqualsLocallyBijective
      AddCommGrpCat.{max u (t + 1)} := surjectiveTower_wEqualsLocallyBijective.{t, u} T
  letI := D.hasDerived
  letI := D.equivalenceAdditive
  letI := D.evaluationLimits
  letI := D.evaluationColimits
  letI : ∀ n : ℕ, (spCoefficientEvaluation l E T D.equivalence n).Additive :=
    fun n ↦ Functor.additive_of_preserves_binary_products
      (spCoefficientEvaluation l E T D.equivalence n)
  letI : EssentiallySmall.{max u (t + 1)} T.ProEt := essentiallySmallSelf.{u} _
  let B := spCoefficientCommRings l E T
  let Ev := spCoefficientEvaluation l E T D.equivalence
  ∃ (P : CochainComplex (spCoefficientTowers l E T) ℤ)
    (a : DerivedCategory.Q.obj P ≅ C),
    let Qn := fun n : ℕ ↦ ((Ev n).mapHomologicalComplex (.up ℤ)).obj P
    let e := spSemilinearEvaluationIso l E T D C P a
    let beta := fun {m n : ℕ} (h : m ≤ n) ↦
      (NatTrans.mapHomologicalComplex (D.ordinaryReduction h) (.up ℤ)).app P
    let q := fun {m n : ℕ} (h : m ≤ n) ↦ spSemilinearChainTransition l E T D P h
    (∀ n : ℕ, systemLevelKFlat.{t + 1, t, max u (t + 1)} B n (Qn n)) ∧
    (∀ {m n : ℕ} (h : m ≤ n),
      DerivedCategory.Q.map (q h) ≫
          (systemRestriction B h).mapDerivedCategoryFactors.inv.app (Qn m) ≫
          (systemRestriction B h).mapDerivedCategory.map (e m).hom =
        (e n).hom ≫ ((systemDerivedTensorAdj D.scalar B h).homEquiv _ _)
          ((D.reduction h).app C)) ∧
    (∀ {m n : ℕ} (h : m ≤ n) (i : ℤ),
      systemTensorSectionFormula.{t + 1, t, max u (t + 1)}
        (J := Scheme.ProEt.topology T) (D.scalar (B.map (homOfLE h).op))
        ((Qn n).X i) ((Qn m).X i) ((beta h).f i) ((q h).f i)) ∧
    (∀ {m n : ℕ} (h : m ≤ n),
      IsIso ((D.scalar (B.map (homOfLE h).op)).model.ε.app (Qn n)) ∧
      (systemDerivedTensor D.scalar B h).map (e n).hom ≫ (D.reduction h).app C =
        (D.scalar (B.map (homOfLE h).op)).model.ε.app (Qn n) ≫
          DerivedCategory.Q.map (beta h) ≫ (e m).hom) ∧
    HasSpSemilinearCompletedLift l E T D C P a


set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Every derived semilinear coefficient tower has compatible flat-term K-flat
representatives, a strict completed-ring derived lift with the specified evaluations
and limit projections, and the original reduction maps on its tensor representatives.
No boundedness, normalization or flatness of the quotient maps is assumed.

Source: blueprint main-20261015, sk-lem-sp-tower.proof.md, preliminary realization;
Bhatt--Scholze, Definition 3.5.3; Stacks 06YS, 0G7E, 06YY and 0940--0941
(blueprint: lem-sp-semilinear-kflat-tower-model).

Proof:
1. Give N times T_proet the vertical topology of lem-weil-pbc-diagram-site-topology.
A module presheaf is a sheaf exactly when each vertical slice is a sheaf: glue on
the covering slice at n, and use separatedness on that same cover after every
horizontal restriction. Conversely extend matching families by horizontal maps.
Thus the ring sheaf with values B_n has precisely the given semilinear towers as
its modules, by det-sp-coefficient-towers-abelian.
2. Evaluation is the inverse image of a geometric morphism. Its right adjoint
places F at j >= n and the terminal sheaf below n. Maps into it are determined
by the map at n. Evaluation preserves finite limits and takes the ring to B_n.
Its module pullback is evaluation by the tensor unitor.
3. Represent C by a complex M of towers. Apply lem-pc-kflat-resolution once on
the diagram site, obtaining a flat-term K-flat P and a quasi-isomorphism P -> M.
4. Apply lem-weil-pbc-ringed-topos-kflat-pullback to the evaluation morphisms.
The evaluated Q_n are flat-term K-flat. Evaluation is exact, so P -> M remains
a quasi-isomorphism at every level.
5. Compose the localized resolution with Q(M) isomorphic to C to obtain a.
Its evaluations give e_n. The strict horizontal squares give the localized
transition equations. All longer maps are composites, with identities at equal
levels, by the strict-system identity and composition laws.
6. Restrict scalars through the completed coefficient projections. The cone
identities make horizontal maps R-linear. This gives U, exactly as normalized
above on every section and morphism. Kernels and sheafified cokernels are
unchanged, so U is exact. Apply D(U) to a and use the localization comparison
to obtain b. Exact evaluation and its compositors give the displayed evaluation
formula. Apply the total derived inverse limit of
lem-weil-pbc-ringed-strict-tower-homotopy-limit to b. The product-triangle first
arrow followed by its nth projection is a natural transformation pi_n;
naturality at b gives the last equation for each evaluation projection.
7. Transpose each horizontal chain transition by the normalized ordinary scalar
adjunction of lem-pur-system-scalar-model. On pure tensors beta sends b tensor x
to b times q(x). Its normalized derived transpose and
lem-pur-derived-change-of-rings identify its localization under the invertible
K-flat counit. Apply naturality of the original canonical reduction to a to
obtain the displayed reduction square. Equal levels give the tensor unitor.
This also retains all composite transitions, including nonflat coefficient maps. -/
theorem sp_semilinear_kflat_tower_model (D : SpCoefficientTowersAbelian l E T)
    (C : @DerivedCategory (spCoefficientTowers l E T) _ _ D.hasDerived) :
    HasSpSemilinearKFlatTowerModel l E T D C := by
  let : HasSheafify (Scheme.ProEt.topology T) AddCommGrpCat.{max u (t + 1)} :=
    surjectiveTower_hasSheafify.{t, u} T
  let : (Scheme.ProEt.topology T).WEqualsLocallyBijective
      AddCommGrpCat.{max u (t + 1)} := surjectiveTower_wEqualsLocallyBijective.{t, u} T
  let := D.hasDerived
  let := D.equivalenceAdditive
  let := D.evaluationLimits
  let := D.evaluationColimits
  let : ∀ n : ℕ, (spCoefficientEvaluation l E T D.equivalence n).Additive :=
    fun n ↦ Functor.additive_of_preserves_binary_products
      (spCoefficientEvaluation l E T D.equivalence n)
  let : EssentiallySmall.{max u (t + 1)} T.ProEt := essentiallySmallSelf.{u} _
  let B := spCoefficientCommRings l E T
  let Ev := spCoefficientEvaluation l E T D.equivalence
  classical
  have hP := kFlatRepresentative l E T D C
  let P := hP.choose
  let a := hP.choose_spec.choose
  have hflat := hP.choose_spec.choose_spec
  let en := spSemilinearEvaluationIso l E T D C P a
  let beta := fun {m n : ℕ} (h : m ≤ n) ↦
    (NatTrans.mapHomologicalComplex (D.ordinaryReduction h) (.up ℤ)).app P
  have red {m n : ℕ} (h : m ≤ n) :
      (systemDerivedTensor D.scalar B h).map (en n).hom ≫ (D.reduction h).app C =
        (D.scalar (B.map (homOfLE h).op)).model.ε.app
          (((Ev n).mapHomologicalComplex (.up ℤ)).obj P) ≫
          DerivedCategory.Q.map (beta h) ≫ (en m).hom := by
    have ht := transportReduction (systemDerivedTensor D.scalar B h) (D.reduction h) a.hom
      ((Ev n).mapDerivedCategoryFactors.app P)
      ((Ev m).mapDerivedCategoryFactors.app P)
      ((D.scalar _).model.ε.app _ ≫ DerivedCategory.Q.map (beta h))
      (by
        simpa only [Category.assoc, B, Ev, beta, Iso.app_hom, Iso.app_inv]
          using D.reduction_rep h P)
    convert ht using 1 <;> simp only [en, spSemilinearEvaluationIso,
      Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom, Category.assoc,
      B, Ev, Iso.app_inv]
  unfold HasSpSemilinearKFlatTowerModel
  dsimp only
  refine ⟨P, a, hflat, ?_, ?_, ?_, completedLift l E T D C P a⟩
  · intro m n h
    have hb : ((systemTensorAdj D.scalar B h).mapHomologicalComplex (.up ℤ)).homEquiv _ _
        (beta h) = spSemilinearChainTransition l E T D P h := by
      apply HomologicalComplex.hom_ext
      intro i
      unfold spSemilinearChainTransition
      change ((systemTensorAdj D.scalar B h).homEquiv _ _
        ((D.ordinaryReduction h).app (P.X i))) = _
      rw [D.ordinaryReduction_eq]
      exact Equiv.apply_symm_apply _ _
    have hr := (systemDerivedTensorAdj D.scalar B h).homEquiv_naturality_left_square
      (en n).hom ((D.reduction h).app C)
      ((D.scalar (B.map (homOfLE h).op)).model.ε.app
        (((Ev n).mapHomologicalComplex (.up ℤ)).obj P) ≫
          DerivedCategory.Q.map (beta h)) (en m).hom (by simpa only [Category.assoc] using red h)
    have ht := (D.scalar (B.map (homOfLE h).op)).transpose
      (((Ev n).mapHomologicalComplex (.up ℤ)).obj P)
      (((Ev m).mapHomologicalComplex (.up ℤ)).obj P) (beta h)
    dsimp only [systemDerivedTensorAdj] at hr
    erw [ht, hb] at hr
    simpa only [Category.assoc] using hr.symm
  · intro m n h i
    apply tensorSectionFormula_of_transpose
    rw [chainTransition_f]
    change (systemTensorAdj D.scalar B h).homEquiv _ _
      ((D.ordinaryReduction h).app (P.X i)) = _
    rw [D.ordinaryReduction_eq]
    exact Equiv.apply_symm_apply _ _
  · intro m n h
    exact ⟨(D.scalar _).model.computes _ (hflat n).1, red h⟩


end AlgebraicGeometry.ProEtale
