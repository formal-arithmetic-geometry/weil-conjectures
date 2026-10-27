/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group K7
-/
module

public import Sheaf.Paper.LisseCompletedSystemData
public import Sheaf.Paper.EtaleMonodromyRealizationData
import Sheaf.SixFunctors.IntegralLisseCoefficientQuotients
import Sheaf.NumberTheory.Padics.IntegersProfiniteTower
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Proetale
import WeilConjectures.SixFunctors.ProEtale.Comparison.ForgetUpperStar
import Mathlib.CategoryTheory.Limits.Types.Limits
import Sheaf.Algebra.Homology.SheafRingCoefficientOrdinaryAdjunction
import WeilConjectures.SixFunctors.ProEtale.Comparison.Linear

/-! # Recovery from an isomorphic normalized reduction tower

Source: Bhatt--Scholze, Proposition 6.8.4(1),(4), pp. 59--60.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits Opposite Topology
open AlgebraicGeometry.ProEtale
namespace AlgebraicGeometry.Scheme
open ProEtale.CompletedLisse

private abbrev restriction {X : Scheme.{u}}
    {R S : Sheaf (ProEt.topology X) CommRingCat.{u + 1}} (f : R ⟶ S) :=
  SheafOfModules.restrictScalars.{u + 1}
    ((sheafCompose _ (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map f)

private noncomputable def restriction_comp {X : Scheme.{u}}
    {R S T : Sheaf (ProEt.topology X) CommRingCat.{u + 1}}
    (f : R ⟶ S) (g : S ⟶ T) (h : R ⟶ T) (hh : h = f ≫ g) :
    restriction g ⋙ restriction f ≅ restriction h :=
  NatIso.ofComponents (fun M ↦ (SheafOfModules.fullyFaithfulForget _).preimageIso
    (PresheafOfModules.isoMk (fun U ↦
      (ModuleCat.restrictScalarsComp'App (f.hom.app U).hom (g.hom.app U).hom
        (h.hom.app U).hom (congrArg (fun k ↦ (k.hom.app U).hom) hh)
        (M.val.obj U)).symm) (by intros; ext x; rfl)))
    (by intros; ext U x; rfl)

private noncomputable def restriction_id {X : Scheme.{u}}
    (R : Sheaf (ProEt.topology X) CommRingCat.{u + 1}) :
    restriction (𝟙 R) ≅ 𝟭 _ := by
  let D : Sheaf (ProEt.topology X) CommRingCat.{u + 1} ⥤
      Sheaf (ProEt.topology X) RingCat.{u + 1} :=
    sheafCompose (ProEt.topology X) (forget₂ CommRingCat RingCat)
  refine NatIso.ofComponents (fun M ↦
    (SheafOfModules.fullyFaithfulForget _).preimageIso
      (PresheafOfModules.isoMk (fun U ↦ ?_) ?_)) ?_
  · exact ModuleCat.restrictScalarsId'App
      (((D.map (𝟙 R)).hom.app U).hom)
      (congrArg (fun k ↦ (k.hom.app U).hom) (D.map_id R)) (M.val.obj U)
  · intros
    ext x
    rfl
  · intros
    ext U x
    rfl

private theorem change_after_iso {X : Scheme.{u}}
    {R S T : Sheaf (ProEt.topology X) CommRingCat.{u + 1}}
    (c : R ≅ S) (f : R ⟶ T) :
    Nonempty (restriction c.hom ⋙ completedAdicChange X f ≅
      completedAdicChange X (c.inv ≫ f)) := by
  let F := restriction c.hom
  let G := restriction c.inv
  let e :=
    CategoryTheory.Equivalence.mk F G
      ((restriction_id S).symm ≪≫
        (restriction_comp c.inv c.hom (𝟙 S) c.inv_hom_id.symm).symm)
      (restriction_comp c.hom c.inv (𝟙 R) c.hom_inv_id.symm ≪≫ restriction_id R)
  have adj (a : R ⟶ T) : completedAdicChange X a ⊣ restriction a := by
    let h := (SheafOfModules.sheafRingCoefficientOrdinaryAdjunction a).choose_spec.choose_spec
    exact (h (completedAdicChange X a) (completedAdicChangeData X a).choose_spec.choose
      (fun k ↦ (completedAdicChangeData X a).choose_spec.choose_spec.choose k)).choose
  have adj' : completedAdicChange X (c.inv ≫ f) ⊣ restriction (c.inv ≫ f) := by
    let h := (SheafOfModules.sheafRingCoefficientOrdinaryAdjunction
      (c.inv ≫ f)).choose_spec.choose_spec
    exact (h (completedAdicChange X (c.inv ≫ f))
      (completedAdicChangeData X (c.inv ≫ f)).choose_spec.choose
      (fun k ↦ (completedAdicChangeData X (c.inv ≫ f)).choose_spec.choose_spec.choose k)).choose
  exact ⟨((e.toAdjunction.comp (adj f)).ofNatIsoRight
    (restriction_comp c.inv f (c.inv ≫ f) rfl)).leftAdjointUniq adj'⟩

private theorem constant_linear_lift (l : ℕ) [Fact l.Prime]
    (E : Type (u + 1)) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (X : Scheme.{u}) (M N : SfIntegralModules l E X)
    (Q : ℕ → Sheaf (ProEt.topology X) AddCommGrpCat.{u + 1})
    (q : ∀ n, (SheafOfModules.toSheaf _).obj N ⟶ Q n)
    (sep : ∀ (U : X.ProEtᵒᵖ) (x y : N.val.obj U),
      (∀ n, (q n).hom.app U x = (q n).hom.app U y) → x = y)
    (kill : ∀ (n : ℕ) (U : X.ProEtᵒᵖ) (x : N.val.obj U),
      (q n).hom.app U
        (lisseIntegerConstantSized l E X U
          (Padic.coefficientExtensionUniformizer l E ^ (n + 1)) • x) = 0)
    (f : (SheafOfModules.toSheaf _).obj M ⟶ (SheafOfModules.toSheaf _).obj N)
    (lin : ∀ (U : X.ProEtᵒᵖ) (a : Padic.coefficientExtensionIntegers l E)
      (x : M.val.obj U), f.hom.app U (lisseIntegerConstantSized l E X U a • x) =
        lisseIntegerConstantSized l E X U a • (show N.val.obj U from f.hom.app U x)) :
    ∃ g : M ⟶ N, (SheafOfModules.toSheaf _).map g = f := by
  classical
  let := spectralNorm.normedField ℚ_[l] E
  let A := Padic.coefficientExtensionIntegers l E
  have scalar (U : X.ProEtᵒᵖ) (a : (lisseIntegerSheafSized l E X).obj.obj U)
      (x : M.val.obj U) : f.hom.app U (a • x) = a • (show N.val.obj U from f.hom.app U x) := by
    apply sep U
    intro n
    let I := Padic.coefficientExtensionIdeal l E (n + 1)
    obtain ⟨e, he, heHome⟩ :=
      (Padic.coefficientExtension_integers_profinite_tower.{u + 1, u + 1} l E).1
    have hc : @Continuous _ _ (inferInstance : TopologicalSpace A) ⊥
        (Ideal.Quotient.mk I) := by
      let : ∀ k : ℕ, TopologicalSpace (Padic.coefficientExtensionRing l E (k + 1)) :=
        fun _ ↦ ⊥
      exact ((continuous_apply n).comp
        (continuous_subtype_val.comp heHome.continuous)).congr (fun z ↦ he z n)
    let r : U.unop.left → A ⧸ I := fun z ↦ Ideal.Quotient.mk I (a.down z)
    have hr : @Continuous _ _ _ ⊥ r := by
      apply continuous_def.mpr
      intro Z hZ
      exact a.down.continuous.isOpen_preimage _ (continuous_def.mp hc Z hZ)
    let V (z : U.unop.left) : U.unop.left.Opens :=
      ⟨r ⁻¹' {r z}, continuous_def.mp hr _ trivial⟩
    let S := Presheaf.equalizerSieve
      ((q n).hom.app U (f.hom.app U (a • x)))
      ((q n).hom.app U (a • (show N.val.obj U from f.hom.app U x)))
    have hS : S ∈ ProEt.topology X U.unop := by
      apply ProEt.mem_topology_of_openImmersion _ (fun z ↦ (V z).ι)
      · intro z
        exact ⟨z, ⟨⟨z, rfl⟩, rfl⟩⟩
      · intro z
        let i := ProEt.ofOpenImmersionHom U.unop (V z).ι
        let W := op (ProEt.ofOpenImmersion U.unop (V z).ι)
        let b := (lisseIntegerSheafSized l E X).obj.map i.op a
        let c := lisseIntegerConstantSized l E X W (a.down z)
        have hbc : (integralLisseReduction l E X n).hom.app W (b - c) = 0 := by
          apply ULift.ext
          apply ContinuousMap.ext
          intro y
          change Ideal.Quotient.mk I (a.down y.val - a.down z) = 0
          rw [map_sub, sub_eq_zero]
          exact y.property
        have hbc' :
            (integralLisseRingMap l E X
              ((sheafCompose _ (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
                (integralLisseReduction l E X n))).val.app W (b - c) = 0 := by
          change (integralLisseReduction l E X n).hom.app W (b - c) * 1 = 0
          simpa only [mul_one] using hbc
        obtain ⟨t, ht⟩ :=
          (integralLisseCoefficient_sectionwise l E X n W).2 (b - c) |>.mp hbc'
        change (lisseIntegerSheafSized l E X).obj.obj W at t
        change lisseIntegerConstantSized l E X W
          (Padic.coefficientExtensionUniformizer l E ^ (n + 1)) * t = b - c at ht
        have hb : b = c + lisseIntegerConstantSized l E X W
            (Padic.coefficientExtensionUniformizer l E ^ (n + 1)) * t := by
          rw [ht, add_sub_cancel]
        change (Q n).obj.map i.op ((q n).hom.app U (f.hom.app U (a • x))) =
          (Q n).obj.map i.op ((q n).hom.app U (a • (show N.val.obj U from f.hom.app U x)))
        rw [← NatTrans.naturality_apply, ← NatTrans.naturality_apply,
          ← NatTrans.naturality_apply]
        change (q n).hom.app W (f.hom.app W (M.val.map i.op (a • x))) =
          (q n).hom.app W (N.val.map i.op (a • (show N.val.obj U from f.hom.app U x)))
        rw [M.val.map_smul, N.val.map_smul]
        have hnat : N.val.map i.op (f.hom.app U x) =
            f.hom.app W (M.val.map i.op x) :=
          (ConcreteCategory.congr_hom (f.hom.naturality i.op) x).symm
        rw [hnat]
        change (q n).hom.app W (f.hom.app W (b • M.val.map i.op x)) =
          (q n).hom.app W (b • (show N.val.obj W from f.hom.app W (M.val.map i.op x)))
        rw [hb, add_smul, add_smul, mul_smul, mul_smul, map_add, map_add, map_add,
          lin W (a.down z), lin W (Padic.coefficientExtensionUniformizer l E ^ (n + 1)),
          kill, kill]
    apply ((isSheaf_iff_isSheaf_of_type _ _).mp
      ((sheafCompose (ProEt.topology X)
        (CategoryTheory.forget AddCommGrpCat.{u + 1})).obj (Q n)).property S hS).isSeparatedFor.ext
    intro Y i hi
    exact hi
  let g : M ⟶ N :=
    ⟨{ app := fun U ↦ ModuleCat.ofHom
        { toFun := f.hom.app U
          map_add' := map_add _
          map_smul' := scalar U }
       naturality := fun i ↦ by
         ext x
         exact ConcreteCategory.congr_hom (f.hom.naturality i) x }⟩
  exact ⟨g, rfl⟩

private theorem ab_limit_sections_ext {X : Scheme.{u}}
    {D : ℕᵒᵖ ⥤ Sheaf (ProEt.topology X) AddCommGrpCat.{u + 1}}
    (c : Cone D) (hc : IsLimit c) (U : X.ProEtᵒᵖ)
    (x y : c.pt.obj.obj U)
    (h : ∀ n : ℕ, (c.π.app (op n)).hom.app U x =
      (c.π.app (op n)).hom.app U y) : x = y := by
  let ev := sheafToPresheaf (ProEt.topology X) AddCommGrpCat.{u + 1} ⋙
    (CategoryTheory.evaluation _ _).obj U ⋙ CategoryTheory.forget AddCommGrpCat.{u + 1}
  apply (Types.isLimitEquivSections (isLimitOfPreserves ev hc)).injective
  apply Subtype.ext
  funext n
  exact h n.unop

/-- Isomorphic integral reduction towers give the same rational module under the
specified completed comparison and monodromy normalization.

Source: Bhatt--Scholze, Proposition 6.8.4(1),(4), pp. 59--60
(blueprint: lem-a1-completed-normalization-recovery).

Proof: Forget to abelian sheaves and transport the given diagram isomorphism by the
etale-to-pro-etale inverse-image functor. Its canonical comparison with forgetting
modules identifies the resulting diagram with the one used by the normalization.
The completed comparison's unit and completion-limit equations identify the underlying
abelian sheaf of M with the limit of its reduction diagram. The normalization's isLimit
identifies its integral model with the limit of the isomorphic diagram. Uniqueness of
limits gives an isomorphism commuting with all reduction projections.
This isomorphism respects constant integral scalars, by reduction_scalar and scalar
and the joint monicity of the limit projections. It respects every continuous integral
coefficient as well: modulo any fixed uniformizer power a continuous coefficient is
locally constant, so the scalar identity holds locally by the constant identity, and
then globally by the sheaf axiom. Joint monicity over all levels gives the identity
before reduction. The inverse has the same property. Thus the isomorphism is one of
modules over the continuous integer sheaf, after transporting M along coefficientIso.
Apply actual change of rings to the rational coefficient sheaf. Composition of scalar
extension identifies the result with completedAdicChange along coefficientIso.inv
followed by the integral-to-field map. Finally compose with the normalization's rational
isomorphism. All steps also apply to the zero module. -/
theorem completed_normalization_recovery (l : ℕ) [Fact l.Prime] (P : Base.{u} l)
    (p : SfMonodromyPoint P.X) (C : Comparison l P)
    (J : SfMonodromyRealization l P.E p) (M : Integral l P)
    (V : SfContinuousRepresentations l P.E p) (B : SfInvariantLattice l P.E V)
    (d : (C.equivalence.functor.obj M).obj.obj ≅ (J.normalization V B).etale) :
    Nonempty (J.functor.obj V ≅
      (completedAdicChange P.X
        (C.coefficientIso.inv ≫ lisseIntegerToFieldSized l P.E P.X)).obj M.obj) := by
  classical
  let R := Integers l P
  let F := (C.equivalence.functor.obj M).obj.obj
  let N := J.normalization V B
  let A := (restriction C.coefficientIso.hom).obj M.obj
  let comp := ProEtale.comparisonUpperStar (ModuleCat.{u + 1} R) P.X
  let forgetE := sheafCompose P.X.smallEtaleTopology
    (forget₂ (ModuleCat.{u + 1} R) AddCommGrpCat.{u + 1})
  let forgetP := sheafCompose (ProEt.topology P.X)
    (forget₂ (ModuleCat.{u + 1} R) AddCommGrpCat.{u + 1})
  let compA := ProEtale.comparisonUpperStar AddCommGrpCat.{u + 1} P.X
  let e := ProEtale.sheafComposeForget₂CompComparisonUpperStarIso R P.X
  let w : proEtaleDiagram l P (C.equivalence.functor.obj M) ≅
      sfMonodromyAbDiagram l P.E P.X N.etale :=
    Functor.associator F forgetE compA ≪≫
      Functor.isoWhiskerLeft F e ≪≫ (Functor.associator F comp forgetP).symm ≪≫
      Functor.isoWhiskerRight (Functor.isoWhiskerRight d comp) forgetP
  let cm := Cone.mk _ (C.reduction M)
  have hm : IsLimit cm := by
    let z := C.equivalence.functor.obj M
    let ei : cm ≅ Cone.mk _ (C.completion z) :=
      Cone.ext ((integralForget l P).mapIso
        ((ObjectProperty.ι _).mapIso (C.equivalence.unitIso.app M)))
        (fun n ↦ (C.unit_projection M n.unop).symm)
    exact (C.completion_limit z).ofIsoLimit ei.symm
  let cn := Cone.mk _ N.projection
  let f := hm.conePointsIsoOfNatIso N.isLimit w
  have hf (n : ℕ) : f.inv ≫ (C.reduction M).app (op n) =
      N.projection.app (op n) ≫ w.inv.app (op n) :=
    hm.conePointsIsoOfNatIso_inv_comp N.isLimit w (op n)
  have sep (U : P.X.ProEtᵒᵖ) (x y : A.val.obj U)
      (h : ∀ n : ℕ, ((C.reduction M).app (op n)).hom.app U x =
        ((C.reduction M).app (op n)).hom.app U y) : x = y :=
    ab_limit_sections_ext cm hm U x y h
  have kill (n : ℕ) (U : P.X.ProEtᵒᵖ) (x : A.val.obj U) :
      ((C.reduction M).app (op n)).hom.app U
        (lisseIntegerConstantSized l P.E P.X U
          (Padic.coefficientExtensionUniformizer l P.E ^ (n + 1)) • x) = 0 := by
    have h := (C.reduction_quotient M n).choose
    have hh := ConcreteCategory.congr_hom (congrArg (fun a ↦ a.hom.app U) h)
      (show ((integralForget l P).obj M.obj).obj.obj U from x)
    exact hh
  have scalar (U : P.X.ProEtᵒᵖ) (a : R) (x : N.integral.val.obj U) :
      f.inv.hom.app U (lisseIntegerConstantSized l P.E P.X U a • x) =
        lisseIntegerConstantSized l P.E P.X U a •
          (show A.val.obj U from f.inv.hom.app U x) := by
    apply sep U
    intro n
    have hh := ConcreteCategory.congr_hom
      (congrArg (fun k ↦ k.hom.app U) (hf n))
    change ∀ y, ((C.reduction M).app (op n)).hom.app U (f.inv.hom.app U y) =
      (w.inv.app (op n)).hom.app U ((N.projection.app (op n)).hom.app U y) at hh
    have hr := ConcreteCategory.congr_hom
      (congrArg (fun k ↦ k.hom.app U) (C.reduction_scalar M n a))
        (f.inv.hom.app U x)
    change ((C.reduction M).app (op n)).hom.app U
      (f.inv.hom.app U (_ • x)) = _
    have hr' : ((C.reduction M).app (op n)).hom.app U
        (lisseIntegerConstantSized l P.E P.X U a •
          (show A.val.obj U from f.inv.hom.app U x)) =
      (compA.map (forgetE.map (a • 𝟙 (F.obj (op n))))).hom.app U
        (((C.reduction M).app (op n)).hom.app U (f.inv.hom.app U x)) := hr
    erw [hh, N.scalar, hr', hh]
    let t := comp.map (d.inv.app (op n))
    have hw : w.inv.app (op n) = forgetP.map t ≫ e.inv.app (F.obj (op n)) := by
      change 𝟙 _ ≫ forgetP.map t ≫ e.inv.app (F.obj (op n)) = _
      exact Category.id_comp _
    have he := e.inv.naturality (a • 𝟙 (F.obj (op n)))
    have hcomp : comp.map (a • 𝟙 (F.obj (op n))) = a • 𝟙 _ := by simp
    change forgetP.map (comp.map (a • 𝟙 (F.obj (op n)))) ≫ _ =
      _ ≫ compA.map (forgetE.map (a • 𝟙 (F.obj (op n)))) at he
    rw [hcomp] at he
    have ht : (a • 𝟙 (comp.obj (N.etale.obj (op n)))) ≫ t =
        t ≫ (a • 𝟙 (comp.obj (F.obj (op n)))) := by
      simp only [Linear.smul_comp, Category.id_comp, Linear.comp_smul]
      exact (Category.comp_id _).symm
    have hh' : forgetP.map (a • 𝟙 (comp.obj (N.etale.obj (op n)))) ≫
        w.inv.app (op n) = w.inv.app (op n) ≫
          compA.map (forgetE.map (a • 𝟙 (F.obj (op n)))) := by
      rw [hw, ← Category.assoc, ← forgetP.map_comp, ht, forgetP.map_comp,
        Category.assoc, he, Category.assoc]
    exact ConcreteCategory.congr_hom
      (congrArg (fun k ↦ k.hom.app U) hh')
        ((N.projection.app (op n)).hom.app U x)
  obtain ⟨g, hg⟩ := constant_linear_lift l P.E P.X N.integral A
    (fun n ↦ (proEtaleDiagram l P (C.equivalence.functor.obj M)).obj (op n))
    (fun n ↦ (C.reduction M).app (op n)) sep kill f.inv scalar
  have : IsIso ((SheafOfModules.toSheaf _).map g) := by rw [hg]; infer_instance
  have : IsIso g := isIso_of_reflects_iso g (SheafOfModules.toSheaf _)
  obtain ⟨c⟩ := change_after_iso C.coefficientIso (lisseIntegerToFieldSized l P.E P.X)
  let ch := completedAdicChange P.X (lisseIntegerToFieldSized l P.E P.X)
  have hch (L : SfIntegralModules l P.E P.X) :
      ch.obj L = SheafOfModules.changeOfRings (lisseIntegerToFieldSized l P.E P.X) L :=
    (completedAdicChangeData P.X (lisseIntegerToFieldSized l P.E P.X)).choose_spec.choose L
  exact ⟨N.rational ≪≫ eqToIso (hch N.integral).symm ≪≫
    ch.mapIso (asIso g) ≪≫ c.app M.obj⟩

end AlgebraicGeometry.Scheme
