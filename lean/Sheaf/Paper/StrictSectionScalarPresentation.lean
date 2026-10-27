/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F2
-/
module
public import Sheaf.Paper.StrictCompletionRestrictionData
import all Sheaf.Paper.PrincipalReductionConeCalculus
import all Sheaf.Paper.CompletionTriangleComparison
import all Sheaf.Algebra.Homology.RoosConeCalculus
import all Sheaf.CategoryTheory.InternalSectionTensorComparison
import WeilConjectures.AlgebraicGeometry.ProEtale.RepleteAddCommGrp
import WeilConjectures.CategoryTheory.ModuleObjects.SequentialLimitEpi

/-! # A strict scalar presentation on section modules -/
@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open scoped CategoryTheory.Obj
open CategoryTheory.InternalAbelianSheafModule
open AlgebraicGeometry.ProEtale
namespace AlgebraicGeometry.ProEtale.StrictCompletionRestriction
section
universe a b w
variable {A : Type a} [Category.{b} A] [Abelian A] [HasCountableProducts A]
  [HasDerivedCategory.{w} A] [CountableAB4Star A]
set_option maxHeartbeats 400000 in
-- Assembly of the scalar tower and both localized descents has many dependent fields.
-- Elaborating the concrete tensor and localization interfaces needs extra heartbeats.
private theorem scalarPresentation (r : End (𝟭 A)) :
    ∃ S : Presentation A, S.scalar = r := by
  let τ (n : ℕ) : 𝟭 (CochainComplex A ℤ) ⟶ 𝟭 _ :=
    NatTrans.mapHomologicalComplex (r ^ (n + 1)) (.up ℤ)
  let a : 𝟭 (CochainComplex A ℤ) ⟶ 𝟭 _ := NatTrans.mapHomologicalComplex r (.up ℤ)
  have hs (n : ℕ) (M : CochainComplex A ℤ) :
      (τ (n + 1)).app M = a.app M ≫ (τ n).app M := by
    ext q
    simp only [τ, a, NatTrans.mapHomologicalComplex_app_f, HomologicalComplex.comp_f,
      pow_succ, End.mul_def, NatTrans.comp_app]
  let D (n : ℕ) := AlgebraicGeometry.ProEtale.strictCone (τ n)
  let t (n : ℕ) : D (n + 1) ⟶ D n := strictConeMap (τ (n + 1)) (τ n) a (hs n)
  let j (n : ℕ) : 𝟭 _ ⟶ D n := strictConeUnit (τ n)
  have hjt (n : ℕ) (M : CochainComplex A ℤ) :
      (j (n + 1)).app M ≫ (t n).app M = (j n).app M :=
    strictConeUnit_map _ _ _ _ M
  let tower := CompletionTriangle.TowerCalculus.functor D t
  let aug : 𝟭 (CochainComplex A ℤ) ⟶ tower ⋙ roosF :=
    { app := fun M ↦ RoosConeCalculus.augmentation
        (CompletionTriangle.TowerCalculus.principalCone D t j hjt M)
      naturality := by
        intro M N f
        symm
        apply RoosConeCalculus.augmentation_natural (tower.map f)
          (CompletionTriangle.TowerCalculus.principalCone D t j hjt M)
          (CompletionTriangle.TowerCalculus.principalCone D t j hjt N) f
        intro n
        ext q
        exact congrArg (fun g ↦ g.f q) ((j n).naturality f).symm }
  let Q := DerivedCategory.Q (C := A)
  let W := HomologicalComplex.quasiIso A (.up ℤ)
  have hD (n : ℕ) : W.IsInvertedBy (D n ⋙ Q) := by
    intro M N f hf
    have := strictCone_quasiIso (τ n) f hf
    change IsIso (Q.map ((D n).map f))
    infer_instance
  let R (n : ℕ) := Localization.lift (D n ⋙ Q) (hD n) Q
  let κ (n : ℕ) : Q ⋙ R n ≅ D n ⋙ Q := Localization.fac (D n ⋙ Q) (hD n) Q
  let step (n : ℕ) : R (n + 1) ⟶ R n :=
    Localization.liftNatTrans Q W (D (n + 1) ⋙ Q) (D n ⋙ Q) (R (n + 1)) (R n)
      (Functor.whiskerRight (t n) Q)
  let unit (n : ℕ) : 𝟭 (DerivedCategory A) ⟶ R n :=
    Localization.liftNatTrans Q W Q (D n ⋙ Q) (𝟭 _) (R n)
      (Functor.whiskerRight (j n) Q)
  have hG : W.IsInvertedBy (tower ⋙ roosF ⋙ Q) := by
    intro M N f hf
    have hq : QuasiIso (roosF.map (tower.map f)) :=
      RoosConeCalculus.roos_quasiIso (tower.map f)
        (RoosConeCalculus.product_quasiIso (tower.map f)
          (fun n ↦ strictCone_quasiIso (τ n) f hf))
    change IsIso (Q.map (roosF.map (tower.map f)))
    infer_instance
  let F := Localization.lift (tower ⋙ roosF ⋙ Q) hG Q
  let ε : Q ⋙ F ≅ tower ⋙ roosF ⋙ Q := Localization.fac _ hG Q
  let c : 𝟭 (DerivedCategory A) ⟶ F :=
    Localization.liftNatTrans Q W Q (tower ⋙ roosF ⋙ Q) (𝟭 _) F
      (Functor.whiskerRight aug Q)
  refine ⟨{
    scalar := r
    tower := tower
    cone := fun _ _ ↦ rfl
    coordinates := fun M n q ↦ principalConeCoordinates ((τ n).app M) q
    coordinates_eq := by
      intro M n q
      simp only [eqToIso_refl, Iso.refl_trans]
      rfl
    diagonal := fun f n q ↦ coneMap_coordinates ((τ n).app _) ((τ n).app _)
      f f ((τ n).naturality f).symm q
    transition := ?_
    augmentation := aug
    augmentation_zero := ?_
    augmentation_level := ?_
    reduction := R
    reduction_descent := κ
    reduction_step := step
    reduction_unit := unit
    reduction_step_descent := ?_
    reduction_unit_descent := ?_
    completion := F
    unit := c
    descent := ε
    unit_descent := ?_ }, rfl⟩
  · intro M n q
    rw [CompletionTriangle.TowerCalculus.tower_step]
    exact coneMap_coordinates _ _ (a.app M) (𝟙 M) (Category.comp_id _ |>.trans (hs n M)) q
  · intro M p
    simpa only [RoosConeCalculus.ucoord_χ] using
      RoosConeCalculus.augment_u
        (CompletionTriangle.TowerCalculus.principalCone D t j hjt M) (p + 1) p (by omega)
  · intro M n p
    have hh := (RoosConeCalculus.augment_coordinates
      (CompletionTriangle.TowerCalculus.principalCone D t j hjt M) (p + 1)).1
    simp only [RoosConeCalculus.v, roosProj_f] at hh
    erw [reassoc_of% hh]
    have hπ := congrArg (fun f ↦ f.f (p + 1)) (Pi.lift_π
      (fun n ↦ (CompletionTriangle.TowerCalculus.principalCone D t j hjt M).π.app (op n)) n)
    exact ((Category.assoc _ _ _).symm.trans
      (congrArg (fun f ↦ f ≫ (principalConeCoordinates ((τ n).app M) (p + 1)).hom) hπ)).trans
        (coneInr_coordinates _ _)
  · intro n M
    dsimp only [step]
    rw [Localization.liftNatTrans_app]
    change ((κ (n + 1)).hom.app M ≫ Q.map ((t n).app M) ≫ (κ n).inv.app M) ≫
      (κ n).hom.app M = _
    simp only [Category.assoc, Iso.inv_hom_id_app]
    rw [CompletionTriangle.TowerCalculus.tower_step]
    exact (Category.assoc _ _ _).symm.trans (Category.comp_id _)
  · intro n M
    dsimp only [unit]
    rw [Localization.liftNatTrans_app]
    simp only [Functor.whiskerRight_app]
    change ((𝟙 _) ≫ Q.map ((j n).app M) ≫ (κ n).inv.app M) ≫ (κ n).hom.app M = _
    simp only [Category.id_comp, Category.assoc, Iso.inv_hom_id_app]
    refine (Category.comp_id (Q.map ((j n).app M))).trans ?_
    apply congrArg (fun k ↦ Q.map k)
    ext q
    obtain ⟨p, hp⟩ := (Equiv.addRight (1 : ℤ)).surjective q
    change p + 1 = q at hp
    subst q
    symm
    rw [HomologicalComplex.comp_f, roosEval_f, ← Category.assoc, ← Category.assoc,
      roosAugment_χ]
    erw [biprod.lift_snd, ← HomologicalComplex.comp_f, Pi.lift_π]
    rfl
  · intro M
    dsimp only [c]
    rw [Localization.liftNatTrans_app]
    change ((𝟙 _) ≫ Q.map (aug.app M) ≫ ε.inv.app M) ≫ ε.hom.app M = _
    simp only [Category.id_comp, Category.assoc, Iso.inv_hom_id_app]
    exact Category.comp_id _
end

section
universe a b c d
variable {A : Type a} [Category.{b} A] {B : Type c} [Category.{d} B]
private def transportScalar (e : A ≌ B) (r : End (𝟭 A)) : End (𝟭 B) :=
  e.counitIso.inv ≫ Functor.whiskerRight (Functor.whiskerLeft e.inverse r) e.functor ≫
    e.counitIso.hom
private theorem transportScalar_app (e : A ≌ B) (r : End (𝟭 A)) (M : A) :
    e.functor.map (r.app M) = (transportScalar e r).app (e.functor.obj M) := by
  dsimp only [transportScalar, NatTrans.comp_app, Functor.whiskerRight_app,
    Functor.whiskerLeft_app]
  have hn := congrArg (fun f ↦ e.functor.map f) (r.naturality (e.unitIso.inv.app M))
  simp only [Functor.id_map, e.functor.map_comp] at hn
  have hi : e.counitIso.hom.app (e.functor.obj M) =
      e.functor.map (e.unitIso.inv.app M) := by
    apply (cancel_epi (e.counitIso.inv.app (e.functor.obj M))).mp
    simp only [Iso.inv_hom_id_app]
    exact (e.counitIso_functor_comp M).symm
  dsimp only [Functor.id_obj, Functor.comp_obj] at hn
  symm
  calc
    _ = e.counitIso.inv.app (e.functor.obj M) ≫
        (e.functor.map (r.app (e.inverse.obj (e.functor.obj M))) ≫
          e.functor.map (e.unitIso.inv.app M)) := by
      simp only [hi]
    _ = e.counitIso.inv.app (e.functor.obj M) ≫
        (e.functor.map (e.unitIso.inv.app M) ≫ e.functor.map (r.app M)) :=
      congrArg (fun k ↦ e.counitIso.inv.app (e.functor.obj M) ≫ k) hn.symm
    _ = _ := by rw [← Category.assoc, ← hi, Iso.inv_hom_id_app, Category.id_comp]

end

section
universe u
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (X : Scheme.{u})
set_option maxHeartbeats 400000 in
-- Assembly of the scalar tower and both localized descents has many dependent fields.
-- Elaborating the concrete tensor and localization interfaces needs extra heartbeats.
private theorem section_scalar_value
    (d : End (Mod.regular (DerivedNakayama.integerRing l E)))
    (M : AdicCompletion.Modules l E X) (U : X.ProEtᵒᵖ)
    (x : ((ModuleObjectRingedComparison.equivalence
      (DerivedNakayama.integerRing l E) X).functor.obj M).val.obj U) :
    (((ModuleObjectRingedComparison.equivalence (DerivedNakayama.integerRing l E) X).functor.map
      ((DerivedNakayama.scalarOnModules l E X d).app M)).val.app U) x =
      sectionScalarValue l E X d U • x := by
  let J := Scheme.ProEt.topology X
  let R := condensedRingObj (DerivedNakayama.integerRing l E) X
  let : MonObj R := (upperStarFromPoint X).monObjObj (DerivedNakayama.integerRing l E)
  let dX := (DerivedNakayama.regularPullbackIso l E X).inv ≫
    (DerivedNakayama.pullback l E X).map d ≫
      (DerivedNakayama.regularPullbackIso l E X).hom
  have hi : (((sectionModuleEquivalence J R).functor.map (λ_ M).inv).val.app U) x =
      comparison_internalTmul J R (𝟙_ _) M U (1 : (sectionRingSheaf J R).obj.obj U) x := by
    let eUnit :=  (sectionModuleEquivalence J R).functor.mapIso (λ_ M)
    have hUnit : Function.Injective (fun z ↦ (eUnit.hom.val.app U) z) := by
      intro z z' h
      have hh := congrArg (fun z ↦ (eUnit.inv.val.app U) z) h
      change ((eUnit.hom ≫ eUnit.inv).val.app U) z =
        ((eUnit.hom ≫ eUnit.inv).val.app U) z' at hh
      rw [eUnit.hom_inv_id] at hh
      exact hh
    apply hUnit
    change (((sectionModuleEquivalence J R).functor.map (λ_ M).inv ≫
      (sectionModuleEquivalence J R).functor.map (λ_ M).hom).val.app U) x = _
    rw [← Functor.map_comp, Iso.inv_hom_id]
    change x = _
    exact (comparison_internalTmul_leftUnitor J R M U
      (1 : (sectionRingSheaf J R).obj.obj U) x |>.trans (one_smul _ _)).symm
  have ht : (((sectionModuleEquivalence J R).functor.map (dX ▷ M)).val.app U)
      (comparison_internalTmul J R (𝟙_ _) M U (1 : (sectionRingSheaf J R).obj.obj U) x) =
      comparison_internalTmul J R (𝟙_ _) M U
        ((dX.hom.hom.app U) (1 : (sectionRingSheaf J R).obj.obj U)) x := by
    have hh := comparison_internalTmul_natural J R dX (𝟙 M) U
      (1 : (sectionRingSheaf J R).obj.obj U) x
    rw [MonoidalCategory.tensorHom_id] at hh
    exact hh
  change (((sectionModuleEquivalence J R).functor.map
    ((λ_ M).inv ≫ dX ▷ M ≫ (λ_ M).hom)).val.app U) x = _
  rw [Functor.map_comp, Functor.map_comp]
  change (((sectionModuleEquivalence J R).functor.map (λ_ M).hom).val.app U)
    ((((sectionModuleEquivalence J R).functor.map (dX ▷ M)).val.app U)
      ((((sectionModuleEquivalence J R).functor.map (λ_ M).inv).val.app U) x)) = _
  rw [hi, ht]
  exact comparison_internalTmul_leftUnitor J R M U _ x
end

universe u
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

/-- A strict section scalar presentation, constructed from the scalar cone functor.
Source: blueprint first-reduction Cones and Locality paragraphs; Stacks 014E and 03EK
(blueprint: lem-sfb-strict-section-scalar-presentation).

Proof: Conjugate the internal scalar by the exact section equivalence and its counit.
Naturality and the triangle identities identify its value on every internal module.
The left unitor sends the local tensor 1 tensor x to x. Naturality of the relative
tensor sends that tensor under the scalar to d(1) tensor x; the unitor therefore
identifies its section action with sectionScalarValue times x. The counit and its
linearity extend this formula to all section modules. Form the strict powers, cone
transitions and augmentation and descend them through derived localization.
Exact countable products ensure that the Roos functor inverts quasi-isomorphisms. -/
theorem strictSectionScalarPresentation (X : Scheme.{u})
    (d : End (Mod.regular (DerivedNakayama.integerRing l E))) :
    ∃ T : Presentation.{u + 2, u + 1, u + 1}
        (ModuleObjectRingedComparison.Modules (DerivedNakayama.integerRing l E) X),
      (∀ M : AdicCompletion.Modules l E X,
        (ModuleObjectRingedComparison.equivalence (DerivedNakayama.integerRing l E) X).functor.map
          ((DerivedNakayama.scalarOnModules l E X d).app M) =
        T.scalar.app ((ModuleObjectRingedComparison.equivalence
          (DerivedNakayama.integerRing l E) X).functor.obj M)) ∧
      (∀ (N : ModuleObjectRingedComparison.Modules (DerivedNakayama.integerRing l E) X)
        (U : X.ProEtᵒᵖ) (x : N.val.obj U),
        (T.scalar.app N).val.app U x = sectionScalarValue l E X d U • x) := by
  let e := ModuleObjectRingedComparison.equivalence.{u} (DerivedNakayama.integerRing l E) X
  let r : End (𝟭 (ModuleObjectRingedComparison.Modules
      (DerivedNakayama.integerRing l E) X)) :=
    transportScalar e (DerivedNakayama.scalarOnModules l E X d)
  let : HasSheafify (Scheme.ProEt.topology X) AddCommGrpCat.{u + 1} := inferInstance
  let : (Scheme.ProEt.topology X).WEqualsLocallyBijective AddCommGrpCat.{u + 1} :=
    smallSiteLocalEquivalences X
  let : CountableAB4Star (AdicCompletion.Modules l E X) :=
    .of_epi_π_app_zero (Mod.epiπAppZeroOfEpi
      AlgebraicGeometry.Scheme.ProEt.epi_π_app_zero_of_epi_addCommGrpCat)
  let : CountableAB4Star
      (ModuleObjectRingedComparison.Modules (DerivedNakayama.integerRing l E) X) :=
    ⟨fun I ↦ HasExactLimitsOfShape.of_codomain_equivalence (Discrete I) e⟩
  obtain ⟨T, hT⟩ := scalarPresentation.{u + 2, u + 1, u + 1} r
  refine ⟨T, ?_, ?_⟩
  · intro M
    rw [hT]
    exact transportScalar_app e _ M
  · intro N U x
    let M := e.inverse.obj N
    let c := e.counitIso.app N
    have hn := T.scalar.naturality c.hom
    have hx := congrArg (fun f ↦ (f.val.app U) ((c.inv.val.app U) x)) hn.symm
    have hc : ((c.inv ≫ c.hom).val.app U) x = x := by rw [c.inv_hom_id]; rfl
    have hr : T.scalar.app (e.functor.obj M) =
        e.functor.map ((DerivedNakayama.scalarOnModules l E X d).app M) := by
      rw [hT]
      exact (transportScalar_app e _ M).symm
    change (c.hom.val.app U) ((T.scalar.app (e.functor.obj M)).val.app U
      ((c.inv.val.app U) x)) = (T.scalar.app N).val.app U
        ((c.hom.val.app U) ((c.inv.val.app U) x)) at hx
    rw [hr] at hx
    dsimp only [e] at hx
    have hv := section_scalar_value l E X d M U ((c.inv.val.app U) x)
    erw [hv] at hx
    rw [(c.hom.val.app U).hom.map_smul] at hx
    change sectionScalarValue l E X d U • ((c.inv ≫ c.hom).val.app U) x =
      (T.scalar.app N).val.app U (((c.inv ≫ c.hom).val.app U) x) at hx
    rw [hc] at hx
    exact hx.symm
end AlgebraicGeometry.ProEtale.StrictCompletionRestriction
